(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libpcap/fuzz_pcap/lib/E2/Lib/Tac.v; 978 of its 1011 lines of code are new or changed and 2109 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/A4.v, with its module paths and module names changed; 3124 of its 3235 lines of code are new or changed and 900 lines of the source are left out. *)
(* Segment F4 of fuzz_ctrl LLVMFuzzerTestOneInput (asan, image A), stated with the official cuts of A/Prog/SlotInv.v
   (Inv_A<addr>_at): no local cut text. The two entry cuts are 0x81dfc (the return point of `jal reac_ctrl_parse`
   at 0x81df8, Inv_A81dfc_at) and 0x81e54 (the target of `beqz s2,81dbc` at 0x81dbc, the empty-record arm,
   Inv_A81e54_at). The out-of-line slow paths 0x82a2c-0x82a34 and 0x82a98-0x82aa0 are not reached.

   0x81dfc-0x81e50 (entry Inv_A81dfc_at): mv s8,a0 (s8 = the parse result t_k j) ; li a0,49 ;
     sd s9,200(s1) (the spill of the block pointer s9 = phi + 18) ; `bgeu a0,s2,81df0` leaves to Inv_A81e88_at
     when the record length is at most 49.  On the long arm it runs the instrumented check of the 1-byte load at
     s7+12 (0x81e0c-0x81e1c: the shadow byte of phi+12 is 0, because the 8-byte granule of phi+12 lies inside the
     addressable block HB(phi) with len >= 50, so neither the slow path 0x82a2c nor the error call 0x82cf8 is
     reached), reads the record byte 12 (b5_PH) and leaves to Inv_A81ea4_at when it is not 136; else the same
     check of the byte at s7+13 (0x81e2c-0x81e3c), computes (byte = 25) into a0, stores it in the spill [s1+240]
     and jumps to Inv_A81ea8_at.  The writes are the two spill words [A+200, A+208) and [A+240, A+248): FRA and
     ENT move by sl_stk_run / ent_store (f4_fra_spill), the cut skeleton by f4_keep1, and the parse output word
     u32 (fr + 176) is carried from the entry to the three exits.
   0x81e54-0x81e80 (entry Inv_A81e54_at, the record length is 0): addi a0,s7,18 ; sd a0,200(s1) ; the five frame
     shadow bytes at s3+22..s3+26 (s3 = S(fr)) are set to 0,0,0,0,4 (they mark the 36 bytes [fr+176, fr+212) of
     the frame as usable) ; mv a0,s7 ; li a1,0 ; ld a2,248(s1) = fr+176 (b5_SPILL) ; `jal reac_ctrl_parse`.  The
     segment runs THROUGH the call on the lib/A contract reac_ctrl_parse_c.v (a Section Hypothesis).  The contract
     asks for mem_inv, which no cut carries, so the call runs on the normalized memory (MemNorm.evt_normalize from
     FRA's ro_agree); its side-stack premises (fp [1%nat] and reac_ctrl_parse_tls) are built at the call from
     FRA's runtime cells (f4_fp_call, after Seg/F9.v's f9_fp_call), its window from fra_win / FRA's window
     conjunct, the bcmp cells from FRA's AsanRTInv.RT (f4_rt_cells) and REAC_CTRL_PARSE_BC from FRA's frame_AG
     conjunct.  The run ends at the return point 0x81e84, Inv_A81e84_at, with a0 = fst (ctrlparse 0 (t_g j)) = t_k j
     and the 36 output bytes at fr + 176 all zero, so u32 (fr + 176) (t_k j) holds.
   The identity record IDj at fr + 2688 (38 bytes, f4_tID_len), the fragment record FGj at fr + 2768, the
   first-fragment spills FSj at [A+88 .. A+120), the length flag [A+232] and the harness input block of FLSI
   (a heap block below stklo, f4_in_frame) are written by no instruction of F4 nor by the parse call (its writes
   are the 36 output cells, its own stack window and the class-1 side-stack bytes), so the keep lemmas move them
   with the b5_FR / b5_SPILL / FLSI cells.  F4 produces b5_F17 ([A+200] = phi + 18) at its four exits from its own
   stores 0x81e04 (long arm) and 0x81e58 (empty arm, which the shadow stores and the call miss), and b5_W240 at
   0x81ea8 from the store 0x81e4c.  b5_PF (slot push 14, the memcpy / parse / compare-spill facts) is carried
   from 0x81dfc to its three exits across the spill words (f4_pf_sp: every cell it names lies below A + 200) and
   is empty at 0x81e84 (flen j = 0, so t_8819 j is false, f4_8819_0). *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable Require Import YK11 YM05 YK0o YK0s YK15 YP09 YO0f YO0d YO09
  YL00 YL0g YL0i YI14 YI16 YL01 YM06.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import Img0 AsanRT AsanRTInv AsanRTFacts PContract MemNorm AsanLift KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Contract FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcModel RcLib RcParse RcAsanLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import memcmp_c bcmp_wrap_c asan_stack_malloc_c
  RcAsanFP reac_ctrl_parse_c reac_ctrl_kind_name_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import SlotModel SlotInv RcAsanFPLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg Require Import Tac_slot Tac_b5 Tac_fs.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require RcIdentModel.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL Require Tac Bytes.
Import YK11.
Open Scope Z_scope.

Module AC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Contract.
Module AF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.FrameAPI.
Module LE := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Exec.

Section S.
Context {fx : YK11.FPState} {LS : lib_shape} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AC.AsanAllocAPI AC.ASYMS AsanRTInv.RT.
Context {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.
(* The callee contract (lib/A/Prog/reac_ctrl_parse_c.v), a Section Hypothesis. *)
Hypothesis HPARSE : reac_ctrl_parse_contract.

(* ---------------- the generated laws and frame_facts, each taken apart once ----------------
   a Theorem Labs lane's rule for its generated laws (append-only at every nesting level; generation N+1 brings named
   sub-projections): this file takes each law's /\ list apart in ONE lemma below (an f4_law_ lemma), which returns
   only the facts the file uses, and every site uses that lemma. No pattern names a binder of a law's list: the list is
   split by decompose, and f4_law_fact closes each returned fact by its type, directly or (a fact under a binder)
   from the split instance of the hypothesis under the same binder. A conjunct that a later generation appends, at
   any level, is left unused. *)
Ltac f4_law_fact :=
  first [ assumption
        | let x := fresh "x" in let Hx := fresh "Hx" in intros x Hx;
          match goal with P : forall _, _ -> _ |- _ =>
            let Q := fresh "Q" in pose proof (P x Hx) as Q; decompose [and] Q;
            repeat match goal with |- _ /\ _ => apply conj end; assumption
          end ].
Ltac f4_law_close := repeat match goal with |- _ /\ _ => apply conj end; f4_law_fact.

Lemma f4_law_blocks : forall H mem md p n,
  AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) H mem md -> In (p, n) H ->
  p mod 16 = 0 /\ 4096 <= p /\ p + n <= AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md /\
  (forall a, p <= a < p + n -> app_mem a) /\ (forall a, p <= a < p + n -> ~ AC.a_in_fs AC.ASYMS mem a).
Proof.
  intros H mem md p n HAH HIn.
  pose proof (AC.a_laws_blocks _ _ _ _ _ (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) _ _ _ _ _ HAH HIn) as L.
  decompose [and] L. f4_law_close.
Qed.

Lemma f4_law_store : forall H mem mem' md,
  AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) H mem md ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ AC.a_store_ok H (AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md) a ->
     mem' (Z_to_bv 64 a) = mem (Z_to_bv 64 a)) ->
  (forall a, 0 <= a < 2 ^ 64 -> writable_at rsegs mem a -> writable_at rsegs mem' a) ->
  AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) H mem' md /\
  (forall a, AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) H mem' md a <->
             AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) H mem md a) /\
  AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem' md = AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md /\
  AC.aa_stkhi AC.ASYMS AsanRTInv.RT (APIf rc) mem' md = AC.aa_stkhi AC.ASYMS AsanRTInv.RT (APIf rc) mem md.
Proof.
  intros H mem mem' md HAH Hagree Hwm.
  pose proof (AC.a_laws_store _ _ _ _ _ (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) _ _ _ _ HAH Hagree Hwm) as L.
  decompose [and] L. f4_law_close.
Qed.

Lemma f4_law_fs_store : forall H mem mem' md FS,
  AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) H mem md ->
  word_mem rsegs mem (AC.as_tp AC.ASYMS) FS -> 0 <= FS < 2 ^ 64 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ AC.a_store_ok H (AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md) a ->
     ~ (FS <= a < FS + AC.FS_SIZE) -> ~ (exists b, FS <= b < FS + AC.FS_SIZE /\ a = shadow_addr b) ->
     mem' (Z_to_bv 64 a) = mem (Z_to_bv 64 a)) ->
  (forall a, 0 <= a < 2 ^ 64 -> writable_at rsegs mem a -> writable_at rsegs mem' a) ->
  AC.a_fs_ok mem' FS ->
  AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) H mem' md /\
  (forall a, AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) H mem' md a <->
             AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) H mem md a) /\
  AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem' md = AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md /\
  AC.aa_stkhi AC.ASYMS AsanRTInv.RT (APIf rc) mem' md = AC.aa_stkhi AC.ASYMS AsanRTInv.RT (APIf rc) mem md.
Proof.
  intros H mem mem' md FS HAH Htp HFS Hagree Hwm Hok.
  pose proof (AC.a_laws_fs_store _ _ _ _ _ (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) _ _ _ _ _ HAH Htp HFS
                Hagree Hwm Hok) as L.
  decompose [and] L. f4_law_close.
Qed.

Lemma f4_law_fs_place : forall H mem md b,
  AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) H mem md ->
  word_mem rsegs mem (AC.as_tp AC.ASYMS) b -> 0 <= b < 2 ^ 64 ->
  AC.GT <= b /\ b + AC.FS_SIZE <= AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md /\ b mod 4096 = 0 /\
  (forall a, b <= a < b + AC.FS_SIZE -> app_mem a).
Proof.
  intros H mem md b HAH Htp Hb.
  pose proof (AC.a_laws_fs_place _ _ _ _ _ (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) _ _ _ _ HAH Htp Hb) as L.
  decompose [and] L. f4_law_close.
Qed.

(* a_laws_fs_state with a_fs_ok, its first conjunct. *)
Lemma f4_law_fs_state : forall H mem md FS,
  AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) H mem md ->
  word_mem rsegs mem (AC.as_tp AC.ASYMS) FS -> 0 <= FS < 2 ^ 64 ->
  (forall a, FS <= a < FS + AC.FS_SIZE -> writable_at rsegs mem a) /\
  (forall a, FS <= a < FS + AC.FS_SIZE -> exists b, mbyte rsegs mem a = Some b) /\
  word_mem rsegs mem (FS + 88) 20 /\ mbyte rsegs mem (FS + 96) = Some (Z_to_bv 8 0) /\
  (forall c, (c <= 10)%nat -> exists h, word_mem rsegs mem (AC.a_fs_hint FS c) h) /\
  (forall c j, (c <= 10)%nat -> 0 <= j < AC.a_fs_M c ->
     mbyte rsegs mem (AC.a_fs_flag FS c j) = Some (Z_to_bv 8 0) \/
     mbyte rsegs mem (AC.a_fs_flag FS c j) = Some (Z_to_bv 8 1)) /\
  (exists DB, 0 <= DB < 2 ^ 64 /\ word_mem rsegs mem (AC.as_tp AC.ASYMS + 8) DB /\ DB <> 0 /\
     word_mem rsegs mem (DB + 24) (AC.as_tp AC.ASYMS) /\
     (forall a, DB + 24 <= a < DB + 32 -> app_mem a) /\
     (forall a, DB + 24 <= a < DB + 32 -> a < AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md) /\
     (forall a, DB + 24 <= a < DB + 32 -> ~ AC.a_in_fs AC.ASYMS mem a)) /\
  (forall C T, word_mem rsegs mem RT_TSDMAIN C -> 0 <= C < 2 ^ 64 -> word_mem rsegs mem (C + 152) T ->
     0 <= T < 2 ^ 64 -> forall i, 0 <= i < 16 -> app_mem (T + 48 + i)).
Proof.
  intros H mem md FS HAH Htp HFS.
  pose proof (AC.a_laws_fs_state _ _ _ _ _ (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) _ _ _ _ HAH Htp HFS) as L.
  unfold AC.a_fs_ok in L. decompose [and] L.
  match goal with E : ex _ |- _ => destruct E as (DB & EB) end.
  decompose [and] EB.
  repeat match goal with |- _ /\ _ => apply conj end;
    (match goal with |- ex _ => exists DB | _ => idtac end); f4_law_close.
Qed.

Lemma f4_law_thread : forall H mem md,
  AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) H mem md ->
  exists C T, word_mem rsegs mem RT_TSDMAIN C /\ 0 < C < 2 ^ 64 /\ 0 < T < 2 ^ 64 /\
    word_mem rsegs mem (C + 152) T /\
    (forall i, 0 <= i < 8 -> AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) H mem md (C + 152 + i)) /\
    (forall i, 0 <= i < 8 -> app_mem (C + 152 + i)) /\
    (forall i, 0 <= i < 16 -> AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) H mem md (T + 48 + i)) /\
    (forall i, 0 <= i < 16 -> exists b, mbyte rsegs mem (T + 48 + i) = Some b).
Proof.
  intros H mem md HAH.
  pose proof (AC.a_laws_thread _ _ _ _ _ (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) _ _ _ HAH) as L.
  decompose [and] L.
  match goal with E : ex _ |- _ => destruct E as (C & T & EB) end.
  exists C, T. decompose [and] EB. f4_law_close.
Qed.

Lemma f4_law_not_owned : forall H mem md a,
  AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) H mem md ->
  AC.a_in_fs AC.ASYMS mem a \/ AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md <= a < APPMEM_END ->
  ~ AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) H mem md a.
Proof.
  intros H mem md a HAH Ha.
  pose proof (AC.a_laws_not_owned _ _ _ _ _ (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) _ _ _ a HAH) as L.
  pose proof (L ltac:(tauto)) as Q. decompose [and] Q. assumption.
Qed.

(* frame_facts (a Theorem Labs lane's, SlotInv.v), taken apart once: the image's segments and the three sink-cell addresses. *)
Lemma f4_ff : ms_segs B = rsegs /\ @sk_ofl_head SH = 0x5fbf08 /\ @sk_ofl_lock SK = 0x5fbf00 /\
  @sk_threaded SK = 0x5fbaa0 + 1.
Proof.
  destruct FF as (SEGS & _ & _ & _ & Hhead & Hlock & Hthr & _).
  exact (conj SEGS (conj Hhead (conj Hlock Hthr))).
Qed.

(* ---------------- kit ---------------- *)

(* An image constant of a generated or callee file (the thread pointer, the kind-name table, the common-flags
   cells), read off its own definition: the proof uses the value without pinning the address, so it holds on
   every image the generated files are made for. *)
Ltac f4_imgc H c := let v := eval vm_compute in c in assert (H : c = v) by (vm_compute; reflexivity).

(* Rewrite a known register slot `getr regs r` to its carried concrete value, from H : rg regs r v. *)
Ltac f4_subst_slot H :=
  let HH := fresh in pose proof H as HH; unfold rg in HH; rewrite HH; clear HH.

Lemma f4_id : forall a b, 0 <= a < 2 ^ 64 -> 0 <= b < 2 ^ 64 -> Z_to_bv 64 a = Z_to_bv 64 b -> a = b.
Proof.
  intros a b Ha Hb E. apply (f_equal (@bv_unsigned 64)) in E.
  rewrite !MState.unsigned_lit in E by lia. exact E.
Qed.

(* An interval of high memory is application memory. *)
Lemma f4_app_ivl : forall lo hi, HIGHMEM_BEG <= lo -> hi <= APPMEM_END -> app_ivl lo hi.
Proof. intros lo hi H1 H2 a Ha. unfold app_mem. right. lia. Qed.

(* The record length is a sum of byte values, so it is never negative. *)
Lemma f4_flen_nn : forall g j, 0 <= flen g j.
Proof.
  intros g j. unfold flen, t_len, f_len, f_L, f_h.
  assert (Hb : forall k, 0 <= inb (g_in g) k) by (intros k; unfold inb; exact (proj1 (bv_unsigned_in_range 8 _))).
  pose proof (Hb (fc (g_in g) j)). pose proof (Hb (fc (g_in g) j + 1)).
  destruct (2 <=? f_left (g_in g) (fc (g_in g) j)); lia.
Qed.

(* An 8-byte cell survives a write whose footprint misses it. *)
Lemma f4_q64_keep : forall W m m' a v, q64 m a v -> Frame.munch W m m' ->
  (forall x, a <= x < a + 8 -> Frame.outside W x) -> q64 m' a v.
Proof.
  intros W m m' a v H MU HW. unfold q64 in *.
  eapply fl_bytes; [exact H | exact MU |]. rewrite length_le8. intros x Hx. apply HW. lia.
Qed.

(* A 4-byte cell survives a write whose footprint misses it. *)
Lemma f4_u32_keep : forall W m m' a v, u32 m a v -> Frame.munch W m m' ->
  (forall x, a <= x < a + 4 -> Frame.outside W x) -> u32 m' a v.
Proof.
  intros W m m' a v H MU HW. unfold u32 in *.
  eapply fl_bytes; [exact H | exact MU |]. rewrite length_le4. intros x Hx. apply HW. lia.
Qed.

(* A thread word survives a write whose footprint misses its eight bytes, and is read back unchanged. *)
Lemma f4_word_eq : forall W m m' a, Frame.munch W m m' ->
  (forall x, a <= x < a + 8 -> Frame.outside W x) -> 0 <= a -> a + 8 <= 2 ^ 64 ->
  forall v, word_mem rsegs m a v <-> word_mem rsegs m' a v.
Proof.
  intros W m m' a MU HW Ha Hhi v.
  assert (HE : forall k, (k < 8)%nat -> m' (Z_to_bv 64 (a + Z.of_nat k)) = m (Z_to_bv 64 (a + Z.of_nat k))).
  { intros k Hk. apply MU. rewrite MState.unsigned_lit by lia. apply HW; lia. }
  split; intros H k Hk; pose proof (H k Hk) as Hb; unfold mbyte in *.
  - rewrite (HE k Hk). exact Hb.
  - rewrite (HE k Hk) in Hb. exact Hb.
Qed.

(* A frame-loop spill word survives a write that misses its eight bytes. The spill's own existential base names
   the same A as FRA: the cell is inside [A, A + 416) and A is far below 2 ^ 64. *)
Lemma f4_spill_keep : forall regs regs' A off v m m' W,
  spill regs m off v -> rg regs 9 A -> 0 <= A < 2 ^ 64 -> A + 416 <= APPMEM_END -> 0 <= off <= 408 ->
  getr regs' 9 = getr regs 9 -> Frame.munch W m m' ->
  (forall x, A + off <= x < A + off + 8 -> Frame.outside W x) ->
  spill regs' m' off v.
Proof.
  intros regs regs' A off v m m' W HS H9 HA HAE Hoff E9 MU HW.
  destruct HS as (A' & H9' & Hq).
  assert (HKa : APPMEM_END = 140737488355328) by (vm_compute; reflexivity).
  assert (HP : 2 ^ 64 = 18446744073709551616) by (vm_compute; reflexivity).
  assert (Hqb : 0 <= A' + off /\ A' + off + Z.of_nat (length (le8 (Z_to_bv 64 v))) <= 2 ^ 64)
    by (unfold q64 in Hq; exact (bytes_at_bound rsegs m (A' + off) _ Hq)).
  rewrite length_le8 in Hqb.
  assert (HAA : A' = A).
  { pose proof (rg_eq64 regs 9 A' A H9' H9) as Hm.
    assert (Hdz : (A' - A) mod 2 ^ 64 = 0).
    { rewrite Zminus_mod, Hm, Z.sub_diag. apply Zmod_0_l. }
    destruct (proj1 (Zmod_divides (A' - A) (2 ^ 64) ltac:(lia)) Hdz) as (q & Hq2).
    rewrite HP in Hq2. lia. }
  subst A'.
  exists A. split; [unfold rg in *; rewrite E9; exact H9|].
  exact (f4_q64_keep W m m' (A + off) v Hq MU HW).
Qed.

(* ADDR-KEEP for a write list that may touch the shadow: a block stays addressable when the shadow bytes of its
   own granules are outside the writes. *)
Lemma f4_addr_keep : forall W m m' p n, addressable m p n -> Frame.munch W m m' ->
  (forall i, 0 <= i < n -> Frame.outside W (shadow_addr (p + i))) -> addressable m' p n.
Proof.
  intros W m m' p n (H1 & H2 & H3 & H) MU HW. split; [lia|]. split; [lia|]. split; [lia|].
  intros i Hi. destruct (H i Hi) as (Hap & b & Hb & Hok). split; [exact Hap|]. exists b. split; [|exact Hok].
  pose proof (in_shadow_range (shadow_addr (p + i)) (shadow_of_app _ Hap)) as HR.
  unfold mrd in *. rewrite (MU (wa (shadow_addr (p + i)))); [exact Hb|].
  rewrite Mem.wa_unsigned by lia. exact (HW i Hi).
Qed.

(* Shadow geometry. *)
Lemma f4_sh_lo : forall a, 0 <= a -> LOWMEM_END <= shadow_addr a.
Proof. intros a Ha. unfold shadow_addr, ASAN_K, LOWMEM_END. assert (0 <= a / 8) by (apply Z.div_pos; lia). lia. Qed.

Lemma f4_sh_hi : forall a, 0 <= a < APPMEM_END -> shadow_addr a < HIGHMEM_BEG.
Proof.
  intros a Ha. unfold shadow_addr, ASAN_K, HIGHMEM_BEG.
  assert (D : a / 8 < 17592186044416) by (apply Z.div_lt_upper_bound; [lia | unfold APPMEM_END in Ha; lia]).
  lia.
Qed.

Lemma f4_sh_hi_le : forall a, 0 <= a <= APPMEM_END -> shadow_addr a <= HIGHMEM_BEG.
Proof.
  intros a Ha. unfold shadow_addr, ASAN_K, HIGHMEM_BEG.
  assert (D : a / 8 <= 17592186044416) by (apply Z.div_le_upper_bound; [lia | unfold APPMEM_END in Ha; lia]).
  lia.
Qed.

Lemma f4_sh_mono : forall x y, x <= y -> shadow_addr x <= shadow_addr y.
Proof. intros x y H. unfold shadow_addr. pose proof (Z.div_le_mono x y 8 ltac:(lia) H). lia. Qed.

(* A strict shadow comparison that only needs y 8-aligned. *)
Lemma f4_sh_lt2 : forall x y, 0 <= x -> x < y -> y mod 8 = 0 -> shadow_addr x < shadow_addr y.
Proof.
  intros x y H0 H Hm. unfold shadow_addr.
  assert (x / 8 < y / 8).
  { apply Z.div_lt_upper_bound; [lia|]. Z.div_mod_to_equations. lia. }
  lia.
Qed.

(* The shadow byte of a frame byte from fr + 216 on is one of the frame's shadow bytes 27..391. *)
Lemma f4_sh_frame : forall fr x, fr mod 8 = 0 -> fr + 216 <= x < fr + FRAME_BYTES ->
  Sfr fr + 27 <= shadow_addr x < Sfr fr + FRAME_SHADOW.
Proof. pose proof FRAME_BYTES_val as HFBval. pose proof FRAME_SHADOW_val as HFSval. intros fr x Hm Hx. unfold Sfr, shadow_addr. Z.div_mod_to_equations. lia. Qed.

(* ---- the frame records of the turn ---- *)

(* The identity record of every turn is ID_SIZE = 38 bytes: ID0 is, and both ingests of a turn (the reply arm's
   rp_id and the fragment arm's fg_id) keep the length (RcIdentModel.ING_length). *)
Lemma f4_tID_len : forall inp j, length (t_ID inp j) = 38%nat.
Proof.
  intros inp j. unfold t_ID. induction j as [|j IH].
  - cbn [fst_at]. unfold fs0. cbn [fs_id]. unfold RcIdentModel.ID0. rewrite repeat_length. reflexivity.
  - cbn [fst_at]. unfold turn. cbv zeta.
    assert (H1 : length (rp_id (fs_id (fst_at inp j)) (t_len inp j) (t_g inp j)) = 38%nat).
    { unfold rp_id. match goal with |- context [if ?c then _ else _] => destruct c end;
        [exact (RcIdentModel.ING_length _ _ _ IH) | exact IH]. }
    assert (H2 : forall st, length (fg_id (rp_id (fs_id (fst_at inp j)) (t_len inp j) (t_g inp j))
                                   (t_len inp j) st (t_g inp j)) = 38%nat).
    { intros st. unfold fg_id. match goal with |- context [if ?c then _ else _] => destruct c end;
        [exact (RcIdentModel.ING_length _ _ _ H1) | exact H1]. }
    destruct (f_opens (t_len inp j) (t_g inp j)); cbn [fs_id]; apply H2.
Qed.

(* The identity record IDj (38 bytes at fr + 2688) survives a write that misses those bytes. *)
Lemma f4_idj_keep : forall g fr j W m m', IDj g fr j m -> Frame.munch W m m' ->
  (forall x, fr + 2688 <= x < fr + 2726 -> Frame.outside W x) -> IDj g fr j m'.
Proof.
  intros g fr j W m m' (Hb & Hok) MU HW. split; [|exact Hok].
  unfold IDBe in *. apply (fl_bytes W m m' (fr + 2688) _ Hb MU).
  rewrite f4_tID_len. intros x Hx. apply HW. lia.
Qed.

(* The harness input block (its bytes and its addressability) survives a write that misses the block's bytes
   and their shadow bytes, when the block exists (for n = 0 both facts are empty). *)
Lemma f4_in_keep : forall g W m m', Frame.munch W m m' ->
  (0 < g_n g -> forall x, g_p g <= x < g_p g + g_n g -> Frame.outside W x /\ Frame.outside W (shadow_addr x)) ->
  bytes_at rsegs m (g_p g) (g_in g) -> addressable m (g_p g) (g_n g) ->
  bytes_at rsegs m' (g_p g) (g_in g) /\ addressable m' (g_p g) (g_n g).
Proof.
  intros g W m m' MU HW Hb Ha.
  destruct (Z_lt_le_dec 0 (g_n g)) as [Hn|Hn].
  - split.
    + apply (fl_bytes W m m' (g_p g) (g_in g) Hb MU). rewrite <- g_n_len.
      intros x Hx. exact (proj1 (HW Hn x Hx)).
    + apply (f4_addr_keep W m m' (g_p g) (g_n g) Ha MU).
      intros i Hi. exact (proj2 (HW Hn (g_p g + i) ltac:(lia))).
  - assert (Hl : length (g_in g) = 0%nat) by (pose proof (g_n_len g); lia).
    split.
    + apply (fl_bytes W m m' (g_p g) (g_in g) Hb MU). rewrite Hl. intros x Hx. lia.
    + apply (f4_addr_keep W m m' (g_p g) (g_n g) Ha MU). intros i Hi. lia.
Qed.

(* ---- base-given drops (the bcmp cells, the spill area and the frame body are byte-backed) ---- *)

(* One byte of a carried byte list, as a one-byte cell. *)
Lemma f4_byte1 : forall m a bs (i : nat) b, bytes_at rsegs m a bs -> nth_error bs i = Some b ->
  bytes_at rsegs m (a + Z.of_nat i) [b].
Proof.
  intros m a bs i b (H0 & H1 & H) Hn.
  assert (Hi : (i < length bs)%nat) by (apply nth_error_Some; rewrite Hn; discriminate).
  split; [lia|]. split; [cbn [length]; lia|].
  intros k Hk. cbn [length] in Hk. destruct k as [|k]; [|lia].
  cbn [nth_error]. replace (a + Z.of_nat i + Z.of_nat 0) with (a + Z.of_nat i) by lia.
  rewrite H by exact Hi. exact Hn.
Qed.

(* A prefix of a carried byte list is carried at the same address (b5_PF states the record's 38 bytes and its
   six-byte compare operands with `<= length`, and a transport across a write needs an exact length). *)
Lemma f4_bytes_first : forall m a bs k, bytes_at rsegs m a bs -> bytes_at rsegs m a (firstn k bs).
Proof.
  intros m a bs k (H0 & H1 & H).
  assert (Hl : (length (firstn k bs) <= length bs)%nat) by (rewrite length_firstn; lia).
  split; [exact H0|]. split; [lia|].
  intros i Hi. rewrite H by lia.
  rewrite <- (firstn_skipn k bs) at 1. apply nth_error_app1. exact Hi.
Qed.

(* memcmp_model reads only the first n bytes of each list. *)
Lemma f4_mcmp_firstn : forall n l r, SFA.memcmp_model (firstn n l) (firstn n r) n = SFA.memcmp_model l r n.
Proof.
  induction n as [|n IH]; intros l r; [reflexivity|].
  destruct l as [|a l]; destruct r as [|b r]; cbn [firstn SFA.memcmp_model]; try reflexivity.
  destruct (bv_unsigned a =? bv_unsigned b); [apply IH | reflexivity].
Qed.

(* The frame body t_phi j is a firstn of flen j bytes, so it has at most flen j bytes. *)
Lemma f4_tphi_len : forall g j, Z.of_nat (length (t_phi (g_in g) j)) <= flen g j.
Proof.
  intros g j. pose proof (f4_flen_nn g j) as H0. unfold flen, t_len, t_phi, f_phi in *.
  rewrite length_firstn, Nat2Z.inj_min, Z2Nat.id by lia. lia.
Qed.

(* The metadata byte of an app byte lies below every address from HIGHMEM_BEG on. *)
Lemma f4_sh_below : forall x A, 0 <= x < APPMEM_END -> HIGHMEM_BEG <= A -> Z.shiftr x 3 + ASAN_K + 1 <= A.
Proof.
  intros x A Hx HA. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
  pose proof (f4_sh_hi x Hx) as H. unfold shadow_addr in H. lia.
Qed.

(* An empty record has no 0x88 0x19 header (t_big is false). *)
Lemma f4_8819_0 : forall g j, flen g j = 0 -> t_8819 (g_in g) j = false.
Proof. intros g j H. unfold t_8819, t_big. unfold flen in H. rewrite H. reflexivity. Qed.

(* The runtime cells the bcmp wrapper of reac_ctrl_parse reads, from FRA's AsanRTInv.RT alone: the real
   bcmp / memcmp addresses, the GOT word of the CF table and its two flag bytes. *)
Lemma f4_rt_cells : forall sp m md, AsanRTInv.RT sp m md ->
  bytes_at rsegs m REAL_BCMP (le8 (wa BCMP)) /\ bytes_at rsegs m REAL_MEMCMP (le8 (wa MEMCMP)) /\
  bytes_at rsegs m GOT_CF (le8 (wa CF)) /\
  bytes_at rsegs m (CF + 254) [Z_to_bv 8 1] /\ bytes_at rsegs m (CF + 255) [Z_to_bv 8 1].
Proof.
  intros sp m md HRT.
  pose proof (AsanRTInv.RT_real_cells sp m md HRT) as HR.
  pose proof (AsanRTInv.RT_cf_cells sp m md HRT) as (Hg & _ & _ & _ & _ & _ & H240 & _).
  split; [exact (AsanRTInv.real_cell_of m REAL_BCMP BCMP HR ltac:(vm_compute; reflexivity))|].
  split; [exact (AsanRTInv.real_cell_of m REAL_MEMCMP MEMCMP HR ltac:(vm_compute; reflexivity))|].
  split; [exact Hg|].
  split.
  - pose proof (f4_byte1 m (RT_CF + 240) _ 14 (Z_to_bv 8 1) H240 eq_refl) as HH.
    replace (RT_CF + 240 + Z.of_nat 14) with (CF + 254) in HH by (unfold RT_CF, CF; lia). exact HH.
  - pose proof (f4_byte1 m (RT_CF + 240) _ 15 (Z_to_bv 8 1) H240 eq_refl) as HH.
    replace (RT_CF + 240 + Z.of_nat 15) with (CF + 255) in HH by (unfold RT_CF, CF; lia). exact HH.
Qed.

(* A byte range that `stk` covers is writable in the `wr_at` form the callee contracts use. *)
Lemma f4_wr : forall m lo hi a n, stk rsegs m lo hi -> lo <= a -> 0 <= n -> a + n <= hi -> wr_at rsegs m a n.
Proof.
  intros m lo hi a n (H0 & H1 & H) Hlo Hn Hhi.
  split; [lia|]. split; [lia|]. intros i Hi. exact (proj1 (H (a + i) ltac:(lia))).
Qed.

(* Any sub-range of the frame body is byte-backed and writable: FLSI's `stk fr (fr + 3136)`. *)
Lemma f4_frame_stk : forall m fr lo hi, stk rsegs m fr (fr + FRAME_BYTES) ->
  fr <= lo -> lo <= hi -> hi <= fr + FRAME_BYTES -> stk rsegs m lo hi.
Proof. pose proof FRAME_BYTES_val as HFBval. pose proof FRAME_SHADOW_val as HFSval.
  intros m fr lo hi (H0 & H1 & H) Hlo Hm Hhi.
  split; [lia|]. split; [lia|]. intros a Ha. apply H. lia.
Qed.

(* Any sub-range of the 416-byte prologue save area [A, A + 416) is byte-backed and writable: it lies inside
   FRA's entry-anchored slot window, because g_S g - 4096 < sp <= A and A + 416 <= g_S g. *)
Lemma f4_spill_stk : forall g fr hb regs mem md A lo hi,
  FRA B APIf ra g fr hb regs mem md -> rg regs 9 A -> 0 <= A < 2 ^ 64 ->
  A <= lo -> lo <= hi -> hi <= A + 416 -> stk rsegs mem lo hi.
Proof. pose proof FRAME_BYTES_val as HFBval. pose proof FRAME_SHADOW_val as HFSval.
  intros g fr hb regs mem md A lo hi HFRA Hr9 HA Hlo Hmid Hhi.
  pose proof HFRA as (A' & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9' & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hsp & Hfa & HA416 & HS4 & HAPP &
    Hspill & Hsel & Hfr24 & Hloc & Hhdr1 & Hhdr2 & Hsh & Hwin & _).
  assert (HSS : AF.SLOT_STACK = 1048576) by reflexivity.
  destruct Hwin as (Hb0 & Hb1 & Hst).
  assert (HA' : 0 <= A' < 2 ^ 64) by lia.
  assert (EA : A = A').
  { pose proof (rg_eq64 regs 9 A A' Hr9 Hr9') as Hm.
    rewrite (Z.mod_small A (2 ^ 64)) in Hm by lia. rewrite (Z.mod_small A' (2 ^ 64)) in Hm by lia. exact Hm. }
  subst A'.
  split; [lia|]. split; [lia|]. intros a Ha. apply Hst. lia.
Qed.

(* Where the harness input block lies (when it exists): a live heap block (a_laws_blocks), so in application
   memory below stklo and off the side stack, and therefore apart from the frame on both frame arms (the real-stack
   frame is above stklo, the side-stack frame is in the FakeStack). *)
Lemma f4_in_frame : forall g fr hb regs mem md,
  FRA B APIf ra g fr hb regs mem md -> f1_IN g mem -> 0 < g_n g ->
  forall x, g_p g <= x < g_p g + g_n g ->
    app_mem x /\ x < AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md /\
    (forall FS, word_mem rsegs mem (AC.as_tp AC.ASYMS) FS -> 0 <= FS < 2 ^ 64 -> ~ (FS <= x < FS + AC.FS_SIZE)) /\
    (x < fr \/ fr + FRAME_BYTES <= x).
Proof. pose proof FRAME_BYTES_val as HFBval. pose proof FRAME_SHADOW_val as HFSval.
  intros g fr hb regs mem md HFRA (HIn & _ & _) Hn x Hx.
  pose proof HFRA as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA416 & HS4 & HAPP &
    Hspill & Hsel & Hfr24 & Hloc & _).
  pose proof (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) as LAWS.
  assert (HIn' : In (g_p g, g_n g) (hb ++ g_H g)) by (apply in_or_app; right; exact (HIn Hn)).
  destruct (f4_law_blocks _ mem md (g_p g) (g_n g) HAH HIn') as (_ & _ & Hst & Happb & Hnfsb).
  pose proof (Happb x Hx) as Hxapp. pose proof (Hnfsb x Hx) as Hxnfs.
  assert (HnFS : forall FS, word_mem rsegs mem (AC.as_tp AC.ASYMS) FS -> 0 <= FS < 2 ^ 64 ->
                   ~ (FS <= x < FS + AC.FS_SIZE)).
  { intros FS Hw HFS HC. apply Hxnfs. exists FS. split; [exact HFS | split; [exact Hw | exact HC]]. }
  split; [exact Hxapp|]. split; [lia|]. split; [exact HnFS|].
  destruct (Z_lt_le_dec x fr) as [Hlt|Hge]; [left; exact Hlt|].
  destruct (Z_lt_le_dec x (fr + FRAME_BYTES)) as [Hlt2|Hge2]; [|right; exact Hge2].
  exfalso. destruct Hloc as [(_ & _ & Hreal) | (_ & _ & Hfs & _)].
  - pose proof (Hreal x ltac:(lia)). lia.
  - apply Hxnfs. exact (Hfs x ltac:(lia)).
Qed.

(* v1.9: the first fragment's body (fs_body, the bytes FSb names at fr + 2880) is empty or a prefix of a 50-byte
   frame from byte 27 on, so it has at most 23 bytes. *)
Lemma f4_fs_body_len : forall inp j, (length (fs_body (fst_at inp j)) <= 23)%nat.
Proof.
  intros inp j. induction j as [|j IH]; [cbn; lia|].
  rewrite fst_at_S. unfold turn. cbv zeta.
  destruct (f_opens (t_len inp j) (t_g inp j)); cbn [fs_body]; [|exact IH].
  assert (Hg : length (t_g inp j) = 50%nat) by (unfold t_g; apply fr50_length).
  rewrite length_firstn, length_skipn, Hg. apply Nat.le_min_r.
Qed.

(* Everything the span's cut skeleton carries (HB, FLSI, LK and the carry b5_C) and the identity record IDj,
   across a write W that keeps the cells they name: the record block and its shadow, the frame body outside the
   parse output cells [fr + 176, fr + 212) (whose bytes stay present), the frame's shadow bytes from 27 on, the
   spills at [A + 32, A + 200), [A + 208, A + 240) and [A + 248, A + 280), the image below GT with its shadow
   (the thread pointer words, the kind-name table), and the harness input block with its shadow. *)
Lemma f4_keepg : forall g j phi fr A regs regs' mem mem' md W,
  FRA B APIf ra g fr (hb1 phi (AC.a_size (flen g j))) regs mem md ->
  HB mem phi (flen g j) -> FLSI g j fr regs mem -> LK g fr j regs mem ->
  b5_C g j phi fr regs mem -> IDj g fr j mem ->
  rg regs 9 A -> 0 <= A < 2 ^ 64 ->
  Frame.munch W mem mem' -> Frame.wmono rsegs mem mem' ->
  (forall x, phi <= x < phi + AC.a_size (flen g j) -> Frame.outside W x) ->
  (forall i, 0 <= i < AC.a_size (flen g j) -> Frame.outside W (shadow_addr (phi + i))) ->
  (forall x, fr <= x < fr + 176 \/ fr + 212 <= x < fr + FRAME_BYTES -> Frame.outside W x) ->
  (forall x, fr <= x < fr + FRAME_BYTES -> Frame.outside W x \/ exists b, mrd rsegs mem' (wa x) = Some b) ->
  (forall x, Sfr fr + 27 <= x < Sfr fr + FRAME_SHADOW -> Frame.outside W x) ->
  (forall x, A + 32 <= x < A + 200 \/ A + 208 <= x < A + 240 \/ A + 248 <= x < A + 280 -> Frame.outside W x) ->
  (forall x, 0 <= x < AC.GT -> Frame.outside W x /\ Frame.outside W (shadow_addr x)) ->
  (0 < g_n g -> forall x, g_p g <= x < g_p g + g_n g -> Frame.outside W x /\ Frame.outside W (shadow_addr x)) ->
  getr regs' 2 = getr regs 2 -> getr regs' 9 = getr regs 9 -> getr regs' 18 = getr regs 18 ->
  getr regs' 21 = getr regs 21 -> getr regs' 23 = getr regs 23 ->
  HB mem' phi (flen g j) /\ FLSI g j fr regs' mem' /\ LK g fr j regs' mem' /\
  b5_C g j phi fr regs' mem' /\ IDj g fr j mem'.
Proof. pose proof FRAME_BYTES_val as HFBval. pose proof FRAME_SHADOW_val as HFSval.
  intros g j phi fr A regs regs' mem mem' md W HFRA HHB HFLSI HLK HC HID H9 HA MU WM
    Hphi Hphish Hfr Hfrst Hfrsh Hsp Himg Hinp E2 E9 E18 E21 E23.
  pose proof HFRA as HF.
  destruct HF as (A0 & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA416 & HS4 & HAPP &
    Hspill & Hsel & Hfr24 & Hloc & Hhdr1 & Hhdr2 & Hsh & Hwin & Hsaved & Herrno & HAG & HWA &
    HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive).
  assert (HKa : APPMEM_END = 140737488355328) by (vm_compute; reflexivity).
  assert (HKg : AC.GT = 6283264) by (vm_compute; reflexivity).
  assert (HKs : AF.SLOT_STACK = 1048576) by (vm_compute; reflexivity).
  assert (HKh : HIGHMEM_BEG = 17594333495296) by (vm_compute; reflexivity).
  assert (HA0r : 0 <= A0 < 2 ^ 64).
  { pose proof Hwin as HW0. unfold stk in HW0. destruct HW0 as (Hw0 & Hw1 & _). lia. }
  assert (HAeq : A = A0).
  { apply f4_id; [lia | lia |]. unfold rg in H9, Hr9. rewrite <- H9. exact Hr9. }
  subst A0.
  assert (Hfr8 : fr mod 8 = 0) by (clear - Hfrm; Z.div_mod_to_equations; lia).
  assert (Htp0 : 0 <= AC.as_tp AC.ASYMS) by (unfold AC.as_tp, AC.ASYMS; cbn; lia).
  assert (Htp1 : AC.as_tp AC.ASYMS + 16 <= AC.GT) by (unfold AC.as_tp, AC.ASYMS, AC.GT; cbn; lia).
  f4_imgc Hkn KIND_NAME.
  assert (Hknl : (length kind_name_bytes <= 4096)%nat) by (vm_compute; lia).
  assert (Himg1 : forall x, 0 <= x < AC.GT -> Frame.outside W x) by (intros x Hx; exact (proj1 (Himg x Hx))).
  destruct HC as (Hs23 & Hs18 & (A1 & H9a & HA1 & HSP & H232) & HPH & HFR & HFS & HKN & HFG & HFSj).
  assert (HA1A : A1 = A).
  { apply f4_id; [lia | lia |]. unfold rg in H9, H9a. rewrite <- H9a. exact H9. }
  subst A1.
  assert (H9' : rg regs' 9 A) by (unfold rg in *; rewrite E9; exact H9).
  (* HB *)
  split.
  { destruct HHB as (Hnz & Had). split; [exact Hnz|].
    exact (f4_addr_keep W mem mem' phi _ Had MU Hphish). }
  (* FLSI *)
  destruct HFLSI as ((HPRO & Hf128 & Hfstk & Hf144 & Hfa17) & Hf216 & Hf224 & Hf248 & HIN & HFLC).
  destruct HPRO as (Hf40 & Hf120 & Hf136 & Hf160 & Hf168 & Hf176 & Hf208 & Hp248 & Hfout6 & Hinb & Hing &
    Hp184 & Hp256 & Hp264 & Hp272 & Hp32).
  destruct HIN as (HINi & HINa & HINb).
  destruct (f4_in_keep g W mem mem' MU Hinp HINb HINa) as (HINb' & HINa').
  split.
  { split.
    { split.
      { split; [exact (f4_spill_keep regs regs' A 40 _ mem mem' W Hf40 H9 HA ltac:(lia) ltac:(lia) E9 MU
                         ltac:(intros x Hx; apply Hsp; lia))|].
        split; [exact (f4_spill_keep regs regs' A 120 _ mem mem' W Hf120 H9 HA ltac:(lia) ltac:(lia) E9 MU
                         ltac:(intros x Hx; apply Hsp; lia))|].
        split; [exact (f4_spill_keep regs regs' A 136 _ mem mem' W Hf136 H9 HA ltac:(lia) ltac:(lia) E9 MU
                         ltac:(intros x Hx; apply Hsp; lia))|].
        split; [exact (f4_spill_keep regs regs' A 160 _ mem mem' W Hf160 H9 HA ltac:(lia) ltac:(lia) E9 MU
                         ltac:(intros x Hx; apply Hsp; lia))|].
        split; [exact (f4_spill_keep regs regs' A 168 _ mem mem' W Hf168 H9 HA ltac:(lia) ltac:(lia) E9 MU
                         ltac:(intros x Hx; apply Hsp; lia))|].
        split; [exact (f4_spill_keep regs regs' A 176 _ mem mem' W Hf176 H9 HA ltac:(lia) ltac:(lia) E9 MU
                         ltac:(intros x Hx; apply Hsp; lia))|].
        split; [exact (f4_spill_keep regs regs' A 208 _ mem mem' W Hf208 H9 HA ltac:(lia) ltac:(lia) E9 MU
                         ltac:(intros x Hx; apply Hsp; lia))|].
        split; [exact (f4_spill_keep regs regs' A 248 _ mem mem' W Hp248 H9 HA ltac:(lia) ltac:(lia) E9 MU
                         ltac:(intros x Hx; apply Hsp; lia))|].
        split.
        { apply (f4_addr_keep W mem mem' (fr + 2624) 6 Hfout6 MU).
          intros i Hi. apply Hfrsh. apply f4_sh_frame; [exact Hfr8 | lia]. }
        split; [exact HINb'|].
        split.
        { intros Hn. destruct (Hing Hn) as (HH & _). split; [exact HH | exact HINa']. }
        (* push 14D: PRO's A4 spills [A + 184 / 256 / 264 / 272]; v1.9: PRO's 16th, [A + 32] = fr + 2880 *)
        split; [exact (f4_spill_keep regs regs' A 184 _ mem mem' W Hp184 H9 HA ltac:(lia) ltac:(lia) E9 MU
                         ltac:(intros x Hx; apply Hsp; lia))|].
        split; [exact (f4_spill_keep regs regs' A 256 _ mem mem' W Hp256 H9 HA ltac:(lia) ltac:(lia) E9 MU
                         ltac:(intros x Hx; apply Hsp; lia))|].
        split; [exact (f4_spill_keep regs regs' A 264 _ mem mem' W Hp264 H9 HA ltac:(lia) ltac:(lia) E9 MU
                         ltac:(intros x Hx; apply Hsp; lia))|].
        split; [exact (f4_spill_keep regs regs' A 272 _ mem mem' W Hp272 H9 HA ltac:(lia) ltac:(lia) E9 MU
                         ltac:(intros x Hx; apply Hsp; lia))|].
        exact (f4_spill_keep regs regs' A 32 _ mem mem' W Hp32 H9 HA ltac:(lia) ltac:(lia) E9 MU
                 ltac:(intros x Hx; apply Hsp; lia)). }
      split; [exact (f4_spill_keep regs regs' A 128 _ mem mem' W Hf128 H9 HA ltac:(lia) ltac:(lia) E9 MU
                       ltac:(intros x Hx; apply Hsp; lia))|].
      split; [apply (fl_stk W mem mem' fr (fr + FRAME_BYTES) Hfstk MU WM); exact Hfrst|].
      split; [exact (f4_spill_keep regs regs' A 144 _ mem mem' W Hf144 H9 HA ltac:(lia) ltac:(lia) E9 MU
                       ltac:(intros x Hx; apply Hsp; lia))|].
      apply (f4_addr_keep W mem mem' (fr + 2691) 17 Hfa17 MU).
      intros i Hi. apply Hfrsh. apply f4_sh_frame; [exact Hfr8 | lia]. }
    split; [exact (f4_spill_keep regs regs' A 216 _ mem mem' W Hf216 H9 HA ltac:(lia) ltac:(lia) E9 MU
                     ltac:(intros x Hx; apply Hsp; lia))|].
    split; [exact (f4_spill_keep regs regs' A 224 _ mem mem' W Hf224 H9 HA ltac:(lia) ltac:(lia) E9 MU
                     ltac:(intros x Hx; apply Hsp; lia))|].
    split; [exact (f4_spill_keep regs regs' A 248 _ mem mem' W Hf248 H9 HA ltac:(lia) ltac:(lia) E9 MU
                     ltac:(intros x Hx; apply Hsp; lia))|].
    split; [split; [exact HINi|]; split; [exact HINa' | exact HINb']|].
    (* FLC (push 14D / 14E; v1.9 slots): the pointer spills, the two record ranges, the compare spills
       [A + 72 / 64] and (v1.9) the two first-body pointers [A + 56 / 48] *)
    destruct HFLC as (Hc256 & Hc184 & Hc192 & Hc80 & Hc88 & Hc96 & Hc272 & Hc264 & Hcfg & Hcid & Hc72 & Hc64 &
      Hc56 & Hc48).
    split; [exact (f4_spill_keep regs regs' A 256 _ mem mem' W Hc256 H9 HA ltac:(lia) ltac:(lia) E9 MU
                     ltac:(intros x Hx; apply Hsp; lia))|].
    split; [exact (f4_spill_keep regs regs' A 184 _ mem mem' W Hc184 H9 HA ltac:(lia) ltac:(lia) E9 MU
                     ltac:(intros x Hx; apply Hsp; lia))|].
    split; [exact (f4_spill_keep regs regs' A 192 _ mem mem' W Hc192 H9 HA ltac:(lia) ltac:(lia) E9 MU
                     ltac:(intros x Hx; apply Hsp; lia))|].
    split; [exact (f4_spill_keep regs regs' A 80 _ mem mem' W Hc80 H9 HA ltac:(lia) ltac:(lia) E9 MU
                     ltac:(intros x Hx; apply Hsp; lia))|].
    split; [exact (f4_spill_keep regs regs' A 88 _ mem mem' W Hc88 H9 HA ltac:(lia) ltac:(lia) E9 MU
                     ltac:(intros x Hx; apply Hsp; lia))|].
    split; [exact (f4_spill_keep regs regs' A 96 _ mem mem' W Hc96 H9 HA ltac:(lia) ltac:(lia) E9 MU
                     ltac:(intros x Hx; apply Hsp; lia))|].
    split; [exact (f4_spill_keep regs regs' A 272 _ mem mem' W Hc272 H9 HA ltac:(lia) ltac:(lia) E9 MU
                     ltac:(intros x Hx; apply Hsp; lia))|].
    split; [exact (f4_spill_keep regs regs' A 264 _ mem mem' W Hc264 H9 HA ltac:(lia) ltac:(lia) E9 MU
                     ltac:(intros x Hx; apply Hsp; lia))|].
    split.
    { apply (f4_addr_keep W mem mem' (fragb fr) 72 Hcfg MU).
      intros i Hi. apply Hfrsh. apply f4_sh_frame; [exact Hfr8 | unfold fragb; lia]. }
    split.
    { apply (f4_addr_keep W mem mem' (fr + 2688) 38 Hcid MU).
      intros i Hi. apply Hfrsh. apply f4_sh_frame; [exact Hfr8 | lia]. }
    split; [exact (f4_spill_keep regs regs' A 72 _ mem mem' W Hc72 H9 HA ltac:(lia) ltac:(lia) E9 MU
                     ltac:(intros x Hx; apply Hsp; lia))|].
    split; [exact (f4_spill_keep regs regs' A 64 _ mem mem' W Hc64 H9 HA ltac:(lia) ltac:(lia) E9 MU
                     ltac:(intros x Hx; apply Hsp; lia))|].
    split; [exact (f4_spill_keep regs regs' A 56 _ mem mem' W Hc56 H9 HA ltac:(lia) ltac:(lia) E9 MU
                     ltac:(intros x Hx; apply Hsp; lia))|].
    exact (f4_spill_keep regs regs' A 48 _ mem mem' W Hc48 H9 HA ltac:(lia) ltac:(lia) E9 MU
             ltac:(intros x Hx; apply Hsp; lia)). }
  (* LK *)
  destruct HLK as (Hj255 & H21 & HOURb).
  split.
  { split; [exact Hj255|]. split; [unfold rg in *; rewrite E21; exact H21|].
    unfold OURb in *. apply (fl_bytes W mem mem' (fr + 2624) (OUR (g_in g)) HOURb MU).
    rewrite OUR_length. intros x Hx. apply Hfr. lia. }
  (* IDj: the 38 identity bytes at fr + 2688 are frame body outside [fr + 176, fr + 212) *)
  assert (HID' : IDj g fr j mem')
    by (apply (f4_idj_keep g fr j W mem mem' HID MU); intros x Hx; apply Hfr; lia).
  split; [|exact HID'].
  (* b5_C *)
  split; [unfold rg in *; rewrite E23; exact Hs23|].
  split; [unfold rg in *; rewrite E18; exact Hs18|].
  split.
  { exists A. split; [exact H9'|]. split; [exact HA|].
    split; [|exact (f4_q64_keep W mem mem' _ _ H232 MU ltac:(intros x Hx; apply Hsp; lia))].
    destruct HSP as (Hq248 & Hq256 & Hq144 & Hq184 & Hq192 & Hq80 & Hq88 & Hq96 & Hq272 & Hq264).
    split; [exact (f4_q64_keep W mem mem' _ _ Hq248 MU ltac:(intros x Hx; apply Hsp; lia))|].
    split; [exact (f4_q64_keep W mem mem' _ _ Hq256 MU ltac:(intros x Hx; apply Hsp; lia))|].
    split; [exact (f4_q64_keep W mem mem' _ _ Hq144 MU ltac:(intros x Hx; apply Hsp; lia))|].
    split; [exact (f4_q64_keep W mem mem' _ _ Hq184 MU ltac:(intros x Hx; apply Hsp; lia))|].
    split; [exact (f4_q64_keep W mem mem' _ _ Hq192 MU ltac:(intros x Hx; apply Hsp; lia))|].
    split; [exact (f4_q64_keep W mem mem' _ _ Hq80 MU ltac:(intros x Hx; apply Hsp; lia))|].
    split; [exact (f4_q64_keep W mem mem' _ _ Hq88 MU ltac:(intros x Hx; apply Hsp; lia))|].
    split; [exact (f4_q64_keep W mem mem' _ _ Hq96 MU ltac:(intros x Hx; apply Hsp; lia))|].
    split; [exact (f4_q64_keep W mem mem' _ _ Hq272 MU ltac:(intros x Hx; apply Hsp; lia))|].
    exact (f4_q64_keep W mem mem' _ _ Hq264 MU ltac:(intros x Hx; apply Hsp; lia)). }
  destruct HPH as (HPHb & HPHp & HPHfs).
  split.
  { split.
    { intros Hlen. pose proof (HPHb Hlen) as Hbs.
      apply (fl_bytes W mem mem' phi (t_g (g_in g) j) Hbs MU).
      unfold t_g. rewrite fr50_length. intros x Hx. apply Hphi.
      unfold AC.a_size. lia. }
    split.
    { intros Hlen. replace (AC.aspZ regs') with (AC.aspZ regs);
        [exact (HPHp Hlen) | unfold AC.aspZ; rewrite E2; reflexivity]. }
    { intros Hlen0 (b & Hb & Hw & Hr). apply (HPHfs Hlen0). exists b. split; [exact Hb|]. split; [|exact Hr].
      apply (proj2 (f4_word_eq W mem mem' (AC.as_tp AC.ASYMS) MU
                      ltac:(intros x Hx; apply Himg1; lia) ltac:(lia) ltac:(lia) b)).
      exact Hw. } }
  destruct HFR as (HFRa & HFRb & HFRc & HFRd).
  split.
  { split.
    { apply (f4_addr_keep W mem mem' (fragb fr) 72 HFRa MU).
      intros i Hi. apply Hfrsh. apply f4_sh_frame; [exact Hfr8 | unfold fragb; lia]. }
    split.
    { apply (f4_addr_keep W mem mem' (fr + 2688) 38 HFRb MU).
      intros i Hi. apply Hfrsh. apply f4_sh_frame; [exact Hfr8 | lia]. }
    split; [|exact HFRd].
    apply (fl_bytes W mem mem' (fragb fr) (t_FG (g_in g) j) HFRc MU).
    rewrite HFRd. unfold fragb. intros x Hx. apply Hfr. lia. }
  destruct HFS as (HFSa & DB & HDB & HDB0 & HDB1).
  split.
  { split.
    { intros FS Hw HFSr Hin. apply (HFSa FS); [|exact HFSr|exact Hin].
      apply (proj2 (f4_word_eq W mem mem' (AC.as_tp AC.ASYMS) MU
                      ltac:(intros x Hx; apply Himg1; lia) ltac:(lia) ltac:(lia) FS)).
      exact Hw. }
    exists DB. split; [|split; [exact HDB0 | exact HDB1]].
    apply (proj1 (f4_word_eq W mem mem' (AC.as_tp AC.ASYMS + 8) MU
                    ltac:(intros x Hx; apply Himg1; lia) ltac:(lia) ltac:(lia) DB)).
    exact HDB. }
  destruct HKN as (HKNa & HKNb).
  split.
  { split.
    { apply (fl_bytes W mem mem' KIND_NAME kind_name_bytes HKNa MU).
      intros x Hx. apply Himg1. lia. }
    apply (f4_addr_keep W mem mem' KIND_NAME 112 HKNb MU).
    intros i Hi. exact (proj2 (Himg (KIND_NAME + i) ltac:(lia))). }
  (* FGj: the 72 fragment bytes at fr + 2768 (= fragb fr, the b5_FR bytes) *)
  destruct HFG as (HFGb & HFGok).
  split.
  { split; [|exact HFGok]. unfold FGBe in *.
    apply (fl_bytes W mem mem' (fr + 2768) (t_FG (g_in g) j) HFGb MU).
    rewrite HFRd. intros x Hx. apply Hfr. lia. }
  (* FSj (v1.9 FSb): the two first-fragment spills [A + 104, A + 120), and the first fragment's body at
     fr + 2880 (first.sroa.7, at most 23 bytes: f4_fs_body_len) with its 35 addressable bytes, frame body above
     the parse output and frame shadow from byte 27 on *)
  destruct HFSj as (Hq104 & Hq112 & Hbody & Hbad & HFI).
  split; [exact (f4_spill_keep regs regs' A 104 _ mem mem' W Hq104 H9 HA ltac:(lia) ltac:(lia) E9 MU
                   ltac:(intros x Hx; apply Hsp; lia))|].
  split; [exact (f4_spill_keep regs regs' A 112 _ mem mem' W Hq112 H9 HA ltac:(lia) ltac:(lia) E9 MU
                   ltac:(intros x Hx; apply Hsp; lia))|].
  split.
  { apply (fl_bytes W mem mem' (fr + 2880) _ Hbody MU).
    pose proof (f4_fs_body_len (g_in g) j) as Hbl. intros x Hx. apply Hfr. lia. }
  split.
  { apply (f4_addr_keep W mem mem' (fr + 2880) 35 Hbad MU).
    intros i Hi. apply Hfrsh. apply f4_sh_frame; [exact Hfr8 | lia]. }
  exact HFI.
Qed.

(* ---------------- the spill writes of the 0x81dfc block ---------------- *)

(* The two spill words the 0x81dfc block may write: [A+200, A+208) on every arm, [A+240, A+248) on the
   0x81e50 edge. *)
Definition f4_Wsp (A : Z) : list (Z * Z) := [(A + 200, A + 208); (A + 240, A + 248)].

(* FRA and ENT move across a write confined to the two spill words: the write is app memory above stklo
   (stklo <= S - SLOT_STACK < sp <= A) and below the entry sp S, so it is a_store_ok for a_laws_store; it misses
   every FRA cell (the frame below A, the frame shadow below HIGHMEM_BEG <= A, the A+304 and A+16..A+32 words,
   the saved registers [S-104, S) and the low runtime and image cells). It lies inside the entry-anchored slot
   window [S - SLOT_STACK, S), so ent_store keeps ENT, and the FakeStack frame record is below stklo
   (fsrec_stklo). *)
Lemma f4_fra_spill : forall g fr hb regs regs' mem mem' md md' Asp,
  FRA B APIf ra g fr hb regs mem md -> ENT APIf g hb mem md ->
  rg regs 9 Asp -> 0 <= Asp < 2 ^ 64 ->
  Frame.munch (f4_Wsp Asp) mem mem' ->
  Frame.wmono rsegs mem mem' ->
  stk rsegs mem' (g_S g - AF.SLOT_STACK) (g_S g) ->
  AsanLift.mat_le md md' ->
  getr regs' 2 = getr regs 2 -> getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 ->
  getr regs' 8 = getr regs 8 -> getr regs' 9 = getr regs 9 -> getr regs' 19 = getr regs 19 ->
  getr regs' 26 = getr regs 26 ->
  FRA B APIf ra g fr hb regs' mem' md' /\ ENT APIf g hb mem' md'.
Proof. pose proof FRAME_BYTES_val as HFBval. pose proof FRAME_SHADOW_val as HFSval.
  intros g fr hb regs regs' mem mem' md md' Asp HFRA HENT H9 HA MU WM HWIN' Hmat
    E2 E3 E4 E8 E9 E19 E26.
  pose proof HFRA as HFRA2.
  destruct HFRA2 as (A0 & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA416 & HS4 & HAPP &
    Hspill & Hsel & Hfr24 & Hloc & Hhdr1 & Hhdr2 & Hsh & Hwin & Hsaved & Herrno & HAG & HWA &
    HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive).
  pose proof (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) as LAWS.
  pose proof (AC.a_laws_stack_high _ _ _ _ _ LAWS (hb ++ g_H g) mem md HAH) as Hstkhigh.
  assert (HKh : HIGHMEM_BEG = 17594333495296) by (vm_compute; reflexivity).
  assert (HKa : APPMEM_END = 140737488355328) by (vm_compute; reflexivity).
  assert (HKs : AF.SLOT_STACK = 1048576) by (vm_compute; reflexivity).
  assert (HKl : LOWMEM_END = 2147450880) by (vm_compute; reflexivity).
  assert (HKk : ASAN_K = 2147450880) by (vm_compute; reflexivity).
  assert (HAsr : 0 <= A0 < 2 ^ 64).
  { pose proof Hwin as HW0. unfold stk in HW0. destruct HW0 as (Hw0 & Hw1 & _). lia. }
  assert (HspN : HIGHMEM_BEG < sp) by lia.
  assert (HA0e : Asp = A0).
  { apply f4_id; [lia | lia |]. unfold rg in H9, Hr9. rewrite <- H9. exact Hr9. }
  subst A0.
  assert (HfrL : 0 <= fr).
  { pose proof (bytes_at_bound rsegs mem fr (le8 (Z_to_bv 64 0x41b58ab3)) Hhdr1) as (Hf0 & _). lia. }
  assert (HA9 : forall A', getr regs 9 = Z_to_bv 64 A' -> 0 <= A' < 2 ^ 64 -> A' = Asp).
  { intros A' HA' HA'r. apply f4_id; [lia | lia |]. rewrite <- HA'. exact H9. }
  unfold f4_Wsp in MU.
  set (W := [(Asp + 200, Asp + 208); (Asp + 240, Asp + 248)]) in MU.
  assert (HOUT : forall x, 0 <= x < HIGHMEM_BEG -> Frame.outside W x).
  { intros x Hx. subst W. cbn [Frame.outside]. repeat split; try exact I; lia. }
  assert (HRO : ro_agree rsegs mem').
  { apply (sl_ro_keep W mem mem' Hro MU). intros x Hx. apply HOUT. lia. }
  assert (HAW : all_app W).
  { subst W. cbn [all_app].
    split; [apply f4_app_ivl; lia | split; [apply f4_app_ivl; lia | exact I]]. }
  assert (HD : rt_disjoint W).
  { subst W. unfold rt_disjoint, RT_LO, RT_HI, RT_GOT_AF, RT_AF, RT_GOT_VERB, RT_VERB, RT_GOT_CF, RT_CF,
      RT_TSDI, RT_TSDK, RT_PGSZ, RT_TP, RT_TSDMAIN, RT_REAL_LO, RT_REAL_HI, RT_IMAP, RT_IMEM, RT_MUG, RT_AGLOB,
      RT_AGLOB_LEN. cbn [disjoint_from]. repeat split; first [exact I | left; lia]. }
  assert (Hwrit : forall a, 0 <= a < 2 ^ 64 -> writable_at rsegs mem a -> writable_at rsegs mem' a)
    by (intros a Ha Hw; exact (WM (Z_to_bv 64 a) Hw)).
  assert (Hmc : forall a, 0 <= a < 2 ^ 64 ->
    ~ AC.a_store_ok (hb ++ g_H g) (AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md) a ->
    mem' (Z_to_bv 64 a) = mem (Z_to_bv 64 a)).
  { intros a Ha Hns. apply MU. rewrite MState.unsigned_lit by lia.
    subst W. cbn [Frame.outside]. repeat split; try exact I; intro HC; apply Hns;
      right; left; lia. }
  destruct (f4_law_store (hb ++ g_H g) mem mem' md HAH Hmc Hwrit) as (HAH' & Hown & HSTKeq & HSTKhi).
  assert (HFRA' : FRA B APIf ra g fr hb regs' mem' md).
  { apply (sl_stk_run B APIf ra empty FF g fr hb regs regs' mem mem' md W
             HFRA MU WM HRO HAW HD HAH' HSTKeq).
    - (* frame header [fr, fr+24) *)
      intros x Hx. subst W. cbn [Frame.outside]. repeat split; try exact I; lia.
    - (* everything below HIGHMEM_BEG *)
      intros x Hx. apply HOUT. lia.
    - (* the frame-base spill [A+304, A+312) *)
      intros A0 HA0 HA0r x Hx. rewrite (HA9 A0 HA0 HA0r) in Hx.
      subst W. cbn [Frame.outside]. repeat split; try exact I; lia.
    - (* the 13 saved caller registers [S-104, S) *)
      intros x Hx. subst W. cbn [Frame.outside]. repeat split; try exact I; lia.
    - (* the 392 frame shadow bytes *)
      intros x Hx. subst W. cbn [Frame.outside]. repeat split; try exact I;
        revert Hx; unfold Sfr, shadow_addr; Z.div_mod_to_equations; lia.
    - (* the fr reload and release-arm selector spills [A+16, A+32) *)
      intros A0 HA0 HA0r x Hx. rewrite (HA9 A0 HA0 HA0r) in Hx.
      subst W. cbn [Frame.outside]. repeat split; try exact I; lia.
    - exact HWIN'.
    - (* the FakeStack frame record: its three cells are at or below stklo *)
      intros Hrec. eapply fsrec_stklo; [exact Hrec | exact HAH | exact MU |].
      intros x Hx _. subst W. cbn [Frame.outside]. repeat split; try exact I; lia.
    - exact E2.
    - exact E3.
    - exact E4.
    - exact E8.
    - exact E9.
    - exact E19.
    - exact E26. }
  split.
  - apply (sl_fra_move B APIf ra g fr hb regs' regs' mem' md md' HFRA'); try reflexivity; exact Hmat.
  - eapply ent_mat; [| exact Hmat].
    eapply ent_store with (W := W); [exact HENT | exact HFRA | exact MU | | exact HSTKeq | exact HSTKhi |].
    + intros x Hx.
      destruct (Z_lt_le_dec x (Asp + 200)) as [H1|H1];
        [| destruct (Z_lt_le_dec x (Asp + 248)) as [H2|H2]].
      * left. subst W. cbn [Frame.outside]. repeat split; try exact I; lia.
      * right. left. lia.
      * left. subst W. cbn [Frame.outside]. repeat split; try exact I; lia.
    + intros a _ Ho. exact (proj2 (Hown a) Ho).
Qed.

(* The cut skeleton across the spill writes: f4_keepg with W = f4_Wsp A, which lies above every cell it keeps
   except the spills [A + 208, A + 240) and [A + 248, A + 280), which it misses. *)
Lemma f4_keep1 : forall g j phi fr A regs regs' mem mem' md,
  FRA B APIf ra g fr (hb1 phi (AC.a_size (flen g j))) regs mem md ->
  HB mem phi (flen g j) -> FLSI g j fr regs mem -> LK g fr j regs mem ->
  b5_C g j phi fr regs mem -> IDj g fr j mem ->
  rg regs 9 A -> 0 <= A < 2 ^ 64 ->
  Frame.munch (f4_Wsp A) mem mem' -> Frame.wmono rsegs mem mem' ->
  getr regs' 2 = getr regs 2 -> getr regs' 9 = getr regs 9 -> getr regs' 18 = getr regs 18 ->
  getr regs' 21 = getr regs 21 -> getr regs' 23 = getr regs 23 ->
  HB mem' phi (flen g j) /\ FLSI g j fr regs' mem' /\ LK g fr j regs' mem' /\
  b5_C g j phi fr regs' mem' /\ IDj g fr j mem'.
Proof. pose proof FRAME_BYTES_val as HFBval. pose proof FRAME_SHADOW_val as HFSval.
  intros g j phi fr A regs regs' mem mem' md HFRA HHB HFLSI HLK HC HID H9 HA MU WM E2 E9 E18 E21 E23.
  pose proof HFRA as HF.
  destruct HF as (A0 & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA416 & HS4 & HAPP &
    Hspill & Hsel & Hfr24 & Hloc & Hhdr1 & Hhdr2 & Hsh & Hwin & Hsaved & Herrno & HAG & HWA &
    HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive).
  pose proof (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) as LAWS.
  pose proof (AC.a_laws_stack_high _ _ _ _ _ LAWS _ mem md HAH) as Hstkhigh.
  assert (HKh : HIGHMEM_BEG = 17594333495296) by (vm_compute; reflexivity).
  assert (HKa : APPMEM_END = 140737488355328) by (vm_compute; reflexivity).
  assert (HKs : AF.SLOT_STACK = 1048576) by (vm_compute; reflexivity).
  assert (HKg : AC.GT = 6283264) by (vm_compute; reflexivity).
  assert (HA0r : 0 <= A0 < 2 ^ 64).
  { pose proof Hwin as HW0. unfold stk in HW0. destruct HW0 as (Hw0 & Hw1 & _). lia. }
  assert (HAeq : A = A0).
  { apply f4_id; [lia | lia |]. unfold rg in H9, Hr9. rewrite <- H9. exact Hr9. }
  subst A0.
  pose proof (fra_app B APIf ra g fr _ regs mem md HFRA) as (HGT & Happ).
  assert (HIn : In (phi, AC.a_size (flen g j)) (hb1 phi (AC.a_size (flen g j)) ++ g_H g))
    by (apply in_or_app; left; left; reflexivity).
  destruct (f4_law_blocks _ mem md phi (AC.a_size (flen g j)) HAH HIn) as (_ & Hphi4096 & Hphistk & _).
  assert (Hasz : 1 <= AC.a_size (flen g j)) by (unfold AC.a_size; lia).
  assert (Hlow : forall x, x < A + 200 -> Frame.outside (f4_Wsp A) x)
    by (intros x Hx; unfold f4_Wsp; cbn [Frame.outside]; repeat split; try exact I; lia).
  assert (HlowS : forall x, 0 <= x < APPMEM_END -> Frame.outside (f4_Wsp A) (shadow_addr x))
    by (intros x Hx; apply Hlow; pose proof (f4_sh_hi x Hx); lia).
  apply (f4_keepg g j phi fr A regs regs' mem mem' md (f4_Wsp A) HFRA HHB HFLSI HLK HC HID H9 HA MU WM).
  - intros x Hx. apply Hlow. lia.
  - intros i Hi. apply HlowS. lia.
  - intros x Hx. apply Hlow. lia.
  - intros x Hx. left. apply Hlow. lia.
  - intros x Hx. apply Hlow. unfold Sfr in Hx. pose proof (f4_sh_hi fr ltac:(lia)). lia.
  - intros x Hx. unfold f4_Wsp. cbn [Frame.outside]. repeat split; try exact I; lia.
  - intros x Hx. split; [apply Hlow; lia | apply HlowS; lia].
  - intros Hn x Hx. pose proof HFLSI as (_ & _ & _ & _ & HIN & _).
    destruct (f4_in_frame g fr _ regs mem md HFRA HIN Hn x Hx) as (Hxa & Hxs & _ & _).
    split; [apply Hlow; lia | apply HlowS; unfold app_mem in Hxa; lia].
  - exact E2.
  - exact E9.
  - exact E18.
  - exact E21.
  - exact E23.
Qed.

(* b5_PF across the spill writes of the 0x81dfc block: every cell it names lies below the written words
   [A + 200, A + 208) and [A + 240, A + 248): the record block (below stklo < A), the frame (fr + 3136 <= A), the
   metadata bytes (below HIGHMEM_BEG < A) and the compare spills [A + 72] / [A + 64]. The record's 38-byte prefix
   and the 6-byte compare operands are cut to their exact length first (f4_bytes_first). *)
Lemma f4_pf_sp : forall g j phi fr A regs regs' mem mem' md,
  FRA B APIf ra g fr (hb1 phi (AC.a_size (flen g j))) regs mem md ->
  b5_PF g j phi fr regs mem -> rg regs 9 A -> 0 <= A < 2 ^ 64 ->
  Frame.munch (f4_Wsp A) mem mem' -> getr regs' 9 = getr regs 9 ->
  b5_PF g j phi fr regs' mem'.
Proof. pose proof FRAME_BYTES_val as HFBval. pose proof FRAME_SHADOW_val as HFSval.
  intros g j phi fr A regs regs' mem mem' md HFRA HPF H9 HA MU E9.
  pose proof HFRA as HF.
  destruct HF as (A0 & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA416 & HS4 & HAPP &
    Hspill & Hsel & Hfr24 & Hloc & Hhdr1 & Hhdr2 & Hsh & Hwin & Hsaved & Herrno & HAG & HWA &
    HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive).
  pose proof (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) as LAWS.
  pose proof (AC.a_laws_stack_high _ _ _ _ _ LAWS _ mem md HAH) as Hstkhigh.
  assert (HKs : AF.SLOT_STACK = 1048576) by (vm_compute; reflexivity).
  assert (HKg : AC.GT = 6283264) by (vm_compute; reflexivity).
  assert (HA0r : 0 <= A0 < 2 ^ 64).
  { pose proof Hwin as HW0. unfold stk in HW0. destruct HW0 as (Hw0 & Hw1 & _). lia. }
  assert (HAeq : A = A0).
  { apply f4_id; [lia | lia |]. unfold rg in H9, Hr9. rewrite <- H9. exact Hr9. }
  subst A0.
  pose proof (fra_app B APIf ra g fr _ regs mem md HFRA) as (HGT & Happ).
  assert (HIn : In (phi, AC.a_size (flen g j)) (hb1 phi (AC.a_size (flen g j)) ++ g_H g))
    by (apply in_or_app; left; left; reflexivity).
  destruct (f4_law_blocks _ mem md phi (AC.a_size (flen g j)) HAH HIn) as (_ & Hphi4096 & Hphistk & _).
  assert (Hasz : flen g j <= AC.a_size (flen g j)) by (unfold AC.a_size; lia).
  assert (Hasz1 : 1 <= AC.a_size (flen g j)) by (unfold AC.a_size; lia).
  assert (Hhi : HIGHMEM_BEG <= A) by lia.
  assert (Hphitop : phi + AC.a_size (flen g j) <= A) by lia.
  assert (Hfrtop : fr + FRAME_BYTES <= A) by lia.
  assert (Hfr0 : 0 <= fr) by lia.
  assert (Hlow : forall x, x < A + 200 -> Frame.outside (f4_Wsp A) x)
    by (intros x Hx; unfold f4_Wsp; cbn [Frame.outside]; repeat split; try exact I; lia).
  destruct HPF as (A1 & H9a & HA1 & Hlong & H8819).
  assert (HA1A : A1 = A) by (apply f4_id; [lia | lia |]; unfold rg in H9, H9a; rewrite <- H9a; exact H9).
  subst A1.
  exists A. split; [unfold rg in *; rewrite E9; exact H9|]. split; [exact HA|].
  split.
  - intros Hle. destruct (Hlong Hle) as ((rb & Hrb & Hrbl) & Hphib).
    split.
    + exists (firstn 38 rb). split; [|rewrite length_firstn; lia].
      apply (fl_bytes (f4_Wsp A) mem mem' phi _ (f4_bytes_first mem phi rb 38 Hrb) MU).
      rewrite length_firstn. intros x Hx. apply Hlow. lia.
    + apply (fl_bytes (f4_Wsp A) mem mem' phi _ Hphib MU).
      pose proof (f4_tphi_len g j) as Hl. intros x Hx. apply Hlow. lia.
  - intros Ht. destruct (H8819 Ht) as
      ((field16 & v14 & v15 & v16 & v17 & Hu16 & Hb14 & Hb15 & Hb16 & Hb17 & Hv14 & Hv15 & Hv16 & Hv17 &
        Hs14 & Hs15 & Hs16 & Hs17 & Ef & Ek) &
       (ls & rs & Hq56 & Hls & Hlsl & Hrs & Hrsl & Hcm & Had) &
       (ls2 & rs2 & Hq48 & Hls2 & Hls2l & Hrs2 & Hrs2l & Hcm2 & Had2)).
    (* the metadata bytes of phi + 14 .. phi + 17 lie below HIGHMEM_BEG <= A *)
    assert (Hshk : forall k, 0 <= k < 50 -> Z.shiftr (phi + k) 3 + ASAN_K + 1 <= A)
      by (intros k Hk; apply f4_sh_below; [lia | exact Hhi]).
    pose proof (Hshk 14 ltac:(lia)) as Hk14. pose proof (Hshk 15 ltac:(lia)) as Hk15.
    pose proof (Hshk 16 ltac:(lia)) as Hk16. pose proof (Hshk 17 ltac:(lia)) as Hk17.
    split; [|split].
    + exists field16, v14, v15, v16, v17. unfold u16, b8 in *.
      split; [apply (fl_bytes (f4_Wsp A) mem mem' _ _ Hu16 MU); rewrite length_le2; intros x Hx; apply Hlow; lia|].
      split; [apply (fl_bytes (f4_Wsp A) mem mem' _ _ Hb14 MU); cbn [length]; intros x Hx; apply Hlow; lia|].
      split; [apply (fl_bytes (f4_Wsp A) mem mem' _ _ Hb15 MU); cbn [length]; intros x Hx; apply Hlow; lia|].
      split; [apply (fl_bytes (f4_Wsp A) mem mem' _ _ Hb16 MU); cbn [length]; intros x Hx; apply Hlow; lia|].
      split; [apply (fl_bytes (f4_Wsp A) mem mem' _ _ Hb17 MU); cbn [length]; intros x Hx; apply Hlow; lia|].
      split; [exact Hv14|]. split; [exact Hv15|]. split; [exact Hv16|]. split; [exact Hv17|].
      split; [apply (fl_bytes (f4_Wsp A) mem mem' _ _ Hs14 MU); cbn [length]; intros x Hx; apply Hlow; lia|].
      split; [apply (fl_bytes (f4_Wsp A) mem mem' _ _ Hs15 MU); cbn [length]; intros x Hx; apply Hlow; lia|].
      split; [apply (fl_bytes (f4_Wsp A) mem mem' _ _ Hs16 MU); cbn [length]; intros x Hx; apply Hlow; lia|].
      split; [apply (fl_bytes (f4_Wsp A) mem mem' _ _ Hs17 MU); cbn [length]; intros x Hx; apply Hlow; lia|].
      split; [exact Ef | exact Ek].
    + exists (firstn 6 ls), (firstn 6 rs).
      split; [exact (f4_q64_keep _ mem mem' _ _ Hq56 MU ltac:(intros x Hx; apply Hlow; lia))|].
      split; [apply (fl_bytes (f4_Wsp A) mem mem' _ _ (f4_bytes_first mem (fr + 186) ls 6 Hls) MU);
              rewrite length_firstn; intros x Hx; apply Hlow; lia|].
      split; [rewrite length_firstn; lia|].
      split; [apply (fl_bytes (f4_Wsp A) mem mem' _ _ (f4_bytes_first mem phi rs 6 Hrs) MU);
              rewrite length_firstn; intros x Hx; apply Hlow; lia|].
      split; [rewrite length_firstn; lia|].
      split; [rewrite f4_mcmp_firstn; exact Hcm|].
      apply (f4_addr_keep _ mem mem' (fr + 186) 6 Had MU).
      intros i Hi. apply Hlow. pose proof (f4_sh_hi (fr + 186 + i) ltac:(lia)). lia.
    + exists (firstn 6 ls2), (firstn 6 rs2).
      split; [exact (f4_q64_keep _ mem mem' _ _ Hq48 MU ltac:(intros x Hx; apply Hlow; lia))|].
      split; [apply (fl_bytes (f4_Wsp A) mem mem' _ _ (f4_bytes_first mem (fr + 180) ls2 6 Hls2) MU);
              rewrite length_firstn; intros x Hx; apply Hlow; lia|].
      split; [rewrite length_firstn; lia|].
      split; [apply (fl_bytes (f4_Wsp A) mem mem' _ _ (f4_bytes_first mem (phi + 6) rs2 6 Hrs2) MU);
              rewrite length_firstn; intros x Hx; apply Hlow; lia|].
      split; [rewrite length_firstn; lia|].
      split; [rewrite f4_mcmp_firstn; exact Hcm2|].
      apply (f4_addr_keep _ mem mem' (fr + 180) 6 Had2 MU).
      intros i Hi. apply Hlow. pose proof (f4_sh_hi (fr + 180 + i) ltac:(lia)). lia.
Qed.

(* ---------------- path 2: the 0x81e54 block, in the Lib engine ----------------
   The callee contract reac_ctrl_parse_c states its run as a Lib.Exec.evt, so the 0x81e54 block (the six stores
   and the call) is stepped by the Lib engine. *)
Import OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.MState
       OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem
       OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Exec
       OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame
       OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Cells
       OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Step
       OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Tac
       OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Bytes.
Import YK11.
Open Scope Z_scope.

(* mkR_of regs is definitionally the explicit 31-slot register map of the Lib engine. *)
Lemma f4_mkR_of_expand : forall regs, Regs6ss.mkR_of regs =
  mkR (getr regs 1) (getr regs 2) (getr regs 3) (getr regs 4) (getr regs 5) (getr regs 6)
  (getr regs 7) (getr regs 8) (getr regs 9) (getr regs 10) (getr regs 11) (getr regs 12)
  (getr regs 13) (getr regs 14) (getr regs 15) (getr regs 16) (getr regs 17) (getr regs 18)
  (getr regs 19) (getr regs 20) (getr regs 21) (getr regs 22) (getr regs 23) (getr regs 24)
  (getr regs 25) (getr regs 26) (getr regs 27) (getr regs 28) (getr regs 29) (getr regs 30) (getr regs 31).
Proof. intros regs. reflexivity. Qed.

(* A byte value is below 256. *)
Lemma f4_byte_range : forall b : byte, 0 <= bv_unsigned b < 256.
Proof.
  intros b. pose proof (bv_unsigned_in_range 8 b) as HR. unfold bv_modulus in HR.
  change (2 ^ Z.of_N 8) with 256 in HR. lia.
Qed.

Lemma f4_word_range : forall w : word, 0 <= bv_unsigned w < 2 ^ 64.
Proof.
  intros w. pose proof (bv_unsigned_in_range 64 w) as H. unfold bv_modulus in H.
  change (2 ^ Z.of_N 64) with (2 ^ 64) in H. lia.
Qed.

Lemma f4_rd8 : forall m a bs, bytes_at rsegs m a bs -> length bs = 8%nat ->
  ov_read_bytes rsegs m (wa a) 8 = Some bs.
Proof.
  intros m a bs H Hl.
  pose proof (bytes_at_ov_read rsegs m a bs 0 8 H ltac:(lia)) as HH.
  change (Z.of_nat 0) with 0 in HH. rewrite Z.add_0_r, skipn_O in HH.
  rewrite firstn_all2 in HH by lia. exact HH.
Qed.

Lemma f4_bytes_cons : forall m a b bs, bytes_at rsegs m a [b] -> bytes_at rsegs m (a + 1) bs ->
  bytes_at rsegs m a (b :: bs).
Proof.
  intros m a b bs (Ha0 & _ & Hb) (_ & Hbl & Hbs). split; [exact Ha0|].
  split; [cbn [length] in *; lia|].
  intros i Hi. destruct i as [|i].
  - pose proof (Hb 0%nat ltac:(cbn [length]; lia)) as H0. cbn [nth_error] in H0 |- *. exact H0.
  - cbn [nth_error]. cbn [length] in Hi.
    replace (a + Z.of_nat (S i)) with (a + 1 + Z.of_nat i) by lia.
    exact (Hbs i ltac:(lia)).
Qed.

Lemma f4_le1_0 : le1 (Z_to_bv 64 0) = [Z_to_bv 8 0].
Proof. vm_compute. reflexivity. Qed.

Lemma f4_le1_4 : le1 (Z_to_bv 64 4) = [Z_to_bv 8 4].
Proof. vm_compute. reflexivity. Qed.

(* Every byte of a carried byte list is present. *)
Lemma f4_pres_at : forall m a (l : list byte) q, bytes_at rsegs m a l -> a <= q < a + Z.of_nat (length l) ->
  exists b, mbyte rsegs m q = Some b.
Proof.
  intros m a l q (Ha & Hl & H) Hq.
  assert (Hi : (Z.to_nat (q - a) < length l)%nat) by lia.
  pose proof (H _ Hi) as Hq5. rewrite Z2Nat.id in Hq5 by lia.
  replace (a + (q - a)) with q in Hq5 by lia.
  destruct (nth_error l (Z.to_nat (q - a))) as [b|] eqn:En; [|apply nth_error_None in En; lia].
  exists b. exact Hq5.
Qed.

(* Two word values read at the same address agree modulo 2^64. *)
Lemma f4_wm_eq : forall m a v v', word_mem rsegs m a v -> word_mem rsegs m a v' ->
  v mod 2 ^ 64 = v' mod 2 ^ 64.
Proof.
  intros m a v v' H H'.
  assert (P : 2 ^ 64 <> 0) by lia.
  assert (E : forall k, (k < 8)%nat -> le_byte (v mod 2 ^ 64) 8 k = le_byte (v' mod 2 ^ 64) 8 k).
  { intros k Hk. pose proof (H k Hk) as H1. pose proof (H' k Hk) as H2.
    assert (H3 : Z_to_bv 8 (le_byte v 8 k) = Z_to_bv 8 (le_byte v' 8 k)) by congruence.
    apply (f_equal bv_unsigned) in H3. rewrite !kb_byte_unsigned in H3. clear H1 H2. rename H3 into H2.
    unfold le_byte in H2 |- *. change (8 * Z.of_nat 8) with 64 in H2 |- *. rewrite !Z.mod_mod by exact P.
    exact H2. }
  assert (R1 : 0 <= v mod 2 ^ 64 < 2 ^ 64) by (apply Z.mod_pos_bound; lia).
  assert (R2 : 0 <= v' mod 2 ^ 64 < 2 ^ 64) by (apply Z.mod_pos_bound; lia).
  rewrite (kb_le8_digits _ R1), (kb_le8_digits _ R2).
  rewrite !E by lia. reflexivity.
Qed.

Lemma f4_wm_norm : forall m a x y, word_mem rsegs m a x -> word_mem rsegs m a y ->
  0 <= y < 2 ^ 64 -> - (2 ^ 64) < x < 2 ^ 64 -> x = y \/ x = y - 2 ^ 64.
Proof.
  intros m a x y Hx Hy Hy0 Hx0.
  pose proof (f4_wm_eq m a x y Hx Hy) as E.
  rewrite (Z.mod_small y (2 ^ 64)) in E by lia.
  destruct (Z_le_gt_dec 0 x) as [Hs|Hs].
  - left. rewrite (Z.mod_small x (2 ^ 64)) in E by lia. exact E.
  - right.
    assert (EM : (x + 2 ^ 64) mod 2 ^ 64 = x mod 2 ^ 64).
    { replace (x + 2 ^ 64) with (x + 1 * 2 ^ 64) by lia. apply Z_mod_plus_full. }
    rewrite (Z.mod_small (x + 2 ^ 64) (2 ^ 64)) in EM by lia. lia.
Qed.

Lemma f4_dj_hi : forall (W : list (Z * Z)) a n, (forall lo hi, In (lo, hi) W -> a + n <= lo) ->
  disjoint_from W a n.
Proof.
  induction W as [|[lo hi] W IH]; intros a n H; cbn [disjoint_from]; [exact I|].
  split; [left; exact (H lo hi (or_introl eq_refl))|].
  apply IH. intros lo' hi' Hin. exact (H lo' hi' (or_intror Hin)).
Qed.

(* Every range at or above GT is apart from the runtime's cells (all below GT). *)
Lemma f4_rt : forall W, (forall lo hi, In (lo, hi) W -> AC.GT <= lo) -> rt_disjoint W.
Proof.
  intros W H. unfold rt_disjoint.
  repeat split; apply f4_dj_hi; intros lo hi Hin; pose proof (H lo hi Hin) as Hl; unfold AC.GT in Hl;
    unfold RT_LO, RT_HI, RT_GOT_AF, RT_AF, RT_GOT_VERB, RT_VERB, RT_GOT_CF, RT_CF, RT_TSDI, RT_TSDK, RT_PGSZ,
      RT_TP, RT_TSDMAIN, RT_REAL_LO, RT_REAL_HI, RT_IMAP, RT_IMEM, RT_MUG, RT_AGLOB, RT_AGLOB_LEN; lia.
Qed.

(* Every FakeStack metadata cell is at or above FS. *)
Lemma f4_fs_meta_lo : forall FS q, fs_meta FS q -> FS <= q.
Proof.
  intros FS q H. unfold fs_meta in H.
  destruct H as [H | [H | [ [c [Hc Hr]] | [c [j [Hc [Hj Heq]]]] ]]].
  - lia.
  - lia.
  - unfold AC.a_fs_hint in Hr. lia.
  - subst q. exact (proj1 (a_fs_flag_range FS c j Hc Hj)).
Qed.

(* The shadow byte k of the frame base is the shadow of the frame byte fr + 8k. *)
Lemma f4_fr_sh : forall fr k, shadow_addr (fr + 8 * k) = Sfr fr + k.
Proof.
  intros fr k. unfold Sfr, shadow_addr.
  replace (fr + 8 * k) with (fr + k * 8) by lia. rewrite Z.div_add by lia. lia.
Qed.

(* An app byte never falls in the shadow of an app range. *)
Lemma f4_app_out_sh : forall x lo hi, app_mem x -> 0 <= lo -> 0 <= hi <= APPMEM_END ->
  ~ (shadow_addr lo <= x < shadow_addr hi).
Proof.
  intros x lo hi Hx Hlo Hhi HC. pose proof (f4_sh_lo lo Hlo). pose proof (f4_sh_hi_le hi Hhi).
  unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in *. lia.
Qed.

(* Every registered global lies in the image, below AC.GT: checked by computation over AF.frame_AG. *)
Definition f4_ag_ok : bool :=
  forallb (fun p => (0 <=? fst p) && (fst p + snd p <=? AC.GT)) AF.frame_AG.

Lemma f4_ag_true : f4_ag_ok = true.
Proof. vm_compute. reflexivity. Qed.

Lemma f4_ag_lt : forall a, in_globals AF.frame_AG a -> 0 <= a < AC.GT.
Proof.
  intros a (lo & n & Hin & Hr).
  pose proof (proj1 (forallb_forall _ _) f4_ag_true (lo, n) Hin) as H.
  apply andb_prop in H as (H1 & H2). apply Z.leb_le in H1. apply Z.leb_le in H2. cbn in H1, H2. lia.
Qed.

(* One byte of an addressable range. *)
Lemma f4_addr1 : forall m p n a, addressable m p n -> p <= a < p + n -> addressable m a 1.
Proof.
  intros m p n a (H0 & Hn & Hhi & Hall) Hx.
  split; [lia|]. split; [lia|]. split; [lia|].
  intros i Hi. replace (a + i) with (p + (a - p + i)) by lia. apply Hall. lia.
Qed.

(* A byte of a CB cell is present. *)
Lemma f4_cell_byte : forall m a n bs x, rw_cells rsegs m a [CB n bs] -> a <= x < a + Z.of_nat n ->
  exists b, mrd rsegs m (wa x) = Some b.
Proof.
  intros m a n bs x ((Hwf & Hb) & _) Hx.
  cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb.
  destruct Hwf as (Hlen & _). cbn [cell_wf] in Hlen.
  destruct Hb as (H0 & H1 & Hall).
  assert (Hi : (Z.to_nat (x - a) < length bs)%nat) by (rewrite Hlen; lia).
  pose proof (Hall (Z.to_nat (x - a)) Hi) as Hm.
  rewrite Z2Nat.id in Hm by lia. replace (a + (x - a)) with x in Hm by lia.
  destruct (nth_error bs (Z.to_nat (x - a))) as [b|] eqn:E;
    [exists b; exact Hm | apply nth_error_None in E; lia].
Qed.

(* ---- the five frame shadow bytes ---- *)

(* The five frame shadow bytes the 0x81e54 block writes (s3+22..s3+26, s3 = S(fr)): the shadow of the 36 parse
   output cells [fr + 176, fr + 212) and of the rest of their last granule. *)
Definition f4_Wsh (fr : Z) : list (Z * Z) := [(Sfr fr + 22, Sfr fr + 27)].

Lemma f4_Wsh_cases : forall fr x, Frame.outside (f4_Wsh fr) x \/ (Sfr fr + 22 <= x < Sfr fr + 27).
Proof.
  intros fr x. unfold f4_Wsh. cbn [Frame.outside].
  destruct (Z_le_gt_dec (Sfr fr + 22) x); [destruct (Z_lt_ge_dec x (Sfr fr + 27))|].
  - right; lia.
  - left. split; [lia | exact I].
  - left. split; [lia | exact I].
Qed.

(* Any app byte is outside the five frame shadow bytes (they lie in the shadow, between LOWMEM_END and
   HIGHMEM_BEG). *)
Lemma f4_Wsh_app : forall fr x, 0 <= fr -> fr + 216 <= APPMEM_END -> app_mem x -> Frame.outside (f4_Wsh fr) x.
Proof.
  intros fr x H0 H1 Hx. unfold f4_Wsh. cbn [Frame.outside]. split; [|exact I]. intros HC.
  pose proof (f4_sh_lo fr H0) as L1. pose proof (f4_sh_hi_le (fr + 216) ltac:(lia)) as L2.
  assert (E : shadow_addr (fr + 216) = Sfr fr + 27).
  { unfold Sfr, shadow_addr. replace (fr + 216) with (fr + 27 * 8) by lia. rewrite Z.div_add by lia. lia. }
  unfold Sfr in HC. rewrite E in L2. unfold Sfr in L2.
  unfold app_mem in Hx. lia.
Qed.

(* The 36 output cells [fr+176, fr+212) are addressable once the five frame shadow bytes mark them. *)
Lemma f4_addr_o : forall m fr, 0 <= fr -> fr mod 32 = 0 ->
  (forall a, fr <= a < fr + FRAME_BYTES -> app_mem a) -> fr + 216 <= APPMEM_END ->
  bytes_at rsegs m (Sfr fr + 22) [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 4] ->
  addressable m (fr + 176) 36.
Proof. pose proof FRAME_BYTES_val as HFBval. pose proof FRAME_SHADOW_val as HFSval.
  intros m fr H0 Hm32 Happ Hend Hbs.
  assert (Hm8 : fr mod 8 = 0) by (Z.div_mod_to_equations; lia).
  pose proof Hbs as (Hb0 & Hbl & Hb).
  split; [lia|]. split; [lia|]. split; [lia|].
  intros i Hi. unfold addr_byte. split; [apply Happ; lia|].
  assert (Hi8lo : 0 <= i / 8) by (apply Z.div_pos; lia).
  assert (Hi8hi : i / 8 <= 4) by (Z.div_mod_to_equations; lia).
  assert (Hshadow : shadow_addr (fr + 176 + i) = Sfr fr + 22 + i / 8).
  { unfold Sfr, shadow_addr.
    assert (E : (fr + 176 + i) / 8 = fr / 8 + 22 + i / 8) by (Z.div_mod_to_equations; lia).
    rewrite E. lia. }
  set (gi := Z.to_nat (i / 8)).
  assert (Hgeq : i / 8 = Z.of_nat gi) by (unfold gi; rewrite Z2Nat.id by lia; reflexivity).
  pose proof (Hb gi ltac:(cbn [length]; unfold gi; lia)) as HE.
  rewrite Hshadow, Hgeq.
  assert (Hmod : (fr + 176 + i) mod 8 = i mod 8) by (Z.div_mod_to_equations; lia).
  destruct gi as [|[|[|[|[|gi]]]]]; cbn [nth_error] in HE;
    try (exfalso; rewrite Hgeq in Hi8hi; cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in Hi8hi; lia).
  - exists (Z_to_bv 8 0). split; [exact HE|]. left. reflexivity.
  - exists (Z_to_bv 8 0). split; [exact HE|]. left. reflexivity.
  - exists (Z_to_bv 8 0). split; [exact HE|]. left. reflexivity.
  - exists (Z_to_bv 8 0). split; [exact HE|]. left. reflexivity.
  - exists (Z_to_bv 8 4). split; [exact HE|].
    right. assert (Hsgn : bv_signed (Z_to_bv 8 4) = 4) by (vm_compute; reflexivity).
    rewrite Hsgn. split; [|lia].
    assert (Hieq : i / 8 = 4) by (rewrite Hgeq; reflexivity).
    assert (i mod 8 < 4) by (Z.div_mod_to_equations; lia). lia.
Qed.

(* The new 392-byte frame shadow list after the five stores. *)
Lemma f4_shnew : forall W fr mem mem' sh l5,
  bytes_at rsegs mem (Sfr fr) sh -> length sh = Z.to_nat FRAME_SHADOW -> Frame.munch W mem mem' ->
  (forall x, Sfr fr <= x < Sfr fr + 22 -> Frame.outside W x) ->
  (forall x, Sfr fr + 27 <= x < Sfr fr + FRAME_SHADOW -> Frame.outside W x) ->
  bytes_at rsegs mem' (Sfr fr + 22) l5 -> length l5 = 5%nat ->
  bytes_at rsegs mem' (Sfr fr) (firstn 22 sh ++ l5 ++ skipn 27 sh) /\
  length (firstn 22 sh ++ l5 ++ skipn 27 sh) = Z.to_nat FRAME_SHADOW.
Proof. pose proof FRAME_BYTES_val as HFBval. pose proof FRAME_SHADOW_val as HFSval.
  intros W fr mem mem' sh l5 Hsh Hlen MU Hlo Hhi H5 Hl5.
  assert (L22 : length (firstn 22 sh) = 22%nat) by (rewrite firstn_length_le; lia).
  assert (L27 : length (skipn 27 sh) = 365%nat) by (rewrite length_skipn; lia).
  split; [|rewrite !length_app, L22, Hl5, L27; reflexivity].
  pose proof Hsh as Hsh1. rewrite <- (firstn_skipn 22 sh) in Hsh1.
  apply Mem.bytes_at_app in Hsh1. destruct Hsh1 as (Hf & _).
  pose proof Hsh as Hsh2. rewrite <- (firstn_skipn 27 sh) in Hsh2.
  apply Mem.bytes_at_app in Hsh2. destruct Hsh2 as (_ & Hs).
  rewrite firstn_length_le in Hs by lia. change (Z.of_nat 27) with 27 in Hs.
  apply Mem.bytes_at_app. split.
  - eapply fl_bytes; [exact Hf | exact MU |]. rewrite L22. change (Z.of_nat 22) with 22.
    intros x Hx. apply Hlo. lia.
  - rewrite L22. change (Z.of_nat 22) with 22. apply Mem.bytes_at_app. split; [exact H5|].
    rewrite Hl5. change (Z.of_nat 5) with 5. replace (Sfr fr + 22 + 5) with (Sfr fr + 27) by lia.
    eapply fl_bytes; [exact Hs | exact MU |]. rewrite L27. change (Z.of_nat 365) with 365.
    intros x Hx. apply Hhi. lia.
Qed.

(* store_ok at an explicit address b inside a carried writable range [a, a + n). *)
Lemma f4_sok_at : forall m a n (j : nat) b,
  wr_at rsegs m a n -> 0 <= b - a -> (b - a) + Z.of_nat j <= n ->
  store_ok rsegs m (wa b) j = true.
Proof.
  intros m a n j b H H1 H2.
  replace b with (a + (b - a)) by lia.
  exact (wr_at_store_ok rsegs m a n (b - a) j H H1 H2).
Qed.

(* store_ok for the current memory at the exact address the engine computes. *)
Ltac f4_sokb W b n :=
  match goal with
  | |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      let H := fresh "HS" in
      assert (H : store_ok rsegs mm (wa b) n = true)
        by (eapply (f4_sok_at mm _ _ n b); [repeat apply wr_at_write; exact W | lia | lia])
  end.

Ltac f4_bw :=
  repeat (apply bytes_at_write_other; [ | lia | simpl_sizes; lia | simpl_sizes; lia]).

(* 0x81e54-0x81e70: the spill of s7 + 18 to [s1 + 200] and the five frame shadow bytes; the spill word holds
   phi + 18 at the end (the shadow bytes lie below the save area). *)
Lemma f4_dbc_st :
  forall (ra0 sp gp tp t0 t1 t2 s0 a0i a1i a2i a3 a4 a5 a6 a7 s2i s4 s5 s6 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (A fr phi : Z),
    0 <= A -> A + 208 <= 2 ^ 64 -> 0 <= fr -> 0 <= Sfr fr -> 0 <= phi < 2 ^ 64 ->
    Sfr fr + 27 <= 2 ^ 64 -> Sfr fr + 27 <= A + 200 ->
    wr_at rsegs m (A + 200) 8 -> wr_at rsegs m (Sfr fr + 22) 5 ->
    LE.evt rsegs
      (fun ms => exists (m1 m2 : word -> option byte) (a0' : word),
         ms = MS (mkR ra0 sp gp tp t0 t1 t2 s0 (Z_to_bv 64 A) a0' a1i a2i a3 a4 a5 a6 a7 s2i
                      (Z_to_bv 64 (Sfr fr)) s4 s5 s6 (Z_to_bv 64 phi) s8 s9 s10 s11 t3 t4 t5 t6)
                 Fr (Z_to_bv 64 0x81e74) fc None m2 (seg_rom rsegs) /\
         Frame.munch [(A + 200, A + 208)] m m1 /\ Frame.wmono rsegs m m1 /\
         Frame.munch (f4_Wsh fr) m1 m2 /\ Frame.wmono rsegs m1 m2 /\
         (forall lo hi, stk rsegs m lo hi -> stk rsegs m1 lo hi) /\
         (forall lo hi, stk rsegs m1 lo hi -> stk rsegs m2 lo hi) /\
         bytes_at rsegs m2 (Sfr fr + 22) [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 4] /\
         q64 m2 (A + 200) (phi + 18))
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 (Z_to_bv 64 A) a0i a1i a2i a3 a4 a5 a6 a7 s2i
               (Z_to_bv 64 (Sfr fr)) s4 s5 s6 (Z_to_bv 64 phi) s8 s9 s10 s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x81e54) fc None m (seg_rom rsegs)).
Proof.
  intros ra0 sp gp tp t0 t1 t2 s0 a0i a1i a2i a3 a4 a5 a6 a7 s2i s4 s5 s6 s8 s9 s10 s11 t3 t4 t5 t6
    Fr fc m A fr phi HA0 HAhi Hfr0 HSfr0 Hphi HSfrhi HSA Wa Wsh.
  (* 0x81e54 addi a0,s7,18 ; 0x81e58 sd a0,200(s1) *)
  step.
  f4_sokb Wa (A + 200) 8%nat. step.
  lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (MU1 : Frame.munch [(A + 200, A + 208)] m mm)
        by (apply (munch_write _ m m (A + 200));
            [apply munch_refl | lia | simpl_sizes; lia | cbn [inside]; simpl_sizes; left; lia]);
      assert (WM1 : Frame.wmono rsegs m mm) by (apply wmono_write; apply wmono_refl);
      assert (ST1 : forall lo hi, stk rsegs m lo hi -> stk rsegs mm lo hi)
        by (intros lo hi Hs; apply stk_write; [exact Hs | lia | simpl_sizes; lia]);
      assert (HQ1 : q64 mm (A + 200) (phi + 18))
        by (unfold q64;
            lazymatch mm with
            | write_to_mem _ _ ?bs =>
                replace bs with (le8 (Z_to_bv 64 (phi + 18)));
                [ apply bytes_at_write_same; [lia | simpl_sizes; lia]
                | first [ reflexivity
                        | (rewrite (MState.unsigned_lit phi) by lia; reflexivity)
                        | (unfold PropExec.v_addi; rewrite (MState.unsigned_lit phi) by lia; reflexivity) ] ]
            end)
  end.
  (* 0x81e5c sb zero,22(s3) .. 0x81e68 sb zero,25(s3) *)
  f4_sokb Wsh (Sfr fr + 22) 1%nat. step.
  f4_sokb Wsh (Sfr fr + 23) 1%nat. step.
  f4_sokb Wsh (Sfr fr + 24) 1%nat. step.
  f4_sokb Wsh (Sfr fr + 25) 1%nat. step.
  (* 0x81e6c li a0,4 ; 0x81e70 sb a0,26(s3) *)
  step.
  f4_sokb Wsh (Sfr fr + 26) 1%nat. step.
  apply evt_done.
  eexists. eexists. eexists.
  split; [reflexivity|].
  split; [exact MU1|].
  split; [exact WM1|].
  split.
  { unfold f4_Wsh.
    repeat (apply munch_write; [ | lia | simpl_sizes; lia | cbn [inside]; simpl_sizes; lia ]).
    apply munch_refl. }
  split.
  { do 5 apply wmono_write. apply wmono_refl. }
  split; [exact ST1|].
  split.
  { intros lo hi Hs. do 5 (apply stk_write; [ | lia | simpl_sizes; lia ]). exact Hs. }
  split; [| unfold q64 in HQ1 |- *; f4_bw; exact HQ1].
  apply f4_bytes_cons.
  { rewrite <- f4_le1_0. f4_bw. apply bytes_at_write_same; [lia | simpl_sizes; lia]. }
  replace (Sfr fr + 22 + 1) with (Sfr fr + 23) by lia.
  apply f4_bytes_cons.
  { rewrite <- f4_le1_0. f4_bw. apply bytes_at_write_same; [lia | simpl_sizes; lia]. }
  replace (Sfr fr + 23 + 1) with (Sfr fr + 24) by lia.
  apply f4_bytes_cons.
  { rewrite <- f4_le1_0. f4_bw. apply bytes_at_write_same; [lia | simpl_sizes; lia]. }
  replace (Sfr fr + 24 + 1) with (Sfr fr + 25) by lia.
  apply f4_bytes_cons.
  { rewrite <- f4_le1_0. f4_bw. apply bytes_at_write_same; [lia | simpl_sizes; lia]. }
  replace (Sfr fr + 25 + 1) with (Sfr fr + 26) by lia.
  rewrite <- f4_le1_4. f4_bw. apply bytes_at_write_same; [lia | simpl_sizes; lia].
Qed.

(* AH, ownership and the stack bounds across the five frame shadow bytes: real arm by a_laws_store (each written
   byte is the shadow of a frame byte, a real-stack byte above stklo); side arm by a_fs_ok_store_AH (the frame lies
   in FS, the written bytes are shadows of FS bytes, and they are not app memory, so not metadata). *)
Lemma f4_fr_ah : forall g fr hb regs mem mem' md,
  FRA B APIf ra g fr hb regs mem md ->
  Frame.munch (f4_Wsh fr) mem mem' -> Frame.wmono rsegs mem mem' ->
  (forall q, 0 <= q < 2 ^ 64 -> (exists b, mbyte rsegs mem q = Some b) -> exists b, mbyte rsegs mem' q = Some b) ->
  AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) (hb ++ g_H g) mem' md /\
  (forall q, AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) (hb ++ g_H g) mem' md q <->
             AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) (hb ++ g_H g) mem md q) /\
  AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem' md = AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md /\
  AC.aa_stkhi AC.ASYMS AsanRTInv.RT (APIf rc) mem' md = AC.aa_stkhi AC.ASYMS AsanRTInv.RT (APIf rc) mem md.
Proof. pose proof FRAME_BYTES_val as HFBval. pose proof FRAME_SHADOW_val as HFSval.
  intros g fr hb regs mem mem' md HFRA MU WM HPRES.
  pose proof (fra_app B APIf ra g fr hb regs mem md HFRA) as (Hgt & Happ).
  destruct HFRA as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA416 & HS4 & HAPP &
    Hspill & Hsel & Hfr24 & Hloc & Hhdr1 & Hhdr2 & Hsh & Hwin & Hsaved & Herrno & HAG & HWA &
    HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive).
  pose proof (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) as LAWS.
  assert (Hw2 : forall a, 0 <= a < 2 ^ 64 -> writable_at rsegs mem a -> writable_at rsegs mem' a)
    by (intros a _ Hw; exact (WM (Z_to_bv 64 a) Hw)).
  assert (Hub : fr + FRAME_BYTES <= APPMEM_END).
  { assert (Ha : app_mem (fr + FRAME_BYTES - 1)) by (apply Happ; lia).
    unfold app_mem, LOWMEM_END, APPMEM_END, HIGHMEM_BEG in Ha. unfold APPMEM_END. destruct Ha as [Ha|Ha]; lia. }
  unfold AC.GT in Hgt.
  destruct Hloc as [(_ & _ & Hreal)|(_ & _ & Hfs & _)].
  - (* real arm: every written address is a_store_ok *)
    assert (P1 : forall a, 0 <= a < 2 ^ 64 ->
              ~ AC.a_store_ok (hb ++ g_H g) (AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md) a ->
              mem' (Z_to_bv 64 a) = mem (Z_to_bv 64 a)).
    { intros a Ha Hn. apply MU. rewrite MState.unsigned_lit by exact Ha.
      destruct (f4_Wsh_cases fr a) as [Ho | Hb]; [exact Ho | exfalso].
      apply Hn. unfold AC.a_store_ok. right; right; right. exists (fr + 8 * (a - Sfr fr)).
      split; [rewrite f4_fr_sh; lia | right; left; apply Hreal; lia]. }
    exact (f4_law_store (hb ++ g_H g) mem mem' md HAH P1 Hw2).
  - (* side arm: the FS word at tp, the frame inside FS *)
    destruct (Hfs fr ltac:(lia)) as (b & Hbr & Hwb & Hbin).
    destruct (Hfs (fr + FRAME_BYTES - 1) ltac:(lia)) as (b' & Hbr' & Hwb' & Hbin').
    assert (Ebb : b' = b).
    { pose proof (f4_wm_eq _ _ _ _ Hwb' Hwb) as E. rewrite !Z.mod_small in E by lia. exact E. }
    subst b'.
    pose proof (f4_law_fs_place _ _ _ b HAH Hwb Hbr) as (_ & Hstkb & _ & Happfs).
    assert (Hsz : b + AC.FS_SIZE <= 2 ^ 64) by (unfold AC.FS_SIZE, AF.SLOT_STACK, APPMEM_END in *; lia).
    assert (Hmeta : forall q, fs_meta b q -> Frame.outside (f4_Wsh fr) q).
    { intros q Hq. pose proof (fs_meta_below b q Hq) as Hq1. pose proof (f4_fs_meta_lo b q Hq) as Hq0.
      assert (Hqa : app_mem q) by (apply Happfs; unfold AC.FS_SIZE; lia).
      destruct (f4_Wsh_cases fr q) as [Ho | Hb]; [exact Ho | exfalso].
      apply (AsanRTFacts.app_not_shadow q Hqa).
      replace q with (shadow_addr (fr + 8 * (q - Sfr fr))) by (rewrite f4_fr_sh; lia).
      apply AsanRTFacts.shadow_of_app, Happ. lia. }
    assert (Hagree : forall q, 0 <= q < 2 ^ 64 ->
              ~ AC.a_store_ok (hb ++ g_H g) (AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md) q ->
              ~ (b <= q < b + AC.FS_SIZE) ->
              ~ (exists c, b <= c < b + AC.FS_SIZE /\ q = shadow_addr c) ->
              mem' (Z_to_bv 64 q) = mem (Z_to_bv 64 q)).
    { intros q Hq _ Hnr Hnsh. apply MU. rewrite MState.unsigned_lit by exact Hq.
      destruct (f4_Wsh_cases fr q) as [Ho | Hb]; [exact Ho | exfalso].
      apply Hnsh. exists (fr + 8 * (q - Sfr fr)).
      split; [unfold AC.FS_SIZE in *; lia | rewrite f4_fr_sh; lia]. }
    exact (a_fs_ok_store_AH AC.ASYMS _ _ _ _ (f4_Wsh fr) (hb ++ g_H g) mem mem' md b LAWS HAH Hwb Hbr Hsz MU
      Hw2 HPRES Hmeta Hagree).
Qed.

(* FRA and ENT across the five frame shadow bytes [S(fr)+22, S(fr)+27): sl_fr_meta with the new 392-byte shadow
   list, and ent_store (the bytes are frame shadow bytes). *)
Lemma f4_fra_sh : forall g fr hb regs mem mem' md,
  FRA B APIf ra g fr hb regs mem md -> ENT APIf g hb mem md ->
  Frame.munch (f4_Wsh fr) mem mem' -> Frame.wmono rsegs mem mem' ->
  bytes_at rsegs mem' (Sfr fr + 22) [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 4] ->
  FRA B APIf ra g fr hb regs mem' md /\ ENT APIf g hb mem' md.
Proof. pose proof FRAME_BYTES_val as HFBval. pose proof FRAME_SHADOW_val as HFSval.
  intros g fr hb regs mem mem' md HFRA HENT MU WM H5.
  assert (HPRES : forall q, 0 <= q < 2 ^ 64 -> (exists b, mbyte rsegs mem q = Some b) ->
                    exists b, mbyte rsegs mem' q = Some b).
  { intros q Hq Hb. destruct (f4_Wsh_cases fr q) as [Ho | Hin].
    - rewrite (KindBGlue.mbyte_munch rsegs (f4_Wsh fr) mem mem' q MU Hq Ho). exact Hb.
    - apply (f4_pres_at mem' (Sfr fr + 22) _ q H5). cbn [length]. lia. }
  destruct (f4_fr_ah g fr hb regs mem mem' md HFRA MU WM HPRES) as (HAH' & Hown & HSTK & HSTKhi).
  pose proof (fra_app B APIf ra g fr hb regs mem md HFRA) as (Hgt & Happ).
  pose proof HFRA as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA416 & HS4 & HAPP &
    Hspill & Hsel & Hfr24 & Hloc & Hhdr1 & Hhdr2 & Hsh & Hwin & Hsaved & Herrno & HAG & HWA &
    HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive).
  pose proof (AC.a_laws_stack_high _ _ _ _ _ (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) _ _ _ HAH) as Hhi.
  assert (HKh : HIGHMEM_BEG = 17594333495296) by (vm_compute; reflexivity).
  assert (HKa : APPMEM_END = 140737488355328) by (vm_compute; reflexivity).
  assert (HKs : AF.SLOT_STACK = 1048576) by (vm_compute; reflexivity).
  assert (HKl : LOWMEM_END = 2147450880) by (vm_compute; reflexivity).
  assert (HKk : ASAN_K = 2147450880) by (vm_compute; reflexivity).
  assert (HKg : AC.GT = 6283264) by (vm_compute; reflexivity).
  assert (HA64 : 0 <= A < 2 ^ 64).
  { pose proof Hwin as HW0. unfold stk in HW0. destruct HW0 as (Hw0 & Hw1 & _). lia. }
  assert (Hub : fr + FRAME_BYTES <= APPMEM_END).
  { assert (Ha : app_mem (fr + FRAME_BYTES - 1)) by (apply Happ; lia).
    unfold app_mem in Ha. destruct Ha as [Ha|Ha]; lia. }
  assert (Hfr0 : 0 <= fr) by lia.
  assert (HSfr : LOWMEM_END <= Sfr fr /\ Sfr fr + FRAME_SHADOW <= HIGHMEM_BEG).
  { unfold Sfr, shadow_addr. Z.div_mod_to_equations. lia. }
  assert (Hout : forall x, (x < Sfr fr + 22 \/ Sfr fr + 27 <= x) -> Frame.outside (f4_Wsh fr) x).
  { intros x Hx. unfold f4_Wsh. cbn [Frame.outside]. split; [lia | exact I]. }
  assert (HA9 : forall A', getr regs 9 = Z_to_bv 64 A' -> 0 <= A' < 2 ^ 64 -> A' = A).
  { intros A' HA' HA'r. apply f4_id; [lia | lia |]. rewrite <- HA'. exact Hr9. }
  assert (HRO : ro_agree rsegs mem').
  { apply (sl_ro_keep (f4_Wsh fr) mem mem' Hro MU). intros x Hx. apply Hout. left. lia. }
  split.
  - apply (sl_fr_meta B APIf ra empty FF g fr hb regs regs mem mem' md (f4_Wsh fr) HFRA MU WM HRO).
    + apply f4_rt. intros lo hi Hin. unfold f4_Wsh in Hin. cbn [In] in Hin.
      destruct Hin as [E|[]]. injection E as <- <-. lia.
    + exact HAH'.
    + exact HSTK.
    + exact Happ.
    + exact Hgt.
    + destruct Hsh as (sh & Hbytes & Hlen).
      exists (firstn 22 sh ++ [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 4] ++ skipn 27 sh).
      apply (f4_shnew (f4_Wsh fr) fr mem mem' sh _ Hbytes Hlen MU).
      * intros x Hx. apply Hout. left. lia.
      * intros x Hx. apply Hout. right. lia.
      * exact H5.
      * reflexivity.
    + intros x _ _ Hns. apply Hout. lia.
    + intros A' HA' HA'r x Hx. rewrite (HA9 A' HA' HA'r) in Hx. apply Hout. right. lia.
    + intros x Hx. apply Hout. right. lia.
    + intros A' HA' HA'r x Hx. rewrite (HA9 A' HA' HA'r) in Hx. apply Hout. right. lia.
    + intros x Hx. left. apply Hout. right. lia.
    + intros a Ha. pose proof (f4_ag_lt a Ha) as Hab.
      apply (addr1_munch (f4_Wsh fr) mem mem' a MU); [|exact (HAG a Ha)].
      apply Hout. left. pose proof (f4_sh_mono a fr ltac:(lia)). unfold Sfr. lia.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + reflexivity.
  - eapply ent_store with (W := f4_Wsh fr); [exact HENT | exact HFRA | exact MU | | exact HSTK | exact HSTKhi |].
    + intros x Hx. destruct (f4_Wsh_cases fr x) as [Ho|Hin]; [left; exact Ho | right; right; right; lia].
    + intros a _ Ho. exact (proj2 (Hown a) Ho).
Qed.

(* ---- the parse call's write set ---- *)

Lemma f4_fsc : forall FS, fs_hint FS 1 = FS + 8 /\ fs_flag FS 1 0 = FS + 20480 /\ fs_M 1 = 8192 /\
  fs_frame FS 1 0 = FS + 1085440 /\ fs_frame FS 1 (fs_M 1) = FS + 2134016.
Proof.
  intros FS. unfold fs_hint, fs_flag, fs_frame, fs_M, fs_B.
  change (Z.of_nat 1) with 1. change (2 ^ (15 - 1)) with 16384. change (2 ^ (14 - 1)) with 8192.
  repeat split; lia.
Qed.

Lemma f4_fpw1 : forall FS, fp_w [1%nat] FS =
  [(FS + 8, FS + 16); (FS + 20480, FS + 28672); (FS + 1085440, FS + 2134016);
   (shadow_addr (FS + 1085440), shadow_addr (FS + 2134016))].
Proof.
  intros FS. unfold fp_w, fp_w1. cbn [flat_map app].
  destruct (f4_fsc FS) as (F1 & F2 & F3 & F4 & F5).
  rewrite F5, F4, F1, F2, F3.
  replace (FS + 8 + 8) with (FS + 16) by lia. replace (FS + 20480 + 8192) with (FS + 28672) by lia.
  reflexivity.
Qed.

Lemma f4_fs_frame0 : forall FS, fs_frame FS 0%nat 0 = FS + 36864.
Proof.
  intros FS. unfold fs_frame, fs_B. cbn [Z.of_nat]. change (2 ^ 20) with 1048576.
  change (2 ^ 0) with 1. lia.
Qed.

Lemma f4_afs_flag1 : forall FS j, AC.a_fs_flag FS 1%nat j = FS + 20480 + j.
Proof.
  intros FS j. unfold AC.a_fs_flag.
  change (2 ^ (15 - Z.of_nat 1)) with 16384. change (2 ^ 15) with 32768. lia.
Qed.

(* A flag byte of a class other than 1 lies at or above FS + 4096 and apart from the class-1 flag bytes
   [FS + 20480, FS + 28672). *)
Lemma f4_flag_other : forall FS c j, (c <= 10)%nat -> c <> 1%nat -> 0 <= j < AC.a_fs_M c ->
  FS + 4096 <= AC.a_fs_flag FS c j /\ (AC.a_fs_flag FS c j < FS + 20480 \/ FS + 28672 <= AC.a_fs_flag FS c j).
Proof.
  intros FS c j Hc Hc1 Hj. unfold AC.a_fs_flag, AC.a_fs_M in *.
  destruct c as [|[|c]].
  - change (2 ^ (14 - Z.of_nat 0)) with 16384 in Hj. change (2 ^ (15 - Z.of_nat 0)) with 32768. lia.
  - exfalso. apply Hc1. reflexivity.
  - assert (P : 2 ^ (15 - Z.of_nat (S (S c))) <= 2 ^ 13) by (apply Z.pow_le_mono_r; lia). lia.
Qed.

(* The writes of the parse call (its munch list) with o <> 0. *)
Definition f4_PW (o S FS : Z) : list (Z * Z) :=
  reac_ctrl_parse_fp o S ++ fp_w [1%nat] FS ++
  [(shadow_addr (S - REAC_CTRL_PARSE_K), shadow_addr S)].

Lemma f4_PW_eq : forall o S FS, o <> 0 -> f4_PW o S FS =
  [(o, o + 36); (S - 8800, S); (FS + 8, FS + 16); (FS + 20480, FS + 28672); (FS + 1085440, FS + 2134016);
   (shadow_addr (FS + 1085440), shadow_addr (FS + 2134016)); (shadow_addr (S - 8800), shadow_addr S)].
Proof.
  intros o S FS Ho. unfold f4_PW, reac_ctrl_parse_fp, REAC_CTRL_PARSE_K.
  replace (o =? 0) with false by (symmetry; apply Z.eqb_neq; exact Ho).
  rewrite f4_fpw1. cbn [app]. reflexivity.
Qed.

Lemma f4_PW_out : forall o S FS x, o <> 0 ->
  ~ (o <= x < o + 36) -> ~ (S - 8800 <= x < S) -> ~ (FS + 8 <= x < FS + 16) ->
  ~ (FS + 20480 <= x < FS + 28672) -> ~ (FS + 1085440 <= x < FS + 2134016) ->
  ~ (shadow_addr (FS + 1085440) <= x < shadow_addr (FS + 2134016)) ->
  ~ (shadow_addr (S - 8800) <= x < shadow_addr S) ->
  Frame.outside (f4_PW o S FS) x.
Proof.
  intros o S FS x Ho N1 N2 N3 N4 N5 N6 N7. rewrite (f4_PW_eq o S FS Ho). cbn [Frame.outside].
  repeat split; try exact I; assumption.
Qed.

(* An app byte apart from the three app ranges of the write set is outside it. *)
Lemma f4_PW_out_app : forall o S FS x, o <> 0 -> app_mem x -> 0 <= FS -> FS + 2134016 <= APPMEM_END ->
  0 <= S - 8800 -> S <= APPMEM_END ->
  ~ (o <= x < o + 36) -> ~ (S - 8800 <= x < S) -> ~ (FS + 8 <= x < FS + 16) ->
  ~ (FS + 20480 <= x < FS + 28672) -> ~ (FS + 1085440 <= x < FS + 2134016) ->
  Frame.outside (f4_PW o S FS) x.
Proof.
  intros o S FS x Ho Hx HF0 HF1 HS0 HS1 N1 N2 N3 N4 N5.
  apply f4_PW_out; try assumption; apply f4_app_out_sh; (assumption || lia).
Qed.

(* The shadow byte of an app byte y is outside the write set when y is apart, granule by granule, from the
   class-1 frames and from the callee window, and the app ranges are in the app halves. *)
Lemma f4_PW_out_sh : forall o S FS y, o <> 0 -> 0 <= y < APPMEM_END ->
  (o + 36 <= LOWMEM_END \/ HIGHMEM_BEG <= o) -> HIGHMEM_BEG <= S - 8800 ->
  (FS + 2134016 <= LOWMEM_END \/ HIGHMEM_BEG <= FS + 8) -> 0 <= FS -> FS mod 8 = 0 -> (S - 8800) mod 8 = 0 ->
  (y < FS + 1085440 \/ FS + 2134016 <= y) -> (y < S - 8800 \/ S <= y) ->
  Frame.outside (f4_PW o S FS) (shadow_addr y).
Proof.
  intros o S FS y Ho Hy Hoa HS HFa HF0 HF8 HS8 Hy1 Hy2.
  pose proof (f4_sh_lo y ltac:(lia)) as L1. pose proof (f4_sh_hi y Hy) as L2.
  apply f4_PW_out; [exact Ho | lia | lia | lia | lia | lia | |].
  - intros [H1 H2]. destruct Hy1 as [Hy1|Hy1].
    + pose proof (f4_sh_lt2 y (FS + 1085440) ltac:(lia) Hy1 ltac:(Z.div_mod_to_equations; lia)). lia.
    + pose proof (f4_sh_mono (FS + 2134016) y Hy1). lia.
  - intros [H1 H2]. destruct Hy2 as [Hy2|Hy2].
    + pose proof (f4_sh_lt2 y (S - 8800) ltac:(lia) Hy2 HS8). lia.
    + pose proof (f4_sh_mono S y Hy2). lia.
Qed.

Lemma f4_PW_lo : forall o S FS lo hi, o <> 0 -> AC.GT <= o -> AC.GT <= FS -> AC.GT + 8800 <= S ->
  In (lo, hi) (f4_PW o S FS) -> AC.GT <= lo.
Proof.
  intros o S FS lo hi Ho H1 H2 H3 Hin. rewrite (f4_PW_eq o S FS Ho) in Hin.
  unfold AC.GT, shadow_addr, ASAN_K in *. cbn [In] in Hin.
  repeat (destruct Hin as [Hin|Hin]; [injection Hin as <- <-;
    first [lia | (assert (0 <= (FS + 1085440) / 8) by (apply Z.div_pos; lia); lia)
               | (assert (0 <= (S - 8800) / 8) by (apply Z.div_pos; lia); lia)] |]); contradiction.
Qed.

(* ---- the side-stack premises of the parse call, built from the base (after Seg/F9.v's f9_fp_call) ---- *)

Lemma f4_dj_pt : forall (Q : Z -> Prop) a b c d, a < b -> c < d ->
  (forall x, a <= x < b -> Q x) -> (forall x, c <= x < d -> ~ Q x) -> RcLay.ly_dj a b c d.
Proof.
  intros Q a b c d Hab Hcd HQ HnQ. unfold RcLay.ly_dj.
  destruct (Z_le_gt_dec b c) as [H|H]; [left; exact H|].
  destruct (Z_le_gt_dec d a) as [H2|H2]; [right; exact H2|].
  exfalso. apply (HnQ (Z.max a c) ltac:(lia)). apply HQ. lia.
Qed.

Lemma f4_le_bytes_to_Z : forall bs : list byte, Z_to_le_bytes (length bs) (bytes_le_to_Z bs) = bs.
Proof.
  induction bs as [|b bs IH]; [reflexivity|]. cbn [length Z_to_le_bytes bytes_le_to_Z].
  pose proof (f4_byte_range b) as Hb.
  assert (HR : 0 <= bytes_le_to_Z bs).
  { rewrite bytes_le_to_Z_le_val. exact (proj1 (le_val_range _ (bytes_ok_map bs))). }
  rewrite lor_shiftl8_add by lia.
  f_equal.
  - apply bv_eq. rewrite Z_to_bv_unsigned. change (bv_wrap 8 ?z) with (z mod 2 ^ 8)%Z.
    change (2 ^ 8) with 256.
    replace (bv_unsigned b + 256 * bytes_le_to_Z bs) with (bv_unsigned b + bytes_le_to_Z bs * 256) by lia.
    rewrite Z.mod_add by lia. apply Z.mod_small. lia.
  - rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 8) with 256.
    replace (bv_unsigned b + 256 * bytes_le_to_Z bs) with (bv_unsigned b + bytes_le_to_Z bs * 256) by lia.
    rewrite Z.div_add, Z.div_small by lia. cbn [Z.add]. exact IH.
Qed.

Lemma f4_le8_of_bytes : forall bs : list byte, length bs = 8%nat -> le8 (Z_to_bv 64 (bytes_le_to_Z bs)) = bs.
Proof.
  intros bs L. unfold le8, word_to_le_bytes. rewrite Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_modulus 64) with (2 ^ 64). rewrite Z_to_le_bytes_mod by (cbn; lia).
  rewrite <- L at 1. apply f4_le_bytes_to_Z.
Qed.

Lemma f4_byte_at : forall m a b, 0 <= a -> a + 1 <= 2 ^ 64 -> mbyte rsegs m a = Some b ->
  bytes_at rsegs m a [b].
Proof.
  intros m a b H0 H1 Hb. split; [exact H0|]. split; [cbn [length]; lia|].
  intros i Hi. cbn [length] in Hi. assert (Ei : i = 0%nat) by lia. subst i.
  cbn [nth_error]. replace (a + Z.of_nat 0) with a by lia. exact Hb.
Qed.

Lemma f4_bytes_PN : forall (P : byte -> Prop) m a k, 0 <= a -> a + Z.of_nat k <= 2 ^ 64 ->
  (forall i, 0 <= i < Z.of_nat k -> exists b, mbyte rsegs m (a + i) = Some b /\ P b) ->
  exists bs, bytes_at rsegs m a bs /\ length bs = k /\ Forall P bs.
Proof.
  intros P m a k. revert a. induction k as [|k IH]; intros a H0 H1 H.
  - exists []. split; [|split; [reflexivity | constructor]].
    split; [exact H0|]. split; [cbn [length]; lia|]. intros i Hi; cbn [length] in Hi; lia.
  - destruct (H 0 ltac:(lia)) as (b & Hb & HPb).
    assert (Hrec : forall i, 0 <= i < Z.of_nat k -> exists b', mbyte rsegs m (a + 1 + i) = Some b' /\ P b').
    { intros i Hi. destruct (H (1 + i) ltac:(lia)) as (b' & Hb' & HP'). exists b'.
      split; [|exact HP']. replace (a + 1 + i) with (a + (1 + i)) by lia. exact Hb'. }
    destruct (IH (a + 1) ltac:(lia) ltac:(lia) Hrec) as (bs & Hbs & Hlen & HPbs).
    exists (b :: bs). split; [|split; [cbn [length]; lia | constructor; assumption]].
    destruct Hbs as (_ & _ & Hnth).
    split; [exact H0|]. split; [cbn [length]; rewrite Hlen; lia|].
    intros i Hi. destruct i as [|i]; cbn [nth_error].
    + replace (a + Z.of_nat 0) with (a + 0) by lia. exact Hb.
    + replace (a + Z.of_nat (S i)) with (a + 1 + Z.of_nat i) by lia.
      apply Hnth. cbn [length] in Hi. lia.
Qed.

Lemma f4_bytes_P : forall (P : byte -> Prop) m a n, 0 <= a -> 0 <= n -> a + n <= 2 ^ 64 ->
  (forall i, 0 <= i < n -> exists b, mbyte rsegs m (a + i) = Some b /\ P b) ->
  exists bs, bytes_at rsegs m a bs /\ Z.of_nat (length bs) = n /\ Forall P bs.
Proof.
  intros P m a n H0 Hn H1 H.
  destruct (f4_bytes_PN P m a (Z.to_nat n) H0 ltac:(rewrite Z2Nat.id by lia; lia)
              ltac:(rewrite Z2Nat.id by lia; exact H)) as (bs & Hbs & Hlen & HP).
  exists bs. split; [exact Hbs|]. split; [rewrite Hlen, Z2Nat.id by lia; reflexivity | exact HP].
Qed.

Lemma f4_word_present : forall m a, 0 <= a -> a + 8 <= 2 ^ 64 ->
  (forall i, 0 <= i < 8 -> exists b, mbyte rsegs m (a + i) = Some b) ->
  exists w : word, bytes_at rsegs m a (le8 w).
Proof.
  intros m a H0 H1 H.
  assert (HP : forall i, 0 <= i < 8 -> exists b, mbyte rsegs m (a + i) = Some b /\ True).
  { intros i Hi. destruct (H i Hi) as (b & Hb). exists b. split; [exact Hb | exact I]. }
  destruct (f4_bytes_P (fun _ => True) m a 8 H0 ltac:(lia) H1 HP) as (bs & Hbs & Hlen & _).
  exists (Z_to_bv 64 (bytes_le_to_Z bs)). rewrite f4_le8_of_bytes by lia. exact Hbs.
Qed.

Ltac f4_num :=
  cbv [RcLay.ly_dj TLS_INDEX REAL_TLS_GET_ADDR TSD_KEY_INITED TSD_KEY
       asan_stack_malloc_c.GOT_CF asan_stack_malloc_c.CF bcmp_wrap_c.GOT_CF bcmp_wrap_c.CF
       GOT_VERBOSITY VERBOSITY DTLS_TPOFF
       RT_TP RT_TSDMAIN RT_GT ASAN_GT AC.as_tp AC.ASYMS AC.GT AC.FS_SIZE FS_SIZE RT_FS_SIZE
       REAC_CTRL_PARSE_K AF.SLOT_STACK FN_STACK HIGHMEM_BEG APPMEM_END LOWMEM_END LOWSHADOW_END HIGHSHADOW_BEG
       ASAN_K] in *; lia.

Ltac f4_dj_split := repeat first [apply Forall_nil | apply Forall_cons]; cbn [fst snd].

(* The callee's side-stack bundle at the call 0x81e80 (o = fr + 176, n = 0): the FakeStack base FS (the word at
   tp, from the runtime's fs cells), its state (a_laws_fs_state), the thread cells (a_laws_thread and the
   runtime's cells), the caller's writes (the callee window and the 36 output cells) apart from the thread cells
   and the side stack's header, and the caller's data range (the 36 output cells) apart from the class-1 bytes:
   the frame is at least 6328320 bytes above FS on both arms (fra_frame). *)
Lemma f4_fp_call : forall g fr hb regs mem md f,
  FRA B APIf ra g fr hb regs mem md ->
  (exists DB, word_mem rsegs mem (AC.as_tp AC.ASYMS + 8) DB /\ 0 <= DB /\ DB + 32 <= 2 ^ 64) ->
  exists FS,
    word_mem rsegs mem (AC.as_tp AC.ASYMS) FS /\ 0 <= FS < 2 ^ 64 /\
    fp [1%nat] mem (AC.as_tp AC.ASYMS) FS (AC.aspZ regs - REAC_CTRL_PARSE_K) (AC.aspZ regs)
      (reac_ctrl_parse_W (fr + 176) (AC.aspZ regs)) (reac_ctrl_parse_D f 0 (fr + 176)) /\
    reac_ctrl_parse_tls mem (AC.as_tp AC.ASYMS) FS (AC.aspZ regs - REAC_CTRL_PARSE_K) (AC.aspZ regs).
Proof. pose proof FRAME_BYTES_val as HFBval. pose proof FRAME_SHADOW_val as HFSval.
  intros g fr hb regs mem md f HFRA (DBp & HDBp & HDBp0 & HDBp1).
  pose proof (fra_app B APIf ra g fr hb regs mem md HFRA) as (Hgt & Happ).
  pose proof (fra_frame B APIf ra g fr hb regs mem md HFRA) as (_ & _ & HFSfr & _).
  pose proof (fra_win B APIf ra g fr hb regs mem md HFRA) as (Hwlo & _).
  destruct HFRA as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA416 & HS4 & HAPP &
    Hspill & Hsel & Hfr24 & Hloc & Hhdr1 & Hhdr2 & Hsh & Hwin & Hsaved & Herrno & HAGf & HWAf &
    HTop1 & HTop2 & HTop3 & Hhb & Hlive).
  rewrite Haspz in Hwlo |- *.
  pose proof (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) as LAWS.
  (* ---- the side stack's base FS ---- *)
  destruct (AsanRTInv.RT_fs_cells _ _ _ HRT)
    as (Htlsidx & Hdtpoff & Hdt & Hdt8 & (FSw & HFSb & HFSok) & (DBw & HDBb & HDBnz)).
  pose proof (bytes_at_le8_word rsegs mem RT_TP FSw HFSb) as HFSwm.
  remember (bv_unsigned FSw) as FS eqn:EFS.
  assert (HFS64 : 0 <= FS < 2 ^ 64) by (rewrite EFS; apply f4_word_range).
  destruct HFSok as (HFSpos & HFSalign & HFSgt & HFSapp).
  pose proof (AC.a_laws_stack_high _ _ _ _ _ LAWS _ _ _ HAH) as NSTK1.
  destruct (f4_law_fs_place _ _ _ _ HAH HFSwm HFS64) as (_ & NFS1 & _ & _).
  destruct (f4_law_fs_state _ _ _ _ HAH HFSwm HFS64)
    as (HFSwr & HFSpres & HFS88 & HFS96 & _ & HFSflag &
        (DBz & HDBzr & HDBzw & HDBznz & HDBztp & HDBzapp & HDBzlo & HDBznfs) & HT48app).
  pose proof (HFSfr FS HFSwm HFS64) as HFSlow.
  assert (NAPP : APPMEM_END < 2 ^ 64) by (unfold APPMEM_END; lia).
  assert (NFSB : FS + 11571200 <= APPMEM_END)
    by (unfold AC.FS_SIZE in NFS1; unfold AF.SLOT_STACK in Hstklo; lia).
  (* ---- the thread record ---- *)
  destruct (f4_law_thread _ _ _ HAH)
    as (C0 & T0 & HC0wm & HC0rng & HT0rng & HT0wm & HC152o & HC152a & HT48o & HT48b).
  destruct (AsanRTInv.RT_uw_cells _ _ _ HRT) as (Htsdi & Htsdk & _ & Htp88 & (Cw & HCwb)).
  pose proof (bytes_at_le8_word rsegs mem RT_TSDMAIN Cw HCwb) as HCwm.
  assert (ECw : bv_unsigned Cw = C0).
  { pose proof (f4_word_range Cw) as HR.
    destruct (f4_wm_norm mem RT_TSDMAIN (bv_unsigned Cw) C0 HCwm HC0wm ltac:(lia) ltac:(lia)) as [E|E];
      [exact E | lia]. }
  assert (HCapp : forall x, C0 + 152 <= x < C0 + 160 -> app_mem x).
  { intros x Hx. pose proof (HC152a (x - (C0 + 152)) ltac:(lia)) as H.
    replace (C0 + 152 + (x - (C0 + 152))) with x in H by lia. exact H. }
  assert (HCpt : forall x, C0 + 152 <= x < C0 + 160 ->
            x < AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md /\ ~ (FS <= x < FS + AC.FS_SIZE)).
  { intros x Hx. pose proof (HC152o (x - (C0 + 152)) ltac:(lia)) as Hown.
    replace (C0 + 152 + (x - (C0 + 152))) with x in Hown by lia.
    pose proof (HCapp x Hx) as Hax.
    split.
    - destruct (Z_lt_le_dec x (AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md)) as [H|H]; [exact H|].
      exfalso. unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in Hax.
      assert (Hst : AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md <= x < APPMEM_END)
        by (unfold APPMEM_END; lia).
      exact (f4_law_not_owned _ _ _ x HAH (or_intror Hst) Hown).
    - intros Hin.
      assert (HFSin : AC.a_in_fs AC.ASYMS mem x)
        by (exists FS; split; [exact HFS64 | split; [exact HFSwm | exact Hin]]).
      exact (f4_law_not_owned _ _ _ x HAH (or_introl HFSin) Hown). }
  assert (HTapp : forall x, T0 + 48 <= x < T0 + 64 -> app_mem x).
  { intros x Hx.
    pose proof (HT48app C0 T0 HC0wm ltac:(lia) HT0wm ltac:(lia) (x - (T0 + 48)) ltac:(lia)) as H.
    replace (T0 + 48 + (x - (T0 + 48))) with x in H by lia. exact H. }
  assert (HTpt : forall x, T0 + 48 <= x < T0 + 64 ->
            x < AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md /\ ~ (FS <= x < FS + AC.FS_SIZE)).
  { intros x Hx. pose proof (HT48o (x - (T0 + 48)) ltac:(lia)) as Hown.
    replace (T0 + 48 + (x - (T0 + 48))) with x in Hown by lia.
    pose proof (HTapp x Hx) as Hax.
    split.
    - destruct (Z_lt_le_dec x (AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md)) as [H|H]; [exact H|].
      exfalso. unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in Hax.
      assert (Hst : AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md <= x < APPMEM_END)
        by (unfold APPMEM_END; lia).
      exact (f4_law_not_owned _ _ _ x HAH (or_intror Hst) Hown).
    - intros Hin.
      assert (HFSin : AC.a_in_fs AC.ASYMS mem x)
        by (exists FS; split; [exact HFS64 | split; [exact HFSwm | exact Hin]]).
      exact (f4_law_not_owned _ _ _ x HAH (or_introl HFSin) Hown). }
  assert (HTpres : forall i, 0 <= i < 16 -> exists b, mbyte rsegs mem (T0 + 48 + i) = Some b).
  { intros i Hi. exact (HT48b i Hi). }
  (* ---- the thread's DTLS word ---- *)
  assert (EDBz : DBz = DBp).
  { pose proof (HDBzapp (DBz + 24) ltac:(lia)) as Ha1.
    pose proof (HDBzapp (DBz + 31) ltac:(lia)) as Ha2.
    unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in Ha1, Ha2.
    destruct (f4_wm_norm mem (AC.as_tp AC.ASYMS + 8) DBz DBp HDBzw HDBp ltac:(lia) ltac:(lia)) as [E|E];
      [exact E | lia]. }
  assert (EDBw : bv_unsigned DBw = DBp).
  { pose proof (f4_word_range DBw) as HR.
    pose proof (bytes_at_le8_word rsegs mem (RT_TP + 8) DBw HDBb) as HDBwm.
    destruct (f4_wm_norm mem (AC.as_tp AC.ASYMS + 8) (bv_unsigned DBw) DBp HDBwm HDBp ltac:(lia) ltac:(lia))
      as [E|E]; [exact E | lia]. }
  assert (HDBpt : forall x, DBp + 24 <= x < DBp + 32 ->
            app_mem x /\ x < AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md /\
            ~ (FS <= x < FS + AC.FS_SIZE)).
  { intros x Hx. rewrite <- EDBz in Hx.
    pose proof (HDBzapp x Hx) as H1. pose proof (HDBzlo x Hx) as H2. pose proof (HDBznfs x Hx) as H4.
    split; [exact H1|]. split; [exact H2|]. intros Hin. apply H4.
    exists FS. split; [exact HFS64 | split; [exact HFSwm | exact Hin]]. }
  assert (HDB24 : bytes_at rsegs mem (bv_unsigned DBw + 24) (le8 (Z_to_bv 64 (AC.as_tp AC.ASYMS)))).
  { rewrite EDBw, <- EDBz.
    apply (word_mem_le8 rsegs mem (DBz + 24) (AC.as_tp AC.ASYMS) HDBztp);
      [cbv [AC.as_tp AC.ASYMS]; lia | lia | lia]. }
  (* ---- numeric bounds of the thread cells ---- *)
  assert (NC0 : C0 + 160 <= APPMEM_END).
  { pose proof (HCapp (C0 + 159) ltac:(lia)) as H.
    unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in H. unfold APPMEM_END. lia. }
  assert (NT0 : T0 + 64 <= APPMEM_END).
  { pose proof (HTapp (T0 + 63) ltac:(lia)) as H.
    unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in H. unfold APPMEM_END. lia. }
  assert (NC : C0 + 160 <= AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md)
    by (pose proof (proj1 (HCpt (C0 + 159) ltac:(lia))); lia).
  assert (NT : T0 + 64 <= AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md)
    by (pose proof (proj1 (HTpt (T0 + 63) ltac:(lia))); lia).
  assert (NDB : DBp + 32 <= AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md)
    by (pose proof (proj1 (proj2 (HDBpt (DBp + 31) ltac:(lia)))); lia).
  (* ---- the words the tls cells name ---- *)
  assert (EDTu : bv_unsigned (Z_to_bv 64 (AC.as_tp AC.ASYMS + 32)) = AC.as_tp AC.ASYMS + 32)
    by (apply MState.unsigned_lit; cbv [AC.as_tp AC.ASYMS]; lia).
  assert (ETSu : bv_unsigned (Z_to_bv 64 RT_TSDMAIN) = RT_TSDMAIN)
    by (apply MState.unsigned_lit; unfold RT_TSDMAIN; lia).
  assert (ETu : bv_unsigned (Z_to_bv 64 T0) = T0) by (apply MState.unsigned_lit; lia).
  pose proof (word_mem_le8 rsegs mem (C0 + 152) T0 HT0wm ltac:(lia) ltac:(lia)
                ltac:(unfold APPMEM_END in *; lia)) as HT0b.
  destruct (f4_word_present mem (T0 + 48) ltac:(lia) ltac:(unfold APPMEM_END in *; lia)
      ltac:(intros i Hi; exact (HTpres i ltac:(lia)))) as (tb & Htb).
  assert (HTpres2 : forall i, 0 <= i < 8 -> exists b, mbyte rsegs mem (T0 + 56 + i) = Some b).
  { intros i Hi. replace (T0 + 56 + i) with (T0 + 48 + (8 + i)) by lia. exact (HTpres (8 + i) ltac:(lia)). }
  destruct (f4_word_present mem (T0 + 56) ltac:(lia) ltac:(unfold APPMEM_END in *; lia) HTpres2) as (te & Hte).
  assert (HTBE : bytes_at rsegs mem (T0 + 48) (le8 tb ++ le8 te)).
  { apply (proj2 (bytes_at_app rsegs mem (T0 + 48) (le8 tb) (le8 te))).
    split; [exact Htb|]. rewrite length_le8.
    replace (T0 + 48 + Z.of_nat 8) with (T0 + 56) by lia. exact Hte. }
  destruct (AsanRTInv.RT_cf_cells _ _ _ HRT) as (Hcf1 & _ & _ & _ & _ & Hcf137 & _ & _).
  destruct (AsanRTInv.RT_opt_cells _ _ _ HRT) as (_ & _ & Hopt3 & Hopt4).
  pose proof (AsanRTInv.RT_real_cells _ _ _ HRT) as HREAL.
  assert (HTLS : asan_tls_cells mem (AC.as_tp AC.ASYMS) (Z_to_bv 64 (AC.as_tp AC.ASYMS + 32))
                   (Z_to_bv 64 RT_TSDMAIN) Cw (Z_to_bv 64 T0) DBw 0).
  { unfold asan_tls_cells. rewrite EDTu, ETSu, ETu, ECw.
    split; [exact Htlsidx|].
    split; [exact (AsanRTInv.real_cell_of mem REAL_TLS_GET_ADDR MUSL_TLS_GET_ADDR HREAL
                     ltac:(vm_compute; reflexivity))|].
    split; [exact Hdt|].
    split; [exact Hdt8|].
    split; [exact Htsdi|].
    split; [lia|].
    split; [exact Htsdk|].
    split; [exact Htp88|].
    split; [exact HCwb|].
    split; [exact HT0b|].
    split; [exists tb, te; exact HTBE|].
    split; [exact Hcf1|].
    split; [exact Hcf137|].
    split; [exact Hopt3|].
    split; [exact Hopt4|].
    split; [exact Hdtpoff|].
    split; [exact HDBb|].
    split; [exact (proj1 HDBnz)|].
    exact HDB24. }
  (* ---- the frame's placement: real stack or side stack ---- *)
  assert (HFSuniq : forall b x, word_mem rsegs mem (AC.as_tp AC.ASYMS) b -> b <= x < b + AC.FS_SIZE ->
            0 <= x < APPMEM_END -> 0 <= b < 2 ^ 64 -> b = FS).
  { intros b x Hb Hbx Hx Hbr.
    pose proof (f4_wm_eq mem _ b FS Hb HFSwm) as E. rewrite !Z.mod_small in E by lia. exact E. }
  assert (HFRQ : forall x, fr <= x < fr + FRAME_BYTES ->
            AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md <= x \/ (FS <= x < FS + AC.FS_SIZE)).
  { intros x Hx. destruct Hloc as [(_ & _ & Hreal) | (_ & _ & Hfs & _)].
    - left. exact (proj1 (Hreal x Hx)).
    - right. destruct (Hfs x Hx) as (b & Hbr & Hb & Hbx).
      pose proof (Happ x Hx) as Hax. unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in Hax.
      rewrite <- (HFSuniq b x Hb Hbx ltac:(unfold APPMEM_END; lia) Hbr). exact Hbx. }
  (* ---- app memory and shadow memory are apart ---- *)
  assert (HGAP : forall x, LOWMEM_END <= x < HIGHMEM_BEG -> ~ app_mem x).
  { intros x Hx Hap. unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in *. lia. }
  assert (AS_C : RcLay.ly_dj (C0 + 152) (C0 + 160) LOWMEM_END HIGHMEM_BEG).
  { apply (f4_dj_pt app_mem); [lia | unfold LOWMEM_END, HIGHMEM_BEG; lia | exact HCapp | exact HGAP]. }
  assert (AS_T : RcLay.ly_dj (T0 + 48) (T0 + 64) LOWMEM_END HIGHMEM_BEG).
  { apply (f4_dj_pt app_mem); [lia | unfold LOWMEM_END, HIGHMEM_BEG; lia | exact HTapp | exact HGAP]. }
  assert (AS_DB : RcLay.ly_dj (DBp + 24) (DBp + 32) LOWMEM_END HIGHMEM_BEG).
  { apply (f4_dj_pt app_mem); [lia | unfold LOWMEM_END, HIGHMEM_BEG; lia
    | intros x Hx; exact (proj1 (HDBpt x Hx)) | exact HGAP]. }
  assert (AS_FR : RcLay.ly_dj fr (fr + FRAME_BYTES) LOWMEM_END HIGHMEM_BEG).
  { apply (f4_dj_pt app_mem); [lia | unfold LOWMEM_END, HIGHMEM_BEG; lia | exact Happ | exact HGAP]. }
  (* ---- the shadow of the class-1 frames and of the callee's window lies between the app ranges ---- *)
  assert (SB1a : LOWMEM_END <= shadow_addr (FS + 1085440)) by (apply f4_sh_lo; lia).
  assert (SB1b : shadow_addr (FS + 2134016) <= HIGHMEM_BEG)
    by (apply f4_sh_hi_le; unfold APPMEM_END in *; lia).
  assert (SB2a : LOWMEM_END <= shadow_addr (sp - REAC_CTRL_PARSE_K)).
  { apply f4_sh_lo. unfold REAC_CTRL_PARSE_K, FN_STACK, AF.SLOT_STACK, HIGHMEM_BEG in *. lia. }
  assert (SB2b : shadow_addr sp <= HIGHMEM_BEG) by (apply f4_sh_hi_le; unfold APPMEM_END in *; lia).
  (* ---- the thread cells are apart from the frame and from the side stack ---- *)
  assert (DJ_C_FR : RcLay.ly_dj fr (fr + FRAME_BYTES) (C0 + 152) (C0 + 160)).
  { apply (f4_dj_pt (fun x => AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md <= x \/
                              (FS <= x < FS + AC.FS_SIZE)));
      [lia | lia | exact HFRQ |].
    intros x Hx Hq. destruct (HCpt x Hx) as (H1 & H2). destruct Hq as [Hq|Hq]; [lia | exact (H2 Hq)]. }
  assert (DJ_T_FR : RcLay.ly_dj fr (fr + FRAME_BYTES) (T0 + 48) (T0 + 64)).
  { apply (f4_dj_pt (fun x => AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md <= x \/
                              (FS <= x < FS + AC.FS_SIZE)));
      [lia | lia | exact HFRQ |].
    intros x Hx Hq. destruct (HTpt x Hx) as (H1 & H2). destruct Hq as [Hq|Hq]; [lia | exact (H2 Hq)]. }
  assert (DJ_DB_FR : RcLay.ly_dj fr (fr + FRAME_BYTES) (DBp + 24) (DBp + 32)).
  { apply (f4_dj_pt (fun x => AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md <= x \/
                              (FS <= x < FS + AC.FS_SIZE)));
      [lia | lia | exact HFRQ |].
    intros x Hx Hq. destruct (HDBpt x Hx) as (_ & H1 & H2). destruct Hq as [Hq|Hq]; [lia | exact (H2 Hq)]. }
  assert (DJ_C_FS : RcLay.ly_dj FS (FS + AC.FS_SIZE) (C0 + 152) (C0 + 160)).
  { apply (f4_dj_pt (fun x => FS <= x < FS + AC.FS_SIZE));
      [unfold AC.FS_SIZE; lia | lia | intros x Hx; exact Hx |].
    intros x Hx. exact (proj2 (HCpt x Hx)). }
  assert (DJ_T_FS : RcLay.ly_dj FS (FS + AC.FS_SIZE) (T0 + 48) (T0 + 64)).
  { apply (f4_dj_pt (fun x => FS <= x < FS + AC.FS_SIZE));
      [unfold AC.FS_SIZE; lia | lia | intros x Hx; exact Hx |].
    intros x Hx. exact (proj2 (HTpt x Hx)). }
  assert (DJ_DB_FS : RcLay.ly_dj FS (FS + AC.FS_SIZE) (DBp + 24) (DBp + 32)).
  { apply (f4_dj_pt (fun x => FS <= x < FS + AC.FS_SIZE));
      [unfold AC.FS_SIZE; lia | lia | intros x Hx; exact Hx |].
    intros x Hx. exact (proj2 (proj2 (HDBpt x Hx))). }
  assert (Hne : (fr + 176 =? 0) = false) by (apply Z.eqb_neq; unfold AC.GT in Hgt; lia).
  (* ---- the goal ---- *)
  clear Hloc Hs5 HFRQ HFSuniq Hfrm Hspm HAm.
  exists FS.
  split; [exact HFSwm|].
  split; [exact HFS64|].
  split.
  { (* fp *)
    exists (Z_to_bv 64 (AC.as_tp AC.ASYMS + 32)), (Z_to_bv 64 RT_TSDMAIN), Cw, (Z_to_bv 64 T0), DBw, 0.
    split; [exact HTLS|].
    split; [rewrite EFS, MState.Z_to_bv_bv_unsigned; exact HFSb|].
    split.
    { unfold fs_place. split; [lia|]. split; [exact HFSalign|].
      split; [unfold ASAN_GT, RT_GT in *; lia|].
      split; [intros a Ha; apply HFSapp; unfold FS_SIZE, RT_FS_SIZE in *; lia|].
      split; [lia|]. split; [unfold FS_SIZE in *; lia|].
      intros a Ha. pose proof (HFSwr a ltac:(unfold AC.FS_SIZE, FS_SIZE in *; lia)) as Hw.
      destruct (HFSpres a ltac:(unfold AC.FS_SIZE, FS_SIZE in *; lia)) as (b & Hb).
      split; [exact Hw | exists b; exact Hb]. }
    split; [exact (word_mem_le8 rsegs mem (FS + 88) 20 HFS88 ltac:(lia) ltac:(lia) ltac:(lia))|].
    split; [apply f4_byte_at; [lia | lia | exact HFS96]|].
    split.
    { apply Forall_cons; [|apply Forall_nil].
      unfold fp_cls. split; [lia|].
      destruct (f4_word_present mem (FS + 8) ltac:(lia) ltac:(lia)
          ltac:(intros i Hi;
                destruct (HFSpres (FS + 8 + i) ltac:(unfold AC.FS_SIZE in *; lia)) as (bb & Hbb);
                exists bb; exact Hbb)) as (h & Hh).
      destruct (f4_bytes_P (fun b => b = Z_to_bv 8 0 \/ b = Z_to_bv 8 1) mem (FS + 20480) 8192
          ltac:(lia) ltac:(lia) ltac:(lia)
          ltac:(intros i Hi;
                pose proof (HFSflag 1%nat i ltac:(lia) ltac:(change (AC.a_fs_M 1%nat) with 8192; lia)) as Hf;
                rewrite f4_afs_flag1 in Hf;
                destruct Hf as [Hf|Hf]; [exists (Z_to_bv 8 0) | exists (Z_to_bv 8 1)];
                  (split; [exact Hf | first [left; reflexivity | right; reflexivity]])))
                as (flags & Hfl & Hfllen & Hflb).
      destruct (f4_fsc FS) as (F1 & F2 & F3 & _ & _).
      exists h, flags. rewrite F1, F2, F3.
      split; [exact Hh|]. split; [exact Hfl|]. split; [exact Hfllen | exact Hflb]. }
    split; [f4_num|].
    split; [intros a Ha; unfold app_mem; right; f4_num|].
    split.
    { (* the caller's writes are apart from the tls cells and the side stack's header *)
      rewrite f4_fs_frame0. unfold reac_ctrl_parse_W, fp_dj. rewrite Hne.
      cbn [fp_tls app]. rewrite ?EDTu, ?ETSu, ?ETu, ?ECw, ?EDBw.
      clear AS_C AS_T AS_DB AS_FR DJ_C_FS DJ_T_FS DJ_DB_FS HFSalign.
      f4_dj_split; f4_num. }
    { (* the caller's data range (the output cells) is apart from the class-1 side-stack bytes *)
      clear AS_C AS_T AS_DB DJ_C_FR DJ_T_FR DJ_DB_FR DJ_C_FS DJ_T_FS DJ_DB_FS HFSalign.
      rewrite f4_fpw1. unfold reac_ctrl_parse_D. rewrite Hne. cbn [Z.ltb Z.compare app].
      unfold fp_dj. f4_dj_split; f4_num. } }
  { (* the tls clause: any witnesses are the ones above *)
    intros DT' TS' C' T' DB' k' HT'.
    assert (HOUT : Forall (fun d => forall x, fst d <= x < snd d -> outside (@nil ivl) x)
                     (fp_tls (AC.as_tp AC.ASYMS) (Z_to_bv 64 (AC.as_tp AC.ASYMS + 32))
                        (Z_to_bv 64 RT_TSDMAIN) Cw (Z_to_bv 64 T0) DBw 0)).
    { apply Forall_forall. intros d _ x _. exact I. }
    destruct (fl_tls_same mem mem [] (AC.as_tp AC.ASYMS)
                (Z_to_bv 64 (AC.as_tp AC.ASYMS + 32)) (Z_to_bv 64 RT_TSDMAIN) Cw (Z_to_bv 64 T0) DBw 0
                DT' TS' C' T' DB' k' HTLS HT' (munch_refl (@nil ivl) mem) HOUT)
      as (E1 & E2 & E3 & E4 & E5 & E6).
    subst DT' TS' C' T' DB' k'.
    rewrite f4_fpw1. unfold fp_dj. cbn [fp_tls app].
    rewrite ?EDTu, ?ETSu, ?ETu, ?ECw, ?EDBw.
    clear AS_FR DJ_C_FR DJ_T_FR DJ_DB_FR HFSalign.
    f4_dj_split; f4_num. }
Qed.

(* ---- the call on the normalized memory (MemNorm): the contract asks for mem_inv, which no cut carries ---- *)

(* The image's segments all end at or below GT, so no address at or above it is read-only. *)
Definition f4_tops (segs : list Segment) (top : Z) : bool :=
  forallb (fun s => Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? top) segs.

Lemma f4_tops_gt : f4_tops rsegs 0x5fe000 = true.
Proof. vm_compute. reflexivity. Qed.

Lemma f4_find_below : forall segs top x n s,
  f4_tops segs top = true -> find_segment segs x n = Some s -> 0 <= n -> x < top \/ n = 0.
Proof.
  induction segs as [|s0 r IH]; intros top x n s Hb H Hn; cbn in H; [discriminate H|].
  unfold f4_tops in Hb. cbn [forallb] in Hb. apply andb_prop in Hb as [H0 Hr].
  apply Z.leb_le in H0.
  destruct (Z.leb (Z.of_N (seg_base s0)) x && Z.leb (x + n) (Z.of_N (seg_base s0) + Z.of_N (seg_size s0))) eqn:E.
  - apply andb_prop in E as [_ E]. apply Z.leb_le in E. lia.
  - exact (IH top x n s Hr H Hn).
Qed.

Lemma f4_ro_gt : forall a, 0x5fe000 <= a < 2 ^ 64 -> ro_addr rsegs (wa a) = false.
Proof.
  intros a Ha. unfold OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.ro_addr.
  match goal with |- context [find_segment ?sg ?x ?n] =>
    destruct (find_segment sg x n) as [s|] eqn:E; [|reflexivity];
    destruct (f4_find_below sg 0x5fe000 x n s f4_tops_gt E ltac:(cbn; lia)) as [L|L];
    [exfalso; rewrite MState.unsigned_lit in L by lia; lia | cbn in L; lia] end.
Qed.

Lemma f4_stk_rel : forall m m0 lo hi, mem_rel rsegs m m0 -> 0x5fe000 <= lo ->
  stk rsegs m lo hi -> stk rsegs m0 lo hi.
Proof.
  intros m m0 lo hi HR Hlo (H0 & H1 & H). split; [lia|]. split; [lia|]. intros a Ha.
  destruct (H a Ha) as (Hw & b & Hb). split.
  - rewrite (wview_rel_rw rsegs m m0 (wa a) HR (f4_ro_gt a ltac:(lia))). exact Hw.
  - exists b. rewrite <- (mrd_rel rsegs m m0 (wa a) HR). exact Hb.
Qed.

Lemma f4_stk_back : forall m m0 lo hi, mem_rel rsegs m m0 -> stk rsegs m0 lo hi -> stk rsegs m lo hi.
Proof.
  intros m m0 lo hi HR (H0 & H1 & H). split; [lia|]. split; [lia|]. intros a Ha.
  destruct (H a Ha) as (Hw & b & Hb). split.
  - rewrite <- (wview_rel_rw rsegs m m0 (wa a) HR (ro_false_of_wview rsegs m m0 (wa a) HR Hw)). exact Hw.
  - exists b. rewrite (mrd_rel rsegs m m0 (wa a) HR). exact Hb.
Qed.

Lemma f4_shrw_rel : forall m m0, mem_rel rsegs m m0 -> shadow_rw m -> shadow_rw m0.
Proof.
  intros m m0 HR H a Ha. pose proof (in_shadow_range a Ha) as Hr.
  destruct (H a Ha) as (Hw & b & Hb).
  assert (Hlo : 0x5fe000 <= a) by (unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in Ha; lia).
  split.
  - rewrite (wview_rel_rw rsegs m m0 (wa a) HR (f4_ro_gt a ltac:(lia))). exact Hw.
  - exists b. rewrite <- (mrd_rel rsegs m m0 (wa a) HR). exact Hb.
Qed.

Lemma f4_shrw_back : forall m m0, mem_rel rsegs m m0 -> shadow_rw m0 -> shadow_rw m.
Proof.
  intros m m0 HR H a Ha.
  destruct (H a Ha) as (Hw & b & Hb). split.
  - rewrite <- (wview_rel_rw rsegs m m0 (wa a) HR (ro_false_of_wview rsegs m m0 (wa a) HR Hw)). exact Hw.
  - exists b. rewrite (mrd_rel rsegs m m0 (wa a) HR). exact Hb.
Qed.

Lemma f4_addr_rel : forall m m0 p n, mem_rel rsegs m m0 -> addressable m p n -> addressable m0 p n.
Proof.
  intros m m0 p n HR (H0 & H1 & H2 & H). split; [exact H0|]. split; [exact H1|]. split; [exact H2|].
  intros i Hi. destruct (H i Hi) as (Hap & b & Hb & Hok). split; [exact Hap|].
  exists b. rewrite <- (mrd_rel rsegs m m0 _ HR). split; [exact Hb | exact Hok].
Qed.

Lemma f4_addr_back : forall m m0 p n, mem_rel rsegs m m0 -> addressable m0 p n -> addressable m p n.
Proof.
  intros m m0 p n HR (H0 & H1 & H2 & H). split; [exact H0|]. split; [exact H1|]. split; [exact H2|].
  intros i Hi. destruct (H i Hi) as (Hap & b & Hb & Hok). split; [exact Hap|].
  exists b. rewrite (mrd_rel rsegs m m0 _ HR). split; [exact Hb | exact Hok].
Qed.

Ltac f4_ba_rel R :=
  first [ apply (proj1 (bytes_at_rel rsegs _ _ _ _ R)); assumption
        | apply (proj2 (bytes_at_rel rsegs _ _ _ _ R)); assumption ].

Lemma f4_cells_rel : forall m m0, mem_rel rsegs m m0 -> asan_cells m -> asan_cells m0.
Proof.
  intros m m0 R H. unfold asan_cells in H |- *.
  repeat match goal with H' : _ /\ _ |- _ => destruct H' end.
  repeat match goal with |- _ /\ _ => split end; f4_ba_rel R.
Qed.

Lemma f4_tls_rel : forall m m0 TP DT TS C T DB k, mem_rel rsegs m m0 ->
  (asan_tls_cells m TP DT TS C T DB k <-> asan_tls_cells m0 TP DT TS C T DB k).
Proof.
  intros m m0 TP DT TS C T DB k R. unfold asan_tls_cells.
  split; intros (H1 & H2 & H3 & H4 & H5 & Hk & H7 & H8 & H9 & H10 & (tb & te & H11) & H12 & H13 & H14 & H15
                 & H16 & H17 & HDB & H19).
  all: split; [f4_ba_rel R|]. all: split; [f4_ba_rel R|]. all: split; [f4_ba_rel R|].
  all: split; [f4_ba_rel R|]. all: split; [f4_ba_rel R|]. all: split; [exact Hk|].
  all: split; [f4_ba_rel R|]. all: split; [f4_ba_rel R|]. all: split; [f4_ba_rel R|].
  all: split; [f4_ba_rel R|]. all: split; [exists tb, te; f4_ba_rel R|].
  all: split; [f4_ba_rel R|]. all: split; [f4_ba_rel R|]. all: split; [f4_ba_rel R|].
  all: split; [f4_ba_rel R|]. all: split; [f4_ba_rel R|]. all: split; [f4_ba_rel R|].
  all: split; [exact HDB|]. all: f4_ba_rel R.
Qed.

Lemma f4_cls_rel : forall m m0 FS c, mem_rel rsegs m m0 -> (fp_cls m FS c <-> fp_cls m0 FS c).
Proof.
  intros m m0 FS c R. unfold fp_cls.
  split; intros (Hc & h & fl & Hh & Hf & Hl & Hb); (split; [exact Hc|]); exists h, fl;
    (split; [f4_ba_rel R|]); (split; [f4_ba_rel R|]); (split; [exact Hl | exact Hb]).
Qed.

Lemma f4_fp_rel : forall cs m m0 TP FS lo hi W D, mem_rel rsegs m m0 ->
  fp cs m TP FS lo hi W D -> fp cs m0 TP FS lo hi W D.
Proof.
  intros cs m m0 TP FS lo hi W D R
    (DT & TS & C & T & DB & k & Htls & Htp & Hpl & H88 & H96 & Hcls & Hlo & Happ & Hw & Hd).
  exists DT, TS, C, T, DB, k.
  split; [exact (proj1 (f4_tls_rel m m0 TP DT TS C T DB k R) Htls)|].
  split; [f4_ba_rel R|].
  split.
  { destruct Hpl as (P1 & P2 & P3 & P4 & P5). split; [exact P1|]. split; [exact P2|]. split; [exact P3|].
    split; [exact P4|]. apply (f4_stk_rel m m0 FS (FS + FS_SIZE) R); [unfold ASAN_GT in P3; lia | exact P5]. }
  split; [f4_ba_rel R|]. split; [f4_ba_rel R|].
  split.
  { eapply Forall_impl; [|exact Hcls]. intros c Hc. exact (proj1 (f4_cls_rel m m0 FS c R) Hc). }
  split; [exact Hlo|]. split; [exact Happ|]. split; [exact Hw | exact Hd].
Qed.

(* The run 0x81e74-0x81e80 and the call, on a memory where mem_inv holds (the normalized one). *)
Lemma f4_dbc_call :
  forall (ra0 gp tp t0 t1 t2 s0 a0i a1i a2i a3 a4 a5 a6 a7 s2i s3i s4 s5 s6 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (A f o S FS : Z) (bs junk : list byte),
    0 <= f < 2 ^ 64 -> 0 <= o < 2 ^ 64 -> o <> 0 -> S < 2 ^ 64 -> S mod 16 = 0 ->
    REAC_CTRL_PARSE_K <= S -> 0 <= A -> A + 256 <= 2 ^ 64 ->
    stk rsegs m (S - REAC_CTRL_PARSE_K) S -> mem_inv rsegs m -> length bs = 50%nat ->
    ov_read_bytes rsegs m (wa (A + 248)) 8 = Some (le8 (Z_to_bv 64 o)) ->
    (50 <= 0 -> 0 < f /\ f + 50 <= 2 ^ 64 /\ (f + 50 <= S - REAC_CTRL_PARSE_K \/ S <= f)) ->
    (forall i, In i (cp_rd 0 bs) -> mrd rsegs m (wa (f + Z.of_nat i)) = nth_error bs i) ->
    (o <> 0 -> o mod 4 = 0 /\ o + 36 <= 2 ^ 64 /\ rw_cells rsegs m o [CB 36 junk] /\
       (o + 36 <= S - REAC_CTRL_PARSE_K \/ S <= o) /\ (50 <= 0 -> o + 36 <= f \/ f + 50 <= o)) ->
    asan_cells m -> shadow_rw m ->
    HIGHMEM_BEG <= S - REAC_CTRL_PARSE_K -> S <= APPMEM_END ->
    addressable m (S - REAC_CTRL_PARSE_K) REAC_CTRL_PARSE_K ->
    (50 <= 0 -> addressable m f 50) ->
    (o <> 0 -> addressable m o 36 /\ app_mem (o + 36) /\ (o + 36 <= GOT_CF \/ CF + 256 <= o)) ->
    addressable m REAC_CTRL_PARSE_BC 6 ->
    bytes_at rsegs m REAL_BCMP (le8 (wa BCMP)) -> bytes_at rsegs m REAL_MEMCMP (le8 (wa MEMCMP)) ->
    bytes_at rsegs m GOT_CF (le8 (wa CF)) ->
    bytes_at rsegs m (CF + 254) [Z_to_bv 8 1] -> bytes_at rsegs m (CF + 255) [Z_to_bv 8 1] ->
    fp [1%nat] m (bv_unsigned tp) FS (S - REAC_CTRL_PARSE_K) S (reac_ctrl_parse_W o S) (reac_ctrl_parse_D f 0 o) ->
    reac_ctrl_parse_tls m (bv_unsigned tp) FS (S - REAC_CTRL_PARSE_K) S ->
    LE.evt rsegs
      (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
         ms' = MS (mkR (Z_to_bv 64 0x81e84) (Z_to_bv 64 S) gp tp t0' t1' t2' s0 (Z_to_bv 64 A)
                       (Z_to_bv 64 (fst (ctrlparse 0 bs))) a1' a2' a3' a4' a5' a6' a7'
                       s2i s3i s4 s5 s6 (Z_to_bv 64 f) s8 s9 s10 s11 t3' t4' t5' t6')
                  Fr (Z_to_bv 64 0x81e84) fc None m' (seg_rom rsegs) /\
         munch (reac_ctrl_parse_fp o S ++ fp_w [1%nat] FS ++
                [(shadow_addr (S - REAC_CTRL_PARSE_K), shadow_addr S)]) m m' /\
         wmono rsegs m m' /\
         stk rsegs m' (S - REAC_CTRL_PARSE_K) S /\ rw_cells rsegs m' o [CB 36 (snd (ctrlparse 0 bs))] /\
         shadow_rw m' /\ addressable m' (S - REAC_CTRL_PARSE_K) REAC_CTRL_PARSE_K /\
         fp [1%nat] m' (bv_unsigned tp) FS (S - REAC_CTRL_PARSE_K) S (reac_ctrl_parse_W o S)
            (reac_ctrl_parse_D f 0 o))
      (MS (mkR ra0 (Z_to_bv 64 S) gp tp t0 t1 t2 s0 (Z_to_bv 64 A) a0i a1i a2i a3 a4 a5 a6 a7
               s2i s3i s4 s5 s6 (Z_to_bv 64 f) s8 s9 s10 s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x81e74) fc None m (seg_rom rsegs)).
Proof.
  intros ra0 gp tp t0 t1 t2 s0 a0i a1i a2i a3 a4 a5 a6 a7 s2i s3i s4 s5 s6 s8 s9 s10 s11 t3 t4 t5 t6
    Fr fc m A f o S FS bs junk Hf Ho Honz HS HS16 HSK HA0 HAhi HST HMI Hlen HRDcur Hbig HRD Hocell
    HAC HSW HHI HAPP HWA HFA Hoaddr HBC H1 H2 H3 H4 H5 HFP HTLS.
  (* 0x81e74 mv a0,s7 ; 0x81e78 li a1,0 ; 0x81e7c ld a2,248(s1) ; 0x81e80 jal reac_ctrl_parse *)
  step. step. step. step.
  pose proof HPARSE as HP. unfold reac_ctrl_parse_contract, REAC_CTRL_PARSE in HP.
  eapply evt_cut.
  { eapply HP with (f := f) (n := 0) (o := o) (S := S) (FS := FS) (fr := bs) (junk := junk);
      try reflexivity; try assumption; try lia. }
  intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & tt3 & tt4 & tt5 & tt6 & m' &
    E & MU & WM & MI & ST & Hrw & Hac & HSW' & Hadr & FP & Htls).
  subst ms'.
  replace (ret_pc (Z_to_bv 64 0x81e84)) with (Z_to_bv 64 0x81e84)
    by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  apply evt_done.
  exists t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', tt3, tt4, tt5, tt6, m'.
  split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact ST|]. split; [exact (Hrw Honz)|].
  split; [exact HSW'|]. split; [exact Hadr | exact FP].
Qed.

(* The same run on the real memory: the call goes through MemNorm.evt_normalize from ro_agree, every premise
   crosses mem_rel to the normalized memory (all of them name addresses at or above GT, where nothing is
   read-only, or bytes_at facts), and the post comes back across mem_rel and ro_same. *)
Lemma f4_dbc_calln :
  forall (ra0 gp tp t0 t1 t2 s0 a0i a1i a2i a3 a4 a5 a6 a7 s2i s3i s4 s5 s6 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (A f o S FS : Z) (bs junk : list byte),
    0 <= f < 2 ^ 64 -> 0x5fe000 <= o -> o + 36 <= 2 ^ 64 -> S < 2 ^ 64 -> S mod 16 = 0 ->
    REAC_CTRL_PARSE_K <= S -> 0 <= A -> A + 256 <= 2 ^ 64 ->
    stk rsegs m (S - REAC_CTRL_PARSE_K) S -> ro_agree rsegs m -> length bs = 50%nat ->
    ov_read_bytes rsegs m (wa (A + 248)) 8 = Some (le8 (Z_to_bv 64 o)) ->
    o mod 4 = 0 -> rw_cells rsegs m o [CB 36 junk] -> (o + 36 <= S - REAC_CTRL_PARSE_K \/ S <= o) ->
    asan_cells m -> shadow_rw m ->
    HIGHMEM_BEG <= S - REAC_CTRL_PARSE_K -> S <= APPMEM_END ->
    addressable m (S - REAC_CTRL_PARSE_K) REAC_CTRL_PARSE_K ->
    addressable m o 36 -> app_mem (o + 36) -> (o + 36 <= GOT_CF \/ CF + 256 <= o) ->
    addressable m REAC_CTRL_PARSE_BC 6 ->
    bytes_at rsegs m REAL_BCMP (le8 (wa BCMP)) -> bytes_at rsegs m REAL_MEMCMP (le8 (wa MEMCMP)) ->
    bytes_at rsegs m GOT_CF (le8 (wa CF)) ->
    bytes_at rsegs m (CF + 254) [Z_to_bv 8 1] -> bytes_at rsegs m (CF + 255) [Z_to_bv 8 1] ->
    fp [1%nat] m (bv_unsigned tp) FS (S - REAC_CTRL_PARSE_K) S (reac_ctrl_parse_W o S) (reac_ctrl_parse_D f 0 o) ->
    reac_ctrl_parse_tls m (bv_unsigned tp) FS (S - REAC_CTRL_PARSE_K) S ->
    LE.evt rsegs
      (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
         ms' = MS (mkR (Z_to_bv 64 0x81e84) (Z_to_bv 64 S) gp tp t0' t1' t2' s0 (Z_to_bv 64 A)
                       (Z_to_bv 64 (fst (ctrlparse 0 bs))) a1' a2' a3' a4' a5' a6' a7'
                       s2i s3i s4 s5 s6 (Z_to_bv 64 f) s8 s9 s10 s11 t3' t4' t5' t6')
                  Fr (Z_to_bv 64 0x81e84) fc None m' (seg_rom rsegs) /\
         munch (reac_ctrl_parse_fp o S ++ fp_w [1%nat] FS ++
                [(shadow_addr (S - REAC_CTRL_PARSE_K), shadow_addr S)]) m m' /\
         wmono rsegs m m' /\ ro_same rsegs m m' /\
         stk rsegs m' (S - REAC_CTRL_PARSE_K) S /\ rw_cells rsegs m' o [CB 36 (snd (ctrlparse 0 bs))] /\
         shadow_rw m' /\ addressable m' (S - REAC_CTRL_PARSE_K) REAC_CTRL_PARSE_K /\
         stk rsegs m' FS (FS + FS_SIZE) /\ fp_cls m' FS 1)
      (MS (mkR ra0 (Z_to_bv 64 S) gp tp t0 t1 t2 s0 (Z_to_bv 64 A) a0i a1i a2i a3 a4 a5 a6 a7
               s2i s3i s4 s5 s6 (Z_to_bv 64 f) s8 s9 s10 s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x81e74) fc None m (seg_rom rsegs)).
Proof.
  intros ra0 gp tp t0 t1 t2 s0 a0i a1i a2i a3 a4 a5 a6 a7 s2i s3i s4 s5 s6 s8 s9 s10 s11 t3 t4 t5 t6
    Fr fc m A f o S FS bs junk Hf Ho Ho36 HS HS16 HSK HA0 HAhi HST HRO Hlen HRDcur Ho4 Hocell Howin
    HAC HSW HHI HAPP HWA Hoaddr Hoapp HoCF HBC H1 H2 H3 H4 H5 HFP HTLS.
  pose proof (mem_rel_normalize rsegs m HRO) as REL.
  set (m0 := normalize rsegs m) in REL.
  assert (HC := f4_dbc_call ra0 gp tp t0 t1 t2 s0 a0i a1i a2i a3 a4 a5 a6 a7 s2i s3i s4 s5 s6 s8 s9 s10 s11
                  t3 t4 t5 t6 Fr fc m0 A f o S FS bs junk Hf ltac:(lia) ltac:(lia) HS HS16 HSK HA0 HAhi).
  pose proof (f4_stk_rel m m0 (S - REAC_CTRL_PARSE_K) S REL ltac:(unfold REAC_CTRL_PARSE_K, HIGHMEM_BEG in *; lia) HST)
    as HST0.
  specialize (HC HST0 (mem_inv_normalize rsegs m) Hlen).
  specialize (HC ltac:(rewrite <- (ov_read_rel rsegs m m0 _ _ REL); exact HRDcur)).
  specialize (HC ltac:(intros Hb; exfalso; lia)).
  specialize (HC ltac:(intros i Hi; change (cp_rd 0 bs) with (@nil nat) in Hi; destruct Hi)).
  specialize (HC ltac:(intros _; split; [exact Ho4|]; split; [lia|]; split;
    [ destruct Hocell as ((Hwf & Hb) & Hw); split; [split; [exact Hwf | f4_ba_rel REL]|];
      apply (wr_at_norm rsegs m m0 o _ REL Hw); intros i Hi; apply f4_ro_gt; cbn in Hi; lia
    | split; [exact Howin | intros Hb; exfalso; lia]])).
  specialize (HC (f4_cells_rel m m0 REL HAC) (f4_shrw_rel m m0 REL HSW) HHI HAPP (f4_addr_rel m m0 _ _ REL HWA)).
  specialize (HC ltac:(intros Hb; exfalso; lia)).
  specialize (HC ltac:(intros _; split; [exact (f4_addr_rel m m0 _ _ REL Hoaddr) | split; [exact Hoapp | exact HoCF]])).
  specialize (HC (f4_addr_rel m m0 _ _ REL HBC)).
  specialize (HC ltac:(f4_ba_rel REL) ltac:(f4_ba_rel REL) ltac:(f4_ba_rel REL) ltac:(f4_ba_rel REL)
                 ltac:(f4_ba_rel REL)).
  specialize (HC (f4_fp_rel _ m m0 _ _ _ _ _ _ REL HFP)).
  specialize (HC ltac:(intros DT TS C T DB k HT0; apply HTLS; exact (proj2 (f4_tls_rel m m0 _ DT TS C T DB k REL) HT0))).
  pose proof (evt_normalize rsegs _ _ Fr _ fc None m (seg_rom rsegs) ltac:(vm_compute; reflexivity) HRO HC) as HN.
  eapply evt_mono; [exact HN|].
  intros ms' (s0' & (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & tt3 & tt4 & tt5 & tt6 & m0' &
    E0 & MU0 & WM0 & ST0 & RW0 & SW0 & AD0 & FP0) & Hrel & Hro').
  subst s0'.
  destruct Hrel as (ER & EF & EP & ESv & ERes & EFc & ERom & HR').
  destruct ms' as [r' f' p' sv' rv' fc' m' ro'].
  cbn [ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_rom ms_mem MS] in ER, EF, EP, ESv, ERes, EFc,
    ERom, HR', Hro'.
  subst r' f' p' sv' rv' fc' ro'.
  exists t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', tt3, tt4, tt5, tt6, m'.
  split; [reflexivity|].
  split; [exact (munch_rel rsegs _ m m0 m' m0' REL HR' Hro' MU0)|].
  split; [exact (wmono_rel rsegs m m0 m' m0' REL HR' Hro' WM0)|].
  split; [exact Hro'|].
  split; [exact (f4_stk_back m' m0' _ _ HR' ST0)|].
  split.
  { destruct RW0 as ((Hwf & Hb) & Hw). split; [split; [exact Hwf | f4_ba_rel HR']|].
    exact (wr_at_rel rsegs m' m0' o _ HR' Hw). }
  split; [exact (f4_shrw_back m' m0' HR' SW0)|].
  split; [exact (f4_addr_back m' m0' _ _ HR' AD0)|].
  destruct FP0 as (DT & TS & C & T & DB & k & _ & _ & Hpl & _ & _ & Hcls & _).
  split.
  { destruct Hpl as (_ & _ & _ & _ & P5). exact (f4_stk_back m' m0' _ _ HR' P5). }
  exact (proj2 (f4_cls_rel m' m0' FS 1 HR') (Forall_inv Hcls)).
Qed.

(* ---- FRA and ENT across the call ---- *)

(* FSREC moves across a write that misses its three cells (the tp word, the class-6 flag byte, the slot's last
   word). *)
Lemma f4_fsrec_keep : forall mem mem' W fr,
  FSREC fr mem -> Frame.munch W mem mem' ->
  (forall FS j x, word_mem rsegs mem (AC.as_tp AC.ASYMS) FS -> 0 <= FS < 2 ^ 64 -> 0 <= j < 256 ->
     fr = FS + 6328320 + j * 4096 ->
     (x = FS + 36352 + j \/ fr + 4088 <= x < fr + 4096 \/ AC.as_tp AC.ASYMS <= x < AC.as_tp AC.ASYMS + 8) ->
     Frame.outside W x) ->
  FSREC fr mem'.
Proof.
  intros mem mem' W fr (FS & j & Htp & HFSr & Hj & Hfr & Hflag & Htail) MU HW.
  assert (HB6 : SMC.fs_B 6 = 4096) by reflexivity.
  assert (HM6 : SMC.fs_M 6 = 256) by reflexivity.
  assert (Hfl : SMC.fs_flag FS 6 j = FS + 36352 + j) by (unfold SMC.fs_flag; cbn; lia).
  assert (Hfrv : fr = FS + 6328320 + j * 4096) by (rewrite Hfr; unfold SMC.fs_frame, SMC.fs_B; cbn; lia).
  rewrite HM6 in Hj.
  assert (HO : forall x, (x = FS + 36352 + j \/ fr + 4088 <= x < fr + 4096 \/
                          AC.as_tp AC.ASYMS <= x < AC.as_tp AC.ASYMS + 8) -> Frame.outside W x)
    by (intros x Hx; exact (HW FS j x Htp HFSr Hj Hfrv Hx)).
  exists FS, j.
  split.
  { intros k Hk.
    assert (Hx : 0 <= AC.as_tp AC.ASYMS + Z.of_nat k < 2 ^ 64) by (unfold AC.as_tp, AC.ASYMS; cbn; lia).
    assert (Hm : mem' (Z_to_bv 64 (AC.as_tp AC.ASYMS + Z.of_nat k))
                 = mem (Z_to_bv 64 (AC.as_tp AC.ASYMS + Z.of_nat k))).
    { apply MU. rewrite MState.unsigned_lit by exact Hx. apply HO. right; right; lia. }
    unfold mbyte. rewrite Hm. exact (Htp k Hk). }
  split; [exact HFSr|].
  split; [rewrite HM6; exact Hj|].
  split; [exact Hfr|].
  split.
  { eapply fl_bytes; [exact Hflag | exact MU |].
    cbn [length]. intros x Hx. apply HO. left. lia. }
  { eapply fl_bytes; [exact Htail | exact MU |].
    rewrite length_le8. intros x Hx. apply HO. right; left. rewrite HB6 in Hx. lia. }
Qed.

(* The FRA rebuild across a run that may also write shadow bytes and side-stack bytes (the callee's class-1 frames):
   RT by RT_meta_write (every shadow byte readable after the run), AH / stklo, the window, FSREC, the registered
   globals and the slot window's addressability from the caller, the rest kept by fl_bytes (their addresses are
   outside W) and wmono (errno). The form of Tac_slot.sl_fr_meta's rebuild for a write outside the frame. *)
Lemma f4_fr_run : forall g fr hb regs mem mem' md W,
  FRA B APIf ra g fr hb regs mem md ->
  Frame.munch W mem mem' -> Frame.wmono rsegs mem mem' -> ro_agree rsegs mem' -> rt_disjoint W ->
  (forall a, in_shadow a -> exists b, mrd rsegs mem' (wa a) = Some b) ->
  AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) (hb ++ g_H g) mem' md ->
  AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem' md = AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md ->
  (forall x, fr <= x < fr + 24 -> Frame.outside W x) ->
  (forall x, 0 <= x < AC.GT -> Frame.outside W x) ->
  (forall A, rg regs 9 A -> 0 <= A < 2 ^ 64 -> forall x, A + 16 <= x < A + 312 -> Frame.outside W x) ->
  (forall x, g_S g - 104 <= x < g_S g -> Frame.outside W x) ->
  (forall x, Sfr fr <= x < Sfr fr + FRAME_SHADOW -> Frame.outside W x) ->
  stk rsegs mem' (g_S g - AF.SLOT_STACK) (g_S g) ->
  (FSREC fr mem -> FSREC fr mem') ->
  (forall a, in_globals AF.frame_AG a -> addressable mem' a 1) ->
  (forall a, g_S g - AF.SLOT_STACK <= a < g_S g -> ~ (fr <= a < fr + FRAME_BYTES) -> addressable mem' a 1) ->
  FRA B APIf ra g fr hb regs mem' md.
Proof. pose proof FRAME_BYTES_val as HFBval. pose proof FRAME_SHADOW_val as HFSval.
  intros g fr hb regs mem mem' md W HFRA MU WM HRO HD HSH HAH' HSTK HWhdr HWimg HWA9 HWsaved HWsh HWwin
    HrecK HAG' HWA'.
  pose proof f4_ff as (SEGS & Hhead & Hlock & Hthr).
  destruct HFRA as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA416 & HS4 & HAPP &
    Hspill & Hsel & Hfr24 & Hloc & Hhdr1 & Hhdr2 & Hsh & Hwin & Hsaved & Herrno & HAG & HWA &
    HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive).
  assert (HSS : AF.SLOT_STACK = 1048576) by reflexivity.
  assert (HA64 : 0 <= A < 2 ^ 64).
  { unfold stk in Hwin. destruct Hwin as (Hw0 & Hw1 & _). lia. }
  assert (KBlo : forall (sg : list Segment) x, 0 <= x -> x < 6283264 -> mbyte sg mem' x = mbyte sg mem x).
  { intros sg x H0 H1. assert (Hm : mem' (Z_to_bv 64 x) = mem (Z_to_bv 64 x)).
    { apply MU. rewrite MState.unsigned_lit by lia. apply HWimg. unfold AC.GT. lia. }
    unfold mbyte. rewrite Hm. reflexivity. }
  exists A, sp, s5.
  split; [exact (AsanRTInv.RT_meta_write sp sp mem mem' md md W HRT MU WM HD HSH)|].
  split; [exact HAH'|].
  split; [exact HRO|].
  split.
  { destruct Hsn as (Hcse & Hohd & Hfd). split; [|split; [|exact Hfd]].
    - destruct Hcse as (Hthrm & Hlockm). split.
      + eapply YI14.val_mem_frame; [|exact Hthrm]. intros x Hx. apply KBlo.
        * lia.
        * rewrite Hthr in Hx. cbn in Hx. lia.
      + eapply YI14.val_mem_frame; [|exact Hlockm]. intros x Hx. apply KBlo.
        * lia.
        * rewrite Hlock in Hx. cbn in Hx. lia.
    - intros k Hk. rewrite KBlo.
      + exact (Hohd k Hk).
      + rewrite Hhead. lia.
      + rewrite Hhead. lia. }
  split; [exact Hhalt|].
  split.
  { intros a Hin. rewrite KBlo.
    - exact (Hgimg a Hin).
    - destruct Hin as (lo & len & Hil & Hr). unfold AF.frame_RELRO in Hil. cbn in Hil.
      repeat (destruct Hil as [E|Hil]; [injection E as <- <-; lia|]); destruct Hil.
    - destruct Hin as (lo & len & Hil & Hr). unfold AF.frame_RELRO in Hil. cbn in Hil.
      repeat (destruct Hil as [E|Hil]; [injection E as <- <-; lia|]); destruct Hil. }
  split; [exact Hr2|].
  split; [exact Hspm|].
  split; [exact Haspz|].
  split; [rewrite HSTK; exact Hstklo|].
  split; [exact Hr4|].
  split; [exact Hr8|].
  split; [exact Hr9|].
  split; [exact Hr3|].
  split; [exact Hr19|].
  split; [exact Hr26|].
  split; [exact Hfrm|].
  split; [exact Hs5|].
  split; [exact HAm|].
  split; [exact HAS|].
  split; [exact Hspa|].
  split; [exact Hfa|].
  split; [exact HA416|].
  split; [exact HS4|].
  split; [exact HAPP|].
  split.
  { unfold q64 in *. eapply fl_bytes; [exact Hspill | exact MU |].
    rewrite length_le8. intros x Hx. exact (HWA9 A Hr9 HA64 x ltac:(lia)). }
  split.
  { unfold q64 in *. eapply fl_bytes; [exact Hsel | exact MU |].
    rewrite length_le8. intros x Hx. exact (HWA9 A Hr9 HA64 x ltac:(lia)). }
  split.
  { unfold q64 in *. eapply fl_bytes; [exact Hfr24 | exact MU |].
    rewrite length_le8. intros x Hx. exact (HWA9 A Hr9 HA64 x ltac:(lia)). }
  split.
  { destruct Hloc as [[H0 [Hspfr Hreal]]|[Hfr0 [Hfsb [Hfs Hrec]]]].
    - left. split; [exact H0|]. split; [exact Hspfr|].
      intros a Ha. rewrite HSTK. exact (Hreal a Ha).
    - right. split; [exact Hfr0|]. split.
      + intros FS Hw HFSr. apply (Hfsb FS); [| exact HFSr].
        intros k Hk. rewrite <- KBlo.
        * exact (Hw k Hk).
        * unfold AC.as_tp, AC.ASYMS. cbn. lia.
        * unfold AC.as_tp, AC.ASYMS. cbn. lia.
      + split; [|exact (HrecK Hrec)].
        intros a Ha. destruct (Hfs a Ha) as (FSb & HFSr & Hw & Hlo & Hhi).
        exists FSb. split; [exact HFSr|]. split; [|split; [exact Hlo | exact Hhi]].
        intros k Hk. rewrite KBlo.
        * exact (Hw k Hk).
        * unfold AC.as_tp, AC.ASYMS. cbn. lia.
        * unfold AC.as_tp, AC.ASYMS. cbn. lia. }
  split.
  { unfold q64 in *. eapply fl_bytes; [exact Hhdr1 | exact MU |].
    rewrite length_le8. intros x Hx. apply HWhdr. lia. }
  split.
  { unfold q64 in *. eapply fl_bytes; [exact Hhdr2 | exact MU |].
    rewrite length_le8. intros x Hx. apply HWhdr. lia. }
  split.
  { destruct Hsh as (sh & Hbytes & Hlen). exists sh. split; [|exact Hlen].
    eapply fl_bytes; [exact Hbytes | exact MU |]. rewrite Hlen. intros x Hx. exact (HWsh x ltac:(lia)). }
  split; [exact HWwin|].
  split.
  { eapply fl_bytes; [exact Hsaved | exact MU |]. intros x Hx.
    apply HWsaved. unfold saved_bytes in Hx. rewrite !length_app, !length_le8 in Hx. cbn in Hx. lia. }
  split.
  { intros a Ha. exact (WM (Z_to_bv 64 a) (Herrno a Ha)). }
  split; [exact HAG'|].
  split; [exact HWA'|].
  split; [exact HSHI1|].
  split; [exact HSHI2|].
  split; [exact HSHI3|].
  split; [exact Hhb | exact Hlive].
Qed.

(* FRA and ENT across the reac_ctrl_parse call at 0x81e80 with o = fr + 176 (the contract's munch list: the 36
   output cells, the callee window, the class-1 side-stack bytes and their shadow, the shadow of the window) and
   the lazy-page step md -> md'. AH / stklo / stkhi and ownership by a_laws_fs_store (the post's fs stk and class-1
   state give a_fs_ok); FRA by f4_fr_run; ENT by ent_munch (no byte ENT names is written: the entry blocks are off
   the side stack and below stklo, the image is below GT, the stack from S on is above the window and the frame,
   and the shadow of those is apart, granule by granule, from the shadow the call writes). *)
Lemma f4_fra_call : forall g fr hb regs regs' mem mem' md md' FS (bs : list byte),
  FRA B APIf ra g fr hb regs mem md ->
  word_mem rsegs mem (AC.as_tp AC.ASYMS) FS -> 0 <= FS < 2 ^ 64 ->
  Frame.munch (f4_PW (fr + 176) (AC.aspZ regs) FS) mem mem' -> Frame.wmono rsegs mem mem' ->
  ro_same rsegs mem mem' ->
  stk rsegs mem' (AC.aspZ regs - REAC_CTRL_PARSE_K) (AC.aspZ regs) ->
  addressable mem' (AC.aspZ regs - REAC_CTRL_PARSE_K) REAC_CTRL_PARSE_K ->
  rw_cells rsegs mem' (fr + 176) [CB 36 bs] ->
  shadow_rw mem' ->
  stk rsegs mem' FS (FS + FS_SIZE) -> fp_cls mem' FS 1 ->
  getr regs' 2 = getr regs 2 -> getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 ->
  getr regs' 8 = getr regs 8 -> getr regs' 9 = getr regs 9 -> getr regs' 19 = getr regs 19 ->
  getr regs' 26 = getr regs 26 ->
  AsanLift.mat_le md md' ->
  FRA B APIf ra g fr hb regs' mem' md' /\ (ENT APIf g hb mem md -> ENT APIf g hb mem' md').
Proof. pose proof FRAME_BYTES_val as HFBval. pose proof FRAME_SHADOW_val as HFSval.
  intros g fr hb regs regs' mem mem' md md' FS bs HFRA Htp HFS MU WM HRS Hstkw HADw HRW HSRW HFSstk Hcls
    E2 E3 E4 E8 E9 E19 E26 Hmat.
  pose proof (fra_app B APIf ra g fr hb regs mem md HFRA) as (Hgt & Happ).
  pose proof (fra_frame B APIf ra g fr hb regs mem md HFRA) as (Hapart & _ & HFSfr & _).
  pose proof (fra_win B APIf ra g fr hb regs mem md HFRA) as (Hwlo & _).
  pose proof HFRA as HF.
  destruct HF as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA416 & HS4 & HAPP &
    Hspill & Hsel & Hfr24 & Hloc & Hhdr1 & Hhdr2 & Hsh & Hwin & Hsaved & Herrno & HAG & HWA &
    HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive).
  pose proof (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) as LAWS.
  pose proof (AC.a_laws_stack_high _ _ _ _ _ LAWS _ _ _ HAH) as Hhi.
  destruct (f4_law_fs_place _ _ _ FS HAH Htp HFS) as (HFSgt & HFSst & HFSal & HFSapp).
  destruct (f4_law_fs_state _ _ _ FS HAH Htp HFS) as (_ & _ & O2 & O3 & O4 & O5 & _ & _).
  pose proof (HFSfr FS Htp HFS) as HFSlow.
  pose proof (Hapart REAC_CTRL_PARSE_K ltac:(unfold REAC_CTRL_PARSE_K, FN_STACK, AF.SLOT_STACK; lia)) as Hwd.
  rewrite Haspz in MU, Hstkw, HADw, Hwd, Hwlo.
  assert (HKh : HIGHMEM_BEG = 17594333495296) by (vm_compute; reflexivity).
  assert (HKa : APPMEM_END = 140737488355328) by (vm_compute; reflexivity).
  assert (HKs : AF.SLOT_STACK = 1048576) by (vm_compute; reflexivity).
  assert (HKl : LOWMEM_END = 2147450880) by (vm_compute; reflexivity).
  assert (HKk : ASAN_K = 2147450880) by (vm_compute; reflexivity).
  assert (HKg : AC.GT = 6283264) by (vm_compute; reflexivity).
  assert (HKp : REAC_CTRL_PARSE_K = 8800) by (vm_compute; reflexivity).
  assert (HKf : FS_SIZE = 11571200) by (vm_compute; reflexivity).
  assert (HKf2 : AC.FS_SIZE = 11571200) by (vm_compute; reflexivity).
  assert (HKn : FN_STACK = 1044480) by (vm_compute; reflexivity).
  f4_imgc HKtp (AC.as_tp AC.ASYMS).
  assert (HP64 : 2 ^ 64 = 18446744073709551616) by reflexivity.
  assert (HA64 : 0 <= A < 2 ^ 64).
  { pose proof Hwin as HW0. unfold stk in HW0. destruct HW0 as (Hw0 & Hw1 & _). lia. }
  assert (Hfr8 : fr mod 8 = 0) by (clear - Hfrm; Z.div_mod_to_equations; lia).
  assert (Hsp8 : (sp - 8800) mod 8 = 0) by (clear - Hspm; Z.div_mod_to_equations; lia).
  assert (HFS8 : FS mod 8 = 0) by (clear - HFSal; Z.div_mod_to_equations; lia).
  assert (Hfrlo : (fr + FRAME_BYTES <= LOWMEM_END \/ HIGHMEM_BEG <= fr) /\ fr + FRAME_BYTES <= APPMEM_END).
  { pose proof (Happ fr ltac:(lia)) as P1. pose proof (Happ (fr + FRAME_BYTES - 1) ltac:(lia)) as P2.
    unfold app_mem in P1, P2. lia. }
  assert (HFSlo : FS + AC.FS_SIZE <= LOWMEM_END \/ HIGHMEM_BEG <= FS).
  { pose proof (HFSapp FS ltac:(lia)) as P1. pose proof (HFSapp (FS + AC.FS_SIZE - 1) ltac:(lia)) as P2.
    unfold app_mem in P1, P2. lia. }
  assert (Harm : (AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md <= fr) \/
                 (FS <= fr /\ fr + FRAME_BYTES <= FS + AC.FS_SIZE)).
  { destruct Hloc as [(_ & _ & Hreal)|(_ & _ & Hfs & _)].
    - left. exact (proj1 (Hreal fr ltac:(lia))).
    - right. destruct (Hfs (fr + FRAME_BYTES - 1) ltac:(lia)) as (b & Hbr & Hb & Hb1).
      pose proof (f4_wm_eq _ _ _ _ Hb Htp) as Heq. rewrite !Z.mod_small in Heq by lia. subst b. lia. }
  assert (Ho0 : fr + 176 <> 0) by lia.
  (* the shadow of an app byte apart from the class-1 frames and from the callee window is outside the call's
     writes *)
  assert (HSHO : forall y, 0 <= y < APPMEM_END -> (y < FS + 1085440 \/ FS + 2134016 <= y) ->
            (y < sp - 8800 \/ sp <= y) -> Frame.outside (f4_PW (fr + 176) sp FS) (shadow_addr y)).
  { intros y Hy Hy1 Hy2. apply f4_PW_out_sh; try lia. }
  assert (HAPO : forall x, app_mem x -> ~ (fr + 176 <= x < fr + 212) -> ~ (sp - 8800 <= x < sp) ->
            ~ (FS + 8 <= x < FS + 16) -> ~ (FS + 20480 <= x < FS + 28672) ->
            ~ (FS + 1085440 <= x < FS + 2134016) -> Frame.outside (f4_PW (fr + 176) sp FS) x).
  { intros x Hx N1 N2 N3 N4 N5.
    apply f4_PW_out_app; [lia | exact Hx | lia | lia | lia | lia | lia | lia | lia | lia | lia]. }
  clear Hfrm Hspm HAm HFSal Hfr8 Hsp8 HFS8.
  (* the side stack's state after the call *)
  assert (Hokp : AC.a_fs_ok mem' FS).
  { destruct HFSstk as (_ & _ & HS).
    destruct Hcls as (_ & h1 & fl & Hh1 & Hfl & Hfll & Hflb).
    destruct (f4_fsc FS) as (F1 & F2 & F3 & F4 & F5).
    split; [|split; [|split; [|split]]].
    - intros a Ha. exact (HS a ltac:(lia)).
    - apply (kb_word_munch rsegs mem mem' (f4_PW (fr + 176) sp FS) (FS + 88) 20 O2 MU). intros k Hk.
      split; [lia|]. apply f4_PW_out_app; try lia. apply HFSapp. lia.
    - rewrite (KindBGlue.mbyte_munch rsegs (f4_PW (fr + 176) sp FS) mem mem' (FS + 96) MU);
        [exact O3 | lia |].
      apply f4_PW_out_app; try lia. apply HFSapp. lia.
    - intros c Hc. destruct (Nat.eq_dec c 1) as [->|Hc1].
      + exists (bv_unsigned h1). exact (bytes_at_le8_word rsegs mem' (fs_hint FS 1) h1 Hh1).
      + destruct (O4 c Hc) as [h Hh].
        exists h. apply (kb_word_munch rsegs mem mem' (f4_PW (fr + 176) sp FS) _ h Hh MU).
        intros k Hk. unfold AC.a_fs_hint.
        assert (Hcz : Z.of_nat c <> 1) by lia.
        split; [lia|]. apply f4_PW_out_app; try lia. apply HFSapp. lia.
    - intros c j Hc Hj. destruct (Nat.eq_dec c 1) as [->|Hc1].
      + destruct Hfl as (_ & _ & Hfl).
        assert (Hj' : (Z.to_nat j < length fl)%nat).
        { change (AC.a_fs_M 1) with (fs_M 1) in Hj. rewrite F3 in Hfll, Hj. lia. }
        destruct (nth_error fl (Z.to_nat j)) as [b|] eqn:En; [|apply nth_error_None in En; lia].
        pose proof (Hfl (Z.to_nat j) Hj') as Hb. rewrite En, Z2Nat.id in Hb by lia.
        assert (Hin : In b fl) by exact (nth_error_In fl _ En).
        rewrite Forall_forall in Hflb.
        replace (AC.a_fs_flag FS 1 j) with (fs_flag FS 1 0 + j)
          by (rewrite F2, f4_afs_flag1; lia).
        destruct (Hflb b Hin) as [-> | ->]; [left | right]; exact Hb.
      + pose proof (a_fs_flag_range FS c j Hc Hj) as Hr.
        pose proof (f4_flag_other FS c j Hc Hc1 Hj) as Ho.
        rewrite (KindBGlue.mbyte_munch rsegs (f4_PW (fr + 176) sp FS) mem mem' (AC.a_fs_flag FS c j) MU);
          [exact (O5 c j Hc Hj) | lia |].
        apply f4_PW_out_app; try lia. apply HFSapp. lia. }
  (* AH and stklo across the call (law: stores into the side stack and its Shadow) *)
  assert (Hagree : forall a, 0 <= a < 2 ^ 64 ->
      ~ AC.a_store_ok (hb ++ g_H g) (AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md) a ->
      ~ (FS <= a < FS + AC.FS_SIZE) -> ~ (exists b, FS <= b < FS + AC.FS_SIZE /\ a = shadow_addr b) ->
      mem' (Z_to_bv 64 a) = mem (Z_to_bv 64 a)).
  { intros a Ha Hns Hnf Hnsh. apply MU. rewrite MState.unsigned_lit by exact Ha.
    apply (f4_PW_out (fr + 176) sp FS a Ho0).
    - intro Hin. destruct Harm as [R1|[S1 S2]].
      + apply Hns. right. left. lia.
      + apply Hnf. lia.
    - intro Hin. apply Hns. right. left. lia.
    - intro Hin. apply Hnf. lia.
    - intro Hin. apply Hnf. lia.
    - intro Hin. apply Hnf. lia.
    - intro Hin. apply Hnsh. exists (8 * (a - ASAN_K)). unfold shadow_addr in *. split; lia.
    - intro Hin. apply Hns. right. right. right. exists (8 * (a - ASAN_K)). unfold shadow_addr in *.
      split; [lia | right; left; lia]. }
  assert (Hwm : forall a, 0 <= a < 2 ^ 64 -> writable_at rsegs mem a -> writable_at rsegs mem' a).
  { intros a _ Hw. exact (WM (Z_to_bv 64 a) Hw). }
  destruct (f4_law_fs_store (hb ++ g_H g) mem mem' md FS HAH Htp HFS Hagree Hwm Hokp)
    as (HAH' & Hown & Hstkeq & Hstkhieq).
  split.
  - apply (sl_fra_move B APIf ra g fr hb regs regs' mem' md md');
      [| exact E2 | exact E3 | exact E4 | exact E8 | exact E9 | exact E19 | exact E26 | exact Hmat].
    apply (f4_fr_run g fr hb regs mem mem' md (f4_PW (fr + 176) sp FS) HFRA MU WM).
    + exact (ro_agree_same rsegs mem mem' Hro HRS).
    + apply f4_rt. intros lo hi Hin. apply (f4_PW_lo (fr + 176) sp FS lo hi Ho0); [lia | lia | lia | exact Hin].
    + intros a Ha. destruct (HSRW a Ha) as (_ & b & Hb). exists b. exact Hb.
    + exact HAH'.
    + exact Hstkeq.
    + intros x Hx. apply HAPO; [apply Happ; lia | lia | lia | lia | lia | lia].
    + intros x Hx. apply HAPO; [unfold app_mem; lia | lia | lia | lia | lia | lia].
    + intros A' HA' HA'r x Hx.
      assert (EA : A' = A) by (apply f4_id; [lia | lia |]; unfold rg in HA', Hr9; rewrite <- HA'; exact Hr9).
      subst A'. apply HAPO; [unfold app_mem; lia | lia | lia | lia | lia | lia].
    + intros x Hx. apply HAPO; [unfold app_mem; lia | lia | lia | lia | lia | lia].
    + intros x Hx.
      replace x with (shadow_addr (fr + 8 * (x - Sfr fr))) by (rewrite f4_fr_sh; lia).
      apply HSHO; lia.
    + apply (fl_stk _ mem mem' (g_S g - AF.SLOT_STACK) (g_S g) Hwin MU WM).
      intros x Hx.
      destruct (Z_lt_le_dec x (sp - 8800)) as [Hl|Hl];
        [|destruct (Z_lt_le_dec x sp) as [Hl2|Hl2];
          [right; destruct Hstkw as (_ & _ & Hs); exact (proj2 (Hs x ltac:(lia)))|]].
      * destruct (Z_le_gt_dec (fr + 176) x) as [C1|C1]; [destruct (Z_lt_ge_dec x (fr + 212)) as [C2|C2]|].
        -- right. exact (f4_cell_byte mem' (fr + 176) 36 bs x HRW ltac:(change (Z.of_nat 36) with 36; lia)).
        -- left. apply HAPO; [unfold app_mem; lia | lia | lia | lia | lia | lia].
        -- left. apply HAPO; [unfold app_mem; lia | lia | lia | lia | lia | lia].
      * destruct (Z_le_gt_dec (fr + 176) x) as [C1|C1]; [destruct (Z_lt_ge_dec x (fr + 212)) as [C2|C2]|].
        -- right. exact (f4_cell_byte mem' (fr + 176) 36 bs x HRW ltac:(change (Z.of_nat 36) with 36; lia)).
        -- left. apply HAPO; [unfold app_mem; lia | lia | lia | lia | lia | lia].
        -- left. apply HAPO; [unfold app_mem; lia | lia | lia | lia | lia | lia].
    + intros Hrec. apply (f4_fsrec_keep mem mem' _ fr Hrec MU).
      intros FS' j x Htp' HFS' Hj Hfrv Hx.
      assert (EFS : FS' = FS).
      { pose proof (f4_wm_eq _ _ _ _ Htp' Htp) as E. rewrite !Z.mod_small in E by lia. exact E. }
      subst FS'.
      destruct Hx as [Hx|[Hx|Hx]].
      * apply HAPO; [apply HFSapp; lia | lia | lia | lia | lia | lia].
      * apply HAPO; [apply HFSapp; lia | lia | lia | lia | lia | lia].
      * apply HAPO; [unfold app_mem; lia | lia | lia | lia | lia | lia].
    + intros a Ha. pose proof (f4_ag_lt a Ha) as Hab.
      apply (addr1_munch _ mem mem' a MU); [|exact (HAG a Ha)].
      apply HSHO; lia.
    + intros a Ha Hnf.
      destruct (Z_le_gt_dec (sp - 8800) a) as [Hw1|Hw1]; [destruct (Z_lt_ge_dec a sp) as [Hw2|Hw2]|].
      * exact (f4_addr1 mem' (sp - REAC_CTRL_PARSE_K) REAC_CTRL_PARSE_K a HADw ltac:(lia)).
      * apply (addr1_munch _ mem mem' a MU); [|exact (HWA a Ha Hnf)]. apply HSHO; lia.
      * apply (addr1_munch _ mem mem' a MU); [|exact (HWA a Ha Hnf)]. apply HSHO; lia.
  - intros HENT. eapply ent_mat; [|exact Hmat].
    eapply ent_munch; [exact HENT | exact HAH | exact MU | | exact Hstkeq | exact Hstkhieq |].
    + intros x Hk. destruct Hk as [Hblk | [Himg | [Habv | [(b & Hor & ->) | Hblks]]]].
      * destruct Hblk as (q & k & i & Hin & Hni & Hi & ->).
        destruct (f4_law_blocks (hb ++ g_H g) mem md q k HAH (in_or_app _ _ _ (or_intror Hin)))
          as (_ & Hq4 & Hend & Happk & Hnfsk).
        pose proof (Happk (q + i) ltac:(lia)) as Happq.
        assert (HnFS : ~ (FS <= q + i < FS + AC.FS_SIZE)).
        { intros HC. apply (Hnfsk (q + i) ltac:(lia)). exists FS. split; [exact HFS | split; [exact Htp | exact HC]]. }
        apply HAPO; [exact Happq | | lia | lia | lia | lia].
        destruct Harm as [R1|[S1 S2]]; lia.
      * pose proof (img_below_GT x Himg) as Hxg.
        apply HAPO; [unfold app_mem; lia | lia | lia | lia | lia | lia].
      * apply HAPO; [unfold app_mem; lia | lia | lia | lia | lia | lia].
      * assert (Hb0 : 0 <= b < APPMEM_END)
          by (destruct Hor as [Hi|Hr]; [pose proof (img_below_GT b Hi) as X|]; lia).
        apply HSHO; [exact Hb0 | |];
          (destruct Hor as [Hi|Hr]; [pose proof (img_below_GT b Hi) as X|]; lia).
      * (* the shadow of an entry block's byte (ENT's 13th conjunct, ent_shd): the byte is app memory below stklo
           and off the side stack, so its shadow is apart from the call's shadow writes *)
        destruct Hblks as (q & k & i & Hin & Hni & Hi & ->).
        destruct (f4_law_blocks (hb ++ g_H g) mem md q k HAH (in_or_app _ _ _ (or_intror Hin)))
          as (_ & Hq4 & Hend & Happk & Hnfsk).
        pose proof (Happk (q + i) ltac:(lia)) as Happq.
        assert (HnFS : ~ (FS <= q + i < FS + AC.FS_SIZE)).
        { intros HC. apply (Hnfsk (q + i) ltac:(lia)). exists FS. split; [exact HFS | split; [exact Htp | exact HC]]. }
        unfold app_mem in Happq.
        apply HSHO; lia.
    + intros a _ Ho. exact (proj2 (Hown a) Ho).
Qed.

(* The cut skeleton across the five frame shadow bytes. *)
Lemma f4_keep2 : forall g j phi fr A regs mem mem' md,
  FRA B APIf ra g fr (hb1 phi (AC.a_size (flen g j))) regs mem md ->
  HB mem phi (flen g j) -> FLSI g j fr regs mem -> LK g fr j regs mem ->
  b5_C g j phi fr regs mem -> IDj g fr j mem ->
  flen g j = 0 -> (phi + 1 <= fr \/ fr + FRAME_BYTES <= phi) ->
  rg regs 9 A -> 0 <= A < 2 ^ 64 ->
  Frame.munch (f4_Wsh fr) mem mem' -> Frame.wmono rsegs mem mem' ->
  HB mem' phi (flen g j) /\ FLSI g j fr regs mem' /\ LK g fr j regs mem' /\
  b5_C g j phi fr regs mem' /\ IDj g fr j mem'.
Proof. pose proof FRAME_BYTES_val as HFBval. pose proof FRAME_SHADOW_val as HFSval.
  intros g j phi fr A regs mem mem' md HFRA HHB HFLSI HLK HC HID Hlen0 Hphifr H9 HA MU WM.
  pose proof (fra_app B APIf ra g fr _ regs mem md HFRA) as (HGT & Happ).
  assert (Hasz : AC.a_size (flen g j) = 1) by (unfold AC.a_size; rewrite Hlen0; lia).
  pose proof HHB as (Hphinz & Hphiad). rewrite Hasz in Hphiad.
  pose proof (addr1_app mem phi Hphiad) as Hphiapp.
  pose proof HFRA as (A0 & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA416 & HS4 & HAPP & _).
  pose proof (AC.a_laws_stack_high _ _ _ _ _ (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) _ _ _ HAH) as Hhi.
  assert (HKh : HIGHMEM_BEG = 17594333495296) by (vm_compute; reflexivity).
  assert (HKa : APPMEM_END = 140737488355328) by (vm_compute; reflexivity).
  assert (HKs : AF.SLOT_STACK = 1048576) by (vm_compute; reflexivity).
  assert (HKg : AC.GT = 6283264) by (vm_compute; reflexivity).
  assert (HKl : LOWMEM_END = 2147450880) by (vm_compute; reflexivity).
  assert (HA0r : 0 <= A0 < 2 ^ 64) by lia.
  assert (HAeq : A = A0) by (apply f4_id; [lia | lia |]; unfold rg in H9, Hr9; rewrite <- H9; exact Hr9).
  subst A0.
  assert (Hfr0 : 0 <= fr) by lia.
  assert (Hfr8 : fr mod 8 = 0) by (clear - Hfrm; Z.div_mod_to_equations; lia).
  assert (Hub : fr + FRAME_BYTES <= APPMEM_END).
  { assert (Ha : app_mem (fr + FRAME_BYTES - 1)) by (apply Happ; lia). unfold app_mem in Ha. lia. }
  assert (HWapp : forall x, app_mem x -> Frame.outside (f4_Wsh fr) x)
    by (intros x Hx; exact (f4_Wsh_app fr x Hfr0 ltac:(lia) Hx)).
  pose proof Hphiad as (Hp0 & _ & Hp2 & _).
  apply (f4_keepg g j phi fr A regs regs mem mem' md (f4_Wsh fr) HFRA HHB HFLSI HLK HC HID H9 HA MU WM).
  - intros x Hx. rewrite Hasz in Hx. replace x with phi by lia. exact (HWapp phi Hphiapp).
  - intros i Hi. rewrite Hasz in Hi. replace (phi + i) with phi by lia.
    unfold f4_Wsh. cbn [Frame.outside]. split; [|exact I]. intros HCx. unfold Sfr in HCx.
    destruct Hphifr as [Hd|Hd].
    + pose proof (f4_sh_lt2 phi fr ltac:(lia) ltac:(lia) Hfr8). lia.
    + assert (E : shadow_addr (fr + FRAME_BYTES) = shadow_addr fr + FRAME_SHADOW).
      { unfold shadow_addr. replace (fr + FRAME_BYTES) with (fr + FRAME_SHADOW * 8) by lia. rewrite Z.div_add by lia. lia. }
      pose proof (f4_sh_mono (fr + FRAME_BYTES) phi Hd). lia.
  - intros x Hx. apply HWapp. apply Happ. lia.
  - intros x Hx. left. apply HWapp. apply Happ. lia.
  - intros x Hx. unfold f4_Wsh. cbn [Frame.outside]. split; [lia | exact I].
  - intros x Hx. apply HWapp. unfold app_mem. right. lia.
  - intros x Hx. split.
    + apply HWapp. unfold app_mem. left. lia.
    + unfold f4_Wsh. cbn [Frame.outside]. split; [|exact I].
      pose proof (f4_sh_mono x fr ltac:(lia)). unfold Sfr. lia.
  - intros Hn x Hx. pose proof HFLSI as (_ & _ & _ & _ & HIN & _).
    destruct (f4_in_frame g fr _ regs mem md HFRA HIN Hn x Hx) as (Hxa & _ & _ & Hxf).
    split; [exact (HWapp x Hxa)|].
    assert (Hx0 : 0 <= x) by (unfold app_mem in Hxa; lia).
    unfold f4_Wsh. cbn [Frame.outside]. split; [|exact I]. intros HCx. unfold Sfr in HCx.
    destruct Hxf as [Hd|Hd].
    + pose proof (f4_sh_lt2 x fr Hx0 Hd Hfr8). lia.
    + assert (E : shadow_addr (fr + FRAME_BYTES) = shadow_addr fr + FRAME_SHADOW).
      { unfold shadow_addr. replace (fr + FRAME_BYTES) with (fr + FRAME_SHADOW * 8) by lia. rewrite Z.div_add by lia. lia. }
      pose proof (f4_sh_mono (fr + FRAME_BYTES) x Hd). lia.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

(* The cut skeleton across the parse call's writes, and the call's write set apart from the prologue save area
   above A + 32 (for the [A + 200] word F4 stored before the call). *)
Lemma f4_keep3 : forall g j phi fr A regs regs' mem mem' md FS (bs : list byte),
  FRA B APIf ra g fr (hb1 phi (AC.a_size (flen g j))) regs mem md ->
  HB mem phi (flen g j) -> FLSI g j fr regs mem -> LK g fr j regs mem ->
  b5_C g j phi fr regs mem -> IDj g fr j mem ->
  flen g j = 0 -> (phi + 1 <= fr \/ fr + FRAME_BYTES <= phi) ->
  rg regs 9 A -> 0 <= A < 2 ^ 64 ->
  word_mem rsegs mem (AC.as_tp AC.ASYMS) FS -> 0 <= FS < 2 ^ 64 ->
  Frame.munch (f4_PW (fr + 176) (AC.aspZ regs) FS) mem mem' -> Frame.wmono rsegs mem mem' ->
  rw_cells rsegs mem' (fr + 176) [CB 36 bs] ->
  getr regs' 2 = getr regs 2 -> getr regs' 9 = getr regs 9 -> getr regs' 18 = getr regs 18 ->
  getr regs' 21 = getr regs 21 -> getr regs' 23 = getr regs 23 ->
  (forall x, A + 32 <= x < A + 416 -> Frame.outside (f4_PW (fr + 176) (AC.aspZ regs) FS) x) /\
  HB mem' phi (flen g j) /\ FLSI g j fr regs' mem' /\ LK g fr j regs' mem' /\
  b5_C g j phi fr regs' mem' /\ IDj g fr j mem'.
Proof. pose proof FRAME_BYTES_val as HFBval. pose proof FRAME_SHADOW_val as HFSval.
  intros g j phi fr A regs regs' mem mem' md FS bs HFRA HHB HFLSI HLK HC HID Hlen0 Hphifr H9 HA Htp HFS MU WM
    HRW E2 E9 E18 E21 E23.
  pose proof (fra_app B APIf ra g fr _ regs mem md HFRA) as (HGT & Happ).
  pose proof (fra_frame B APIf ra g fr _ regs mem md HFRA) as (Hapart & _ & HFSfr & _).
  pose proof (fra_win B APIf ra g fr _ regs mem md HFRA) as (Hwlo & _).
  pose proof HHB as (Hphinz & Hphiad).
  pose proof HFRA as (A0 & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA416 & HS4 & HAPP & _).
  pose proof (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) as LAWS.
  pose proof (AC.a_laws_stack_high _ _ _ _ _ LAWS _ _ _ HAH) as Hhi.
  destruct (f4_law_fs_place _ _ _ FS HAH Htp HFS) as (HFSgt & HFSst & HFSal & HFSapp).
  pose proof (HFSfr FS Htp HFS) as HFSlow.
  pose proof (Hapart REAC_CTRL_PARSE_K ltac:(unfold REAC_CTRL_PARSE_K, FN_STACK, AF.SLOT_STACK; lia)) as Hwd.
  rewrite Haspz in MU, Hwd, Hwlo.
  assert (HKh : HIGHMEM_BEG = 17594333495296) by (vm_compute; reflexivity).
  assert (HKa : APPMEM_END = 140737488355328) by (vm_compute; reflexivity).
  assert (HKs : AF.SLOT_STACK = 1048576) by (vm_compute; reflexivity).
  assert (HKl : LOWMEM_END = 2147450880) by (vm_compute; reflexivity).
  assert (HKg : AC.GT = 6283264) by (vm_compute; reflexivity).
  assert (HKp : REAC_CTRL_PARSE_K = 8800) by (vm_compute; reflexivity).
  assert (HKf2 : AC.FS_SIZE = 11571200) by (vm_compute; reflexivity).
  assert (HKn : FN_STACK = 1044480) by (vm_compute; reflexivity).
  f4_imgc HKtp (AC.as_tp AC.ASYMS).
  assert (HA0r : 0 <= A0 < 2 ^ 64) by lia.
  assert (HAeq : A = A0) by (apply f4_id; [lia | lia |]; unfold rg in H9, Hr9; rewrite <- H9; exact Hr9).
  subst A0.
  assert (Hfr0 : 0 <= fr) by lia.
  assert (Hfr8 : fr mod 8 = 0) by (clear - Hfrm; Z.div_mod_to_equations; lia).
  assert (Hsp8 : (sp - 8800) mod 8 = 0) by (clear - Hspm; Z.div_mod_to_equations; lia).
  assert (HFS8 : FS mod 8 = 0) by (clear - HFSal; Z.div_mod_to_equations; lia).
  assert (Hfrlo : (fr + FRAME_BYTES <= LOWMEM_END \/ HIGHMEM_BEG <= fr) /\ fr + FRAME_BYTES <= APPMEM_END).
  { pose proof (Happ fr ltac:(lia)) as P1. pose proof (Happ (fr + FRAME_BYTES - 1) ltac:(lia)) as P2.
    unfold app_mem in P1, P2. lia. }
  assert (HFSlo : FS + AC.FS_SIZE <= LOWMEM_END \/ HIGHMEM_BEG <= FS).
  { pose proof (HFSapp FS ltac:(lia)) as P1. pose proof (HFSapp (FS + AC.FS_SIZE - 1) ltac:(lia)) as P2.
    unfold app_mem in P1, P2. lia. }
  assert (Ho0 : fr + 176 <> 0) by lia.
  assert (Hasz : AC.a_size (flen g j) = 1) by (unfold AC.a_size; rewrite Hlen0; lia).
  (* the record block: below stklo, off the side stack *)
  assert (HIn : In (phi, AC.a_size (flen g j)) (hb1 phi (AC.a_size (flen g j)) ++ g_H g))
    by (apply in_or_app; left; left; reflexivity).
  destruct (f4_law_blocks _ mem md phi (AC.a_size (flen g j)) HAH HIn) as (_ & Hp4096 & Hpst & Hpapp & Hpnfs).
  rewrite Hasz in Hpst, Hpapp, Hpnfs.
  pose proof (Hpapp phi ltac:(lia)) as Hphiapp. pose proof (Hpnfs phi ltac:(lia)) as Hphinfs.
  assert (HphinFS : ~ (FS <= phi < FS + AC.FS_SIZE)).
  { intros HCx. apply Hphinfs. exists FS. split; [exact HFS | split; [exact Htp | exact HCx]]. }
  assert (HSHO : forall y, 0 <= y < APPMEM_END -> (y < FS + 1085440 \/ FS + 2134016 <= y) ->
            (y < sp - 8800 \/ sp <= y) -> Frame.outside (f4_PW (fr + 176) sp FS) (shadow_addr y)).
  { intros y Hy Hy1 Hy2. apply f4_PW_out_sh; try lia. }
  assert (HAPO : forall x, app_mem x -> ~ (fr + 176 <= x < fr + 212) -> ~ (sp - 8800 <= x < sp) ->
            ~ (FS + 8 <= x < FS + 16) -> ~ (FS + 20480 <= x < FS + 28672) ->
            ~ (FS + 1085440 <= x < FS + 2134016) -> Frame.outside (f4_PW (fr + 176) sp FS) x).
  { intros x Hx N1 N2 N3 N4 N5.
    apply f4_PW_out_app; [lia | exact Hx | lia | lia | lia | lia | lia | lia | lia | lia | lia]. }
  clear Hfrm Hspm HAm HFSal Hfr8 Hsp8 HFS8.
  split.
  { rewrite Haspz. intros x Hx. apply HAPO; [unfold app_mem; lia | lia | lia | lia | lia | lia]. }
  apply (f4_keepg g j phi fr A regs regs' mem mem' md _ HFRA HHB HFLSI HLK HC HID H9 HA MU WM).
  - intros x Hx. rewrite Hasz in Hx. replace x with phi by lia. apply HAPO; [exact Hphiapp | lia | lia | lia | lia | lia].
  - intros i Hi. rewrite Hasz in Hi. replace (phi + i) with phi by lia. apply HSHO; lia.
  - intros x Hx. apply HAPO; [apply Happ; lia | lia | lia | lia | lia | lia].
  - intros x Hx.
    destruct (Z_le_gt_dec (fr + 176) x) as [C1|C1]; [destruct (Z_lt_ge_dec x (fr + 212)) as [C2|C2]|].
    + right. exact (f4_cell_byte mem' (fr + 176) 36 bs x HRW ltac:(change (Z.of_nat 36) with 36; lia)).
    + left. apply HAPO; [apply Happ; lia | lia | lia | lia | lia | lia].
    + left. apply HAPO; [apply Happ; lia | lia | lia | lia | lia | lia].
  - intros x Hx.
    replace x with (shadow_addr (fr + 8 * (x - Sfr fr))) by (rewrite f4_fr_sh; lia).
    apply HSHO; lia.
  - intros x Hx. apply HAPO; [unfold app_mem; lia | lia | lia | lia | lia | lia].
  - intros x Hx. split.
    + apply HAPO; [unfold app_mem; lia | lia | lia | lia | lia | lia].
    + apply HSHO; lia.
  - intros Hn x Hx. pose proof HFLSI as (_ & _ & _ & _ & HIN & _).
    destruct (f4_in_frame g fr _ regs mem md HFRA HIN Hn x Hx) as (Hxa & Hxs & HxFS & Hxf).
    pose proof (HxFS FS Htp HFS) as HxF.
    split.
    + apply HAPO; [exact Hxa | lia | lia | lia | lia | lia].
    + apply HSHO; [unfold app_mem in Hxa; lia | lia | lia].
  - exact E2.
  - exact E9.
  - exact E18.
  - exact E21.
  - exact E23.
Qed.

(* The kind and output of the parse of an empty record. *)
Lemma f4_ctrlparse0 : forall bs, ctrlparse 0 bs = (0, repeat cp_z 36).
Proof. intros bs. reflexivity. Qed.

(* The first four of the 36 zero output bytes are the u32 word 0. *)
Lemma f4_u32_zero : forall m a, rw_cells rsegs m a [CB 36 (repeat cp_z 36)] -> u32 m a 0.
Proof.
  intros m a ((_ & Hb) & _). cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb.
  replace (repeat cp_z 36) with (repeat cp_z 4 ++ repeat cp_z 32) in Hb by (rewrite <- repeat_app; reflexivity).
  apply Mem.bytes_at_app in Hb. destruct Hb as (Hb & _).
  unfold u32. match goal with |- ?P ?l => replace l with (repeat cp_z 4) by (vm_compute; reflexivity) end.
  exact Hb.
Qed.

(* ---------------- path 2: the segment lemma of the entry cut 0x81e54 ---------------- *)

Lemma f4_seg_dbc : forall j,
  Hat B APIf ra (Inv_A81e84_at B APIf ra) j -> Hat B APIf ra (Inv_A81e54_at B APIf ra) j.
Proof. pose proof FRAME_BYTES_val as HFBval. pose proof FRAME_SHADOW_val as HFSval.
  intros j Hexit g c HInv.
  pose proof (proj1 FF) as SEGS.
  destruct HInv as (phi & regs & mem & md & fr & Ec & HFRA & HENT &
    (Hgn & Hj & HHB & HFLSI & HLK & HC & Hlen0 & Hphifr & HID & _)).
  subst c. rewrite SEGS.
  pose proof HC as HC0.
  destruct HC0 as (Hs7 & Hs2 & (A & H9 & HA & _) & _ & _ & _ & _).
  pose proof (fra_app B APIf ra g fr _ regs mem md HFRA) as (HGT & Happ).
  pose proof HFRA as HFRA2.
  destruct HFRA2 as (Asp & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA416 & HS4 & HAPP &
    Hspill & Hsel & Hfr24 & Hloc & Hhdr1 & Hhdr2 & Hshb & Hwin & Hsaved & Herrno & HAG & HWA &
    HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive).
  pose proof (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) as LAWS.
  pose proof (AC.a_laws_stack_high _ _ _ _ _ LAWS _ mem md HAH) as Hstkhi.
  assert (HKh : HIGHMEM_BEG = 17594333495296) by (vm_compute; reflexivity).
  assert (HKa : APPMEM_END = 140737488355328) by (vm_compute; reflexivity).
  assert (HKs : AF.SLOT_STACK = 1048576) by (vm_compute; reflexivity).
  assert (HKl : LOWMEM_END = 2147450880) by (vm_compute; reflexivity).
  assert (HKk : ASAN_K = 2147450880) by (vm_compute; reflexivity).
  assert (HKg : AC.GT = 6283264) by (vm_compute; reflexivity).
  assert (HKp : REAC_CTRL_PARSE_K = 8800) by (vm_compute; reflexivity).
  assert (HKn : FN_STACK = 1044480) by (vm_compute; reflexivity).
  f4_imgc HKtp (AC.as_tp AC.ASYMS).
  f4_imgc HC5 asan_stack_malloc_c.CF.
  f4_imgc HC4 asan_stack_malloc_c.GOT_CF.
  f4_imgc HC5' bcmp_wrap_c.CF.
  f4_imgc HC4' bcmp_wrap_c.GOT_CF.
  assert (HAspR : 0 <= Asp < 2 ^ 64).
  { pose proof Hwin as HW0. unfold stk in HW0. destruct HW0 as (Hw0 & Hw1 & _). lia. }
  assert (HAeq : A = Asp) by (apply f4_id; [lia | lia |]; unfold rg in H9, Hr9; rewrite <- H9; exact Hr9).
  subst Asp.
  assert (Hfr0 : 0 <= fr) by lia.
  assert (Hfr8 : fr mod 8 = 0) by (clear - Hfrm; Z.div_mod_to_equations; lia).
  assert (HfrH : fr + FRAME_BYTES <= APPMEM_END).
  { pose proof (Happ (fr + FRAME_BYTES - 1) ltac:(lia)) as Ha. unfold app_mem in Ha. lia. }
  assert (HSfrlo : LOWMEM_END <= Sfr fr) by (unfold Sfr; apply f4_sh_lo; lia).
  assert (HSfrhi : Sfr fr + FRAME_SHADOW <= HIGHMEM_BEG).
  { unfold Sfr. pose proof (f4_sh_hi (fr + FRAME_BYTES - 1) ltac:(lia)) as Hh.
    pose proof (f4_sh_mono fr (fr + FRAME_BYTES - 1) ltac:(lia)). unfold shadow_addr in *.
    Z.div_mod_to_equations. lia. }
  pose proof HHB as (Hphinz & Hphiad).
  assert (Hasz : AC.a_size (flen g j) = 1) by (unfold AC.a_size; rewrite Hlen0; lia).
  pose proof Hphiad as (Hp0 & _ & Hp2 & _). rewrite Hasz in Hp2.
  (* the wr_at premises of the six stores *)
  assert (Wa : wr_at rsegs mem (A + 200) 8).
  { apply (f4_wr mem (A + 200) (A + 208)); [| lia | lia | lia].
    exact (f4_spill_stk g fr _ regs mem md A (A + 200) (A + 208) HFRA H9 HA
             ltac:(lia) ltac:(lia) ltac:(lia)). }
  assert (Wsh : wr_at rsegs mem (Sfr fr + 22) 5).
  { pose proof (AsanRTInv.RT_shadow_rw sp mem md HRT) as HSW0.
    split; [lia|]. split; [lia|]. intros i Hi.
    assert (Ei : Sfr fr + 22 + i = shadow_addr (fr + 176 + 8 * i))
      by (unfold Sfr, shadow_addr; Z.div_mod_to_equations; lia).
    rewrite Ei.
    exact (proj1 (HSW0 (shadow_addr (fr + 176 + 8 * i))
      (shadow_of_app (fr + 176 + 8 * i) (Happ (fr + 176 + 8 * i) ltac:(lia))))). }
  assert (HTPu : bv_unsigned (getr regs 4) = AC.as_tp AC.ASYMS)
    by (rewrite Hr4; apply MState.unsigned_lit; lia).
  assert (Htk : t_k (g_in g) j = fst (ctrlparse 0 (t_g (g_in g) j))).
  { unfold t_k. unfold flen in Hlen0. rewrite Hlen0. reflexivity. }
  apply (sl_run_lib regs (Z_to_bv 64 0x81e54) mem md
    (fun R0 pc' mem' =>
       pc' = Z_to_bv 64 0x81e84 /\
       getr R0 2 = getr regs 2 /\ getr R0 3 = getr regs 3 /\ getr R0 4 = getr regs 4 /\
       getr R0 8 = getr regs 8 /\ getr R0 9 = getr regs 9 /\ getr R0 19 = getr regs 19 /\
       getr R0 21 = getr regs 21 /\ getr R0 26 = getr regs 26 /\
       getr R0 23 = getr regs 23 /\ getr R0 18 = getr regs 18 /\
       getr R0 10 = Z_to_bv 64 (fst (ctrlparse 0 (t_g (g_in g) j))) /\
       exists m2 FS,
         FRA B APIf ra g fr (hb1 phi (AC.a_size (flen g j))) regs m2 md /\
         ENT APIf g (hb1 phi (AC.a_size (flen g j))) m2 md /\
         HB m2 phi (flen g j) /\ FLSI g j fr regs m2 /\ LK g fr j regs m2 /\ b5_C g j phi fr regs m2 /\
         IDj g fr j m2 /\ q64 m2 (A + 200) (phi + 18) /\
         word_mem rsegs m2 (AC.as_tp AC.ASYMS) FS /\ 0 <= FS < 2 ^ 64 /\
         Frame.munch (f4_PW (fr + 176) sp FS) m2 mem' /\ Frame.wmono rsegs m2 mem' /\ ro_same rsegs m2 mem' /\
         stk rsegs mem' (sp - REAC_CTRL_PARSE_K) sp /\
         rw_cells rsegs mem' (fr + 176) [CB 36 (snd (ctrlparse 0 (t_g (g_in g) j)))] /\
         shadow_rw mem' /\ addressable mem' (sp - REAC_CTRL_PARSE_K) REAC_CTRL_PARSE_K /\
         stk rsegs mem' FS (FS + FS_SIZE) /\ fp_cls mem' FS 1)
    (Post B APIf ra g)).
  - exact Hhalt.
  - (* the run 0x81e54 -> 0x81e84 *)
    rewrite f4_mkR_of_expand.
    f4_subst_slot Hr2. f4_subst_slot H9. f4_subst_slot Hr19. f4_subst_slot Hs7.
    eapply LE.evt_cut.
    { eapply f4_dbc_st with (A := A) (fr := fr) (phi := phi);
        [lia | lia | lia | lia | lia | lia | lia | exact Wa | exact Wsh]. }
    intros ms1 (m1 & m2 & a0' & E1 & MU1 & WM1 & MU2 & WM2 & ST1 & ST2 & HSH2 & HQ2).
    subst ms1.
    (* FRA, ENT and the cut skeleton at m1 (the spill) and at m2 (the five shadow bytes) *)
    assert (MUsp : Frame.munch (f4_Wsp A) mem m1).
    { apply (Frame.munch_weaken [(A + 200, A + 208)] (f4_Wsp A) mem m1); [|exact MU1].
      unfold Frame.sub_fp, f4_Wsp. intros x Hx. cbn [Frame.outside] in *. tauto. }
    destruct (f4_fra_spill g fr _ regs regs mem m1 md md A HFRA HENT H9 HA MUsp WM1 (ST1 _ _ Hwin)
                (AsanLift.mat_refl md) eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl)
      as (HFRA1 & HENT1).
    destruct (f4_keep1 g j phi fr A regs regs mem m1 md HFRA HHB HFLSI HLK HC HID H9 HA MUsp WM1
                eq_refl eq_refl eq_refl eq_refl eq_refl) as (HHB1 & HFLSI1 & HLK1 & HC1 & HID1).
    destruct (f4_fra_sh g fr _ regs m1 m2 md HFRA1 HENT1 MU2 WM2 HSH2) as (HFRA2 & HENT2).
    destruct (f4_keep2 g j phi fr A regs m1 m2 md HFRA1 HHB1 HFLSI1 HLK1 HC1 HID1 Hlen0 Hphifr H9 HA MU2 WM2)
      as (HHB2 & HFLSI2 & HLK2 & HC2 & HID2).
    (* the call's premises at m2 *)
    pose proof HC2 as (_ & _ & (A2 & H9b & HA2 & HSP2 & _) & _ & _ & (_ & HDB2) & _).
    assert (EA2 : A2 = A) by (apply f4_id; [lia | lia |]; unfold rg in H9, H9b; rewrite <- H9b; exact H9).
    subst A2.
    destruct HSP2 as (Hq248 & _).
    destruct (f4_fp_call g fr _ regs m2 md phi HFRA2 HDB2) as (FS & Htp2 & HFS & HFP & HTLS).
    destruct (fra_callee_fp B APIf ra g fr _ regs m2 md REAC_CTRL_PARSE_K [1%nat] FS
                (AC.aspZ regs - REAC_CTRL_PARSE_K) (AC.aspZ regs) _ _ HFRA2 ltac:(lia) HFP HTLS
                ltac:(lia) ltac:(lia)) as (HK1 & HK2 & HK3 & HSTKw & HAPPw & HADw & _ & _).
    rewrite Haspz in HK1, HK2, HK3, HSTKw, HADw, HFP, HTLS.
    pose proof (fra_frame B APIf ra g fr _ regs m2 md HFRA2) as (Hapart & _ & _ & _).
    pose proof (Hapart REAC_CTRL_PARSE_K ltac:(lia)) as Hwd. rewrite Haspz in Hwd.
    pose proof HFRA2 as (A4 & sp4 & s54 & HRT2 & _ & HRO2 & _).
    pose proof HFLSI2 as ((_ & _ & Hfstk2 & _ & _) & _).
    pose proof (f4_frame_stk m2 fr (fr + 176) (fr + 212) Hfstk2 ltac:(lia) ltac:(lia) ltac:(lia))
      as HSTKo2.
    destruct (stk_carve rsegs m2 (fr + 176) (fr + 212) 36 HSTKo2 ltac:(cbn; lia)) as (_ & junk & HRWo).
    replace (fr + 212 - Z.of_nat 36) with (fr + 176) in HRWo by (cbn; lia).
    assert (HADDRo : addressable m2 (fr + 176) 36)
      by (apply (f4_addr_o m2 fr ltac:(lia) Hfrm Happ ltac:(lia) HSH2)).
    assert (HAG2 : forall a, in_globals AF.frame_AG a -> addressable m2 a 1).
    { destruct HFRA2 as (A3 & sp3 & s53 & HRT3 & HAH3 & Hro3 & Hsn3 & Hhalt3 & Hgimg3 & Hr23 & Hspm3 & Haspz3 &
        Hstklo3 & Hr43 & Hr83 & Hr93 & Hr33 & Hr193 & Hr263 & Hfrm3 & Hs53 & HAm3 & HAS3 & Hspa3 & Hfa3 & HA4163 &
        HS43 & HAPP3 & Hspill3 & Hsel3 & Hfr243 & Hloc3 & Hhdr13 & Hhdr23 & Hsh3 & Hwin3 & Hsaved3 & Herrno3 &
        HAG3 & HWA3 & HSHI13 & HSHI23 & HSHI33 & Hhb3 & Hlive3).
      exact HAG3. }
    assert (HBCA2 : addressable m2 REAC_CTRL_PARSE_BC 6).
    { split; [unfold REAC_CTRL_PARSE_BC; lia|]. split; [unfold REAC_CTRL_PARSE_BC; lia|].
      split; [unfold REAC_CTRL_PARSE_BC; lia|].
      intros i Hi.
      assert (Hg : addressable m2 (REAC_CTRL_PARSE_BC + i) 1).
      { apply HAG2. exists REAC_CTRL_PARSE_BC, 7. split; [|lia].
        unfold AF.frame_AG, REAC_CTRL_PARSE_BC. cbn [In]. repeat (first [left; reflexivity | right]). }
      destruct Hg as (_ & _ & _ & Hg). pose proof (Hg 0 ltac:(lia)) as Hg0. rewrite Z.add_0_r in Hg0.
      exact Hg0. }
    destruct (f4_rt_cells _ _ _ HRT2) as (HBY1 & HBY2 & HBY3 & HBY4 & HBY5).
    eapply LE.evt_mono.
    { eapply (f4_dbc_calln _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m2 A phi (fr + 176) sp FS
                (t_g (g_in g) j) junk).
      - lia.
      - unfold AC.GT in HGT. lia.
      - lia.
      - lia.
      - exact Hspm.
      - lia.
      - lia.
      - lia.
      - exact HSTKw.
      - exact HRO2.
      - unfold t_g. apply fr50_length.
      - apply f4_rd8; [exact Hq248 | apply length_le8].
      - clear - Hfrm. Z.div_mod_to_equations. lia.
      - exact HRWo.
      - destruct Hwd as [Hd|Hd]; [left; lia | right; lia].
      - exact (AsanRTInv.RT_cells _ _ _ HRT2).
      - exact (AsanRTInv.RT_shadow_rw _ _ _ HRT2).
      - lia.
      - lia.
      - exact HADw.
      - exact HADDRo.
      - apply Happ. lia.
      - right. unfold AC.GT in HGT. lia.
      - exact HBCA2.
      - exact HBY1.
      - exact HBY2.
      - exact HBY3.
      - exact HBY4.
      - exact HBY5.
      - rewrite HTPu. exact HFP.
      - rewrite HTPu. exact HTLS. }
    { intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & tt3 & tt4 & tt5 & tt6 & m' &
        E & MU3 & WM3 & HRS3 & ST3 & RW3 & SW3 & AD3 & FSS3 & CLS3).
      eexists _, (Z_to_bv 64 0x81e84), m'. split; [exact E|].
      split; [reflexivity|].
      split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
      split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
      split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
      split; [reflexivity|]. split; [reflexivity|].
      exists m2, FS.
      split; [exact HFRA2|]. split; [exact HENT2|]. split; [exact HHB2|]. split; [exact HFLSI2|].
      split; [exact HLK2|]. split; [exact HC2|]. split; [exact HID2|]. split; [exact HQ2|].
      split; [exact Htp2|]. split; [exact HFS|].
      split; [exact MU3|]. split; [exact WM3|]. split; [exact HRS3|]. split; [exact ST3|].
      split; [exact RW3|]. split; [exact SW3|]. split; [exact AD3|]. split; [exact FSS3 | exact CLS3]. }
  - (* rebuilding the exit cut *)
    intros R0 pc' mem' regs' md'
      (Hpc & Er2 & Er3 & Er4 & Er8 & Er9 & Er19 & Er21 & Er26 & Er23 & Er18 & Er10 &
       m2 & FS & HFRA2 & HENT2 & HHB2 & HFLSI2 & HLK2 & HC2 & HID2 & HQ2 & Htp2 & HFS & MU3 & WM3 & HRS3 & ST3 &
       RW3 & SW3 & AD3 & FSS3 & CLS3) Hreg Hmat.
    subst pc'.
    assert (Fr2 : getr regs' 2 = getr regs 2) by (rewrite Hreg; exact Er2).
    assert (Fr3 : getr regs' 3 = getr regs 3) by (rewrite Hreg; exact Er3).
    assert (Fr4 : getr regs' 4 = getr regs 4) by (rewrite Hreg; exact Er4).
    assert (Fr8 : getr regs' 8 = getr regs 8) by (rewrite Hreg; exact Er8).
    assert (Fr9 : getr regs' 9 = getr regs 9) by (rewrite Hreg; exact Er9).
    assert (Fr19 : getr regs' 19 = getr regs 19) by (rewrite Hreg; exact Er19).
    assert (Fr21 : getr regs' 21 = getr regs 21) by (rewrite Hreg; exact Er21).
    assert (Fr26 : getr regs' 26 = getr regs 26) by (rewrite Hreg; exact Er26).
    assert (Fr23 : getr regs' 23 = getr regs 23) by (rewrite Hreg; exact Er23).
    assert (Fr18 : getr regs' 18 = getr regs 18) by (rewrite Hreg; exact Er18).
    assert (Fr10 : getr regs' 10 = Z_to_bv 64 (fst (ctrlparse 0 (t_g (g_in g) j))))
      by (rewrite Hreg; exact Er10).
    rewrite <- Haspz in MU3, ST3, AD3.
    destruct (f4_fra_call g fr _ regs regs' m2 mem' md md' FS _ HFRA2 Htp2 HFS MU3 WM3 HRS3 ST3 AD3 RW3 SW3
                FSS3 CLS3 Fr2 Fr3 Fr4 Fr8 Fr9 Fr19 Fr26 Hmat) as (HFRA' & HENTi).
    pose proof (HENTi HENT2) as HENT'.
    destruct (f4_keep3 g j phi fr A regs regs' m2 mem' md FS _ HFRA2 HHB2 HFLSI2 HLK2 HC2 HID2 Hlen0 Hphifr H9 HA
                Htp2 HFS MU3 WM3 RW3 Fr2 Fr9 Fr18 Fr21 Fr23) as (HWA3 & HHB' & HFLSI' & HLK' & HC' & HID').
    rewrite f4_ctrlparse0 in RW3, Fr10. cbn [fst snd] in RW3, Fr10.
    assert (Hk0 : t_k (g_in g) j = 0) by (rewrite Htk, f4_ctrlparse0; reflexivity).
    rewrite <- SEGS. apply Hexit.
    exists phi, regs', mem', md', fr.
    split; [reflexivity|].
    split; [exact HFRA'|]. split; [exact HENT'|].
    split; [exact Hgn|]. split; [exact Hj|]. split; [exact HHB'|]. split; [exact HFLSI'|].
    split; [exact HLK'|]. split; [exact HC'|].
    split; [lia|].
    rewrite Hk0.
    split; [unfold rg; exact Fr10|].
    split; [exact (f4_u32_zero mem' (fr + 176) RW3)|].
    split; [exact HID'|].
    (* b5_F17: the word 0x81e58 stored at [A + 200], which the shadow stores and the call miss *)
    split.
    { exists A. split; [unfold rg; rewrite Fr9; exact H9|]. split; [exact HA|].
      exact (f4_q64_keep _ m2 mem' _ _ HQ2 MU3 ltac:(intros x Hx; apply HWA3; lia)). }
    (* b5_PF: every part is guarded off on the empty arm (flen j = 0, so t_8819 j is false) *)
    exists A. split; [unfold rg; rewrite Fr9; exact H9|]. split; [exact HA|].
    split; [intros Hl; exfalso; lia | intros E; rewrite (f4_8819_0 g j Hlen0) in E; discriminate].
Qed.

(* ---------------- path 1 runs in the UL engine ----------------
   The UL step tactic steps a register file `mkR (getr regs 1) ...` (as F5 does); the 0x81dfc block is run with
   Tac_slot.sl_run in the UL engine, imported here for the rest of the Section. *)
Import OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Tac OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Bytes.
Import YK11.
Open Scope Z_scope.

(* The register file as the UL engine's own 31-slot map: its simp_regs only unfolds the UL `mkR`. *)
Lemma f4_mkR_of_expandu : forall regs, Regs6ss.mkR_of regs =
  mkR (getr regs 1) (getr regs 2) (getr regs 3) (getr regs 4) (getr regs 5) (getr regs 6)
  (getr regs 7) (getr regs 8) (getr regs 9) (getr regs 10) (getr regs 11) (getr regs 12)
  (getr regs 13) (getr regs 14) (getr regs 15) (getr regs 16) (getr regs 17) (getr regs 18)
  (getr regs 19) (getr regs 20) (getr regs 21) (getr regs 22) (getr regs 23) (getr regs 24)
  (getr regs 25) (getr regs 26) (getr regs 27) (getr regs 28) (getr regs 29) (getr regs 30) (getr regs 31).
Proof. intros regs. reflexivity. Qed.

Lemma f4_store_oku : forall m m' a (n : nat),
  (forall i, 0 <= i < Z.of_nat n -> wview rsegs m (wa (a + i)) <> None) -> wmono rsegs m m' ->
  0 <= a -> a + Z.of_nat n <= 2 ^ 64 -> store_ok rsegs m' (wa a) n = true.
Proof.
  intros m m' a n H Hw Ha Hn.
  assert (WR : wr_at rsegs m' a (Z.of_nat n)) by (split; [lia|]; split; [lia|]; intros i Hi; apply Hw, H, Hi).
  pose proof (wr_at_store_ok rsegs m' a (Z.of_nat n) 0 n WR ltac:(lia) ltac:(lia)) as HS.
  rewrite Z.add_0_r in HS. exact HS.
Qed.

Lemma f4_store_ok_stku : forall m m' lo hi a (n : nat),
  stk rsegs m lo hi -> wmono rsegs m m' -> lo <= a -> a + Z.of_nat n <= hi -> 0 <= a ->
  a + Z.of_nat n <= 2 ^ 64 -> store_ok rsegs m' (wa a) n = true.
Proof.
  intros m m' lo hi a n (_ & _ & HS) WM H1 H2 H3 H4.
  apply (f4_store_oku m m' a n); [|exact WM|exact H3|exact H4].
  intros i Hi. exact (proj1 (HS (a + i) ltac:(lia))).
Qed.

Lemma f4_rd1u : forall m a b, bytes_at rsegs m a [b] -> ov_read_bytes rsegs m (wa a) 1 = Some [b].
Proof.
  intros m a b H.
  pose proof (bytes_at_ov_read rsegs m a [b] 0 1 H ltac:(cbn; lia)) as HH.
  rewrite Z.add_0_r in HH. cbn [firstn skipn] in HH. exact HH.
Qed.

Lemma f4_ba_keep1u : forall m a bs c b (n : Z),
  Z.of_nat (length bs) = n -> 0 <= a -> a + n <= 2 ^ 64 -> bytes_at rsegs m c [b] ->
  (c + 1 <= a \/ a + n <= c) -> bytes_at rsegs (write_to_mem m (wa a) bs) c [b].
Proof.
  intros m a bs c b n Hn Ha Hb H Hd.
  apply bytes_at_write_other; [exact H | exact Ha | rewrite Hn; exact Hb |].
  cbn [length]. rewrite Hn. exact Hd.
Qed.

Lemma f4_zxb_equ : forall (b : byte) x, x = bv_unsigned b -> zxb b = Z_to_bv 64 x.
Proof. intros b x ->. reflexivity. Qed.

Lemma f4_seqzu : forall w : word, PropExec.v_sltiu w 1 = Z_to_bv 64 (if bv_unsigned w =? 0 then 1 else 0).
Proof.
  intros w. unfold PropExec.v_sltiu. change (bv_wrap 64 1) with 1%Z.
  pose proof (bv_unsigned_in_range 64 w) as Hr. unfold bv_modulus in Hr.
  replace (bv_unsigned w <? 1) with (bv_unsigned w =? 0)
    by (destruct (Z.eqb_spec (bv_unsigned w) 0); destruct (Z.ltb_spec (bv_unsigned w) 1); lia).
  destruct (bv_unsigned w =? 0); reflexivity.
Qed.

Lemma f4_eqb_lit : forall x y, 0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 ->
  bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 y) = (x =? y).
Proof. intros x y Hx Hy. unfold bv_eqb. rewrite !MState.unsigned_lit by lia. reflexivity. Qed.

(* `addi a0,a0,-25 ; seqz a0,a0` on a byte value: the 0/1 indicator of (byte = 25). *)
Lemma f4_sub25 : forall v, 0 <= v < 256 -> (bv_unsigned (Z_to_bv 64 (v - 25)) =? 0) = (v =? 25).
Proof.
  intros v Hv. rewrite MState.unsigned_lit_wrap.
  destruct (Z.eqb_spec v 25) as [->|Hne].
  - replace (25 - 25) with 0 by lia. reflexivity.
  - apply Z.eqb_neq. destruct (Z_lt_le_dec v 25) as [Hlt|Hge].
    + replace ((v - 25) mod 2 ^ 64) with (v - 25 + 2 ^ 64); [lia|].
      symmetry. rewrite <- (Z.mod_add (v - 25) 1 (2 ^ 64)) by lia.
      rewrite Z.mul_1_l. apply Z.mod_small. lia.
    + rewrite Z.mod_small by lia. lia.
Qed.

(* One byte of a carried byte list, as a 1-byte cell. *)
Lemma f4_ba_nth : forall m a (bs : list byte) (k : nat), bytes_at rsegs m a bs -> (k < length bs)%nat ->
  bytes_at rsegs m (a + Z.of_nat k) [nth k bs cp_z].
Proof.
  intros m a bs k H Hk. destruct H as (H0 & H1 & H).
  split; [lia|]. split; [cbn [length]; lia|].
  intros i Hi. destruct i as [|i]; [|cbn [length] in Hi; lia].
  cbn [nth_error Z.of_nat]. rewrite Z.add_0_r. rewrite (H k Hk).
  apply nth_error_nth'. exact Hk.
Qed.

(* The shadow byte of phi+k is 0 when the block (phi, L) with L >= 50 is addressable and the 8-byte granule of
   phi+k lies inside [phi, phi+50). *)
Lemma f4_sh_at : forall m phi L k, addressable m phi (AC.a_size L) -> 50 <= L -> 7 <= k <= 42 ->
  bytes_at rsegs m (Z.shiftr (phi + k) 3 + ASAN_K) [Z_to_bv 8 0].
Proof.
  intros m phi L k HA HL Hk.
  pose proof HA as (Hp0 & _ & _ & _).
  pose proof (Z.mod_pos_bound (phi + k) 8 ltac:(lia)) as Hr.
  assert (H8 : addressable m (phi + (k - (phi + k) mod 8)) 8)
    by (apply (addressable_sub m phi (AC.a_size L)); [exact HA | lia | lia | unfold AC.a_size; lia]).
  destruct (meta8 m _ H8) as [[_ RB] _].
  assert (E : Z.shiftr (phi + (k - (phi + k) mod 8)) 3 = Z.shiftr (phi + k) 3).
  { rewrite !Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
    pose proof (Z.div_mod (phi + k) 8 ltac:(lia)) as D.
    replace (phi + (k - (phi + k) mod 8)) with ((phi + k) / 8 * 8) by lia.
    rewrite Z.div_mul by lia. reflexivity. }
  rewrite E in RB. exact RB.
Qed.

(* ---------------- path 1: the segment lemma of the entry cut 0x81dfc ---------------- *)

Lemma seg_F4_d64 : forall j,
  Hat B APIf ra (Inv_A81e88_at B APIf ra) j ->
  Hat B APIf ra (Inv_A81ea4_at B APIf ra) j ->
  Hat B APIf ra (Inv_A81ea8_at B APIf ra) j ->
  Hat B APIf ra (Inv_A81dfc_at B APIf ra) j.
Proof. pose proof FRAME_BYTES_val as HFBval. pose proof FRAME_SHADOW_val as HFSval.
  intros j Hdf0 He0c He10 g c HInv.
  pose proof (proj1 FF) as SEGS.
  destruct HInv as (phi & regs & mem & md & fr & Ec & HFRA & HENT &
    (Hgn & Hj & HHB & HFLSI & HLK & HC & _ & Ha0 & Hs9 & Hs6 & Hu32 & HID & HPF)).
  subst c. rewrite SEGS.
  pose proof HC as HC0.
  destruct HC0 as (Hs7 & Hs2 & (A & H9 & HA & _) & HPH & _ & _ & _).
  pose proof HFRA as HFRA2.
  destruct HFRA2 as (Asp & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA416 & HS4 & HAPP &
    Hspill & Hsel & Hfr24 & Hloc & Hhdr1 & Hhdr2 & Hshq & Hwin & Hsaved & Herrno & HAG & HWA &
    HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive).
  pose proof (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) as LAWS.
  pose proof (AC.a_laws_stack_high _ _ _ _ _ LAWS (hb1 phi (AC.a_size (flen g j)) ++ g_H g) mem md HAH)
    as Hstkhigh.
  assert (HKh : HIGHMEM_BEG = 17594333495296) by (vm_compute; reflexivity).
  assert (HKa : APPMEM_END = 140737488355328) by (vm_compute; reflexivity).
  assert (HKs : AF.SLOT_STACK = 1048576) by (vm_compute; reflexivity).
  assert (HKk : ASAN_K = 2147450880) by (vm_compute; reflexivity).
  assert (HKl : LOWMEM_END = 2147450880) by (vm_compute; reflexivity).
  assert (HAspR : 0 <= Asp < 2 ^ 64).
  { pose proof Hwin as HW0. unfold stk in HW0. destruct HW0 as (Hw0 & Hw1 & _). lia. }
  assert (HAeq : A = Asp).
  { apply f4_id; [lia | lia |]. unfold rg in H9, Hr9. rewrite <- H9. exact Hr9. }
  subst A.
  pose proof HHB as (Hphinz & HAd).
  pose proof HAd as (Had0 & Had1 & Had2 & _).
  assert (HIn : In (phi, AC.a_size (flen g j)) (hb1 phi (AC.a_size (flen g j)) ++ g_H g))
    by (apply in_or_app; left; left; reflexivity).
  destruct (f4_law_blocks _ mem md phi (AC.a_size (flen g j)) HAH HIn) as (Hp16 & Hp4096 & Hpstk & _).
  pose proof (f4_flen_nn g j) as Hflen0.
  assert (Hasz : flen g j <= AC.a_size (flen g j)) by (unfold AC.a_size; lia).
  assert (Hphitop : phi + AC.a_size (flen g j) <= Asp) by lia.
  (* the two spill cells are byte-backed: they lie inside the 416-byte save area *)
  pose proof (f4_spill_stk g fr _ regs mem md Asp (Asp + 200) (Asp + 248) HFRA Hr9 HAspR
                ltac:(lia) ltac:(lia) ltac:(lia)) as HSTK.
  assert (HS200 : store_ok rsegs mem (wa (Asp + 200)) 8 = true).
  { apply (f4_store_ok_stku mem mem (Asp + 200) (Asp + 248) (Asp + 200) 8%nat HSTK (wmono_refl rsegs mem)); lia. }
  (* the exits' common part, after a write confined to the two spill words *)
  assert (REB : forall (regs' : bvmap 5 word) (mem' : word -> option byte) md',
    Frame.munch (f4_Wsp Asp) mem mem' -> Frame.wmono rsegs mem mem' ->
    stk rsegs mem' (g_S g - AF.SLOT_STACK) (g_S g) -> AsanLift.mat_le md md' ->
    getr regs' 2 = getr regs 2 -> getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 ->
    getr regs' 8 = getr regs 8 -> getr regs' 9 = getr regs 9 -> getr regs' 19 = getr regs 19 ->
    getr regs' 26 = getr regs 26 -> getr regs' 18 = getr regs 18 -> getr regs' 21 = getr regs 21 ->
    getr regs' 23 = getr regs 23 ->
    FRA B APIf ra g fr (hb1 phi (AC.a_size (flen g j))) regs' mem' md' /\
    ENT APIf g (hb1 phi (AC.a_size (flen g j))) mem' md' /\
    HB mem' phi (flen g j) /\ FLSI g j fr regs' mem' /\ LK g fr j regs' mem' /\
    b5_C g j phi fr regs' mem' /\ IDj g fr j mem' /\ u32 mem' (fr + 176) (t_k (g_in g) j) /\
    b5_PF g j phi fr regs' mem').
  { intros regs' mem' md' MU WM HWIN Hmat E2 E3 E4 E8 E9 E19 E26 E18 E21 E23.
    destruct (f4_fra_spill g fr _ regs regs' mem mem' md md' Asp HFRA HENT Hr9 HAspR MU WM HWIN Hmat
                E2 E3 E4 E8 E9 E19 E26) as (HFRA' & HENT').
    destruct (f4_keep1 g j phi fr Asp regs regs' mem mem' md HFRA HHB HFLSI HLK HC HID Hr9 HAspR MU WM
                E2 E9 E18 E21 E23) as (HHB' & HFLSI' & HLK' & HC' & HID').
    split; [exact HFRA'|]. split; [exact HENT'|]. split; [exact HHB'|]. split; [exact HFLSI'|].
    split; [exact HLK'|]. split; [exact HC'|]. split; [exact HID'|].
    split.
    { apply (f4_u32_keep (f4_Wsp Asp) mem mem' (fr + 176) _ Hu32 MU).
      intros x Hx. unfold f4_Wsp. cbn [Frame.outside]. repeat split; try exact I; lia. }
    exact (f4_pf_sp g j phi fr Asp regs regs' mem mem' md HFRA HPF Hr9 HAspR MU E9). }
  destruct (Z_le_gt_dec (flen g j) 49) as [Hshort|Hlong].
  - (* ---- the short arm (len <= 49): `bgeu a0,s2` taken, exit 0x81e88 ---- *)
    apply (sl_run regs (Z_to_bv 64 0x81dfc) mem md
      (fun R pc' mem' => pc' = Z_to_bv 64 0x81e88 /\
         getr R 2 = getr regs 2 /\ getr R 3 = getr regs 3 /\ getr R 4 = getr regs 4 /\
         getr R 8 = getr regs 8 /\ getr R 9 = getr regs 9 /\ getr R 19 = getr regs 19 /\
         getr R 21 = getr regs 21 /\ getr R 26 = getr regs 26 /\
         getr R 23 = getr regs 23 /\ getr R 18 = getr regs 18 /\
         getr R 24 = Z_to_bv 64 (t_k (g_in g) j) /\
         mem' = write_to_mem mem (wa (Asp + 200)) (le8 (Z_to_bv 64 (phi + 18))))
      (Post B APIf ra g)).
    + exact Hhalt.
    + rewrite f4_mkR_of_expandu.
      f4_subst_slot Ha0. f4_subst_slot Hs9. f4_subst_slot Hr9. f4_subst_slot Hs2.
      (* 0x81dfc mv s8,a0 ; 0x81e00 li a0,49 ; 0x81e04 sd s9,200(s1) ; 0x81e08 bgeu a0,s2 : taken *)
      step. step. step. step.
      rewrite (rc_ltu_lit64 49 (flen g j)) by lia.
      replace (49 <? flen g j) with false by (symmetry; apply Z.ltb_ge; lia).
      cbn [negb]. cbv iota.
      finish.
      all: simp_regs; try reflexivity.
    + intros R pc' mem' regs' md'
        (Hpc & HR2 & HR3 & HR4 & HR8 & HR9 & HR19 & HR21 & HR26 & HR23 & HR18 & HR24 & Hmem) Hreg Hmat.
      subst pc' mem'.
      assert (MU : Frame.munch (f4_Wsp Asp) mem (write_to_mem mem (wa (Asp + 200)) (le8 (Z_to_bv 64 (phi + 18))))).
      { unfold f4_Wsp. apply (munch_write _ mem mem (Asp + 200) (le8 (Z_to_bv 64 (phi + 18))));
          [ apply munch_refl | lia | rewrite length_le8; lia
          | rewrite length_le8; cbn [inside]; left; lia ]. }
      assert (WM : Frame.wmono rsegs mem (write_to_mem mem (wa (Asp + 200)) (le8 (Z_to_bv 64 (phi + 18)))))
        by (apply wmono_write; apply wmono_refl).
      assert (HWIN : stk rsegs (write_to_mem mem (wa (Asp + 200)) (le8 (Z_to_bv 64 (phi + 18))))
                       (g_S g - AF.SLOT_STACK) (g_S g))
        by (apply stk_write; [exact Hwin | lia | rewrite length_le8; lia]).
      destruct (REB regs' _ md' MU WM HWIN Hmat
                  ltac:(rewrite Hreg; exact HR2) ltac:(rewrite Hreg; exact HR3) ltac:(rewrite Hreg; exact HR4)
                  ltac:(rewrite Hreg; exact HR8) ltac:(rewrite Hreg; exact HR9) ltac:(rewrite Hreg; exact HR19)
                  ltac:(rewrite Hreg; exact HR26) ltac:(rewrite Hreg; exact HR18) ltac:(rewrite Hreg; exact HR21)
                  ltac:(rewrite Hreg; exact HR23))
        as (RFRA & RENT & RHB & RFLSI & RLK & RC & RID & Ru32 & RPF).
      rewrite <- SEGS. apply Hdf0.
      exists phi, regs', (write_to_mem mem (wa (Asp + 200)) (le8 (Z_to_bv 64 (phi + 18)))), md', fr.
      split; [reflexivity|].
      split; [exact RFRA|]. split; [exact RENT|].
      split; [exact Hgn|]. split; [exact Hj|]. split; [exact RHB|]. split; [exact RFLSI|].
      split; [exact RLK|]. split; [exact RC|].
      split; [lia|].
      split; [unfold rg; rewrite Hreg, HR24; reflexivity|].
      split; [exact Ru32|]. split; [exact RID|].
      (* b5_F17: the word 0x81e04 just stored at [A + 200] *)
      split; [|exact RPF].
      exists Asp. split; [unfold rg in *; rewrite Hreg, HR9; exact Hr9|]. split; [exact HAspR|].
      unfold q64. apply bytes_at_write_same; [lia | rewrite length_le8; lia].
  - (* ---- the long arm (50 <= len): the instrumented checks of the bytes phi+12 and phi+13 ---- *)
    assert (Hbig : t_big (g_in g) j = true) by (unfold t_big; apply Z.leb_le; unfold flen in Hlong; lia).
    destruct HPH as (HPHb & _ & _).
    pose proof (HPHb ltac:(lia)) as HGbytes.
    pose proof (Hs6 ltac:(lia)) as Hs6'.
    assert (Hglen : length (t_g (g_in g) j) = 50%nat) by (unfold t_g; apply fr50_length).
    assert (Hsh12 : bytes_at rsegs mem (Z.shiftr (phi + 12) 3 + ASAN_K) [Z_to_bv 8 0])
      by (apply (f4_sh_at mem phi (flen g j) 12 HAd); lia).
    assert (Hsh13 : bytes_at rsegs mem (Z.shiftr (phi + 13) 3 + ASAN_K) [Z_to_bv 8 0])
      by (apply (f4_sh_at mem phi (flen g j) 13 HAd); lia).
    pose proof (f4_ba_nth mem phi (t_g (g_in g) j) 12 HGbytes ltac:(rewrite Hglen; lia)) as Hb12.
    pose proof (f4_ba_nth mem phi (t_g (g_in g) j) 13 HGbytes ltac:(rewrite Hglen; lia)) as Hb13.
    change (Z.of_nat 12) with 12 in Hb12. change (Z.of_nat 13) with 13 in Hb13.
    assert (Hv12r : 0 <= cp_v (t_g (g_in g) j) 12 < 256) by (apply f4_byte_range).
    assert (Hv13r : 0 <= cp_v (t_g (g_in g) j) 13 < 256) by (apply f4_byte_range).
    (* The shadow bytes of phi+12 / phi+13 lie below the spill word (they are below HIGHMEM_BEG <= A).
       lia cannot see through Z.shiftr, so the two bounds are established here. *)
    assert (Hsa12 : Z.shiftr (phi + 12) 3 + ASAN_K + 1 <= Asp + 200).
    { rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8. Z.div_mod_to_equations. lia. }
    assert (Hsa13 : Z.shiftr (phi + 13) 3 + ASAN_K + 1 <= Asp + 200).
    { rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8. Z.div_mod_to_equations. lia. }
    destruct (Z.eq_dec (cp_v (t_g (g_in g) j) 12) 136) as [H12eq|H12ne].
    + (* byte 12 is 136: the check of byte 13, the spill [s1+240] and the jump to 0x81ea8 *)
      assert (H8819 : b2z (t_8819 (g_in g) j) = (if cp_v (t_g (g_in g) j) 13 =? 25 then 1 else 0)).
      { unfold b2z, t_8819. rewrite Hbig.
        replace (cp_v (t_g (g_in g) j) 12 =? 0x88) with true by (symmetry; apply Z.eqb_eq; exact H12eq).
        cbn [andb]. change 0x19 with 25. destruct (cp_v (t_g (g_in g) j) 13 =? 25); reflexivity. }
      apply (sl_run regs (Z_to_bv 64 0x81dfc) mem md
        (fun R pc' mem' => pc' = Z_to_bv 64 0x81ea8 /\
           getr R 2 = getr regs 2 /\ getr R 3 = getr regs 3 /\ getr R 4 = getr regs 4 /\
           getr R 8 = getr regs 8 /\ getr R 9 = getr regs 9 /\ getr R 19 = getr regs 19 /\
           getr R 21 = getr regs 21 /\ getr R 26 = getr regs 26 /\
           getr R 23 = getr regs 23 /\ getr R 18 = getr regs 18 /\ getr R 22 = getr regs 22 /\
           getr R 25 = getr regs 25 /\
           getr R 24 = Z_to_bv 64 (t_k (g_in g) j) /\
           mem' = write_to_mem (write_to_mem mem (wa (Asp + 200)) (le8 (Z_to_bv 64 (phi + 18))))
                    (wa (Asp + 240)) (le8 (Z_to_bv 64 (b2z (t_8819 (g_in g) j)))))
        (Post B APIf ra g)).
      * exact Hhalt.
      * rewrite f4_mkR_of_expandu.
        f4_subst_slot Ha0. f4_subst_slot Hs9. f4_subst_slot Hr9. f4_subst_slot Hs2.
        f4_subst_slot Hs7. f4_subst_slot Hr26.
        (* 0x81dfc mv s8,a0 ; 0x81e00 li a0,49 ; 0x81e04 sd s9,200(s1) ; 0x81e08 bgeu a0,s2 : not taken *)
        step. step. step. step.
        rewrite (rc_ltu_lit64 49 (flen g j)) by lia.
        replace (49 <? flen g j) with true by (symmetry; apply Z.ltb_lt; lia).
        cbn [negb]. cbv iota.
        lazymatch goal with
        | |- _ _ _ (MS _ _ _ _ _ ?mm _) =>
          assert (RD12s : ov_read_bytes rsegs mm (wa (Z.shiftr (phi + 12) 3 + ASAN_K)) 1 = Some [Z_to_bv 8 0])
            by (apply f4_rd1u; apply (f4_ba_keep1u mem _ _ _ _ 8);
                  [ rewrite length_le8; reflexivity | lia | lia | exact Hsh12 | left; lia ]);
          assert (RD13s : ov_read_bytes rsegs mm (wa (Z.shiftr (phi + 13) 3 + ASAN_K)) 1 = Some [Z_to_bv 8 0])
            by (apply f4_rd1u; apply (f4_ba_keep1u mem _ _ _ _ 8);
                  [ rewrite length_le8; reflexivity | lia | lia | exact Hsh13 | left; lia ]);
          assert (RD12 : ov_read_bytes rsegs mm (wa (phi + 12)) 1
                           = Some [nth 12 (t_g (g_in g) j) cp_z])
            by (apply f4_rd1u; apply (f4_ba_keep1u mem _ _ _ _ 8);
                  [ rewrite length_le8; reflexivity | lia | lia | exact Hb12 | left; lia ]);
          assert (RD13 : ov_read_bytes rsegs mm (wa (phi + 13)) 1
                           = Some [nth 13 (t_g (g_in g) j) cp_z])
            by (apply f4_rd1u; apply (f4_ba_keep1u mem _ _ _ _ 8);
                  [ rewrite length_le8; reflexivity | lia | lia | exact Hb13 | left; lia ]);
          assert (HS240 : store_ok rsegs mm (wa (Asp + 240)) 8 = true)
            by (apply (f4_store_ok_stku mem mm (Asp + 200) (Asp + 248) (Asp + 240) 8%nat HSTK);
                  [ apply wmono_write; apply wmono_refl | lia | lia | lia | lia ])
        end.
        (* 0x81e0c addi a0,s7,12 ; 0x81e10 srli a1,a0,3 ; 0x81e14 add a1,a1,s10 *)
        step. rewrite ?(MState.unsigned_lit phi) by lia.
        step. step. rewrite ?(MState.unsigned_lit (phi + 12)) by lia.
        (* 0x81e18 lb a1,0(a1) : the shadow byte is 0 ; 0x81e1c bnez a1 : not taken *)
        step.
        replace (sxb (Z_to_bv 8 0)) with (Z_to_bv 64 0) by (apply bv_eq; vm_compute; reflexivity).
        step. if_false.
        (* 0x81e20 lbu a0,0(a0) ; 0x81e24 li a1,136 ; 0x81e28 bne a0,a1 : not taken *)
        step. step. step.
        rewrite (f4_zxb_equ (nth 12 (t_g (g_in g) j) cp_z) (cp_v (t_g (g_in g) j) 12)) by reflexivity.
        rewrite (f4_eqb_lit (cp_v (t_g (g_in g) j) 12) 136) by lia.
        replace (cp_v (t_g (g_in g) j) 12 =? 136) with true by (symmetry; apply Z.eqb_eq; exact H12eq).
        cbn [negb]. cbv iota.
        (* 0x81e2c addi a0,s7,13 ; 0x81e30 srli a1,a0,3 ; 0x81e34 add a1,a1,s10 *)
        step. rewrite ?(MState.unsigned_lit phi) by lia.
        step. step. rewrite ?(MState.unsigned_lit (phi + 13)) by lia.
        (* 0x81e38 lb a1,0(a1) : the shadow byte is 0 ; 0x81e3c bnez a1 : not taken *)
        step.
        replace (sxb (Z_to_bv 8 0)) with (Z_to_bv 64 0) by (apply bv_eq; vm_compute; reflexivity).
        step. if_false.
        (* 0x81e40 lbu a0,0(a0) ; 0x81e44 addi a0,a0,-25 ; 0x81e48 seqz a0,a0 *)
        step.
        rewrite (f4_zxb_equ (nth 13 (t_g (g_in g) j) cp_z) (cp_v (t_g (g_in g) j) 13)) by reflexivity.
        step. rewrite ?(MState.unsigned_lit (cp_v (t_g (g_in g) j) 13)) by lia.
        step. rewrite f4_seqzu.
        rewrite ?(MState.unsigned_lit_wrap (cp_v (t_g (g_in g) j) 13 - 25)).
        (* 0x81e4c sd a0,240(s1) ; 0x81e50 j 81e10 *)
        step. step.
        finish.
        all: simp_regs; try reflexivity.
        rewrite H8819. do 3 f_equal.
        rewrite <- (f4_sub25 (cp_v (t_g (g_in g) j) 13)) by lia.
        rewrite MState.unsigned_lit_wrap. reflexivity.
      * intros R pc' mem' regs' md'
          (Hpc & HR2 & HR3 & HR4 & HR8 & HR9 & HR19 & HR21 & HR26 & HR23 & HR18 & HR22 & HR25 & HR24 & Hmem)
          Hreg Hmat.
        subst pc' mem'.
        assert (MU1 : Frame.munch (f4_Wsp Asp) mem
                        (write_to_mem mem (wa (Asp + 200)) (le8 (Z_to_bv 64 (phi + 18))))).
        { unfold f4_Wsp. apply (munch_write _ mem mem (Asp + 200) (le8 (Z_to_bv 64 (phi + 18))));
            [ apply munch_refl | lia | rewrite length_le8; lia
            | rewrite length_le8; cbn [inside]; left; lia ]. }
        assert (MU : Frame.munch (f4_Wsp Asp) mem
                       (write_to_mem (write_to_mem mem (wa (Asp + 200)) (le8 (Z_to_bv 64 (phi + 18))))
                          (wa (Asp + 240)) (le8 (Z_to_bv 64 (b2z (t_8819 (g_in g) j)))))).
        { unfold f4_Wsp in *.
          apply (munch_write _ mem _ (Asp + 240) (le8 (Z_to_bv 64 (b2z (t_8819 (g_in g) j)))));
            [ exact MU1 | lia | rewrite length_le8; lia
            | rewrite length_le8; cbn [inside]; right; left; lia ]. }
        assert (WM : Frame.wmono rsegs mem
                       (write_to_mem (write_to_mem mem (wa (Asp + 200)) (le8 (Z_to_bv 64 (phi + 18))))
                          (wa (Asp + 240)) (le8 (Z_to_bv 64 (b2z (t_8819 (g_in g) j))))))
          by (apply wmono_write; apply wmono_write; apply wmono_refl).
        assert (HWIN : stk rsegs
                         (write_to_mem (write_to_mem mem (wa (Asp + 200)) (le8 (Z_to_bv 64 (phi + 18))))
                            (wa (Asp + 240)) (le8 (Z_to_bv 64 (b2z (t_8819 (g_in g) j)))))
                         (g_S g - AF.SLOT_STACK) (g_S g)).
        { apply stk_write; [apply stk_write; [exact Hwin | lia | rewrite length_le8; lia]
                           | lia | rewrite length_le8; lia]. }
        assert (Hq240 : q64 (write_to_mem (write_to_mem mem (wa (Asp + 200)) (le8 (Z_to_bv 64 (phi + 18))))
                               (wa (Asp + 240)) (le8 (Z_to_bv 64 (b2z (t_8819 (g_in g) j)))))
                          (Asp + 240) (b2z (t_8819 (g_in g) j))).
        { unfold q64. apply bytes_at_write_same; [lia | rewrite length_le8; lia]. }
        destruct (REB regs' _ md' MU WM HWIN Hmat
                    ltac:(rewrite Hreg; exact HR2) ltac:(rewrite Hreg; exact HR3) ltac:(rewrite Hreg; exact HR4)
                    ltac:(rewrite Hreg; exact HR8) ltac:(rewrite Hreg; exact HR9) ltac:(rewrite Hreg; exact HR19)
                    ltac:(rewrite Hreg; exact HR26) ltac:(rewrite Hreg; exact HR18)
                    ltac:(rewrite Hreg; exact HR21) ltac:(rewrite Hreg; exact HR23))
          as (RFRA & RENT & RHB & RFLSI & RLK & RC & RID & Ru32 & RPF).
        rewrite <- SEGS. apply He10.
        exists phi, regs',
          (write_to_mem (write_to_mem mem (wa (Asp + 200)) (le8 (Z_to_bv 64 (phi + 18))))
             (wa (Asp + 240)) (le8 (Z_to_bv 64 (b2z (t_8819 (g_in g) j))))), md', fr.
        split; [reflexivity|].
        split; [exact RFRA|]. split; [exact RENT|].
        split; [exact Hgn|]. split; [exact Hj|]. split; [exact RHB|]. split; [exact RFLSI|].
        split; [exact RLK|]. split; [exact RC|].
        split; [lia|].
        split; [unfold rg in *; rewrite Hreg, HR22; exact Hs6'|].
        split; [unfold rg; rewrite Hreg, HR24; reflexivity|].
        split; [unfold rg in *; rewrite Hreg, HR25; exact Hs9|].
        split.
        { exists Asp. split; [unfold rg in *; rewrite Hreg, HR9; exact Hr9|].
          split; [exact HAspR | exact Hq240]. }
        split; [exact Ru32|]. split; [exact RID|].
        (* b5_F17: the word 0x81e04 stored at [A + 200], which the 0x81e4c store misses *)
        split.
        { exists Asp. split; [unfold rg in *; rewrite Hreg, HR9; exact Hr9|]. split; [exact HAspR|].
          unfold q64. apply bytes_at_write_other;
            [ apply bytes_at_write_same; [lia | rewrite length_le8; lia] | lia | rewrite length_le8; lia
            | rewrite !length_le8; lia ]. }
        (* b5_W240: the word 0x81e4c just stored at [A + 240], b2z (t_8819 j) *)
        split; [|exact RPF].
        exists Asp. split; [unfold rg in *; rewrite Hreg, HR9; exact Hr9|]. split; [exact HAspR|].
        exists (b2z (t_8819 (g_in g) j)). split; [exact Hq240|].
        destruct (t_8819 (g_in g) j); cbv [b2z]; repeat split; intros; try lia; discriminate.
    + (* byte 12 is not 136: `bne a0,a1` taken, exit 0x81ea4 *)
      assert (H8819f : t_8819 (g_in g) j = false).
      { unfold t_8819.
        replace (cp_v (t_g (g_in g) j) 12 =? 0x88) with false by (symmetry; apply Z.eqb_neq; exact H12ne).
        rewrite andb_false_r. rewrite andb_false_l. reflexivity. }
      apply (sl_run regs (Z_to_bv 64 0x81dfc) mem md
        (fun R pc' mem' => pc' = Z_to_bv 64 0x81ea4 /\
           getr R 2 = getr regs 2 /\ getr R 3 = getr regs 3 /\ getr R 4 = getr regs 4 /\
           getr R 8 = getr regs 8 /\ getr R 9 = getr regs 9 /\ getr R 19 = getr regs 19 /\
           getr R 21 = getr regs 21 /\ getr R 26 = getr regs 26 /\
           getr R 23 = getr regs 23 /\ getr R 18 = getr regs 18 /\ getr R 22 = getr regs 22 /\
           getr R 25 = getr regs 25 /\
           getr R 24 = Z_to_bv 64 (t_k (g_in g) j) /\
           mem' = write_to_mem mem (wa (Asp + 200)) (le8 (Z_to_bv 64 (phi + 18))))
        (Post B APIf ra g)).
      * exact Hhalt.
      * rewrite f4_mkR_of_expandu.
        f4_subst_slot Ha0. f4_subst_slot Hs9. f4_subst_slot Hr9. f4_subst_slot Hs2.
        f4_subst_slot Hs7. f4_subst_slot Hr26.
        step. step. step. step.
        rewrite (rc_ltu_lit64 49 (flen g j)) by lia.
        replace (49 <? flen g j) with true by (symmetry; apply Z.ltb_lt; lia).
        cbn [negb]. cbv iota.
        lazymatch goal with
        | |- _ _ _ (MS _ _ _ _ _ ?mm _) =>
          assert (RD12s : ov_read_bytes rsegs mm (wa (Z.shiftr (phi + 12) 3 + ASAN_K)) 1 = Some [Z_to_bv 8 0])
            by (apply f4_rd1u; apply (f4_ba_keep1u mem _ _ _ _ 8);
                  [ rewrite length_le8; reflexivity | lia | lia | exact Hsh12 | left; lia ]);
          assert (RD12 : ov_read_bytes rsegs mm (wa (phi + 12)) 1
                           = Some [nth 12 (t_g (g_in g) j) cp_z])
            by (apply f4_rd1u; apply (f4_ba_keep1u mem _ _ _ _ 8);
                  [ rewrite length_le8; reflexivity | lia | lia | exact Hb12 | left; lia ])
        end.
        step. rewrite ?(MState.unsigned_lit phi) by lia.
        step. step. rewrite ?(MState.unsigned_lit (phi + 12)) by lia.
        step.
        replace (sxb (Z_to_bv 8 0)) with (Z_to_bv 64 0) by (apply bv_eq; vm_compute; reflexivity).
        step. if_false.
        step. step. step.
        rewrite (f4_zxb_equ (nth 12 (t_g (g_in g) j) cp_z) (cp_v (t_g (g_in g) j) 12)) by reflexivity.
        rewrite (f4_eqb_lit (cp_v (t_g (g_in g) j) 12) 136) by lia.
        replace (cp_v (t_g (g_in g) j) 12 =? 136) with false by (symmetry; apply Z.eqb_neq; exact H12ne).
        cbn [negb]. cbv iota.
        finish.
        all: simp_regs; try reflexivity.
      * intros R pc' mem' regs' md'
          (Hpc & HR2 & HR3 & HR4 & HR8 & HR9 & HR19 & HR21 & HR26 & HR23 & HR18 & HR22 & HR25 & HR24 & Hmem)
          Hreg Hmat.
        subst pc' mem'.
        assert (MU : Frame.munch (f4_Wsp Asp) mem
                       (write_to_mem mem (wa (Asp + 200)) (le8 (Z_to_bv 64 (phi + 18))))).
        { unfold f4_Wsp. apply (munch_write _ mem mem (Asp + 200) (le8 (Z_to_bv 64 (phi + 18))));
            [ apply munch_refl | lia | rewrite length_le8; lia
            | rewrite length_le8; cbn [inside]; left; lia ]. }
        assert (WM : Frame.wmono rsegs mem (write_to_mem mem (wa (Asp + 200)) (le8 (Z_to_bv 64 (phi + 18)))))
          by (apply wmono_write; apply wmono_refl).
        assert (HWIN : stk rsegs (write_to_mem mem (wa (Asp + 200)) (le8 (Z_to_bv 64 (phi + 18))))
                         (g_S g - AF.SLOT_STACK) (g_S g))
          by (apply stk_write; [exact Hwin | lia | rewrite length_le8; lia]).
        destruct (REB regs' _ md' MU WM HWIN Hmat
                    ltac:(rewrite Hreg; exact HR2) ltac:(rewrite Hreg; exact HR3) ltac:(rewrite Hreg; exact HR4)
                    ltac:(rewrite Hreg; exact HR8) ltac:(rewrite Hreg; exact HR9) ltac:(rewrite Hreg; exact HR19)
                    ltac:(rewrite Hreg; exact HR26) ltac:(rewrite Hreg; exact HR18)
                    ltac:(rewrite Hreg; exact HR21) ltac:(rewrite Hreg; exact HR23))
          as (RFRA & RENT & RHB & RFLSI & RLK & RC & RID & Ru32 & RPF).
        rewrite <- SEGS. apply He0c.
        exists phi, regs', (write_to_mem mem (wa (Asp + 200)) (le8 (Z_to_bv 64 (phi + 18)))), md', fr.
        split; [reflexivity|].
        split; [exact RFRA|]. split; [exact RENT|].
        split; [exact Hgn|]. split; [exact Hj|]. split; [exact RHB|]. split; [exact RFLSI|].
        split; [exact RLK|]. split; [exact RC|].
        split; [lia|].
        split; [unfold rg in *; rewrite Hreg, HR22; exact Hs6'|].
        split; [unfold rg; rewrite Hreg, HR24; reflexivity|].
        split; [unfold rg in *; rewrite Hreg, HR25; exact Hs9|].
        split; [exact H8819f|]. split; [exact Ru32|]. split; [exact RID|].
        (* b5_F17: the word 0x81e04 just stored at [A + 200] *)
        split; [|exact RPF].
        exists Asp. split; [unfold rg in *; rewrite Hreg, HR9; exact Hr9|]. split; [exact HAspR|].
        unfold q64. apply bytes_at_write_same; [lia | rewrite length_le8; lia].
Qed.

(* ---------------- segment F4 ----------------
   The two entry cuts of the segment, each proved against the exits F5 enters: the 0x81dfc block leaves to
   Inv_A81e88_at (the record length is at most 49), Inv_A81ea4_at (the byte at s7+12 is not 136) or Inv_A81ea8_at
   (it is 136, and [s1+240] holds the 0/1 value of "the byte at s7+13 is 25"); the 0x81e54 block runs through
   `jal reac_ctrl_parse` and lands at its return point Inv_A81e84_at. *)
Lemma seg_F4 : forall j,
  Hat B APIf ra (Inv_A81e88_at B APIf ra) j ->
  Hat B APIf ra (Inv_A81ea4_at B APIf ra) j ->
  Hat B APIf ra (Inv_A81ea8_at B APIf ra) j ->
  Hat B APIf ra (Inv_A81e84_at B APIf ra) j ->
  Hat B APIf ra (Inv_A81dfc_at B APIf ra) j /\ Hat B APIf ra (Inv_A81e54_at B APIf ra) j.
Proof. pose proof FRAME_BYTES_val as HFBval. pose proof FRAME_SHADOW_val as HFSval.
  intros j Hdf0 He0c He10 Hdec.
  split; [exact (seg_F4_d64 j Hdf0 He0c He10) | exact (f4_seg_dbc j Hdec)].
Qed.

End S.
