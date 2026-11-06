(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_bigint/lib/L5TCopyS.v, with its module paths and module names changed; 3817 of its 3853 lines of code are new or changed and 212 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/ctrl_lay_block.v, with its module paths and module names changed; 371 of its 396 lines of code are new or changed and 3828 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/Seg/P2.v, with its module paths and module names changed; 554 of its 593 lines of code are new or changed and 357 lines of the source are left out. *)
(* Segment F7 of LLVMFuzzerTestOneInput, image B (the asan-ubsan build of libreac v1.9.0), range 0x8215c-0x82170
   (slot-plan-asan-ubsan section 2 row F7, call KN@0x82170): the check of the second parse result against the carried
   kind, and the first reac_ctrl_kind_name call. The image-B port of lib/A/Prog/Seg/F7.v.
     0x8215c bne a0,s8,0x82fa4   a0 = s8 = v (the parse result, carried): not taken
     0x82160 ld  a0,280(s1)      a0 = [A+280] = fr+176 (the record pointer spill, FLI)
     0x82164 lw  a0,0(a0)        a0 = sext32 [fr+176] = v (0 <= v < 2^31)
     0x82168 bne s8,a0,0x82fa4   s8 = a0 = v: not taken
     0x8216c mv  a0,s8           a0 = v
     0x82170 jal reac_ctrl_kind_name
   v1.9.0 reloads the record pointer from the spill [A+280] (the patched image kept it in s6). The range has no
   instrumented check (no load of a shadow byte) and no branch to the trap 0x82fa0. The segment runs through the call
   (the lib/B contract reac_ctrl_kind_name_contract, a Section Hypothesis) and ends at its return point 0x82174 with
   a0 = kind_name_addr v. The callee writes only its stack window W = [sp-16, sp); FRA moves across that write by
   the local lemma sl_win_run (W lies in [HIGHMEM_BEG, sp), disjoint from the frame by fra_frame at
   K = REAC_CTRL_KIND_NAME_FRAME), then to the end model by Tac_slot.sl_fra_move.
   Both cuts are the OFFICIAL Inv_B8215c_at / Inv_B82174_at of lib/B/Prog/SlotInv.v (adopt 7, a working branch 5d00119968):
   seg_F7 is S_F7 of the image-B segment forms. FRA gives what the cut text leaves out: sp <= APPMEM_END (sp <= A <=
   S < APPMEM_END), the frame in app memory above GT (fra_app) and apart from the callee window (fra_frame), and
   Phi's live block (Phi, a_size len) below stklo <= sp - FN_STACK (a_laws_blocks, fra_win). Every conjunct the cuts
   carry is kept across the call: the registers are callee-saved; the spills (FM, FLI, FTURN's [A+224] / [A+232],
   [A+248] = 1 - sum_ok, F272's [A+272], [A+280], FLVsp) lie in [A, A + 448) at or above sp; the frame's bytes at
   Phi (FTURN) and its first 50 bytes (for len >= 50) lie in Phi's block below the window; the two frame records
   (REC0, 38 + 72 bytes), the local `first` (FSj, [fr + 2880, fr + 2920)), the parse struct t_B j at fr + 176 with
   its 36 addressable bytes (FPS), our[], RAD and the frame's stk lie in the frame, which the window misses. The cuts
   carry no mem_inv (FRA gives ro_agree only); the KN string premise comes from ro_agree through the normalized
   memory (kn_strings_ro), and ro_agree after the call from the KN window lying above every read-only image address
   (f7_ro_low). *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Reusable Require Import YK11 YM05 YK0o YK0s YK15 YP09 YO0f YO0d YO09
  YL00 YL0g YL0i YI14 YI16 YL01 YM06.
(* The fragment / identity record models (fg_next / fg_class, the rf_* length facts, ING_length) and the parse model
   (ctrlparse_length), for the record lengths f7_FG_length / f7_ID_length and t_B's 36 bytes; imported before the
   main imports below, so those keep their names. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcModel RcRec RcFrag RcFragLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require RcIdentModel RcParse.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import Img0 AsanRT AsanRTInv AsanRTFacts PContract MemNorm AsanLift KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Contract FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcKind RcKindLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import reac_ctrl_kind_name_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import SlotModel SlotInv RcAsanFPLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.Seg Require Import Tac_slot.
Import ListNotations.
Import YK11.
Open Scope Z_scope.

Module AC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Contract.
Module AF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.FrameAPI.
Module LE := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Exec.
Module BMN := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.MemNorm.
Module LMem := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.

(* The lw at 0x82164 sign-extends the low 32 bits; a value below 2^31 is kept. *)
Lemma f7_sx32_small : forall v, 0 <= v < 2 ^ 31 -> sx32 (Z_to_bv 64 v) = Z_to_bv 64 v.
Proof.
  intros v Hv. unfold sx32. rewrite (unsigned_lit v) by lia. f_equal.
  unfold bv_swrap. change (bv_half_modulus 32) with (2 ^ 31). unfold bv_wrap. change (bv_modulus 32) with (2 ^ 32).
  rewrite Z.mod_small by lia. lia.
Qed.

Lemma kn_len : length kind_name_bytes = 112%nat.
Proof. reflexivity. Qed.

(* The kind-name strings are read-only image bytes (the same check as reac_ctrl_kind_name_strings_in_image). *)
Lemma kn_strings : forall m, mem_inv rsegs m -> kind_name_strings m.
Proof.
  intros m Hm x Hx. destruct (Z.leb_spec x 13) as [Hle|Hgt].
  - destruct (rc_Z_le13 x ltac:(lia)) as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->| -> ]]]]]]]]]]]]];
      (apply rc_ro_in_image; [exact Hm | vm_compute; reflexivity]).
  - assert (E : kind_name_addr x = QMARK)
      by (unfold kind_name_addr; rewrite (proj2 (Z.leb_gt x 13) Hgt); reflexivity).
    rewrite E, (kind_name_big x Hgt).
    apply rc_ro_in_image; [exact Hm | vm_compute; reflexivity].
Qed.

(* The same strings over a memory that only agrees with the image on its read-only bytes (FRA's ro_agree): the
   strings are read-only bytes, so the memory reads them as its normalization does, where mem_inv holds. *)
Lemma kn_strings_ro : forall m, ro_agree rsegs m -> kind_name_strings m.
Proof.
  intros m Hro x Hx.
  apply (proj2 (BMN.bytes_at_rel rsegs m (BMN.normalize rsegs m) _ _ (BMN.mem_rel_normalize rsegs m Hro))).
  exact (kn_strings (BMN.normalize rsegs m) (BMN.mem_inv_normalize rsegs m) x Hx).
Qed.

(* A segment found for [x, x + n) with n > 0 ends at or below every bound on the segment tops (the text of
   lib/B/BzBridge.v's find_segment_below). *)
Lemma f7_find_below : forall (sl : list Segment) (top x n : Z) s,
  forallb (fun s => Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? top) sl = true ->
  find_segment sl x n = Some s -> 0 <= n -> x < top \/ n = 0.
Proof.
  induction sl as [|s0 r IH]; intros top x n s Hb H Hn; cbn in H; [discriminate H|].
  cbn [forallb] in Hb. apply andb_prop in Hb as [H0 Hr].
  apply Z.leb_le in H0.
  destruct (Z.leb (Z.of_N (seg_base s0)) x && Z.leb (x + n) (Z.of_N (seg_base s0) + Z.of_N (seg_size s0))) eqn:E.
  - apply andb_prop in E as [_ E]. apply Z.leb_le in E. lia.
  - exact (IH top x n s Hr H Hn).
Qed.

(* Every read-only address of image B is below HIGHMEM_BEG (all image segments end below it), so a callee
   stack window, which lies above HIGHMEM_BEG, writes no read-only byte. *)
Lemma f7_ro_low : forall a, LMem.ro_addr rsegs a = true -> bv_unsigned a < HIGHMEM_BEG.
Proof.
  intros a H. unfold LMem.ro_addr in H.
  destruct (find_segment rsegs (bv_unsigned a) 1) as [s|] eqn:E; [|discriminate H].
  destruct (f7_find_below rsegs HIGHMEM_BEG (bv_unsigned a) 1 s ltac:(vm_compute; reflexivity) E ltac:(lia))
    as [L|L]; [exact L | discriminate L].
Qed.

(* A spill base A' read through s1 with a cell q64 at A' + off (off < 448) is the spill base A of FRA, when
   0 <= A and A + 448 <= 2^64 (FRA: sp <= A, and A + 448 <= S with the saved registers below S). *)
Lemma f7_base_eq : forall (A A' off v : Z) (m : word -> option byte),
  Z_to_bv 64 A' = Z_to_bv 64 A -> 0 <= A -> A + 448 <= 2 ^ 64 -> 0 <= off < 448 ->
  q64 m (A' + off) v -> A' = A.
Proof.
  intros A A' off v m E HA0 HA1 Hoff Hq.
  unfold q64, bytes_at in Hq. destruct Hq as (Hq0 & Hq1 & _).
  rewrite length_le8 in Hq1. change (Z.of_nat 8) with 8 in Hq1.
  apply (f_equal (bv_unsigned (n:=64))) in E. rewrite !MState.unsigned_lit_wrap in E.
  rewrite (Z.mod_small A) in E by lia.
  Z.div_mod_to_equations. lia.
Qed.

(* ---- The frame-loop bundles across the call (as lib/B/Prog/SegCF/F8.v's f8_*_keep). Every conjunct of FLI / FM
   is either a register the callee keeps or a spill cell [A + off, A + off + 8) with off <= 312, and FRA puts the
   whole save area [A, A + 448) at or above sp, so the callee's window [sp - 16, sp) is outside every one of them.
   FLI's memory facts (our[]'s six bytes addressable at fr + 2624, the frame body stk fr (fr + FRAME_BYTES) and the
   three frame records addressable, RAD) and FSj (the local `first` at fr + 2880) are inside the frame, which the
   window also misses (fra_frame). ---- *)

(* One spill cell [A + off] of the FRA spill base A survives a run whose writes all lie below A. *)
Lemma f7_spill_keep : forall regs regs' m m' W off v A,
  spill regs m off v -> rg regs 9 A -> getr regs' 9 = getr regs 9 ->
  0 <= off < 448 -> 0 <= A -> A + 448 <= 2 ^ 64 ->
  (forall x, A <= x -> Frame.outside W x) -> Frame.munch W m m' -> spill regs' m' off v.
Proof.
  intros regs regs' m m' W off v A HS HA E9 Hoff HA0 HA1 Hout MU.
  unfold spill in HS |- *. destruct HS as (A' & HA' & Hq).
  assert (EA : A' = A).
  { apply (f7_base_eq A A' off v m); [| exact HA0 | exact HA1 | exact Hoff | exact Hq].
    unfold rg in HA', HA. rewrite <- HA'. exact HA. }
  subst A'. exists A. split; [unfold rg in *; rewrite E9; exact HA'|].
  unfold q64 in *. eapply fl_bytes; [exact Hq | exact MU |].
  rewrite length_le8. intros x Hx. apply Hout. lia.
Qed.

(* FLI: s11, the loop-invariant spills, our[]'s and the records' addressability, the frame's stk and KNT (the
   KIND_NAME table's bytes and addressability; the table [0x9f580, 0x9f5f0) is image memory below HIGHMEM_BEG,
   which W misses, and W is app memory, so the table's shadow bytes are kept too). *)
Lemma f7_fli_keep : forall g fr regs regs' m m' W A,
  FLI g fr regs m -> rg regs 9 A -> getr regs' 9 = getr regs 9 -> getr regs' 27 = getr regs 27 ->
  0 <= A -> A + 448 <= 2 ^ 64 -> (forall x, A <= x -> Frame.outside W x) -> Frame.munch W m m' ->
  Frame.wmono rsegs m m' -> all_app W -> (forall x, fr <= x < fr + FRAME_BYTES -> Frame.outside W x) ->
  (forall x, 0 <= x < HIGHMEM_BEG -> Frame.outside W x) ->
  FLI g fr regs' m'.
Proof.
  intros g fr regs regs' m m' W A HF HA E9 E27 HA0 HA1 Hout MU WM AW Hfr Himg.
  unfold FLI, RAD in HF. unfold FLI, RAD.
  repeat match goal with H : _ /\ _ |- _ => destruct H end.
  repeat match goal with |- _ /\ _ => split end;
    first [ match goal with HK : KNT m |- KNT m' =>
              destruct HK as (HKB & HKA); split;
              [ eapply fl_bytes; [exact HKB | exact MU |]; rewrite kn_len; intros x Hx; apply Himg;
                change (Z.of_nat 112) with 112 in Hx; unfold KIND_NAME, HIGHMEM_BEG in *; lia
              | eapply addressable_kept; [exact HKA | exact (munch_meta W m m' MU AW)] ] end
          | eapply f7_spill_keep;
              [ eassumption | exact HA | exact E9 | lia | exact HA0 | exact HA1 | exact Hout | exact MU ]
          | unfold rg in *; rewrite E27; assumption
          | eapply addressable_kept; [eassumption | exact (munch_meta W m m' MU AW)]
          | eapply (Frame.stk_transport rsegs W m m'); [eassumption | exact MU | exact WM |];
            intros x Hx; left; apply Hfr; lia ].
Qed.

(* The body of the first-fragment state is at most 23 bytes (the bytes after position 27 of the 50-byte frame
   prefix t_g), so FSb's three byte groups lie inside `first`, [fr + 2880, fr + 2920) (Tac_ro.tr_body_length). *)
Lemma f7_body_length : forall inp j, (length (fs_body (fst_at inp j)) <= 23)%nat.
Proof.
  intros inp j. induction j as [|j IH].
  - cbn. lia.
  - rewrite fst_at_S. unfold turn.
    destruct (f_opens (t_len inp j) (t_g inp j)); cbn [fs_body]; [|exact IH].
    rewrite length_firstn, length_skipn. unfold t_g. rewrite fr50_length. lia.
Qed.

(* FSj (v1.9.0): the local `first` at fr + 2880 (have / n / body and its 40 bytes addressable), inside the frame;
   its last conjunct FI reads the ghost bytes only. *)
Lemma f7_fsj_keep : forall g fr j regs regs' m m' W,
  FSj g fr j regs m -> Frame.munch W m m' -> all_app W ->
  (forall x, fr <= x < fr + FRAME_BYTES -> Frame.outside W x) ->
  FSj g fr j regs' m'.
Proof.
  pose proof FRAME_BYTES_val as HFBv.
  intros g fr j regs regs' m m' W HF MU AW Hfr.
  unfold FSj, FSb, u32, b8 in *. destruct HF as (Hh & Hn & Hb & Hfst & HFI).
  pose proof (f7_body_length (g_in g) j) as Hbl.
  split; [apply (fl_bytes W m m' _ _ Hh MU); rewrite length_le4; intros x Hx; apply Hfr; lia|].
  split; [apply (fl_bytes W m m' _ _ Hn MU); cbn [length]; intros x Hx; apply Hfr; lia|].
  split; [apply (fl_bytes W m m' _ _ Hb MU); intros x Hx; apply Hfr; lia|].
  split; [exact (sl_addr_keep m m' W (fr + 2880) 40 Hfst MU AW) | exact HFI].
Qed.

(* FM: the fill-flag spill [A+184], s8 = k, s6 = 1, s9 = sum_ok and the block-pointer spill [A+312]. *)
Lemma f7_fm_keep : forall g j phi fr regs regs' m m' W A,
  FM g j phi fr regs m -> rg regs 9 A -> getr regs' 9 = getr regs 9 ->
  getr regs' 22 = getr regs 22 -> getr regs' 24 = getr regs 24 -> getr regs' 25 = getr regs 25 ->
  0 <= A -> A + 448 <= 2 ^ 64 -> (forall x, A <= x -> Frame.outside W x) -> Frame.munch W m m' ->
  FM g j phi fr regs' m'.
Proof.
  intros g j phi fr regs regs' m m' W A HF HA E9 E22 E24 E25 HA0 HA1 Hout MU.
  unfold FM in HF. destruct HF as (H184 & H24 & H22 & H25 & H312). unfold FM.
  split; [eapply f7_spill_keep;
            [exact H184 | exact HA | exact E9 | lia | exact HA0 | exact HA1 | exact Hout | exact MU]|].
  split; [unfold rg in *; rewrite E24; exact H24|].
  split; [unfold rg in *; rewrite E22; exact H22|].
  split; [unfold rg in *; rewrite E25; exact H25|].
  eapply f7_spill_keep;
    [exact H312 | exact HA | exact E9 | lia | exact HA0 | exact HA1 | exact Hout | exact MU].
Qed.

(* ---- The turn's two frame records keep fixed lengths (model): the fragment record t_FG j 72 bytes (fg_next keeps
   72 in every class) and the identity record t_ID j 38 bytes (every ingest keeps 38, RcIdentModel.ING_length).
   Copied from prover a Theorem Labs lane's lib/B/Prog/Seg/F20.v (a working branch 81dc3c31079, its rl_ lemmas, renamed f7_), which this
   file does not import, except that f7_FG_length closes with the extra lemma f7_g_len where F20 unfolds t_g and applies fr50_length. REC0's transport across the call needs both records inside the frame body. ---- *)
Lemma f7_g_len : forall inp j, length (t_g inp j) = 50%nat.
Proof. intros inp j. unfold t_g. apply fr50_length. Qed.
Lemma f7_fg_n : forall len g, fg_fr len g = true -> 1 <= fg_n g <= 22.
Proof.
  intros len g H. unfold fg_fr in H. rewrite !andb_true_iff in H.
  destruct H as (H & _). destruct H as (H & Hn2). destruct H as (_ & Hn1).
  apply Z.leb_le in Hn1. apply Z.leb_le in Hn2. lia.
Qed.
Lemma f7_keep_T : forall st g, fg_keep st g = true -> fg_T st g <= 64.
Proof.
  intros st g H. unfold fg_keep in H. rewrite !andb_true_iff in H.
  destruct H as (_ & H). apply Z.leb_le in H. lia.
Qed.
Lemma f7_next_length : forall f fr pa pp pn len st g, length st = 72%nat -> length g = 50%nat ->
  length (fg_next st g (fg_class f fr pa pp pn len st g)) = 72%nat.
Proof.
  intros f fr pa pp pn len st g HL HG. unfold fg_class.
  destruct ((f =? 0) || (fr =? 0) || (pa =? 0) || (pp =? 0) || (pn =? 0)); [cbn [fg_next]; exact HL|].
  destruct (fg_fr len g) eqn:FR; cbn [negb]; [|cbn [fg_next]; exact HL].
  destruct (bat g 19 =? 1).
  - cbn [fg_next]. pose proof (f7_fg_n len g FR) as Hn. unfold fg_first, fg_body.
    rewrite !length_app, length_skipn, (RcFragLib.rf_bsl_length g 6 6),
      (RcFragLib.rf_bsl_length g 27 (fg_n g)) by lia.
    cbn [length]. lia.
  - destruct (fg_keep st g) eqn:KEEP; cbn [negb]; [|cbn [fg_next]; apply RcFragLib.rf_clear_length; exact HL].
    destruct (fg_close st g); cbn [negb fg_next]; apply RcFragLib.rf_clear_length, RcFragLib.rf_fg_join_length;
      solve [exact HL | exact HG | apply (f7_fg_n len); exact FR | apply f7_keep_T; exact KEEP].
Qed.
Lemma f7_FG_length : forall inp j, length (t_FG inp j) = 72%nat.
Proof.
  intros inp j. induction j as [|j IH].
  - reflexivity.
  - unfold t_FG in *. rewrite fst_at_S. unfold turn.
    destruct (f_opens (t_len inp j) (t_g inp j)); cbn [fs_fg]; unfold fg_st, fcls;
      apply (f7_next_length 1 1 1 1 1); solve [exact IH | apply f7_g_len].
Qed.
Lemma f7_ID_length : forall inp j, length (t_ID inp j) = 38%nat.
Proof.
  intros inp j. induction j as [|j IH].
  - reflexivity.
  - unfold t_ID in *. rewrite fst_at_S. unfold turn. cbv zeta.
    assert (Hr : length (rp_id (fs_id (fst_at inp j)) (t_len inp j) (t_g inp j)) = 38%nat).
    { unfold rp_id. match goal with |- context [if ?c then _ else _] => destruct c end;
        [apply RcIdentModel.ING_length; exact IH | exact IH]. }
    assert (Hf : length (fg_id (rp_id (fs_id (fst_at inp j)) (t_len inp j) (t_g inp j)) (t_len inp j)
                           (fs_fg (fst_at inp j)) (t_g inp j)) = 38%nat).
    { unfold fg_id. match goal with |- context [if ?c then _ else _] => destruct c end;
        [apply RcIdentModel.ING_length; exact Hr | exact Hr]. }
    destruct (f_opens (t_len inp j) (t_g inp j)); cbn [fs_id]; exact Hf.
Qed.

Section S.
Context {fx : FPState} {LS : lib_shape} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AC.AsanAllocAPI AC.ASYMS AsanRTInv.RT.
Context {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.

(* The callee contract (lib/B/Prog/reac_ctrl_kind_name_c.v), a Section Hypothesis as the brief prescribes. *)
Hypothesis HKN : reac_ctrl_kind_name_contract.

(* The one lazy-model run of this file (AsanLift.evt_SR_canon_lazy), used once, for the F7 run 0x8215c -> 0x82174.
   That run reads the spill [A+280, A+288), the parse-record word [fr+176, fr+180), the KIND_NAME table
   [0x9f580, 0x9f5f0), the kind-name strings in the image (0x211e0-0x213e0), the runtime cells and the shadow bytes
   the callee reads; it writes only the callee's stack window [sp-16, sp). The KN contract speaks Lib.Exec.evt, so
   this is Tac_slot.sl_run without its ul_entry step. *)
Lemma sl_run_lib : forall regs pc mem md
  (K : bvmap 5 word -> word -> (word -> option byte) -> Prop) (P : config -> Prop),
  m_halted md = None ->
  LE.evt rsegs
    (fun ms => exists R pc' mem', ms = MS R fp_regs pc' fp_csr None mem' (seg_rom rsegs) /\ K R pc' mem')
    (MS (Regs6ss.mkR_of regs) fp_regs pc fp_csr None mem (seg_rom rsegs)) ->
  (forall R pc' mem' regs' md', K R pc' mem' -> (forall r, getr regs' r = getr R r) -> AsanLift.mat_le md md' ->
     SR rsegs (mkCfg (mkst regs' pc' mem' (seg_rom rsegs)) md') P) ->
  SR rsegs (mkCfg (mkst regs pc mem (seg_rom rsegs)) md) P.
Proof.
  intros regs pc mem md K P Hh HE HK.
  eapply (AsanLift.evt_SR_canon_lazy rsegs (mkst regs pc mem (seg_rom rsegs)) _ md P); [exact HE | exact Hh |].
  intros ms' md' (can & (R & pc' & mem' & -> & HKR) & Heq) Hmat.
  destruct Heq as (HR & HF & Hpc & Hsvc & Hres & Hfc & Hm & Hrom).
  destruct ms' as [regs' fr' pcv' svc' rv' fc' m' ro'].
  cbn in HR, HF, Hpc, Hsvc, Hres, Hfc, Hm, Hrom. subst.
  apply (HK R _ _ regs' md' HKR); [apply kb_getr_eqv; exact HR | exact Hmat].
Qed.

(* FRA moves across a run whose writes W lie in [HIGHMEM_BEG, sp) and miss the frame header [fr, fr + 24):
   Tac_slot.sl_win_run, whose FakeStack-record premise comes from Tac_slot's fsrec_munch_lo and whose input-block
   premise from fra_in_apart, both from the premise that W writes nothing below stklo outside the frame body; its
   window [S - SLOT_STACK, sp) is the lower part of the entry-anchored window [S - SLOT_STACK, S) on mem' (stk_split
   at sp, S - 4096 < sp <= A <= S). *)
Lemma sl_win_run : forall g fr hb regs regs' mem mem' md W,
  FRA B APIf ra g fr hb regs mem md ->
  Frame.munch W mem mem' -> Frame.wmono rsegs mem mem' -> ro_agree rsegs mem' ->
  all_app W -> rt_disjoint W ->
  AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) (hb ++ g_H g) mem' md ->
  AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem' md = AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md ->
  (forall x, x < HIGHMEM_BEG \/ AC.aspZ regs <= x -> Frame.outside W x) ->
  (forall x, fr <= x < fr + 24 -> Frame.outside W x) ->
  (forall x, x < AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md ->
     ~ (fr + 24 <= x < fr + FRAME_BYTES) -> Frame.outside W x) ->
  (forall a, fr <= a < fr + FRAME_BYTES -> app_mem a) ->
  stk rsegs mem' (g_S g - AF.SLOT_STACK) (g_S g) ->
  getr regs' 2 = getr regs 2 -> getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 ->
  getr regs' 8 = getr regs 8 -> getr regs' 9 = getr regs 9 -> getr regs' 19 = getr regs 19 ->
  getr regs' 26 = getr regs 26 ->
  FRA B APIf ra g fr hb regs' mem' md.
Proof.
  intros g fr hb regs regs' mem mem' md W HFRA MU WM HRO HAW HD HAH' HSTK HWout HWhdr HWfs Happ HWIN
    E2 E3 E4 E8 E9 E19 E26.
  pose proof (fra_in_apart B APIf ra g fr hb regs mem md HFRA) as Hinap.
  pose proof HFRA as HF0.
  destruct HF0 as (A & sp & s5 & _ & HAH & _ & _ & _ & _ & _ & _ & Haspz & _ & _ & _ & _ & _ & _ & _ & _ & _ &
    _ & HAS & Hspa & _ & _ & HS4 & _).
  assert (HSS : AF.SLOT_STACK = 1048576) by reflexivity.
  destruct (stk_split rsegs mem' (g_S g - AF.SLOT_STACK) (AC.aspZ regs) (g_S g) HWIN
              ltac:(rewrite Haspz; lia)) as (HWIN' & _).
  apply (Tac_slot.sl_win_run B APIf ra empty FF g fr hb regs regs' mem mem' md W HFRA MU WM HRO HAW HD HAH' HSTK
           HWout HWhdr); [| | exact Happ | exact HWIN' | exact E2 | exact E3 | exact E4 | exact E8 | exact E9 |
           exact E19 | exact E26].
  - intros Hrec. eapply fsrec_munch_lo with (W := W); [exact Hrec | exact HAH | exact MU | exact HWfs].
  - (* the input block: below stklo and apart from the frame (fra_in_apart), so outside W by HWfs *)
    intros x Hx. destruct (Hinap x Hx) as (_ & Hxlo & Hxf & _). apply HWfs; [exact Hxlo | lia].
Qed.

(* The run 0x8215c -> 0x82174 over explicit registers: the two compares not taken, the record pointer reload from the
   spill [A+280] and the word load through it, and the KN call composed with its contract (window [sp-16, sp)). *)
Lemma f7_evt :
  forall (ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8v s9 s10 s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (A kp v lo : Z),
    s1 = Z_to_bv 64 A -> bytes_at rsegs m (A + 280) (le8 (Z_to_bv 64 kp)) ->
    a0 = Z_to_bv 64 v -> s8v = Z_to_bv 64 v -> 0 <= v < 2 ^ 31 ->
    bytes_at rsegs m kp (le4 (Z_to_bv 64 v)) ->
    bytes_at rsegs m KIND_NAME kind_name_bytes -> kind_name_strings m ->
    stk rsegs m lo (bv_unsigned sp) -> lo + REAC_CTRL_KIND_NAME_FRAME <= bv_unsigned sp ->
    KIND_NAME + 112 <= bv_unsigned sp - REAC_CTRL_KIND_NAME_FRAME ->
    asan_cells m -> shadow_rw m -> addressable m KIND_NAME 112 ->
    (forall x, GOT_CELL_K <= x < GOT_CELL_K + 8 \/ CELL_K <= x < CELL_K + 8 \/ in_shadow x ->
       outside [(bv_unsigned sp - REAC_CTRL_KIND_NAME_FRAME, bv_unsigned sp)] x) ->
    LE.evt rsegs
      (fun ms' => exists (a1' a2' a3' : word) (m' : word -> option byte),
         ms' = MS (mkR (Z_to_bv 64 0x82174) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (kind_name_addr v))
                       a1' a2' a3' a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8v s9 s10 s11 t3 t4 t5 t6)
                  Fr (Z_to_bv 64 0x82174) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned sp - REAC_CTRL_KIND_NAME_FRAME, bv_unsigned sp)] m m' /\
         wmono rsegs m m' /\ (mem_inv rsegs m -> mem_inv rsegs m') /\ stk rsegs m' lo (bv_unsigned sp))
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8v s9 s10 s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x8215c) fc None m (seg_rom rsegs)).
Proof.
  intros ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8v s9 s10 s11 t3 t4 t5 t6
    Fr fc m A kp v lo -> H280 -> -> Hv Hkp HKB HKS HST Hlo Hkn HAC HSW HAD Hout.
  assert (HL280 : ov_read_bytes rsegs m (wa (A + 280)) 8 = Some (le8 (Z_to_bv 64 kp))).
  { pose proof (bytes_at_ov_read rsegs m (A + 280) (le8 (Z_to_bv 64 kp)) 0 8 H280 ltac:(rewrite length_le8; lia))
      as HH.
    cbn [Z.of_nat] in HH. rewrite Z.add_0_r, skipn_O in HH.
    rewrite firstn_all2 in HH by (rewrite length_le8; lia). exact HH. }
  assert (HLkp : ov_read_bytes rsegs m (wa kp) 4 = Some (le4 (Z_to_bv 64 v))).
  { pose proof (bytes_at_ov_read rsegs m kp (le4 (Z_to_bv 64 v)) 0 4 Hkp ltac:(rewrite length_le4; lia)) as HH.
    cbn [Z.of_nat] in HH. rewrite Z.add_0_r, skipn_O in HH.
    rewrite firstn_all2 in HH by (rewrite length_le4; lia). exact HH. }
  (* 0x8215c bne a0,s8 : a0 = s8, not taken *)
  step. rewrite bv_eqb_refl. cbn [negb]. cbv iota.
  (* 0x82160 ld a0,280(s1) ; 0x82164 lw a0,0(a0) *)
  step. step. rewrite (f7_sx32_small v Hv).
  (* 0x82168 bne s8,a0 : equal, not taken *)
  step. rewrite bv_eqb_refl. cbn [negb]. cbv iota.
  (* 0x8216c mv a0,s8 ; 0x82170 jal reac_ctrl_kind_name *)
  step. step.
  pose proof HKN as HK. unfold reac_ctrl_kind_name_contract, REAC_CTRL_KIND_NAME in HK.
  eapply evt_cut.
  { eapply HK with (lo := lo).
    - exact HKB.
    - exact HKS.
    - exact HST.
    - exact Hlo.
    - exact Hkn.
    - exact HAC.
    - exact HSW.
    - exact HAD.
    - exact Hout. }
  intros ms' (a1' & a2' & a3' & m' & E & MU & WM & MI & ST' & _).
  subst ms'.
  replace (ret_pc (Z_to_bv 64 0x82174)) with (Z_to_bv 64 0x82174)
    by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  rewrite (unsigned_lit v) by lia.
  apply evt_done.
  exists a1', a2', a3', m'.
  split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MI | exact ST'].
Qed.

(* seg_F7 on SlotInv's cuts (S_F7 of the image-B segment forms): from the F7 cut Inv_B8215c_at through the first
   reac_ctrl_kind_name call to the F8 cut Inv_B82174_at. *)
Lemma seg_F7 : forall j : nat,
  Hat B APIf ra (Inv_B82174_at B APIf ra) j -> Hat B APIf ra (Inv_B8215c_at B APIf ra) j.
Proof.
  intros j Hexit g c HInv.
  pose proof (proj1 FF) as SEGS.
  destruct HInv as (phi & regs & mem & md & fr & Ec & HFRA & HENT & Hgn & Hj & HHB & HLK & Hs2 & Hs4 &
    HFM & HFS & HKNB & HKNA & Hs9 & Hrec & HFT & HREC & HFPS & H272 &
    A & v & HFLV & Ha0 & Hs8 & Hv & Hs6 & Hu32).
  subst c. rewrite SEGS.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  (* FRA gives what the cut text leaves out: the frame in app memory above GT (fra_app) and apart from the KN
     window (fra_frame at K = REAC_CTRL_KIND_NAME_FRAME) *)
  destruct (fra_app B APIf ra g fr _ regs mem md HFRA) as (HGTfr & Hfrapp).
  destruct (fra_frame B APIf ra g fr _ regs mem md HFRA) as (Hplace & _ & _ & _).
  assert (Hdisjfr : fr + FRAME_BYTES <= AC.aspZ regs - REAC_CTRL_KIND_NAME_FRAME \/ AC.aspZ regs <= fr)
    by (apply Hplace; unfold FN_STACK, REAC_CTRL_KIND_NAME_FRAME, AF.SLOT_STACK; lia).
  destruct (fra_win B APIf ra g fr _ regs mem md HFRA) as (Hlow & HST0).
  pose proof HFRA as HFRA2.
  destruct HFRA2 as (A2 & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA416 & HS4 & HAPP &
    Hspill & Hsel & Hfr56 & Hloc & Hhdr1 & Hhdr2 &
    Hshf & Hwin & Hsaved & Herrno & HAG & HWA & HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive).
  (* sp <= A <= S < APPMEM_END *)
  assert (HaspB : AC.aspZ regs <= APPMEM_END) by lia.
  pose proof (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) as LAWS.
  pose proof (AC.a_laws_stack_high _ _ _ _ _ LAWS (hb1 phi (AC.a_size (flen g j)) ++ g_H g) mem md HAH) as Hstkhi.
  (* Phi's live block (Phi, a_size len) ends at or below stklo <= sp - FN_STACK (fra_win), below the KN window *)
  destruct (lw_blocks (APIf rc) (hb1 phi (AC.a_size (flen g j)) ++ g_H g) mem md phi
              (AC.a_size (flen g j)) HAH ltac:(apply in_or_app; left; unfold hb1; cbn [In]; left; reflexivity))
    as [_ _ Hphiend _ _].
  assert (Hsphi : HIGHMEM_BEG + AF.SLOT_STACK - 4096 < sp) by lia.
  assert (Hspb : 0 <= sp < 2 ^ 64)
    by (rewrite Haspz in HaspB; unfold HIGHMEM_BEG, APPMEM_END, AF.SLOT_STACK in *; lia).
  (* the spill base A2 = s1 of FRA lies in [sp, 2^64 - 448] (the saved registers [S-104, S) end below 2^64) *)
  assert (HA2b : A2 + 448 <= 2 ^ 64).
  { pose proof Hsaved as Hb. unfold bytes_at in Hb. destruct Hb as (_ & Hb1 & _).
    unfold saved_bytes in Hb1. rewrite !length_app, !length_le8 in Hb1. cbn in Hb1. lia. }
  (* the FLVsp spill base is A2 *)
  assert (EA : A = A2).
  { destruct HFLV as (H9A & Hq120 & _).
    apply (f7_base_eq A2 A 120 (fragb fr + 15) mem); [| lia | exact HA2b | lia | exact Hq120].
    unfold rg in H9A, Hr9. rewrite <- H9A. exact Hr9. }
  subst A.
  (* the KN premises over the entry memory *)
  assert (Hlo0 : AC.aspZ regs - FN_STACK + REAC_CTRL_KIND_NAME_FRAME <= AC.aspZ regs)
    by (unfold FN_STACK, AF.SLOT_STACK, REAC_CTRL_KIND_NAME_FRAME; lia).
  assert (Hkn0 : KIND_NAME + 112 <= AC.aspZ regs - REAC_CTRL_KIND_NAME_FRAME)
    by (rewrite Haspz; unfold KIND_NAME, REAC_CTRL_KIND_NAME_FRAME, HIGHMEM_BEG, AF.SLOT_STACK in *; lia).
  assert (Hout0 : forall x, GOT_CELL_K <= x < GOT_CELL_K + 8 \/ CELL_K <= x < CELL_K + 8 \/ in_shadow x ->
            Frame.outside [(AC.aspZ regs - REAC_CTRL_KIND_NAME_FRAME, AC.aspZ regs)] x).
  { intros x Hx. cbn [Frame.outside]. split; [|exact I]. intros [HH1 HH2]. rewrite Haspz in *.
    unfold GOT_CELL_K, CELL_K, in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG,
      REAC_CTRL_KIND_NAME_FRAME, AF.SLOT_STACK in *. lia. }
  set (W := [(AC.aspZ regs - REAC_CTRL_KIND_NAME_FRAME, AC.aspZ regs)]).
  apply (sl_run_lib regs (Z_to_bv 64 0x8215c) mem md
    (fun R0 pc' mem' =>
       pc' = Z_to_bv 64 0x82174 /\
       getr R0 2 = getr regs 2 /\ getr R0 3 = getr regs 3 /\ getr R0 4 = getr regs 4 /\
       getr R0 8 = getr regs 8 /\ getr R0 9 = getr regs 9 /\ getr R0 18 = getr regs 18 /\
       getr R0 19 = getr regs 19 /\ getr R0 20 = getr regs 20 /\ getr R0 21 = getr regs 21 /\
       getr R0 22 = getr regs 22 /\ getr R0 24 = getr regs 24 /\ getr R0 25 = getr regs 25 /\
       getr R0 26 = getr regs 26 /\ getr R0 27 = getr regs 27 /\
       getr R0 10 = Z_to_bv 64 (kind_name_addr v) /\
       Frame.munch W mem mem' /\ Frame.wmono rsegs mem mem' /\
       stk rsegs mem' (AC.aspZ regs - FN_STACK) (AC.aspZ regs))
    (Post B APIf ra g)).
  - exact Hhalt.
  - eapply LE.evt_mono.
    { unfold Regs6ss.mkR_of.
      eapply f7_evt with (A := A2) (kp := fr + 176) (v := v) (lo := AC.aspZ regs - FN_STACK).
      - unfold rg in Hr9; exact Hr9.
      - unfold q64 in Hs6; exact Hs6.
      - unfold rg in Ha0; exact Ha0.
      - unfold rg in Hs8; exact Hs8.
      - exact Hv.
      - unfold u32 in Hu32; exact Hu32.
      - exact HKNB.
      - exact (kn_strings_ro mem Hro).
      - exact HST0.
      - exact Hlo0.
      - exact Hkn0.
      - exact (AsanRTInv.RT_cells sp mem md HRT).
      - exact (AsanRTInv.RT_shadow_rw sp mem md HRT).
      - exact HKNA.
      - exact Hout0. }
    { intros ms' (a1' & a2' & a3' & m' & E & MU & WM & _ & ST').
      eexists _, (Z_to_bv 64 0x82174), m'. split; [exact E|].
      split; [reflexivity|].
      do 15 (split; [reflexivity|]).
      split; [exact MU|]. split; [exact WM|]. exact ST'. }
  - intros R0 pc' mem' regs' md' (Hpc & Er2 & Er3 & Er4 & Er8 & Er9 & Er18 & Er19 & Er20 & Er21 & Er22 &
      Er24 & Er25 & Er26 & Er27 & Er10 & MU & WM & ST') Hreg Hmat.
    subst pc'.
    assert (Fr2 : getr regs' 2 = getr regs 2) by (rewrite Hreg; exact Er2).
    assert (Fr3 : getr regs' 3 = getr regs 3) by (rewrite Hreg; exact Er3).
    assert (Fr4 : getr regs' 4 = getr regs 4) by (rewrite Hreg; exact Er4).
    assert (Fr8 : getr regs' 8 = getr regs 8) by (rewrite Hreg; exact Er8).
    assert (Fr9 : getr regs' 9 = getr regs 9) by (rewrite Hreg; exact Er9).
    assert (Fr18 : getr regs' 18 = getr regs 18) by (rewrite Hreg; exact Er18).
    assert (Fr19 : getr regs' 19 = getr regs 19) by (rewrite Hreg; exact Er19).
    assert (Fr20 : getr regs' 20 = getr regs 20) by (rewrite Hreg; exact Er20).
    assert (Fr21 : getr regs' 21 = getr regs 21) by (rewrite Hreg; exact Er21).
    assert (Fr22 : getr regs' 22 = getr regs 22) by (rewrite Hreg; exact Er22).
    assert (Fr24 : getr regs' 24 = getr regs 24) by (rewrite Hreg; exact Er24).
    assert (Fr25 : getr regs' 25 = getr regs 25) by (rewrite Hreg; exact Er25).
    assert (Fr26 : getr regs' 26 = getr regs 26) by (rewrite Hreg; exact Er26).
    assert (Fr27 : getr regs' 27 = getr regs 27) by (rewrite Hreg; exact Er27).
    assert (Fr10 : getr regs' 10 = Z_to_bv 64 (kind_name_addr v)) by (rewrite Hreg; exact Er10).
    assert (HaspEq : AC.aspZ regs' = AC.aspZ regs) by (unfold AC.aspZ; rewrite Fr2; reflexivity).
    (* the window W = [sp-16, sp): app, runtime-disjoint, inside the stack store range, below A2 >= sp *)
    assert (HWlo : forall x, x < HIGHMEM_BEG \/ AC.aspZ regs <= x -> Frame.outside W x).
    { intros x Hx. subst W. cbn [Frame.outside]. split; [|exact I]. intros [HH1 HH2].
      rewrite Haspz in *. unfold REAC_CTRL_KIND_NAME_FRAME, HIGHMEM_BEG, AF.SLOT_STACK in *. lia. }
    assert (HWbelow : forall x, x < AC.aspZ regs - REAC_CTRL_KIND_NAME_FRAME -> Frame.outside W x).
    { intros x Hx. subst W. cbn [Frame.outside]. split; [|exact I]. intros [HH1 HH2]. lia. }
    assert (HWfr : forall x, fr <= x < fr + FRAME_BYTES -> Frame.outside W x).
    { intros x Hx. subst W. cbn [Frame.outside]. split; [|exact I]. intros [HH1 HH2].
      destruct Hdisjfr as [Hd|Hd]; lia. }
    (* Phi's block [Phi, Phi + a_size len) lies below the window *)
    assert (HWphi : forall x, phi <= x < phi + AC.a_size (flen g j) -> Frame.outside W x).
    { intros x Hx. apply HWbelow. unfold FN_STACK, AF.SLOT_STACK, REAC_CTRL_KIND_NAME_FRAME in *. lia. }
    (* ro_agree after the call: the KN window lies above HIGHMEM_BEG and every read-only byte below it *)
    assert (HroM : ro_agree rsegs mem').
    { intros a Ha. unfold mrd. rewrite (MU a); [exact (Hro a Ha) |].
      apply HWlo. left. exact (f7_ro_low a Ha). }
    assert (Hallapp : all_app W).
    { subst W. cbn [all_app]. split; [|exact I]. intros a Ha. unfold app_mem. right.
      rewrite Haspz in *. unfold REAC_CTRL_KIND_NAME_FRAME, HIGHMEM_BEG, APPMEM_END, AF.SLOT_STACK in *. lia. }
    assert (Hrtdj : rt_disjoint W).
    { subst W. unfold rt_disjoint, RT_LO, RT_HI, RT_GOT_AF, RT_AF, RT_GOT_VERB, RT_VERB, RT_GOT_CF, RT_CF,
        RT_TSDI, RT_TSDK, RT_PGSZ, RT_TP, RT_TSDMAIN, RT_REAL_LO, RT_REAL_HI, RT_IMAP, RT_IMEM, RT_MUG, RT_AGLOB,
        RT_AGLOB_LEN, AC.GT, REAC_CTRL_KIND_NAME_FRAME, HIGHMEM_BEG, AF.SLOT_STACK in *.
      rewrite Haspz in *. cbn [disjoint_from]. repeat split; first [left; lia | exact I]. }
    assert (HstoreC : forall a, 0 <= a < 2 ^ 64 ->
      ~ AC.a_store_ok (hb1 phi (AC.a_size (flen g j)) ++ g_H g)
          (AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md) a ->
      mem' (Z_to_bv 64 a) = mem (Z_to_bv 64 a)).
    { intros a Ha Hns. apply MU. rewrite MState.unsigned_lit by lia. subst W.
      cbn [Frame.outside]. split; [|exact I]. intros [HH1 HH2]. apply Hns.
      unfold AC.a_store_ok. right; left. rewrite Haspz in *.
      unfold REAC_CTRL_KIND_NAME_FRAME, AF.SLOT_STACK in *. split; lia. }
    assert (HwmL : forall a, 0 <= a < 2 ^ 64 -> writable_at rsegs mem a -> writable_at rsegs mem' a)
      by (intros a Ha Hw; exact (WM (Z_to_bv 64 a) Hw)).
    destruct (lw_store (APIf rc) (hb1 phi (AC.a_size (flen g j)) ++ g_H g) mem mem' md HAH HstoreC HwmL)
      as [HAH' HownEq HSTKeq HSTKhieq].
    (* the entry-anchored window [S - SLOT_STACK, S) on mem': outside W from the entry window, inside W from the
       callee's stk post on [sp - FN_STACK, sp) *)
    assert (HSTKS : stk rsegs mem' (g_S g - AF.SLOT_STACK) (g_S g)).
    { assert (HK16 : REAC_CTRL_KIND_NAME_FRAME = 16) by reflexivity.
      destruct (stk_split rsegs mem (g_S g - AF.SLOT_STACK) (AC.aspZ regs - REAC_CTRL_KIND_NAME_FRAME) (g_S g)
                  Hwin ltac:(rewrite Haspz; unfold AF.SLOT_STACK in *; lia)) as (Hw1 & Hw2).
      destruct (stk_split rsegs mem (AC.aspZ regs - REAC_CTRL_KIND_NAME_FRAME) (AC.aspZ regs) (g_S g) Hw2
                  ltac:(rewrite Haspz; lia)) as (_ & Hw3).
      destruct (stk_split rsegs mem' (AC.aspZ regs - FN_STACK) (AC.aspZ regs - REAC_CTRL_KIND_NAME_FRAME)
                  (AC.aspZ regs) ST' ltac:(unfold FN_STACK, AF.SLOT_STACK; lia)) as (_ & HwW).
      assert (Hw1' : stk rsegs mem' (g_S g - AF.SLOT_STACK) (AC.aspZ regs - REAC_CTRL_KIND_NAME_FRAME)).
      { eapply (Frame.stk_transport rsegs _ mem mem'); [exact Hw1 | exact MU | exact WM |].
        intros x Hx. left. subst W. cbn [Frame.outside]. split; [|exact I]. intros [HH1 HH2]. lia. }
      assert (Hw3' : stk rsegs mem' (AC.aspZ regs) (g_S g)).
      { eapply (Frame.stk_transport rsegs _ mem mem'); [exact Hw3 | exact MU | exact WM |].
        intros x Hx. left. apply HWlo. right. lia. }
      apply (stk_merge rsegs mem' _ (AC.aspZ regs) _); [| exact Hw3' | rewrite Haspz; unfold AF.SLOT_STACK in *; lia].
      apply (stk_merge rsegs mem' _ (AC.aspZ regs - REAC_CTRL_KIND_NAME_FRAME) _); [exact Hw1' | exact HwW |].
      rewrite Haspz; unfold AF.SLOT_STACK in *; lia. }
    assert (HFRA' : FRA B APIf ra g fr (hb1 phi (AC.a_size (flen g j))) regs' mem' md).
    { apply (sl_win_run g fr (hb1 phi (AC.a_size (flen g j))) regs regs' mem mem' md W HFRA MU WM HroM Hallapp
               Hrtdj HAH' HSTKeq HWlo).
      - intros x Hx. apply HWfr. lia.
      - (* W = [sp - 16, sp) lies above stklo: stklo <= S - SLOT_STACK and S - 4096 < sp (FRA) *)
        intros x Hx _. subst W. cbn [Frame.outside]. split; [|exact I]. intros [HH1 HH2].
        rewrite Haspz in *. unfold REAC_CTRL_KIND_NAME_FRAME, AF.SLOT_STACK in *. lia.
      - exact Hfrapp.
      - exact HSTKS.
      - exact Fr2.
      - exact Fr3.
      - exact Fr4.
      - exact Fr8.
      - exact Fr9.
      - exact Fr19.
      - exact Fr26. }
    assert (HFRA'' : FRA B APIf ra g fr (hb1 phi (AC.a_size (flen g j))) regs' mem' md').
    { apply (sl_fra_move B APIf ra g fr (hb1 phi (AC.a_size (flen g j))) regs' regs' mem' md md' HFRA');
        try reflexivity; exact Hmat. }
    assert (HWhiA : forall x, sp <= x -> Frame.outside W x) by (intros x Hx; apply HWlo; right; lia).
    assert (HA20 : 0 <= A2) by lia.
    assert (HWA2 : forall x, A2 <= x -> Frame.outside W x) by (intros x Hx; apply HWhiA; lia).
    assert (Hspk : forall off w, 0 <= off < 448 -> spill regs mem off w -> spill regs' mem' off w).
    { intros off w Hoff HS.
      exact (f7_spill_keep regs regs' mem mem' W off w A2 HS Hr9 Fr9 Hoff HA20 HA2b HWA2 MU). }
    (* the three frame-loop bundles across the call: every conjunct is a kept register or a spill above A2, except
       FLI's memory facts (our[] and the records addressable, the frame's stk), which the window W misses (HWfr),
       and FLI's KNT, image memory below HIGHMEM_BEG, which W also misses (HWimg) *)
    destruct HLK as (HjLK & Hsp240 & HOURb & HFLI).
    assert (HWimg : forall x, 0 <= x < HIGHMEM_BEG -> Frame.outside W x)
      by (intros x Hx; apply HWlo; left; lia).
    assert (HFLI' : FLI g fr regs' mem')
      by (apply (f7_fli_keep g fr regs regs' mem mem' W A2); assumption).
    assert (HFM' : FM g j phi fr regs' mem')
      by (apply (f7_fm_keep g j phi fr regs regs' mem mem' W A2); assumption).
    assert (HFS' : FSj g fr j regs' mem')
      by exact (f7_fsj_keep g fr j regs regs' mem mem' W HFS MU Hallapp HWfr).
    (* ENT: the KN window W = [sp - 16, sp) lies inside the slot window [S - SLOT_STACK, S) (FRA's
       g_S g - 4096 < sp and sp <= A <= g_S g), so the run writes no byte of an entry block, of the image, of the
       stack at or above S, or of their shadow; the stack bounds and the runtime's ownership of an image byte
       come from the same a_laws_store. ent_mat then carries ENT across the run's model step. *)
    assert (HWcases : forall x, 0 <= x < 2 ^ 64 -> Frame.outside W x \/
      (g_S g - AF.SLOT_STACK <= x < g_S g) \/ (fr <= x < fr + FRAME_BYTES) \/ (Sfr fr <= x < Sfr fr + FRAME_SHADOW)).
    { intros x Hx.
      assert (HSSv : AF.SLOT_STACK = 1048576) by reflexivity.
      assert (HKNv : REAC_CTRL_KIND_NAME_FRAME = 16) by reflexivity.
      destruct (Z_lt_le_dec x (AC.aspZ regs - REAC_CTRL_KIND_NAME_FRAME)) as [Hl|Hl].
      { left. subst W. cbn [Frame.outside]. split; [|exact I]. intros [HH1 HH2]. lia. }
      destruct (Z_lt_le_dec x (AC.aspZ regs)) as [Hh|Hh].
      { right; left. rewrite Haspz in Hl, Hh. lia. }
      left. subst W. cbn [Frame.outside]. split; [|exact I]. intros [HH1 HH2]. lia. }
    assert (HENT' : ENT APIf g (hb1 phi (AC.a_size (flen g j))) mem' md).
    { apply (ent_store B APIf ra g fr (hb1 phi (AC.a_size (flen g j))) regs mem mem' md W
               HENT HFRA MU HWcases HSTKeq HSTKhieq).
      intros a _ Hown0. exact (proj2 (HownEq a) Hown0). }
    assert (HENT'' : ENT APIf g (hb1 phi (AC.a_size (flen g j))) mem' md')
      by (eapply ent_mat; [exact HENT' | exact Hmat]).
    assert (HIexit : Inv_B82174_at B APIf ra g j
                       (mkCfg (mkst regs' (Z_to_bv 64 0x82174) mem' (seg_rom rsegs)) md')).
    { exists phi, regs', mem', md', fr. rewrite SEGS. split; [reflexivity|].
      split; [exact HFRA''|].
      split; [exact HENT''|].
      split; [exact Hgn|].
      split; [exact Hj|].
      split.
      { destruct HHB as (Hphinz & Hphiad). split; [exact Hphinz|].
        eapply sl_addr_keep; [exact Hphiad | exact MU | exact Hallapp]. }
      split.
      { split; [exact HjLK|]. split.
        - exact (Hspk 240 _ ltac:(lia) Hsp240).
        - split.
          + unfold OURb in *. apply (fl_bytes W mem mem' (fr + 2624) (OUR (g_in g)) HOURb MU).
            rewrite OUR_length. intros x Hx. apply HWfr. cbn [Z.of_nat] in Hx. lia.
          + exact HFLI'. }
      split; [unfold rg in *; rewrite Fr18; exact Hs2|].
      split; [unfold rg in *; rewrite Fr20; exact Hs4|].
      split; [exact HFM'|].
      split; [exact HFS'|].
      split.
      { apply (fl_bytes W mem mem' KIND_NAME kind_name_bytes HKNB MU).
        rewrite kn_len. intros x Hx. apply HWlo. left. change (Z.of_nat 112) with 112 in Hx.
        unfold KIND_NAME, HIGHMEM_BEG in *. lia. }
      split; [eapply sl_addr_keep; [exact HKNA | exact MU | exact Hallapp]|].
      (* [A+248] = 1 - sum_ok: a spill above A2 *)
      split; [exact (Hspk 248 _ ltac:(lia) Hs9)|].
      (* the frame's first 50 bytes at Phi (len >= 50): inside Phi's block, below the window *)
      split.
      { intros H50. apply (fl_bytes W mem mem' phi (t_g (g_in g) j) (Hrec H50) MU).
        rewrite f7_g_len. intros x Hx. change (Z.of_nat 50) with 50 in Hx. apply HWphi.
        unfold AC.a_size, flen in *. lia. }
      (* FTURN: the two cursor spills above A2, the frame's len bytes at Phi inside its block *)
      split.
      { destruct HFT as (H224 & H232 & HPB & HPL).
        split; [exact (Hspk 224 _ ltac:(lia) H224)|].
        split; [exact (Hspk 232 _ ltac:(lia) H232)|].
        split; [|exact HPL].
        apply (fl_bytes W mem mem' phi (t_phi (g_in g) j) HPB MU).
        intros x Hx. apply HWphi. unfold AC.a_size, flen in *. lia. }
      (* REC0: the identity record [fr + 2688, fr + 2726) and the fragment record [fr + 2768, fr + 2840), in the
         frame *)
      split.
      { unfold REC0, FREC, IDb, FGb, IDBe, FGBe in HREC |- *.
        destruct HREC as ((HID & Hidok) & (HFG & Hfgok)).
        split; split; try assumption.
        - apply (fl_bytes W mem mem' (fr + 2688) (t_ID (g_in g) j) HID MU).
          rewrite f7_ID_length. intros x Hx. change (Z.of_nat 38) with 38 in Hx. apply HWfr. lia.
        - apply (fl_bytes W mem mem' (fr + 2768) (t_FG (g_in g) j) HFG MU).
          rewrite f7_FG_length. intros x Hx. change (Z.of_nat 72) with 72 in Hx. apply HWfr. lia. }
      (* FPS: the parse struct t_B j (36 bytes, ctrlparse_length) at fr + 176 and its addressability, in the frame *)
      split.
      { destruct HFPS as (HpB & HpA). split.
        - unfold pBb in *. apply (fl_bytes W mem mem' (fr + 176) (t_B (g_in g) j) HpB MU).
          unfold t_B. rewrite RcParse.ctrlparse_length. intros x Hx. change (Z.of_nat 36) with 36 in Hx.
          apply HWfr. lia.
        - eapply sl_addr_keep; [exact HpA | exact MU | exact Hallapp]. }
      (* F272: [A+272] above A2 *)
      split; [unfold F272 in *; exact (Hspk 272 _ ltac:(lia) H272)|].
      exists A2, v.
      split.
      { destruct HFLV as (H9A & Hq120 & Hq128 & Hq256 & Hq304 & Hq296). unfold q64 in *.
        split; [unfold rg in *; rewrite Fr9; exact H9A|].
        split; [apply (fl_bytes W mem mem' _ _ Hq120 MU); rewrite length_le8; intros x Hx; apply HWhiA; lia|].
        split; [apply (fl_bytes W mem mem' _ _ Hq128 MU); rewrite length_le8; intros x Hx; apply HWhiA; lia|].
        split; [apply (fl_bytes W mem mem' _ _ Hq256 MU); rewrite length_le8; intros x Hx; apply HWhiA; lia|].
        split; [apply (fl_bytes W mem mem' _ _ Hq304 MU); rewrite length_le8; intros x Hx; apply HWhiA; lia|].
        apply (fl_bytes W mem mem' _ _ Hq296 MU); rewrite length_le8; intros x Hx; apply HWhiA; lia. }
      split; [unfold rg; exact Fr10|].
      split; [unfold rg in *; rewrite Fr24; exact Hs8|].
      split; [exact Hv|].
      split; [unfold q64 in *; apply (fl_bytes W mem mem' _ _ Hs6 MU); rewrite length_le8; intros x Hx;
              apply HWhiA; lia|].
      unfold u32 in *. apply (fl_bytes W mem mem' _ _ Hu32 MU).
      rewrite length_le4. intros x Hx. apply HWfr. lia. }
    pose proof (Hexit g _ HIexit) as HSR. rewrite SEGS in HSR. exact HSR.
Qed.

End S.
