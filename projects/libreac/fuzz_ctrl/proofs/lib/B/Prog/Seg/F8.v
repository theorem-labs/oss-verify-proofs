(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_bigint/lib/L5TCopyS.v, with its module paths and module names changed; 3817 of its 3853 lines of code are new or changed and 212 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/ctrl_lay_block.v, with its module paths and module names changed; 371 of its 396 lines of code are new or changed and 3828 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/Seg/P2.v, with its module paths and module names changed; 485 of its 520 lines of code are new or changed and 361 lines of the source are left out. *)
(* Segment F8 of LLVMFuzzerTestOneInput, image B (asan-ubsan, libreac v1.9.0), range 0x82174-0x8217c (v1.8
   0x820fc-0x82104; segment table row S_F8: IDENTICAL), through the call to its return point 0x82180 (F9's entry).
   The image-B port of lib/A/Prog/Seg/F8.v.
     0x82174 beqz a0,0x82fa4     a0 = kind_name_addr v, the result of the first reac_ctrl_kind_name call at
                                 0x82170, a nonzero table address: not taken
     0x82178 mv   a0,s8          a0 = s8 = v
     0x8217c jal  reac_ctrl_kind_name
   The range has no instrumented check (no load of a shadow byte). The branch at 0x82174 goes to the fail block and
   is not taken. The segment runs through the call (the lib/B contract reac_ctrl_kind_name_contract, a Section
   Hypothesis) and ends at its return point 0x82180 with a0 = kind_name_addr v and the name bytes at that address
   (the contract's post). The callee writes only its stack window W = [sp-16, sp); FRA crosses that write by
   Tac_slot.sl_callee_keep (W is the callee window of K = REAC_CTRL_KIND_NAME_FRAME, the frame is apart from it
   by fra_frame) and ENT by Tac_slot.ent_store plus ent_mat.

   Cuts: the entry is the official Inv_B82174_at and the exit the official Inv_B82180_at of lib/B/Prog/SlotInv.v,
   used as they stand (S_F8). The run changes no register but a0 and writes only the callee window, so every
   conjunct is carried: the registers kept, the spills above the window (sp <= A; v1.9: [A+248] = 1 - sum_ok and
   [A+280] = fr + 176), the Phi bytes below it (a live block ends at or below stklo <= sp - FN_STACK), and the
   frame bytes (the two records, the parse struct at fr + 176 and, v1.9, the local `first` of FSj at fr + 2880),
   which the window misses (fra_frame's placement). *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Reusable Require Import YK11 YM05 YK0o YK0s YK15 YP09 YO0f YO0d YO09
  YL00 YL0g YL0i YI14 YI16 YL01 YM06.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import Img0 AsanRT AsanRTInv AsanRTFacts PContract MemNorm AsanLift KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Contract FrameAPI.
(* The fragment-record model (fg_next / fg_class and the rf_* length facts), imported as lib/B/Prog/Seg/F12.v does,
   for the record length f8_t_FG_length; placed before this file's main imports so those keep their names. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcModel RcRec RcFrag RcFragLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require RcIdentModel.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcKind RcKindLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import reac_ctrl_kind_name_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import SlotModel SlotInv RcAsanFPLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.Seg Require Import Tac_slot.
(* Tac_ro supplies lk_keep / fli_mem / fsj_keep. It is Required but not Imported, and the final YK11 import below is
   spelled with its full path: Requiring it loads other modules named YK11 (lib.Reusable.YK11, lib.A.Reusable.YK11),
   which makes a bare `Import YK11` ambiguous and silently pick the wrong FPState / getr, so CUTST's fx and SlotInv's
   rg-getr stop matching. Qualify its names at use. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.Seg Require Tac_ro.
Import ListNotations.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Reusable Require Import YK11.
Open Scope Z_scope.

Module AC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Contract.
Module AF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.FrameAPI.
Module LE := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Exec.
Module BMN := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.MemNorm.

Lemma f8_kn_len : length kind_name_bytes = 112%nat.
Proof. reflexivity. Qed.

Lemma f8_g_len : forall inp j, length (t_g inp j) = 50%nat.
Proof. intros inp j. unfold t_g. apply fr50_length. Qed.

(* ---- The turn's two frame records keep their lengths: the identity record 38 bytes (RcIdentModel.ID_SIZE; the
   ingest keeps it, ING_length) and the fragment record 72 bytes (fg_next keeps it in every class; copied from
   lib/B/Prog/Seg/F12.v, which this file does not import). ---- *)

Lemma f8_first_length : forall st g, length st = 72%nat -> length g = 50%nat -> 1 <= fg_n g <= 22 ->
  length (fg_first st g) = 72%nat.
Proof.
  intros st g HL HG Hn. unfold fg_first, fg_body.
  rewrite !length_app, length_skipn, (rf_bsl_length g 6 6), (rf_bsl_length g 27 (fg_n g)) by lia.
  cbn [length]. lia.
Qed.

Lemma f8_fr_fg_n : forall len g, fg_fr len g = true -> 1 <= fg_n g <= 22.
Proof.
  intros len g H. unfold fg_fr in H. rewrite !andb_true_iff in H.
  destruct H as (H & _). destruct H as (H & Hn2). destruct H as (_ & Hn1).
  apply Z.leb_le in Hn1. apply Z.leb_le in Hn2. lia.
Qed.

Lemma f8_keep_T : forall st g, fg_keep st g = true -> fg_T st g <= 64.
Proof.
  intros st g H. unfold fg_keep in H. rewrite !andb_true_iff in H.
  destruct H as (_ & H). apply Z.leb_le in H. lia.
Qed.

Lemma f8_next_length : forall f fr pa pp pn len st g, length st = 72%nat -> length g = 50%nat ->
  length (fg_next st g (fg_class f fr pa pp pn len st g)) = 72%nat.
Proof.
  intros f fr pa pp pn len st g HL HG. unfold fg_class.
  destruct ((f =? 0) || (fr =? 0) || (pa =? 0) || (pp =? 0) || (pn =? 0)); [cbn [fg_next]; exact HL|].
  destruct (fg_fr len g) eqn:FR; cbn [negb]; [|cbn [fg_next]; exact HL].
  destruct (bat g 19 =? 1).
  - cbn [fg_next]. apply f8_first_length; [exact HL | exact HG | apply (f8_fr_fg_n len); exact FR].
  - destruct (fg_keep st g) eqn:KEEP; cbn [negb]; [|cbn [fg_next]; apply rf_clear_length; exact HL].
    destruct (fg_close st g); cbn [negb fg_next]; apply rf_clear_length, rf_fg_join_length;
      solve [exact HL | exact HG | apply (f8_fr_fg_n len); exact FR | apply f8_keep_T; exact KEEP].
Qed.

Lemma f8_t_FG_length : forall inp j, length (t_FG inp j) = 72%nat.
Proof.
  intros inp j. induction j as [|j IH].
  - reflexivity.
  - unfold t_FG in *. rewrite fst_at_S. unfold turn.
    destruct (f_opens (t_len inp j) (t_g inp j)); cbn [fs_fg]; unfold fg_st, fcls;
      apply (f8_next_length 1 1 1 1 1); solve [exact IH | apply f8_g_len].
Qed.

Lemma f8_t_ID_length : forall inp j, length (t_ID inp j) = 38%nat.
Proof.
  intros inp j. induction j as [|j IH].
  - reflexivity.
  - unfold t_ID in *. rewrite fst_at_S. unfold turn.
    assert (Hr : length (rp_id (fs_id (fst_at inp j)) (t_len inp j) (t_g inp j)) = 38%nat).
    { unfold rp_id. match goal with |- context [if ?c then _ else _] => destruct c end;
        [apply RcIdentModel.ING_length; exact IH | exact IH]. }
    destruct (f_opens (t_len inp j) (t_g inp j)); cbn [fs_id]; unfold fg_id;
      (match goal with |- context [if ?c then _ else _] => destruct c end;
       [apply RcIdentModel.ING_length; exact Hr | exact Hr]).
Qed.

(* The kind-name strings are read-only image bytes (the same check as reac_ctrl_kind_name_strings_in_image). *)
Lemma f8_kn_strings : forall m, mem_inv rsegs m -> kind_name_strings m.
Proof.
  intros m Hm x Hx. destruct (Z.leb_spec x 13) as [Hle|Hgt].
  - destruct (rc_Z_le13 x ltac:(lia)) as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->| -> ]]]]]]]]]]]]];
      (apply rc_ro_in_image; [exact Hm | vm_compute; reflexivity]).
  - assert (E : kind_name_addr x = QMARK)
      by (unfold kind_name_addr; rewrite (proj2 (Z.leb_gt x 13) Hgt); reflexivity).
    rewrite E, (kind_name_big x Hgt).
    apply rc_ro_in_image; [exact Hm | vm_compute; reflexivity].
Qed.

(* The same strings over a memory that only agrees with the image on its read-only bytes (FRA's ro_agree, push
   5c): the strings are read-only bytes, so the memory reads them as its normalization does. *)
Lemma f8_kn_strings_ro : forall m, ro_agree rsegs m -> kind_name_strings m.
Proof.
  intros m Hro x Hx.
  apply (proj2 (BMN.bytes_at_rel rsegs m (BMN.normalize rsegs m) _ _ (BMN.mem_rel_normalize rsegs m Hro))).
  exact (f8_kn_strings (BMN.normalize rsegs m) (BMN.mem_inv_normalize rsegs m) x Hx).
Qed.

(* Every kind-name address (a table entry or QMARK) is a nonzero 64-bit value. *)
Lemma f8_kn_addr_range : forall x, 0 < kind_name_addr x < 2 ^ 64.
Proof.
  intros x. unfold kind_name_addr.
  destruct (x <=? 13); [|unfold QMARK; lia].
  destruct (nth_in_or_default (Z.to_nat x) kind_name_addrs QMARK) as [Hin|Heq].
  - revert Hin. generalize (nth (Z.to_nat x) kind_name_addrs QMARK) as y. intros y Hin.
    unfold kind_name_addrs in Hin. cbn [In] in Hin.
    repeat (destruct Hin as [<-|Hin]; [lia|]). destruct Hin.
  - rewrite Heq. unfold QMARK. lia.
Qed.

Lemma f8_eqb0_false : forall v, 0 < v < 2 ^ 64 -> bv_eqb (Z_to_bv 64 v) (Z_to_bv 64 0) = false.
Proof.
  intros v Hv. apply Bool.not_true_iff_false. intro HC. apply bv_eqb_eq in HC.
  apply (f_equal bv_unsigned) in HC. rewrite !MState.unsigned_lit in HC by lia. lia.
Qed.

(* A spill base A' read through s1 with a cell q64 at A' + off (off < 448) is the spill base A of FRA, when
   0 <= A and A + 448 <= 2^64 (FRA: sp <= A, and A + 448 <= S with the saved registers below S). *)
Lemma f8_base_eq : forall (A A' off v : Z) (m : word -> option byte),
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

(* Move an rg fact to a register-equal state. SlotInv's rg unfolds to `getr_slotinv regs r = ...`, while a
   register-equality written in this file names this file's `getr` - a DIFFERENT constant, convertible but not
   syntactically equal, so a `rewrite` of the equality (keyed on the head constant) does not fire on a variable
   register r. eq_trans closes it through conversion (delta) instead. The caller applies it with r inferred from
   the carried rg fact, so no register literal is written at the call site. *)
Lemma f8_rg_move : forall (regs regs' : bvmap 5 word) (r : bv 5) (v : Z),
  rg regs r v -> getr regs' r = getr regs r -> rg regs' r v.
Proof. intros regs regs' r v H E. unfold rg in H |- *. exact (eq_trans E H). Qed.

(* ---- The frame-loop bundles across the call. Every conjunct of FLI / FM is either a register the callee keeps
   or a spill cell [A + off, A + off + 8) with off <= 336, and FRA puts the whole save area [A, A + 448) at or above
   sp, so the callee's window [sp - 16, sp) is outside every one of them. FLI's memory facts and FSj (the local
   `first`) are inside the frame, which the window also misses (fra_frame's placement). ---- *)

(* One spill cell [A + off] of the FRA spill base A survives a run whose writes all lie below A. *)
Lemma f8_spill_keep : forall regs regs' m m' W off v A,
  spill regs m off v -> rg regs 9 A -> getr regs' 9 = getr regs 9 ->
  0 <= off < 448 -> 0 <= A -> A + 448 <= 2 ^ 64 ->
  (forall x, A <= x -> Frame.outside W x) -> Frame.munch W m m' -> spill regs' m' off v.
Proof.
  intros regs regs' m m' W off v A HS HA E9 Hoff HA0 HA1 Hout MU.
  unfold spill in HS |- *. destruct HS as (A' & HA' & Hq).
  assert (EA : A' = A).
  { apply (f8_base_eq A A' off v m); [| exact HA0 | exact HA1 | exact Hoff | exact Hq].
    unfold rg in HA', HA. rewrite <- HA'. exact HA. }
  subst A'. exists A. split; [exact (f8_rg_move regs regs' _ _ HA' E9)|].
  unfold q64 in *. eapply fl_bytes; [exact Hq | exact MU |].
  rewrite length_le8. intros x Hx. apply Hout. lia.
Qed.

(* FSj (v1.9): the local `first` at [fr + 2880, fr + 2920) and its addressability, across a write that misses it. *)
Lemma f8_fsj_keep : forall g fr j regs regs' m m' W,
  FSj g fr j regs m -> Frame.munch W m m' -> (forall x, fr + 2880 <= x < fr + 2920 -> Frame.outside W x) ->
  addressable m' (fr + 2880) 40 -> FSj g fr j regs' m'.
Proof.
  intros g fr j regs regs' m m' W HF MU Hout Had.
  apply (Tac_ro.fsj_keep g fr j regs regs' m m' HF); [|exact Had].
  intros a bs Ha Hab Hb. apply (fl_bytes W m m' a bs Hb MU). intros x Hx. apply Hout. lia.
Qed.

(* FM (v1.9): the fill-flag spill [A+184], s8 = k, s6 = 1, s9 = sum_ok and the block-pointer spill [A+312]. *)
Lemma f8_fm_keep : forall g j phi fr regs regs' m m' W A,
  FM g j phi fr regs m -> rg regs 9 A -> getr regs' 9 = getr regs 9 ->
  getr regs' 22 = getr regs 22 -> getr regs' 24 = getr regs 24 -> getr regs' 25 = getr regs 25 ->
  0 <= A -> A + 448 <= 2 ^ 64 -> (forall x, A <= x -> Frame.outside W x) -> Frame.munch W m m' ->
  FM g j phi fr regs' m'.
Proof.
  intros g j phi fr regs regs' m m' W A HF HA E9 E22 E24 E25 HA0 HA1 Hout MU.
  unfold FM in HF. destruct HF as (H184 & H24 & H22 & H25 & H312). unfold FM.
  split; [eapply f8_spill_keep;
            [exact H184 | exact HA | exact E9 | lia | exact HA0 | exact HA1 | exact Hout | exact MU]|].
  split; [exact (f8_rg_move regs regs' _ _ H24 E24)|].
  split; [exact (f8_rg_move regs regs' _ _ H22 E22)|].
  split; [exact (f8_rg_move regs regs' _ _ H25 E25)|].
  eapply f8_spill_keep;
    [exact H312 | exact HA | exact E9 | lia | exact HA0 | exact HA1 | exact Hout | exact MU].
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

(* ---- FRA facts by name. Each picks its conjunct by statement (tauto), never by position. ---- *)

Lemma f8_fra_halt : forall g fr hb regs mem md, FRA B APIf ra g fr hb regs mem md -> m_halted md = None.
Proof. intros g fr hb regs mem md (A & sp & s5 & HF). tauto. Qed.

Lemma f8_fra_ro : forall g fr hb regs mem md, FRA B APIf ra g fr hb regs mem md -> ro_agree rsegs mem.
Proof. intros g fr hb regs mem md (A & sp & s5 & HF). tauto. Qed.

Lemma f8_fra_ah : forall g fr hb regs mem md, FRA B APIf ra g fr hb regs mem md ->
  AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) (hb ++ g_H g) mem md.
Proof. intros g fr hb regs mem md (A & sp & s5 & HF). tauto. Qed.

Lemma f8_fra_rt : forall g fr hb regs mem md, FRA B APIf ra g fr hb regs mem md ->
  AsanRTInv.RT (AC.aspZ regs) mem md.
Proof.
  intros g fr hb regs mem md HFRA. pose proof HFRA as (A & sp & s5 & HF).
  assert (Hsp : AC.aspZ regs = sp) by tauto. rewrite Hsp. tauto.
Qed.

(* The numeric facts of FRA this segment needs: the spill base A = s1 with sp <= A, A + 448 <= S, S < APPMEM_END,
   S - 4096 < sp, and the entry-anchored window (whose bounds give 0 <= S - SLOT_STACK and S <= 2^64). *)
Lemma f8_fra_nums : forall g fr hb regs mem md, FRA B APIf ra g fr hb regs mem md ->
  exists A, rg regs 9 A /\ AC.aspZ regs <= A /\ A + 448 <= g_S g /\ g_S g < APPMEM_END /\
    0 <= g_S g - AF.SLOT_STACK /\ g_S g <= 2 ^ 64 /\ g_S g - 4096 < AC.aspZ regs /\
    stk rsegs mem (g_S g - AF.SLOT_STACK) (g_S g).
Proof.
  intros g fr hb regs mem md HFRA. pose proof HFRA as (A & sp & s5 & HF).
  assert (Hsp : AC.aspZ regs = sp) by tauto.
  assert (Hwin : stk rsegs mem (g_S g - AF.SLOT_STACK) (g_S g)) by tauto.
  pose proof Hwin as (Hw0 & Hw1 & _).
  exists A. rewrite Hsp.
  split; [tauto|]. split; [tauto|]. split; [tauto|]. split; [tauto|].
  split; [lia|]. split; [lia|]. split; [tauto | exact Hwin].
Qed.

(* The one lazy-model run of this file (AsanLift.evt_SR_canon_lazy), used once, for the F8 run 0x82174 -> 0x82180.
   That run reads the KIND_NAME table [0x9f580, 0x9f5f0), the kind-name strings in the image, the runtime cells and
   the shadow bytes the callee reads; it writes only the callee's stack window [sp-16, sp). The KN contract speaks
   Lib.Exec.evt, so this is Tac_slot.sl_run without its ul_entry step. *)
Lemma f8_run_lib : forall regs pc mem md
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

(* The run 0x82174 -> 0x82180 over explicit registers: beqz a0 not taken (a0 <> 0), mv a0,s8, and the KN call
   composed with its contract (window [sp-16, sp)), landing at 0x82180 with a0 = kind_name_addr v and the name
   bytes at that address. *)
Lemma f8_evt :
  forall (ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8v s9 s10 s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (v lo : Z),
    bv_eqb a0 (Z_to_bv 64 0) = false -> s8v = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
    bytes_at rsegs m KIND_NAME kind_name_bytes -> kind_name_strings m ->
    stk rsegs m lo (bv_unsigned sp) -> lo + REAC_CTRL_KIND_NAME_FRAME <= bv_unsigned sp ->
    KIND_NAME + 112 <= bv_unsigned sp - REAC_CTRL_KIND_NAME_FRAME ->
    asan_cells m -> shadow_rw m -> addressable m KIND_NAME 112 ->
    (forall x, GOT_CELL_K <= x < GOT_CELL_K + 8 \/ CELL_K <= x < CELL_K + 8 \/ in_shadow x ->
       outside [(bv_unsigned sp - REAC_CTRL_KIND_NAME_FRAME, bv_unsigned sp)] x) ->
    LE.evt rsegs
      (fun ms' => exists (a1' a2' a3' : word) (m' : word -> option byte),
         ms' = MS (mkR (Z_to_bv 64 0x82180) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (kind_name_addr v))
                       a1' a2' a3' a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8v s9 s10 s11 t3 t4 t5 t6)
                  Fr (Z_to_bv 64 0x82180) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned sp - REAC_CTRL_KIND_NAME_FRAME, bv_unsigned sp)] m m' /\
         wmono rsegs m m' /\ stk rsegs m' lo (bv_unsigned sp) /\
         bytes_at rsegs m' (kind_name_addr v) (cstr_bytes (kind_name v)))
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8v s9 s10 s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x82174) fc None m (seg_rom rsegs)).
Proof.
  intros ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8v s9 s10 s11 t3 t4 t5 t6
    Fr fc m v lo Hnz -> Hv HKB HKS HST Hlo Hkn HAC HSW HAD Hout.
  (* 0x82174 beqz a0 : a0 <> 0, not taken *)
  step. rewrite Hnz. cbv iota.
  (* 0x82178 mv a0,s8 ; 0x8217c jal reac_ctrl_kind_name *)
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
  intros ms' (a1' & a2' & a3' & m' & E & MU & WM & MI & ST' & HN).
  subst ms'.
  replace (ret_pc (Z_to_bv 64 0x82180)) with (Z_to_bv 64 0x82180)
    by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  rewrite (MState.unsigned_lit v) in HN |- * by lia.
  apply evt_done.
  exists a1', a2', a3', m'.
  split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact ST' | exact HN].
Qed.

(* S_F8 (forms-asan-ubsan-v190.md (a working note, not in this delivery)). *)
Lemma seg_F8 : forall j, Hat B APIf ra (Inv_B82180_at B APIf ra) j -> Hat B APIf ra (Inv_B82174_at B APIf ra) j.
Proof.
  intros j Hexit g c HInv. pose proof FRAME_BYTES_val as HFBv.
  pose proof (proj1 FF) as SEGS.
  destruct HInv as (phi & regs & mem & md & fr & Ec & HFRA & HENT & Hgn & Hj & HHB & HLK & Hs2 & Hs4 & HFM & HFS &
    HKNB & HKNA & H248 & Hrec & HFT & HREC & HFPS & H272 & A & v & HFLV & Ha0 & Hs8 & Hv & Hq280 & Hu32).
  subst c. rewrite SEGS.
  (* FRA facts, all by name *)
  pose proof (f8_fra_halt g fr _ regs mem md HFRA) as Hhalt.
  pose proof (f8_fra_ro g fr _ regs mem md HFRA) as Hro.
  pose proof (f8_fra_ah g fr _ regs mem md HFRA) as HAH.
  pose proof (f8_fra_rt g fr _ regs mem md HFRA) as HRT.
  destruct (fra_win B APIf ra g fr _ regs mem md HFRA) as (Hwlo & HST0).
  destruct (fra_frame B APIf ra g fr _ regs mem md HFRA) as (Hplace & _ & _ & _).
  destruct (fra_app B APIf ra g fr _ regs mem md HFRA) as (HGTfr & Hfrapp).
  destruct (f8_fra_nums g fr _ regs mem md HFRA) as (Ab & H9b & HspA & HA448 & HSapp & HSlo0 & HShi & HS4 & Hwin).
  pose proof (AC.a_laws_stack_high _ _ _ _ _ (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) _ mem md HAH) as Hhigh.
  assert (HSS : AF.SLOT_STACK = 1048576) by reflexivity.
  assert (HFN : FN_STACK = 1044480) by reflexivity.
  assert (HKNK : REAC_CTRL_KIND_NAME_FRAME = 16) by reflexivity.
  assert (HHM : HIGHMEM_BEG = 0x10007fff8000) by reflexivity.
  assert (HKNa : KIND_NAME = 0x9f580) by reflexivity.
  assert (HGTv : AC.GT = 0x5fe000) by reflexivity.
  assert (Hasp0 : 0 < AC.aspZ regs) by lia.
  assert (HaspB : AC.aspZ regs <= APPMEM_END) by lia.
  assert (HA2b : Ab + 448 <= 2 ^ 64) by lia.
  assert (HA0 : 0 <= Ab) by lia.
  (* the frame is apart from the callee's window [sp - 16, sp), and ends below APPMEM_END *)
  pose proof (Hplace REAC_CTRL_KIND_NAME_FRAME ltac:(lia)) as Hdisjfr.
  assert (Hfrhi : fr + FRAME_BYTES <= APPMEM_END).
  { pose proof (Hfrapp (fr + FRAME_BYTES - 1) ltac:(lia)) as Hap.
    unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in Hap |- *. lia. }
  (* the FLVsp spill base is FRA's *)
  assert (EA : A = Ab).
  { destruct HFLV as (H9A & Hq120 & _).
    apply (f8_base_eq Ab A 120 (fragb fr + 15) mem); [| exact HA0 | exact HA2b | lia | exact Hq120].
    unfold rg in H9A, H9b. rewrite <- H9A. exact H9b. }
  subst A.
  (* the branch at 0x82174: a0 = kind_name_addr v is nonzero *)
  assert (Hnz0 : bv_eqb (getr regs 10) (Z_to_bv 64 0) = false).
  { unfold rg in Ha0. rewrite Ha0. apply f8_eqb0_false. apply f8_kn_addr_range. }
  (* the KN premises over the entry memory *)
  assert (Hlo0 : AC.aspZ regs - FN_STACK + REAC_CTRL_KIND_NAME_FRAME <= AC.aspZ regs) by lia.
  assert (Hkn0 : KIND_NAME + 112 <= AC.aspZ regs - REAC_CTRL_KIND_NAME_FRAME) by lia.
  assert (Hout0 : forall x, GOT_CELL_K <= x < GOT_CELL_K + 8 \/ CELL_K <= x < CELL_K + 8 \/ in_shadow x ->
            Frame.outside [(AC.aspZ regs - REAC_CTRL_KIND_NAME_FRAME, AC.aspZ regs)] x).
  { intros x Hx. cbn [Frame.outside]. split; [|exact I]. intros [HH1 HH2].
    unfold GOT_CELL_K, CELL_K, in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG in *. lia. }
  apply (f8_run_lib regs (Z_to_bv 64 0x82174) mem md
    (fun R0 pc' mem' =>
       pc' = Z_to_bv 64 0x82180 /\
       getr R0 2 = getr regs 2 /\ getr R0 3 = getr regs 3 /\ getr R0 4 = getr regs 4 /\
       getr R0 8 = getr regs 8 /\ getr R0 9 = getr regs 9 /\ getr R0 18 = getr regs 18 /\
       getr R0 19 = getr regs 19 /\ getr R0 20 = getr regs 20 /\ getr R0 21 = getr regs 21 /\
       getr R0 22 = getr regs 22 /\ getr R0 24 = getr regs 24 /\ getr R0 25 = getr regs 25 /\
       getr R0 26 = getr regs 26 /\ getr R0 27 = getr regs 27 /\
       getr R0 10 = Z_to_bv 64 (kind_name_addr v) /\
       Frame.munch [(AC.aspZ regs - REAC_CTRL_KIND_NAME_FRAME, AC.aspZ regs)] mem mem' /\
       Frame.wmono rsegs mem mem' /\
       stk rsegs mem' (AC.aspZ regs - FN_STACK) (AC.aspZ regs) /\
       bytes_at rsegs mem' (kind_name_addr v) (cstr_bytes (kind_name v)))
    (Post B APIf ra g)).
  - exact Hhalt.
  - eapply LE.evt_mono.
    { unfold Regs6ss.mkR_of.
      eapply f8_evt with (v := v) (lo := AC.aspZ regs - FN_STACK).
      - exact Hnz0.
      - unfold rg in Hs8; exact Hs8.
      - lia.
      - exact HKNB.
      - exact (f8_kn_strings_ro mem Hro).
      - exact HST0.
      - exact Hlo0.
      - exact Hkn0.
      - exact (AsanRTInv.RT_cells _ mem md HRT).
      - exact (AsanRTInv.RT_shadow_rw _ mem md HRT).
      - exact HKNA.
      - exact Hout0. }
    { intros ms' (a1' & a2' & a3' & m' & E & MU & WM & ST' & HN).
      eexists _, (Z_to_bv 64 0x82180), m'. split; [exact E|].
      split; [reflexivity|].
      split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
      split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
      split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
      split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
      split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
      split; [exact MU|]. split; [exact WM|]. split; [exact ST' | exact HN]. }
  - intros R0 pc' mem' regs' md' (Hpc & Er2 & Er3 & Er4 & Er8 & Er9 & Er18 & Er19 & Er20 & Er21 & Er22 &
      Er24 & Er25 & Er26 & Er27 & Er10 & MU & WM & ST' & HN) Hreg Hmat.
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
    (* the window W = [sp-16, sp): app memory above HIGHMEM_BEG, runtime-disjoint, below the save area and apart
       from the frame *)
    assert (HWlo : forall x, x < HIGHMEM_BEG \/ AC.aspZ regs <= x ->
              Frame.outside [(AC.aspZ regs - REAC_CTRL_KIND_NAME_FRAME, AC.aspZ regs)] x).
    { intros x Hx. cbn [Frame.outside]. split; [|exact I]. intros [HH1 HH2]. lia. }
    assert (HWfr : forall x, fr <= x < fr + FRAME_BYTES ->
              Frame.outside [(AC.aspZ regs - REAC_CTRL_KIND_NAME_FRAME, AC.aspZ regs)] x).
    { intros x Hx. cbn [Frame.outside]. split; [|exact I]. intros [HH1 HH2].
      destruct Hdisjfr as [Hd|Hd]; lia. }
    assert (HWA2 : forall x, Ab <= x -> Frame.outside [(AC.aspZ regs - REAC_CTRL_KIND_NAME_FRAME, AC.aspZ regs)] x)
      by (intros x Hx; apply HWlo; right; lia).
    assert (Hallapp : all_app [(AC.aspZ regs - REAC_CTRL_KIND_NAME_FRAME, AC.aspZ regs)]).
    { cbn [all_app]. split; [|exact I]. intros a Ha. unfold app_mem. right.
      unfold HIGHMEM_BEG, APPMEM_END in *. lia. }
    (* ro_agree on the run's memory: every read-only byte is in the image, below GT, and the window is above it *)
    assert (HroM : ro_agree rsegs mem').
    { apply (sl_ro_keep _ mem mem' Hro MU). intros x Hx. apply HWlo. left. lia. }
    (* AH, the stack bounds and the runtime's ownership of an image byte, across the callee's window store *)
    assert (HstoreC : forall a, 0 <= a < 2 ^ 64 ->
      ~ AC.a_store_ok (hb1 phi (AC.a_size (flen g j)) ++ g_H g)
          (AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md) a ->
      mem' (Z_to_bv 64 a) = mem (Z_to_bv 64 a)).
    { intros a Ha Hns. apply MU. rewrite MState.unsigned_lit by lia.
      cbn [Frame.outside]. split; [|exact I]. intros [HH1 HH2]. apply Hns.
      unfold AC.a_store_ok. right; left. split; lia. }
    assert (HwmL : forall a, 0 <= a < 2 ^ 64 -> writable_at rsegs mem a -> writable_at rsegs mem' a)
      by (intros a Ha Hw; exact (WM (Z_to_bv 64 a) Hw)).
    destruct (lw_store (APIf rc) _ mem mem' md HAH HstoreC HwmL) as [HAH' HownEq HSTKeq HSTKhieq].
    (* the entry-anchored window [S - SLOT_STACK, S) on mem', from the callee's stk post *)
    destruct (Frame.stk_split rsegs mem' (AC.aspZ regs - FN_STACK)
                (AC.aspZ regs - REAC_CTRL_KIND_NAME_FRAME) (AC.aspZ regs) ST' ltac:(lia)) as (_ & HSTw).
    pose proof (sl_win_stk B APIf ra g fr _ regs mem md mem' REAC_CTRL_KIND_NAME_FRAME HFRA ltac:(lia) MU WM HSTw)
      as HSTKS.
    (* FRA across the callee's window write and the model step *)
    assert (HFRA'' : FRA B APIf ra g fr (hb1 phi (AC.a_size (flen g j))) regs' mem' md').
    { apply (sl_callee_keep B APIf ra empty FF g fr _ regs regs' mem mem' md md' REAC_CTRL_KIND_NAME_FRAME
               HFRA MU WM HSTKS);
        [ lia | exact HaspB | destruct Hdisjfr as [Hd|Hd]; [right; lia | left; lia] | exact Hfrhi
        | exact Fr2 | exact Fr3 | exact Fr4 | exact Fr8 | exact Fr9 | exact Fr19 | exact Fr26 | exact Hmat ]. }
    (* ENT: the KN window lies inside the slot window [S - SLOT_STACK, S), so no byte of an entry block, of the
       image, of the stack at or above S or of their shadow changed *)
    assert (HWcases : forall x, 0 <= x < 2 ^ 64 ->
      Frame.outside [(AC.aspZ regs - REAC_CTRL_KIND_NAME_FRAME, AC.aspZ regs)] x \/
      (g_S g - AF.SLOT_STACK <= x < g_S g) \/ (fr <= x < fr + FRAME_BYTES) \/ (Sfr fr <= x < Sfr fr + FRAME_SHADOW)).
    { intros x Hx.
      destruct (Z_lt_le_dec x (AC.aspZ regs - REAC_CTRL_KIND_NAME_FRAME)) as [Hl|Hl].
      { left. cbn [Frame.outside]. split; [|exact I]. intros [HH1 HH2]. lia. }
      destruct (Z_lt_le_dec x (AC.aspZ regs)) as [Hh|Hh].
      { right; left. lia. }
      left. cbn [Frame.outside]. split; [|exact I]. intros [HH1 HH2]. lia. }
    assert (HENT'' : ENT APIf g (hb1 phi (AC.a_size (flen g j))) mem' md').
    { eapply ent_mat; [|exact Hmat].
      apply (ent_store B APIf ra g fr _ regs mem mem' md _ HENT HFRA MU HWcases HSTKeq HSTKhieq).
      intros a _ Hown0. exact (proj2 (HownEq a) Hown0). }
    (* the frame-loop bundles across the call *)
    (* The callee window as one name for fl_bytes: an evar window `_` does not unify with MU's (convertible but
       differently-headed) munch, so it is passed explicitly, as F7 does. HWout_lo gives the outside facts for the
       bytes below the window (the record buffer), stated on the literal window so its cbn proof reduces. *)
    pose (Wk := [(AC.aspZ regs - REAC_CTRL_KIND_NAME_FRAME, AC.aspZ regs)]).
    assert (HWout_lo : forall x, x < AC.aspZ regs - REAC_CTRL_KIND_NAME_FRAME ->
              Frame.outside [(AC.aspZ regs - REAC_CTRL_KIND_NAME_FRAME, AC.aspZ regs)] x).
    { intros x Hx. cbn [Frame.outside]. split; [|exact I]. intros [HH1 HH2]. lia. }
    destruct HLK as (HjLK & Hsp232 & HOURb & HFLI).
    destruct (Tac_ro.fli_mem g fr regs mem HFLI) as (Hour6 & Hfrstk & HRid & HRfg & HKNT & Hfst).
    assert (Hfst' : addressable mem' (fr + 2880) 40) by (eapply sl_addr_keep; [exact Hfst | exact MU | exact Hallapp]).
    assert (Hspk : forall off w, 0 <= off <= 336 -> spill regs mem off w -> spill regs' mem' off w).
    { intros off w Hoff HS.
      exact (f8_spill_keep regs regs' mem mem'
               [(AC.aspZ regs - REAC_CTRL_KIND_NAME_FRAME, AC.aspZ regs)] off w Ab HS H9b Fr9
               ltac:(lia) HA0 HA2b HWA2 MU). }
    (* KNT across the call: the kind-name table (112 bytes at KIND_NAME) is image data, far below the callee's
       16-byte window (Hkn0), so its bytes stay and no shadow byte of the table changes (the window is app
       memory, Hallapp). *)
    assert (HKNT' : KNT mem').
    { split.
      - apply (fl_bytes Wk mem mem' KNC.KIND_NAME KNC.kind_name_bytes (proj1 HKNT) MU).
        assert (HKL : Z.of_nat (length KNC.kind_name_bytes) = 112) by reflexivity.
        rewrite HKL. intros x Hx. apply HWout_lo. lia.
      - eapply sl_addr_keep; [exact (proj2 HKNT) | exact MU | exact Hallapp]. }
    assert (HLK' : LK g fr j regs' mem').
    { apply (Tac_ro.lk_keep g fr j regs regs' mem mem');
        [ split; [exact HjLK|]; split; [exact Hsp232|]; split; [exact HOURb | exact HFLI]
        | exact (f8_rg_move regs regs' _ _ (proj1 HFLI) Fr27)
        | eapply sl_addr_keep; [exact Hour6 | exact MU | exact Hallapp]
        | eapply (Frame.stk_transport rsegs _ mem mem');
            [exact Hfrstk | exact MU | exact WM | intros x Hx; left; apply HWfr; lia]
        | eapply sl_addr_keep; [exact HRid | exact MU | exact Hallapp]
        | eapply sl_addr_keep; [exact HRfg | exact MU | exact Hallapp]
        | exact HKNT'
        | exact Hfst'
        | unfold OURb in *; apply (fl_bytes Wk mem mem' (fr + 2624) (OUR (g_in g)) HOURb MU);
            rewrite OUR_length; intros x Hx; apply HWfr; cbn [Z.of_nat] in Hx; lia
        | exact Hspk ]. }
    assert (HFM' : FM g j phi fr regs' mem')
      by (apply (f8_fm_keep g j phi fr regs regs' mem mem' _ Ab HFM H9b Fr9 Fr22 Fr24 Fr25 HA0 HA2b HWA2 MU)).
    assert (HFS' : FSj g fr j regs' mem').
    { apply (f8_fsj_keep g fr j regs regs' mem mem' Wk HFS MU); [|exact Hfst'].
      intros x Hx. apply HWfr. lia. }
    (* Phi is a live block of the cut's heap, so it ends at or below stklo, below the callee's window *)
    assert (Hin : In (phi, AC.a_size (flen g j)) (hb1 phi (AC.a_size (flen g j)) ++ g_H g))
      by (apply in_or_app; left; unfold hb1; cbn [In]; left; reflexivity).
    destruct (lw_blocks (APIf rc) _ mem md phi (AC.a_size (flen g j)) HAH Hin) as [_ _ Hend _ _].
    (* the record bytes (len >= 50) *)
    assert (Hrec' : 50 <= flen g j -> bytes_at rsegs mem' phi (t_g (g_in g) j)).
    { intros H50. pose proof (Hrec H50) as HG.
      apply (fl_bytes Wk mem mem' phi (t_g (g_in g) j) HG MU).
      rewrite f8_g_len. intros x Hx. change (Z.of_nat 50) with 50 in Hx.
      apply HWout_lo. unfold AC.a_size in Hend. lia. }
    (* FTURN: the two spills above the window, the frame bytes at Phi below it (their length is at most len) *)
    assert (HFT' : FTURN g j phi regs' mem').
    { destruct HFT as (H224 & H232 & HPB & HPL).
      split; [exact (Hspk 224 _ ltac:(lia) H224)|].
      split; [exact (Hspk 232 _ ltac:(lia) H232)|].
      split; [|exact HPL].
      apply (fl_bytes Wk mem mem' phi (t_phi (g_in g) j) HPB MU).
      intros x Hx. apply HWout_lo. unfold AC.a_size, flen in Hend. lia. }
    (* REC0: the identity record [fr + 2688, fr + 2726) and the fragment record [fr + 2768, fr + 2840), both in the
       frame, which the window misses *)
    assert (HREC' : REC0 g fr j mem').
    { unfold REC0, FREC, IDb, FGb, IDBe, FGBe in HREC |- *.
      destruct HREC as ((HID & Hidok) & (HFG & Hfgok)).
      split; split; try assumption.
      - apply (fl_bytes Wk mem mem' (fr + 2688) (t_ID (g_in g) j) HID MU).
        rewrite f8_t_ID_length. change (Z.of_nat 38) with 38. intros x Hx. apply HWfr. lia.
      - apply (fl_bytes Wk mem mem' (fr + 2768) (t_FG (g_in g) j) HFG MU).
        rewrite f8_t_FG_length. change (Z.of_nat 72) with 72. intros x Hx. apply HWfr. lia. }
    (* FPS: the parse struct's 36 bytes at fr + 176 (in the frame, which the window misses) and their
       addressability; F272: the spill [A+272] above the window *)
    assert (HFPS' : FPS g fr j mem').
    { destruct HFPS as (HpB & HadB). split.
      - unfold pBb in *. apply (fl_bytes Wk mem mem' (fr + 176) (t_B (g_in g) j) HpB MU).
        assert (Lb : length (t_B (g_in g) j) = 36%nat)
          by (apply OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.RcParse.ctrlparse_length).
        rewrite Lb. change (Z.of_nat 36) with 36. intros x Hx. apply HWfr. lia.
      - eapply sl_addr_keep; [exact HadB | exact MU | exact Hallapp]. }
    assert (H272' : F272 g j regs' mem') by (unfold F272 in *; exact (Hspk 272 _ ltac:(lia) H272)).
    assert (HIexit : Inv_B82180_at B APIf ra g j
                       (mkCfg (mkst regs' (Z_to_bv 64 0x82180) mem' (seg_rom rsegs)) md')).
    { exists phi, regs', mem', md', fr. rewrite SEGS. split; [reflexivity|].
      split; [exact HFRA''|].
      split; [exact HENT''|].
      split; [exact Hgn|].
      split; [exact Hj|].
      split.
      { destruct HHB as (Hphinz & Hphiad). split; [exact Hphinz|].
        eapply sl_addr_keep; [exact Hphiad | exact MU | exact Hallapp]. }
      split; [exact HLK'|].
      split; [exact (f8_rg_move regs regs' _ _ Hs2 Fr18)|].
      split; [exact (f8_rg_move regs regs' _ _ Hs4 Fr20)|].
      split; [exact HFM'|].
      split; [exact HFS'|].
      split.
      { apply (fl_bytes Wk mem mem' KIND_NAME kind_name_bytes HKNB MU).
        rewrite f8_kn_len. intros x Hx. apply HWlo. left. change (Z.of_nat 112) with 112 in Hx. lia. }
      split; [eapply sl_addr_keep; [exact HKNA | exact MU | exact Hallapp]|].
      split; [exact (Hspk 248 _ ltac:(lia) H248)|].
      split; [exact Hrec'|].
      split; [exact HFT'|].
      split; [exact HREC'|].
      split; [exact HFPS'|].
      split; [exact H272'|].
      exists Ab, v.
      split.
      { destruct HFLV as (H9A & Hq120 & Hq128 & Hq256 & Hq304 & Hq296). unfold q64 in *.
        split; [exact (f8_rg_move regs regs' _ _ H9A Fr9)|].
        split; [apply (fl_bytes Wk mem mem' _ _ Hq120 MU); rewrite length_le8; intros x Hx; apply HWA2; lia|].
        split; [apply (fl_bytes Wk mem mem' _ _ Hq128 MU); rewrite length_le8; intros x Hx; apply HWA2; lia|].
        split; [apply (fl_bytes Wk mem mem' _ _ Hq256 MU); rewrite length_le8; intros x Hx; apply HWA2; lia|].
        split; [apply (fl_bytes Wk mem mem' _ _ Hq304 MU); rewrite length_le8; intros x Hx; apply HWA2; lia|].
        apply (fl_bytes Wk mem mem' _ _ Hq296 MU); rewrite length_le8; intros x Hx; apply HWA2; lia. }
      split; [unfold rg; exact Fr10|].
      split; [exact (f8_rg_move regs regs' _ _ Hs8 Fr24)|].
      split; [exact Hv|].
      split.
      { unfold q64 in *. apply (fl_bytes Wk mem mem' _ _ Hq280 MU).
        rewrite length_le8. intros x Hx. apply HWA2. lia. }
      split.
      { unfold u32 in *. apply (fl_bytes Wk mem mem' _ _ Hu32 MU).
        rewrite length_le4. intros x Hx. apply HWfr. lia. }
      exact HN. }
    pose proof (Hexit g _ HIexit) as HSR. rewrite SEGS in HSR. exact HSR.
Qed.

End S.
