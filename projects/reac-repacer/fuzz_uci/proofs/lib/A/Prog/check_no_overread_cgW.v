(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs: copied from proofs/cgif/cgif_file_fuzzer/lib/YCbq.v, with its module paths changed and off_img's image bounds taken from the unit's own Reusable/YImgTop.v. *)
(* Modified by Theorem Labs: copied from proofs/libreac/fuzz_grant/lib/YCbq.v (donor image sha256 c2c7559b29bd), with its module paths changed. *)
(* Modified by Theorem Labs, 2026-10: a new file, lib/A/Prog/check_no_overread_cgW.v, that proves reac-repacer/fuzz_uci's check_no_overread on image A (fuzz_uci.asan 0x7f4fc; lib/A/Prog/check_no_overread_cg.v uci_check_no_overread_cg_holds_stmt); from the donor lib/Reusable/YCbq.v it takes aj_intrin_at's proof, carried to rp_uci_int's realizes contract at uci_sigma US_rp_uci_int and its stack window RUI_STK (cnoW_rui_at), and mbyte_of_aview's case split, at two addresses (cnoW_garr8_move); everything else is new. *)
(* check_no_overread_cgW: the walk of check_no_overread (fuzz_uci.asan 0x7f4fc, 76 slots of lib/A/Prog/UciPList.v from
   AF_check_no_overread = 0x214) in the PA engine (lib/A/Prog/PaRun.v, UciPPaLib.v: paj_run_tok, psrr_branch_tok),
   in the form of the released image-A walk of fuzz_boxreg's read_name (proofs/libreac/fuzz_boxreg/lib/A/Prog/ReadName.v:
   malloc, __asan_memcpy and a shadow-checked terminator store, cut by the same core rules).

   The phases and the UBSan walk's (lib/U/Prog/check_no_overread_cg.v) they correspond to:
   - +0x00 .. +0x40 and malloc (n + 1) (cno_entry_cf): the prologue, s0 = cur, s1 = n, s4 = r, s5 = the shadow base
     (read through its GOT word and cell, uci_cells), a0 = n + 1; malloc by amalloc04_rule;
   - +0x44 .. +0x4c and the second malloc (cno_ph2m_cf);
   - +0x50 .. +0xe0 (cno_ph3_cf): the two NULL branches (refuted: 4096 <= P, Q, the malloc rule's post); n = 0 skips the
     copies; otherwise __asan_memcpy (P, r, n) and (Q, r, n) by aintrin_realizes OCpy (aj_intrin_at); the terminator
     stores P[n] = '0' and Q[n] = ' ', each after its shadow check; rp_uci_int (P, n, cur) and (Q, n, cur) by the
     frozen rp_uci_int contract (cnoW_rui_at); `bne s4, a0` (refuted: both results are rp_uci_int_m of the same n
     bytes, since both copies hold the reply bytes);
   - free (P) at +0xe4 by afree04_rule (cno_ph4_cf);
   - the epilogue and the tail call free (Q) at +0x10c, which returns to the caller (cno_ph5_cf).
   The report branches (+0x118 .. +0x12c, __asan_report_store1) are never reached: P[n] and Q[n] are the last bytes of
   live blocks of n + 1 bytes, so their shadow is addressable (range_addressable_of_block), which the PA engine's
   shadow entries (mkSHE, slots 104 and 105) carry through the check and its slow path. The abort calls (+0x110,
   +0x114) are reached only by the refuted branches.
   Traces: s0 holds cur, an int, at both mallocs and the first free, so the chain is empty (bad_next) and the traces are
   uci_cno_ufix's; the tail free runs with the caller's ra and s0, so its trace is the entry context (uci_cno_uctx).
   The walk keeps a journal that starts at the call (frame CNO_STK at the entry sp, no footprint); the closing theorem
   composes it into the caller's journal. *)
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI0s.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YI00.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require Import YG0s.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.A.Prog Require Import PaRun PaShadow UciPSyms UciPList UciPPa.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.A.Prog Require Import PaJournal.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require Import YImgTop.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.A.Prog Require Import PaStep UciPPaLib UciPImg UciPAddr.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.A Require Import AB1v.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.A Require AE2k.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.A.Rt Require Import ConstsViewDef.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Spec Require Import UciModel.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.A.Prog Require Import UciCg.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.A.Prog Require rp_uci_int_cg check_no_overread_cg.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Module PR := OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.A.Prog.rp_uci_int_cg.
Module CNO := OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.A.Prog.check_no_overread_cg.
#[global] Remove Hints OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

Definition SB : Z := 0x7fff8000.
Definition Bspan : Z * Z := (SB, SB + 2 ^ 44 - 1).
Definition PTR (al : Z) : afact := mkAF 4096 140737479966720 al.
Definition cnoW_facts : facts :=
  mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (11%nat, mkAF 0 255 0); (32%nat, mkAF SB SB 0)] [] [].
Definition ss_cno : sstate :=
  mkSS AF_check_no_overread sr_atoms [stack_region 0x40; got_regionP; bcell_regionP 32] None cnoW_facts.

Section W. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
#[local] Existing Instance AE2k.tfib_sink_head.
Local Abbreviation SEGS := (@pa_segs _ uci_listing PI_uci).
Local Abbreviation VAL := (@pa_val _ uci_listing PI_uci).
Local Abbreviation BASE := (@pa_val _ uci_listing PI_uci A_TEXT).
Lemma cnoW_base : @pa_val _ uci_listing PI_uci A_TEXT = 0x7f2e8.
Proof. reflexivity. Qed.
Lemma cnoW_got : @pa_val _ uci_listing PI_uci (A_OBJ 0) = UCells.GOT_CELL_K.
Proof. vm_compute. reflexivity. Qed.
Lemma cnoW_cell : @pa_val _ uci_listing PI_uci (A_OBJ 8) = UCells.CELL_K.
Proof. vm_compute. reflexivity. Qed.

Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis CELLS : uci_cells B.
Let RUN := paj_run B LAWS.
Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI_uci).

Lemma cnoW_entry : forall (W : world SEGS) (regs : bvmap 5 word) (memc : word -> option byte) lyc Sc mdc n,
  AR SEGS B lyc Sc W memc mdc ->
  (forall a, spZ regs - 0x40 <= a < spZ regs -> apresent (w_H W) memc a) ->
  2 ^ 46 <= spZ regs <= 2 ^ 47 -> spZ regs mod 16 = 0 ->
  getr regs 11 = w64 n -> 0 <= n <= 255 ->
  st_ok_pi SEGS VAL (Eimg (Ereg regs [Z_to_bv 64 SB])) ss_cno
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_check_no_overread)) memc (seg_rom SEGS))).
Proof.
  intros W regs memc lyc Sc mdc n HAR Hpres Hsp H16 H11 Hn.
  pose proof (proj1 (Forall_forall _ _) (am_const _ _ _ _ (proj1 HAR))) as HC.
  destruct (CELLS lyc) as (C1 & C2 & _).
  pose proof (rdword_cell B lyc _ UCells.CELL_K UCells.ASAN_K ltac:(unfold UCells.ASAN_K; lia) (HC _ C1)) as Kcell.
  pose proof (rdword_cell B lyc _ UCells.GOT_CELL_K UCells.CELL_K ltac:(unfold UCells.CELL_K; lia) (HC _ C2)) as Kgot.
  rewrite <- cnoW_cell in Kcell, Kgot. rewrite <- cnoW_got in Kgot.
  pose proof (pa_val_range (A_OBJ 0)) as R0. pose proof (pa_val_range (A_OBJ 8)) as R8.
  pose proof (pa_obj_img 0 ltac:(lia)) as I0. pose proof (pa_obj_img 8 ltac:(lia)) as I8.
  rewrite restrict_mkst_fx.
  set (E := Eimg (Ereg regs [Z_to_bv 64 SB])).
  assert (E2 : ew E 2 = getr regs 2) by (unfold E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
  assert (E11 : ew E 11 = getr regs 11) by (unfold E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 11 11%bv eq_refl)).
  assert (E32 : ew E 32 = Z_to_bv 64 SB) by (unfold E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
  assert (EO0 : ew E (A_OBJ 0) = Z_to_bv 64 (VAL (A_OBJ 0))) by (unfold E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
  assert (EO8 : ew E (A_OBJ 8) = Z_to_bv 64 (VAL (A_OBJ 8))) by (unfold E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
  assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
  assert (Un : bv_unsigned (ew E 11) = n) by (rewrite E11, H11; unfold w64; apply unsigned_lit_small; lia).
  assert (USB : bv_unsigned (ew E 32) = SB) by (rewrite E32; apply unsigned_lit_small; unfold SB; lia).
  assert (UO0 : bv_unsigned (ew E (A_OBJ 0)) = VAL (A_OBJ 0)) by (rewrite EO0; apply unsigned_lit_small; lia).
  assert (UO8 : bv_unsigned (ew E (A_OBJ 8)) = VAL (A_OBJ 8)) by (rewrite EO8; apply unsigned_lit_small; lia).
  unfold ss_cno. apply pa_entry_st_ok_full.
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - unfold stack_region, got_regionP, bcell_regionP.
    repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    + rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
    + rewrite UO0. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 0)) 0 8 (SOff (A_OBJ 8) 0) (VAL (A_OBJ 8)));
        [ cbn [sv_denot]; rewrite EO8, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
        | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | cbn; lia |].
      rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) memc _ _ Kgot).
    + rewrite UO8. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 8)) 0 8 (SOff 32 0) SB);
        [ cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
        | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); unfold SB; lia | cbn; lia |].
      rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) memc _ _ Kcell).
  - apply pairwise_disjoint_of_extents. unfold stack_region, got_regionP, bcell_regionP, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. cbn [base_val].
    rewrite Usp, UO0, UO8.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    rewrite cnoW_got, cnoW_cell. unfold UCells.GOT_CELL_K, UCells.CELL_K.
    repeat split; lia.
  - split; [|split; [exact I | exact I]].
    cbn [cnoW_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite Usp, Un, USB.
    change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
    repeat match goal with |- _ /\ _ => split end; try exact I; unfold SB; lia.
Qed.

Ltac cno_awr Usp :=
  lazymatch goal with |- awr_ok ?Ex ?rsx ?stkx ?spx ?fpx ?b0x ?bcx ?lyx ?ownx =>
    let rs' := eval vm_compute in rsx in change (awr_ok Ex rs' stkx spx fpx b0x bcx lyx ownx) end;
  repeat first
  [ apply awr_ok_nil
  | apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia|]
  | eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 2%nat 0);
    [ reflexivity | rewrite Usp; lia | cbn [YP09.r_wlo]; unfold CNO.CNO_STK, CNO.CNO_FRAME, ASTACK; lia | cbn [YP09.r_whi]; lia |]
  ].
(* The same, when the regions also hold bytes of the two new blocks (P, m) and (Q, m). *)
Ltac cno_awr2 Usp P Q m HinP HfP HinQ HfQ Hreq :=
  lazymatch goal with |- awr_ok ?Ex ?rsx ?stkx ?spx ?fpx ?b0x ?bcx ?lyx ?ownx =>
    let rs' := eval vm_compute in rsx in change (awr_ok Ex rs' stkx spx fpx b0x bcx lyx ownx) end;
  repeat first
  [ apply awr_ok_nil
  | apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia|]
  | eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 2%nat 0);
    [ reflexivity | rewrite Usp; lia | cbn [YP09.r_wlo]; unfold CNO.CNO_STK, CNO.CNO_FRAME, ASTACK; lia | cbn [YP09.r_whi]; lia |]
  | eapply awr_ok_cons_gen;
    [ reflexivity | eassumption
    | cbn [YP09.r_wlo YP09.r_whi]; intros a Ha; right; right; left;
      first [ exists P, m; split; [exact HinP | split; [exact HfP | rewrite ?Hreq; lia]]
            | exists Q, m; split; [exact HinQ | split; [exact HfQ | rewrite ?Hreq; lia]] ]
    | ] ].

(* A run writes only the windows of its regions: a byte outside them keeps its view. *)
Lemma cnoW_run_keep : forall E rs H (m m' : word -> option byte) X n (V : Z -> option Z),
  frame_of E rs (mrestrict H m) (mrestrict H m') ->
  (forall i, 0 <= i < n -> 0 <= X + i < 2 ^ 64 /\ ~ in_wrange E rs (X + i)) ->
  (forall i, 0 <= i < n -> aview SEGS H m (X + i) = V i) ->
  forall i, 0 <= i < n -> aview SEGS H m' (X + i) = V i.
Proof.
  intros E rs H m m' X n V HF Hw HV i Hi. rewrite <- (HV i Hi). apply (aview_eq_of SEGS). apply HF.
  destruct (Hw i Hi) as [Hr Hn]. rewrite unsigned_lit_small by lia. exact Hn.
Qed.

(* A symbolic atom plus an offset, read as a word. *)
Lemma cnoW_den : forall E (k : nat) v z, ew E k = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> 0 <= v + z < 2 ^ 64 ->
  sv_denot E (SOff k z) = Z_to_bv 64 (v + z).
Proof.
  intros E k v z H Hv Hz. rewrite denot_lit_U, U_SOff, H, unsigned_lit_small by lia. rewrite zcanon_id by (unfold M64; lia).
  reflexivity.
Qed.
Lemma cnoW_den0 : forall E (k : nat), sv_denot E (SOff k 0) = ew E k.
Proof. intros E k. cbn [sv_denot]. rewrite Z.add_0_r. apply Z_to_bv_bv_unsigned. Qed.
Lemma cnoW_add_val : forall E (a b : nat) va vb, ew E a = Z_to_bv 64 va -> ew E b = Z_to_bv 64 vb ->
  0 <= va -> 0 <= vb -> va + vb < 2 ^ 64 -> sv_denot E (SAlu ALU_ADD (SOff a 0) (SOff b 0)) = Z_to_bv 64 (va + vb).
Proof.
  intros E a b va vb Ha Hb H1 H2 H3. rewrite denot_lit_U, U_SAlu. cbn [zalu_raw].
  rewrite !U_SOff, Ha, Hb, !unsigned_lit_small by lia. rewrite !Z.add_0_r.
  rewrite !(zcanon_id va), !(zcanon_id vb) by (unfold M64; lia). rewrite zcanon_id by (unfold M64; lia). reflexivity.
Qed.
Lemma cnoW_U0 : forall E (k : nat), U E (SOff k 0) = bv_unsigned (ew E k).
Proof.
  intros E k. rewrite U_SOff, Z.add_0_r. apply zcanon_id. pose proof (bv_unsigned_in_range 64 (ew E k)) as H.
  change (bv_modulus 64) with (2 ^ 64) in H. unfold M64. lia.
Qed.
Lemma cnoW_U : forall E (k : nat) v z, ew E k = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> 0 <= v + z < 2 ^ 64 ->
  U E (SOff k z) = v + z.
Proof.
  intros E k v z H Hv Hz. rewrite U_SOff, H, unsigned_lit_small by lia. apply zcanon_id. unfold M64. lia.
Qed.
(* An int, as a 64-bit word, is below 2^31 or at least 2^64 - 2^31. *)
Lemma cnoW_int_word : forall cur, INT_MIN <= cur <= INT_MAX ->
  bv_unsigned (w64 cur) < 2 ^ 31 \/ 2 ^ 64 - 2 ^ 31 <= bv_unsigned (w64 cur).
Proof.
  intros cur Hc. unfold w64. rewrite Z_to_bv_unsigned. unfold bv_wrap, INT_MIN, INT_MAX in *. change (bv_modulus 64) with (2 ^ 64).
  destruct (Z_lt_le_dec cur 0) as [Hneg|Hpos].
  - right. rewrite <- (Z.mod_add cur 1 (2 ^ 64)) by lia. rewrite Z.mod_small by lia. lia.
  - left. rewrite Z.mod_small by lia. lia.
Qed.
(* At a call whose s0 holds an int, the frame-pointer chain is empty (bad_next). *)
Lemma cnoW_chain_nil : forall ly rd (regsT : bvmap 5 word),
  4096 <= raZ regsT -> ly_top ly <= 2 ^ 47 -> alloc_ceiling <= spZ regsT <= 2 ^ 47 ->
  s0Z regsT < 2 ^ 31 \/ 2 ^ 64 - 2 ^ 31 <= s0Z regsT ->
  chain_pre ly rd regsT [].
Proof.
  intros ly rd regsT Hra Htop Hsp Hs0. pose proof asan_consts as (C1 & _).
  unfold chain_pre. split; [exact Hra|].
  destruct (frame0_ok ly regsT); [|reflexivity].
  replace (bad_next (spZ regsT) (ly_top ly) (s0Z regsT)) with true; [reflexivity|].
  symmetry. unfold bad_next. apply orb_true_iff. left. apply orb_true_iff.
  destruct Hs0 as [Hs0|Hs0]; [left; apply Z.leb_le; lia | right; apply Z.leb_le; lia].
Qed.
(* The tail free's trace: the free's pc followed by the entry context. *)
Lemma cnoW_trace_ctx : forall pc0 (regsT : bvmap 5 word) ch,
  call_trace0 pc0 regsT ch = uci_utrace pc0 (raZ regsT :: spine ch).
Proof.
  intros pc0 regsT ch. unfold call_trace0, unwind_of_chain, uci_utrace, spine. f_equal. f_equal.
  cbn [flat_map]. f_equal. induction ch as [|[[f ra] v] t IH]; cbn; [reflexivity | rewrite IH; reflexivity].
Qed.
(* Two blocks added, then removed: the blocks are the entry's again, up to order. *)
Lemma cnoW_perm2 : forall (L l1 l2 m1 m2 : list (Z * Z)) p q,
  l1 ++ p :: l2 = (L ++ [p]) ++ [q] -> m1 ++ q :: m2 = l1 ++ l2 -> Permutation (m1 ++ m2) L.
Proof.
  intros L l1 l2 m1 m2 p q H1 H2.
  assert (A : Permutation (l1 ++ l2) (L ++ [q])).
  { apply (Permutation_cons_inv (a := p)). transitivity (l1 ++ p :: l2); [apply Permutation_middle|].
    rewrite H1, <- app_assoc. cbn [app]. symmetry. apply Permutation_middle. }
  apply (Permutation_cons_inv (a := q)). transitivity (m1 ++ q :: m2); [apply Permutation_middle|].
  rewrite H2. transitivity (L ++ [q]); [exact A|]. symmetry. apply Permutation_cons_append.
Qed.
(* The trace of a call whose chain is empty, from the record's fixed trace (uci_utrace pc0 [ra]). *)
Lemma cnoW_trace_fix : forall pc0 ra (regsT : bvmap 5 word) (U : list (list Z)),
  raZ regsT = ra -> In (uci_utrace pc0 [ra]) U -> In (call_trace0 pc0 regsT []) U.
Proof.
  intros pc0 ra regsT U Hra H. rewrite call_trace_nil, Hra. unfold uci_utrace in H. cbn [flat_map app] in H.
  destruct (ra =? pc0); exact H.
Qed.

(* A fresh environment slot no part of the state names may be set. *)
Lemma cnoW_st_ok_ewset : forall E ss ms k w,
  st_ok_pi (@pa_segs _ uci_listing PI_uci) (@pa_val _ uci_listing PI_uci) E ss ms ->
  ss_atoms_p (fun m => negb (Nat.eqb m k)) ss = true ->
  st_ok_pi (@pa_segs _ uci_listing PI_uci) (@pa_val _ uci_listing PI_uci) (ewset E k w) ss ms.
Proof.
  intros E ss ms k w HS Hat. unfold st_ok_pi in *.
  eapply (st_ok_agree_p (fun m => negb (Nat.eqb m k))); [exact HS | | destruct ss; exact Hat].
  split; [|reflexivity]. intros m Hm. apply negb_true_iff, Nat.eqb_neq in Hm. apply ew_ewset_other. exact Hm.
Qed.
Lemma cnoW_img_env_ewset : forall E k w,
  img_env (@pa_val _ uci_listing PI_uci) A_LIM E -> (k < A_TEXT)%nat ->
  img_env (@pa_val _ uci_listing PI_uci) A_LIM (ewset E k w).
Proof. intros E k w HE Hk a Ha. rewrite ew_ewset_other by lia. exact (HE a Ha). Qed.
Lemma cnoW_set_reg : forall E ss ms (r : bv 5) e,
  st_ok_pi (@pa_segs _ uci_listing PI_uci) (@pa_val _ uci_listing PI_uci) E ss ms -> r <> 0%bv ->
  getr (ms_regs ms) r = sv_denot E e ->
  st_ok_pi (@pa_segs _ uci_listing PI_uci) (@pa_val _ uci_listing PI_uci) E
    (mkSS (ss_pc ss) (sr_set (ss_regs ss) r e) (ss_mem ss) (ss_resv ss) (ss_facts ss)) ms.
Proof.
  intros E ss ms r e HS Hr He. apply (st_ok_set_reg _ E _ ms r e HS Hr He).
Qed.

(* Move every slot fact  ew Eo k = v  of an older environment to the current one (the runs and calls only grow
   the environment above the slots these facts name). *)
Ltac cno_env HS :=
  let Ex := lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ => Ex | st_ok _ ?Ex _ _ => Ex end in
  repeat match goal with
  | H : ew ?Eo ?k = ?v |- _ =>
      lazymatch Eo with
      | Ex => fail
      | _ => let H2 := fresh "Ew" in
             assert (H2 : ew Ex k = v)
               by (repeat first [ rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia ]; exact H);
             clear H; rename H2 into H
      end
  end;
  repeat match goal with H : img_env _ _ ?Ey |- _ => lazymatch Ey with Ex => fail | _ => clear H end end.
(* A register's symbolic value, then its value from the slot facts. *)
Ltac cno_reg HS r Hr :=
  lazymatch type of HS with
  | st_ok_pi ?segs ?val ?E ?ss (restrict ?H ?ms) =>
    pose proof (st_ok_pi_restrict_reg H E ss ms r HS) as Hr;
    let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Hr;
    cbn [ms_regs restrict mkst] in Hr
  | st_ok ?segs ?E ?ss (restrict ?H ?ms) =>
    pose proof (st_ok_restrict_reg segs H E ss ms r HS) as Hr;
    let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Hr;
    cbn [ms_regs restrict mkst] in Hr
  end.
Ltac cno_regv HS r Hr :=
  cno_reg HS r Hr;
  lazymatch type of Hr with
  | _ = sv_denot ?Ex (SOff 240 ?z) =>
      let HEx := lazymatch goal with H : img_env _ _ Ex |- _ => H end in
      change (SOff 240 z) with (SOff A_TEXT z) in Hr; rewrite (codeptr_val Ex z HEx) in Hr
  | _ = sv_denot ?Ex (SOff ?k 0) =>
      rewrite cnoW_den0 in Hr; match goal with Hk : ew Ex k = _ |- _ => rewrite Hk in Hr end
  | _ = sv_denot ?Ex (SOff ?k ?z) =>
      match goal with Hk : ew Ex k = Z_to_bv 64 ?v |- _ => rewrite (cnoW_den Ex k v z Hk) in Hr by lia end
  | _ => idtac
  end.
(* Drop stale machine states, word lists and duplicate img_env facts; name the current machine state ms. *)
Ltac cno_tidy HS :=
  let m := lazymatch type of HS with
    | st_ok_pi _ _ _ _ (restrict _ ?m) => m | st_ok _ _ _ (restrict _ ?m) => m end in
  repeat match goal with
    | x : machine_state |- _ => lazymatch x with m => fail | _ => clear x end
    | x : list word |- _ => clear x
  end;
  repeat match goal with H1 : img_env ?a ?b ?c, H2 : img_env ?a ?b ?c |- _ => clear H2 end;
  try (is_var m; rename m into ms).
(* A byte outside every write window of a concrete region list. *)
Ltac cno_notwin :=
  let rg := fresh "rg" in let Hin := fresh "Hin" in let Hr := fresh "Hr" in
  unfold in_wrange; intros (rg & Hin & Hr);
  lazymatch type of Hin with In _ ?rsx => let rs' := eval vm_compute in rsx in change (In rg rs') in Hin end;
  cbn [In] in Hin;
  repeat (destruct Hin as [Hin | Hin]; [subst rg; cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi] in Hr | ]);
  try contradiction;
  repeat match goal with Hb : bv_unsigned (ew ?Ey ?k) = _ |- _ =>
    match type of Hr with context [bv_unsigned (ew Ey k)] => rewrite Hb in Hr end end;
  lia.
(* Carry a content fact  forall i, 0 <= i < n -> aview .. m (X + i) = V i  over a run (its frame fact HFr). *)
Ltac cno_keepC HFr CP :=
  lazymatch type of CP with
  | forall i, 0 <= i < ?nn -> aview ?sg ?Hh ?m (?X + i) = @?V i =>
    lazymatch type of HFr with frame_of ?Ex ?rsx (mrestrict _ m) (mrestrict _ ?m') =>
      let CP2 := fresh "CPx" in
      assert (CP2 : forall i, 0 <= i < nn -> aview sg Hh m' (X + i) = V i);
      [ apply (cnoW_run_keep Ex rsx Hh m m' X nn V HFr); [intros i Hi; split; [lia | cno_notwin] | exact CP]
      | clear CP; rename CP2 into CP; cbv beta in CP ] end end.
Ltac cno_usp HS E2 :=
  let Ex := lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ => Ex | st_ok _ ?Ex _ _ => Ex end in
  repeat match goal with H : bv_unsigned (ew ?Ey _) = _ |- _ => lazymatch Ey with Ex => fail | _ => clear H end end;
  try (match goal with H : bv_unsigned (ew Ex 2) = spZ _ |- _ => clear H end);
  assert (Usp : bv_unsigned (ew Ex 2) = spZ _) by (rewrite E2; apply unsigned_lit_small; lia);
  try (match goal with H : ew Ex 104 = Z_to_bv 64 ?v |- _ =>
         assert (Ub104 : bv_unsigned (ew Ex 104) = v) by (rewrite H; apply unsigned_lit_small; lia) end);
  try (match goal with H : ew Ex 105 = Z_to_bv 64 ?v |- _ =>
         assert (Ub105 : bv_unsigned (ew Ex 105) = v) by (rewrite H; apply unsigned_lit_small; lia) end).
Ltac cno_norm HS := lazymatch type of HS with st_ok_pi ?sg ?vl ?Ex ?ss3 ?msx =>
  let v := eval vm_compute in ss3 in change (st_ok_pi sg vl Ex v msx) in HS end.
Ltac cno_shok HS :=
  try (match goal with H : sh_ok _ _ _ _ _ |- _ => clear H end);
  lazymatch type of HS with st_ok_pi ?sg _ ?Ex _ (restrict (w_H ?Wx) ?msx) =>
    assert (SHOK : sh_ok sg (SOff 32 0) [] Ex (mrestrict (w_H Wx) (ms_mem msx))) by apply Forall_nil end.

(* A block a call adds is not among the blocks before it (the blocks of an AR state are pairwise disjoint). *)
Lemma cnoW_fresh : forall ly S (W : world SEGS) mem md (bl : list (Z * Z)) b,
  AR SEGS B ly S W mem md -> ablocks B ly S = bl ++ [b] -> 0 <= snd b -> ~ In b bl.
Proof.
  intros ly S W mem md bl b HAR Hbl Hn Hin. apply in_split in Hin as (l1 & l2 & Hl).
  pose proof (sep_blocks_pos SEGS B LAWS ly S W mem md b b l1 l2 [] HAR) as Hd.
  rewrite Hbl, Hl, <- app_assoc in Hd. cbn [app] in Hd. specialize (Hd eq_refl).
  unfold zdisjoint, block_rng in Hd. cbn [fst snd] in Hd. pose proof (req_size_pos (snd b) Hn). lia.
Qed.

Section Walk.
Hypothesis ML : ameter_laws MT.
Hypothesis MALPC : pc_wrap_malloc (as_code B) = uci_sigma US___interceptor_trampoline_malloc.
Hypothesis FREEPC : pc_wrap_free (as_code B) = uci_sigma US___interceptor_trampoline_free.
Hypothesis ROU : uci_ro_rd_unowned B.
Hypothesis ROE : uci_rom_no_errno B.
Hypothesis UFIX : CNO.uci_cno_ufix B.
Hypothesis AM : forall fx' : YK11.FPState, @amalloc04_rule fx' rc AE2k.tfib_sink_head tfibsegs B MT.
Hypothesis AF : forall fx' : YK11.FPState, @afree04_rule fx' rc AE2k.tfib_sink_head tfibsegs B MT.
Hypothesis AMC : forall fx' : YK11.FPState, @aintrin_realizes fx' rc tfibsegs B OCpy (uci_sigma US___asan_memcpy).
Hypothesis RUI : forall fx' : YK11.FPState, @PR.uci_rp_uci_int_cg fx' rc B (uci_sigma US_rp_uci_int).

(* The reply bytes the rp_uci_int contract asks, at a copy whose bytes view as the source's. *)
Lemma cnoW_garr8_move : forall H H' (m m' : word -> option byte) a a' (l : list Z),
  (forall i, 0 <= i < Z.of_nat (length l) -> aview SEGS H' m' (a' + i) = aview SEGS H m (a + i)) ->
  garr8 SEGS (mrestrict H m) a l -> garr8 SEGS (mrestrict H' m') a' l.
Proof.
  intros H H' m m' a a' l Hv Hg j Hj. destruct (Hg j Hj) as [Hm Hr]. split; [|exact Hr].
  intros k Hk. assert (k = 0%nat) as -> by lia. specialize (Hm 0%nat Hk). rewrite <- Hm.
  pose proof (Hv (Z.of_nat j) ltac:(lia)) as E. unfold aview in E. cbn [Z.of_nat]. rewrite !Z.add_0_r.
  destruct (mbyte SEGS (mrestrict H' m') (a' + Z.of_nat j)) as [b'|],
           (mbyte SEGS (mrestrict H m) (a + Z.of_nat j)) as [b|]; cbn in E; try discriminate; [|reflexivity].
  injection E as E. f_equal. apply bv_eq. exact E.
Qed.

(* musl memchr's constant window, read through a journal from an entry state whose read-only view is the image's. *)
Lemma cnoW_consts : forall STK sp0 ly S (W0 : world SEGS) mem0 md0 own ly' S' W' mem' md' k,
  ajournal SEGS B STK sp0 [] ly S W0 mem0 md0 own ly' S' W' mem' md' k ->
  uci_ro_rd_unowned B -> uci_rom_no_errno B -> uci_rom_view_rd W0 mem0 ->
  consts_view SEGS PR.UCI_MC_LO PR.UCI_MC_HI W' mem'.
Proof.
  intros STK sp0 ly S W0 mem0 md0 own ly' S' W' mem' md' k HJ HO HE HV a Ha.
  pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F3 & _).
  assert (Hrd : uci_in_ro_rd a) by (unfold uci_in_ro_rd, UCI_RO_RD; apply Exists_cons_tl, Exists_cons_hd;
    unfold in_zr, PR.UCI_MC_LO, PR.UCI_MC_HI in *; cbn [fst snd]; lia).
  destruct (uci_ro_rd_scoped B HO HE a Hrd) as [Hno He].
  destruct (uci_ro_rd_rom_clean a Hrd) as [(sg & Hin & _ & Hr) _].
  rewrite (F3 a ltac:(exists sg; split; [exact Hin | exact Hr]) Hno He (fp_spares_closed [] a sink_closed_nil)).
  exact (HV a Hrd).
Qed.

(* rp_uci_int's realizes-form contract, carried through a journal (aj_intrin_at's shape): the call writes only its
   stack window, at the same AR state. *)
Lemma cnoW_rui_at : forall (W : world SEGS) regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k
    (rr nn cc : Z) (bs : list byte) (o : Z) raw,
  ajournal SEGS B STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k ->
  spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> PR.RUI_STK - o <= STK ->
  getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) -> getr regsT 1 = raw -> YK0s.ret_ok raw ->
  getr regsT 10 = w64 rr -> getr regsT 11 = w64 nn -> getr regsT 12 = w64 cc ->
  0 <= nn <= PR.REPLY_MAX -> Z.of_nat (length bs) = nn -> INT_MIN <= cc <= INT_MAX -> 0 < rr -> rr + nn <= 2 ^ 63 ->
  garr8 SEGS (mrestrict (w_H W) memT) rr (map (fun b : byte => bv_unsigned b) bs) ->
  (forall x, rr <= x < rr + nn -> aview SEGS (w_H W) memT x <> None /\ ~ (sp0 + o - PR.RUI_STK <= x < sp0 + o)) ->
  amem_range rr nn ->
  range_addressable (aview SEGS (w_H W) memT) SHADOW_OFF rr nn ->
  (0 < nn -> shadow_hull_vis (aview SEGS (w_H W) memT) rr nn) ->
  consts_view SEGS PR.UCI_MC_LO PR.UCI_MC_HI W memT ->
  SRr SEGS W (mkCfg (mkst regsT (Z_to_bv 64 (uci_sigma US_rp_uci_int)) memT (seg_rom SEGS)) mdc)
    (fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
       c2 = mkCfg (mkst regs2 raw mem2 (seg_rom SEGS)) md2 /\
       ajournal SEGS B STK sp0 FP ly S W0 mem md own lyc Sc W mem2 md2 k /\
       aregs_preserved regsT regs2 /\ getr regs2 10 = w64 (rp_uci_int_m (PR.PRc.zbytes bs) cc) /\
       (forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 + o - PR.RUI_STK <= a < sp0 + o) ->
          aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) memT a) /\
       (forall a, apresent (w_H W) memT a -> apresent (w_H W) mem2 a)).
Proof.
  intros W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k rr nn cc bs o raw HJ Hsp Hal Hneg Hbud Hgp Htp Hra Hraw
    H10 H11 H12 Hnn Hlen Hcc Hr0 Hrn Hg Hvis Hamr Hrng Hhull Hcv.
  pose proof HJ as (HAR & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk & _ & _ & _ & _ & _ & Hpres & Hstatic & F5 & HQT).
  pose proof Hstatic as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
  pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Eslo & Eshi & _).
  assert (Hrs : PR.RUI_STK = 4144) by reflexivity. assert (ESTACK = 4096) as Hes by reflexivity.
  pose proof asan_consts as (C1 & _).
  assert (HPRE : ecall_pre SEGS B lyc Sc W regsT memT mdc).
  { eapply (ecall_pre_at SEGS B STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k regsT o HJ Hsp Hal Hneg);
      [lia | rewrite Hra; exact Hraw | exact Hgp | exact Htp]. }
  eapply SRr_mono.
  { apply (RUI fx lyc Sc W regsT memT mdc rr nn cc bs HPRE); try assumption.
    - rewrite Eslo, Hsp. lia.
    - intros x Hx. apply Hpres. lia.
    - intros x Hx. rewrite Hsp. exact (Hvis x Hx). }
  cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HAR2 & HP & Hsame & Hres & Hfr & Hpres2).
  rewrite Hsp in Hfr.
  split; [reflexivity|]. exists regs2, mem2, md2.
  split; [unfold cfg_at, raZ; rewrite Hra; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity|].
  split.
  { eapply (ajournal_after_write SEGS B LAWS pa_segs_low STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k mem2 md2
      (fun a => sp0 + o - PR.RUI_STK <= a < sp0 + o) Sc own HJ).
    - intros a Ha Hna. exact (Hfr a Ha Hna).
    - exact Hpres2.
    - exact Hsame.
    - intros a Ha. left. left. lia.
    - exact HAR2.
    - reflexivity. - reflexivity. - lia. - exact Hfrs. - exact HQT. }
  split; [exact HP|]. split; [exact Hres|]. split; [exact Hfr | exact Hpres2].
Qed.

Lemma cnoW_walk : forall (W : world SEGS) (regs : bvmap 5 word) (memc : word -> option byte) lyc Sc mdc
    (r n cur T : Z) (bs : list byte) ch (CTX : list (list Z)),
  ajournal SEGS B CNO.CNO_STK (spZ regs) [] lyc Sc W memc mdc [] lyc Sc W memc mdc 0 ->
  YK0s.ret_ok (getr regs 1) -> 4096 <= raZ regs ->
  getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
  getr regs 10 = w64 r -> getr regs 11 = w64 n -> getr regs 12 = w64 cur ->
  achain lyc (aview SEGS (w_H W) memc) (spZ regs) (s0Z regs) ch -> CNO.uci_cno_uctx B CTX ->
  In (raZ regs :: spine ch) CTX ->
  INT_MIN <= cur <= INT_MAX -> 0 <= n <= PR.REPLY_MAX -> Z.of_nat (length bs) = n ->
  (0 < n -> exists bA nA, In (bA, nA) (ablocks B lyc Sc) /\ bA <= r /\ r + n <= bA + nA) ->
  garr8 SEGS (mrestrict (w_H W) memc) r (map (fun b : byte => bv_unsigned b) bs) ->
  uci_rom_view_rd W memc ->
  st_nev Sc + CNO.CNO_EV <= EV_MAX -> blocks_bytes Sc + CNO.CNO_LIVE <= LIVE_MAX ->
  mo_ok MT Sc T -> CNO.uci_cno_cost MT n <= T ->
  SRr SEGS W (cfg_at SEGS (BASE + AF_check_no_overread) regs memc mdc)
    (fun W2 c2 => exists ly2 S2 regs2 mem2 md2,
       c2 = mkCfg (mkst regs2 (getr regs 1) mem2 (seg_rom SEGS)) md2 /\
       ajournal SEGS B CNO.CNO_STK (spZ regs) [] lyc Sc W memc mdc [] ly2 S2 W2 mem2 md2 CNO.CNO_EV /\
       aregs_preserved regs regs2 /\
       Permutation (ablocks B ly2 S2) (ablocks B lyc Sc) /\
       mo_le MT Sc S2 (CNO.uci_cno_cost MT n)).
Proof.
  intros W regs memc lyc Sc mdc r n cur T bs ch CTX HJ Hra Hra4 Hgp Htp H10 H11 H12 Hch HUCTX HCTX Hcur Hn Hlen
    Hblk Hbytes Hrom Hev Hlive Hmo Hcost.
  pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
  pose proof Hstk as (Hal16 & _ & Hceil & Hslo & Hshi & H47 & Hbot & Htop1 & Htop2).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  assert (HSTK : CNO.CNO_STK = 16448) by reflexivity.
  assert (HRM : PR.REPLY_MAX = 255) by reflexivity.
  assert (Hsp : 2 ^ 46 <= spZ regs <= 2 ^ 47) by lia.
  pose proof (cnoW_entry W regs memc lyc Sc mdc n HAR
    ltac:(intros a Ha; apply Hpres; lia) Hsp Hal16 H11 ltac:(lia)) as HS.
  remember (Eimg (Ereg regs [Z_to_bv 64 SB])) as E eqn:HE.
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  assert (EL : forall k, (k < A_TEXT)%nat -> ew E k = ew (Ereg regs [Z_to_bv 64 SB]) k)
    by (intros k Hk; subst E; apply Eimg_low; exact Hk).
  assert (E1 : ew E 1 = getr regs 1) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 1 1%bv eq_refl)).
  assert (E2 : ew E 2 = Z_to_bv 64 (spZ regs))
    by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl); symmetry; apply Z_to_bv_bv_unsigned).
  assert (E3 : ew E 3 = w64 (as_gp B)) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 3 3%bv eq_refl); exact Hgp).
  assert (E4 : ew E 4 = w64 (as_tp B)) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 4 4%bv eq_refl); exact Htp).
  assert (E10 : ew E 10 = Z_to_bv 64 r) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
  assert (E11 : ew E 11 = Z_to_bv 64 n) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl); exact H11).
  assert (E8 : ew E 8 = getr regs 8) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 8 8%bv eq_refl)).
  assert (E12 : ew E 12 = Z_to_bv 64 cur) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 12 12%bv eq_refl); exact H12).
  assert (E32 : ew E 32 = Z_to_bv 64 SB) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
  assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; apply unsigned_lit_small; lia).
  assert (HAE : env_agree 32 (Ereg regs [Z_to_bv 64 SB]) E)
    by (split; [intros k Hk; apply EL; unfold A_TEXT; lia | subst E; reflexivity]).
  clear HE EL.
  assert (SHOK : sh_ok SEGS (SOff 32 0) [] E (mrestrict (w_H W) memc)) by constructor.
  unfold cfg_at. change (w64 (BASE + AF_check_no_overread)) with (Z_to_bv 64 (BASE + AF_check_no_overread)).
  (* 1. +0x00 .. +0x40: the prologue, s0 = cur, s1 = n, s4 = r, s5 = the shadow base, s3 = a0 = n + 1; malloc. *)
  paj_run_tok RUN HS HJ SHOK Bspan; [cno_awr Usp |].
  clear HF HFr HG.
  cno_regv HS (10%bv : bv 5) Ra0. cno_regv HS (1%bv : bv 5) Rra. cno_regv HS (2%bv : bv 5) Rsp1.
  cno_regv HS (3%bv : bv 5) Qgp. cno_regv HS (4%bv : bv 5) Qtp. cno_regv HS (8%bv : bv 5) Rs0.
  assert (Qa0 : getr (ms_regs ms) 10 = w64 (n + 1)) by exact Ra0.
  assert (Qsp : spZ (ms_regs ms) = spZ regs + -64) by (unfold spZ at 1; rewrite Rsp1; apply unsigned_lit_small; lia).
  assert (Qraz : raZ (ms_regs ms) = BASE + 600) by (unfold raZ; rewrite Rra; apply unsigned_lit_small; rewrite cnoW_base; lia).
  assert (Qs0 : s0Z (ms_regs ms) = bv_unsigned (w64 cur)) by (unfold s0Z; rewrite Rs0; reflexivity).
  assert (Qch : chain_pre lyc (aview SEGS (w_H W) (ms_mem ms)) (ms_regs ms) [])
    by (apply cnoW_chain_nil; [rewrite Qraz, cnoW_base; lia | lia | rewrite Qsp; lia | rewrite Qs0; exact (cnoW_int_word cur Hcur)]).
  assert (Qtr : In (call_trace0 (pc_malloc_ra0 (as_code B)) (ms_regs ms) []) (as_universe B))
    by (apply (cnoW_trace_fix _ CNO.UCI_CNO_RA_MALLOC1); [rewrite Qraz, cnoW_base; reflexivity | exact (proj1 UFIX)]).
  pmkst HS.
  change (pa_sigma US___interceptor_trampoline_malloc) with (uci_sigma US___interceptor_trampoline_malloc).
  rewrite <- MALPC.
  eapply SRr_bind.
  { eapply (AM fx W (ms_regs ms) (ms_mem ms) CNO.CNO_STK (spZ regs) [] lyc Sc W memc mdc [] lyc Sc _ 0 (n + 1) (-64)
      (Z_to_bv 64 (BASE + 600)) [] HJ Qa0);
      [ unfold MALLOC_MAX; lia | unfold CNO.CNO_LIVE in Hlive; lia | exact Qsp | reflexivity | lia
      | rewrite HSTK; unfold ASTACK; lia | exact Qgp | exact Qtp | exact Rra | apply ret_ok_codeptr_v; [lia | reflexivity]
      | unfold CNO.CNO_EV in Hev; lia | exact Qch | exact Qtr
      | apply (mo_ok_le MT ML Sc _ T Hmo); unfold CNO.uci_cno_cost in Hcost;
        pose proof (mo_malloc_nonneg MT ML (n + 1) ltac:(lia)); pose proof (mo_free_nonneg MT ML); lia ]. }
  intros W1 c1 HW1 (ly1 & S1 & regs1 & mem1 & md1 & P & -> & HJ1 & HP1 & HR1 & Hfr1 & HP4096 & Hbl1 & HK1 & MLE1).
  clear Ra0 Rra Rsp1 Rs0 Qa0 Qsp Qgp Qtp Qraz Qs0 Qch Qtr.
  (* 2. Back from malloc at +0x44 with a0 = P: the frame is kept (acall_kept), P a new block of n + 1 bytes. *)
  pose proof HJ1 as (HAR1 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HJ1pres & _).
  jafter_call_keep_pi HS 40%nat regs1 (mrestrict (w_H W1) mem1) HP1 [0%nat] HS2.
  match type of HS2 with ?tq -> _ => assert (HRK : tq) end.
  { cbn [ms_mem restrict]. apply Forall_cons; [|apply Forall_nil].
    split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite Usp; intros a Ha;
      [ apply (mbyte_of_aview SEGS); apply (proj1 HK1); [lia | lia]
      | intros _; apply (apresent_writable SEGS); apply HJ1pres; lia ]. }
  specialize (HS2 HRK). clear HS HRK. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
  assert (EP : ew (havoc E 40 (map (getr regs1) CLOB)) 44 = Z_to_bv 64 P) by (cbn [ew havoc]; exact HR1).
  assert (HEI1 : img_env VAL A_LIM (havoc E 40 (map (getr regs1) CLOB))) by (apply img_env_havoc; [exact HEI | cbv; lia]).
  cno_env HS. cno_usp HS E2. cno_shok HS.
  assert (HfP : ~ In (P, n + 1) (ablocks B lyc Sc)) by (eapply cnoW_fresh; [exact HAR1 | exact Hbl1 | cbn; lia]).
  clear HK1 HP1 HJ HW1. try clear ms.
  (* 3. +0x44 .. +0x4c: s2 = P, a0 = n + 1; the second malloc (n + 1). *)
  paj_run_tok RUN HS HJ1 SHOK Bspan; [cno_awr Usp |].
  clear HF HFr HG. cno_env HS. cno_usp HS E2. cno_tidy HS.
  cno_regv HS (10%bv : bv 5) Ra0. cno_regv HS (1%bv : bv 5) Rra. cno_regv HS (2%bv : bv 5) Rsp1.
  cno_regv HS (3%bv : bv 5) Qgp. cno_regv HS (4%bv : bv 5) Qtp. cno_regv HS (8%bv : bv 5) Rs0.
  assert (Qa0 : getr (ms_regs ms) 10 = w64 (n + 1)) by exact Ra0.
  assert (Qsp : spZ (ms_regs ms) = spZ regs + -64) by (unfold spZ at 1; rewrite Rsp1; apply unsigned_lit_small; lia).
  assert (Qraz : raZ (ms_regs ms) = BASE + 612) by (unfold raZ; rewrite Rra; apply unsigned_lit_small; rewrite cnoW_base; lia).
  assert (Qs0 : s0Z (ms_regs ms) = bv_unsigned (w64 cur)) by (unfold s0Z; rewrite Rs0; reflexivity).
  pose proof HJ1 as (_ & Hly1 & _ & _ & _ & _ & Hnev1 & _).
  assert (Htop1' : ly_top ly1 = ly_top lyc) by (destruct Hly1 as (_ & _ & _ & _ & _ & _ & _ & _ & Et & _); exact Et).
  assert (Qch : chain_pre ly1 (aview SEGS (w_H W1) (ms_mem ms)) (ms_regs ms) [])
    by (apply cnoW_chain_nil; [rewrite Qraz, cnoW_base; lia | lia | rewrite Qsp; lia | rewrite Qs0; exact (cnoW_int_word cur Hcur)]).
  assert (Qtr : In (call_trace0 (pc_malloc_ra0 (as_code B)) (ms_regs ms) []) (as_universe B))
    by (apply (cnoW_trace_fix _ CNO.UCI_CNO_RA_MALLOC2); [rewrite Qraz, cnoW_base; reflexivity | exact (proj1 (proj2 UFIX))]).
  assert (Qbb : blocks_bytes S1 = blocks_bytes Sc + (n + 1))
    by (rewrite (blocks_bytes_bsum B ly1 S1), (blocks_bytes_bsum B lyc Sc), Hbl1, bsum_app; cbn [bsum fold_right snd]; lia).
  pmkst HS.
  change (pa_sigma US___interceptor_trampoline_malloc) with (uci_sigma US___interceptor_trampoline_malloc).
  rewrite <- MALPC.
  eapply SRr_bind.
  { eapply (AM fx W1 (ms_regs ms) (ms_mem ms) CNO.CNO_STK (spZ regs) [] lyc Sc W memc mdc [] ly1 S1 _ 1 (n + 1) (-64)
      (Z_to_bv 64 (BASE + 612)) [] HJ1 Qa0);
      [ unfold MALLOC_MAX; lia | unfold CNO.CNO_LIVE in Hlive; lia | exact Qsp | reflexivity | lia
      | rewrite HSTK; unfold ASTACK; lia | exact Qgp | exact Qtp | exact Rra | apply ret_ok_codeptr_v; [lia | reflexivity]
      | unfold CNO.CNO_EV in Hev; lia | exact Qch | exact Qtr
      | apply (mok_station MT Sc S1 T (mo_malloc MT (n + 1)) (mo_malloc MT (n + 1)) ML Hmo MLE1);
        unfold CNO.uci_cno_cost in Hcost;
        pose proof (mo_malloc_nonneg MT ML (n + 1) ltac:(lia)); pose proof (mo_free_nonneg MT ML); lia ]. }
  intros W2 c2 HW2 (ly2 & S2 & regs2 & mem2 & md2 & Q & -> & HJ2 & HP2 & HR2 & Hfr2 & HQ4096 & Hbl2 & HK2 & MLE2).
  clear Ra0 Rra Rsp1 Rs0 Qa0 Qsp Qgp Qtp Qraz Qs0 Qch Qtr.
  (* 4. Back from the second malloc at +0x50 with a0 = Q. *)
  pose proof HJ2 as (HAR2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HJ2pres & _).
  jafter_call_keep_pi HS 56%nat regs2 (mrestrict (w_H W2) mem2) HP2 [0%nat] HS2.
  match type of HS2 with ?tq -> _ => assert (HRK : tq) end.
  { cbn [ms_mem restrict]. apply Forall_cons; [|apply Forall_nil].
    split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite Usp; intros a Ha;
      [ apply (mbyte_of_aview SEGS); apply (proj1 HK2); [lia | lia]
      | intros _; apply (apresent_writable SEGS); apply HJ2pres; lia ]. }
  specialize (HS2 HRK). clear HS HRK. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
  lazymatch type of HS with st_ok_pi _ _ (havoc ?Eo 56 ?ws) _ _ =>
    assert (EQ : ew (havoc Eo 56 ws) 60 = Z_to_bv 64 Q) by (cbn [ew havoc]; exact HR2);
    assert (HEI2 : img_env VAL A_LIM (havoc Eo 56 ws)) by (apply img_env_havoc; [assumption | cbv; lia]) end.
  cno_env HS. cno_usp HS E2. cno_shok HS.
  assert (HfQ1 : ~ In (Q, n + 1) (ablocks B ly1 S1)) by (eapply cnoW_fresh; [exact HAR2 | exact Hbl2 | cbn; lia]).
  assert (HfQ : ~ In (Q, n + 1) (ablocks B lyc Sc)) by (intros H; apply HfQ1; rewrite Hbl1; apply in_or_app; left; exact H).
  assert (HinP : In (P, n + 1) (ablocks B ly2 S2))
    by (rewrite Hbl2, Hbl1; apply in_or_app; left; apply in_or_app; right; left; reflexivity).
  assert (HinQ : In (Q, n + 1) (ablocks B ly2 S2)) by (rewrite Hbl2; apply in_or_app; right; left; reflexivity).
  assert (HPQ : (P, n + 1) <> (Q, n + 1)) by (intros Heq; apply HfQ1; rewrite <- Heq, Hbl1; apply in_or_app; right; left; reflexivity).
  assert (Hreq : req_size (n + 1) = n + 1) by (unfold req_size; destruct (Z.eqb_spec (n + 1) 0); lia).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR2 HinP) as (_ & HP0 & HPc & HPapp & HPpres & _).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR2 HinQ) as (_ & HQ0 & HQc & HQapp & HQpres & _).
  rewrite Hreq in HPc, HPapp, HPpres, HQc, HQapp, HQpres.
  pose proof (sep_blocks SEGS B LAWS _ _ _ _ _ _ _ _ _ HAR2 HinP HinQ HPQ) as HdPQ.
  unfold zdisjoint in HdPQ. cbn [fst snd] in HdPQ. rewrite Hreq in HdPQ.
  clear HK2 HP2 HJ1 HW2. try clear ms.
  (* 5. +0x50 beqz s2 and +0x58 beqz a0: P and Q are not NULL (4096 <= P, Q). +0x5c beqz s1: n = 0 or not. *)
  psrr_branch_tok RUN BR HS SHOK Bspan.
  1: { exfalso. rewrite branch_eq_U, U_lit in Hc by lia. rewrite (cnoW_U _ 44 P 0 EP) in Hc by lia.
       apply Z.eqb_eq in Hc. lia. }
  clear Hc.
  paj_run_tok RUN HS HJ2 SHOK Bspan; [cno_awr Usp |].
  clear HF HFr HG. cno_env HS. cno_usp HS E2. cno_shok HS. cno_tidy HS.
  psrr_branch_tok RUN BR HS SHOK Bspan.
  1: { exfalso. rewrite branch_eq_U, U_lit in Hc by lia. rewrite (cnoW_U _ 60 Q 0 EQ) in Hc by lia.
       apply Z.eqb_eq in Hc. lia. }
  clear Hc.
  paj_run_tok RUN HS HJ2 SHOK Bspan; [cno_awr Usp |].
  clear HF HFr HG. cno_env HS. cno_usp HS E2. cno_shok HS. cno_tidy HS.
  psrr_branch_tok RUN BR HS SHOK Bspan.
  all: rewrite branch_eq_U, U_lit in Hc by lia; rewrite (cnoW_U _ 11 n 0 E11) in Hc by lia.
  1: shelve.
  (* 6. n <> 0: +0x60 .. +0x6c, memcpy (P, r, n) (__asan_memcpy, aj_intrin_at). *)
  apply Z.eqb_neq in Hc. rewrite Z.add_0_r in Hc.
  destruct (Hblk ltac:(lia)) as (bA & nA & HinA & HbA & HrA).
  assert (HinA2 : In (bA, nA) (ablocks B ly2 S2)) by (rewrite Hbl2, Hbl1; apply in_or_app; left; apply in_or_app; left; exact HinA).
  assert (HAP : (bA, nA) <> (P, n + 1)) by (intros Heq; apply HfP; rewrite <- Heq; exact HinA).
  assert (HAQ : (bA, nA) <> (Q, n + 1)) by (intros Heq; apply HfQ; rewrite <- Heq; exact HinA).
  pose proof (sep_blocks SEGS B LAWS _ _ _ _ _ _ _ _ _ HAR2 HinA2 HinP HAP) as HdAP.
  pose proof (sep_blocks SEGS B LAWS _ _ _ _ _ _ _ _ _ HAR2 HinA2 HinQ HAQ) as HdAQ.
  unfold zdisjoint in HdAP, HdAQ. cbn [fst snd] in HdAP, HdAQ. rewrite Hreq in HdAP, HdAQ.
  destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR2 HinA2) as (_ & HA0 & HAc & HAapp & HApres & _).
  pose proof (req_size_pos nA ltac:(lia)) as HnA.
  paj_run_tok RUN HS HJ2 SHOK Bspan; [cno_awr Usp |].
  clear HF HFr HG. cno_env HS. cno_usp HS E2. cno_tidy HS.
  cno_regv HS (10%bv : bv 5) Ra0. cno_regv HS (11%bv : bv 5) Ra1. cno_regv HS (12%bv : bv 5) Ra2.
  cno_regv HS (1%bv : bv 5) Rra. cno_regv HS (2%bv : bv 5) Rsp1.
  cno_regv HS (3%bv : bv 5) Qgp. cno_regv HS (4%bv : bv 5) Qtp.
  assert (Qsp : spZ (ms_regs ms) = spZ regs + -64) by (unfold spZ at 1; rewrite Rsp1; apply unsigned_lit_small; lia).
  pmkst HS.
  change (pa_sigma US___asan_memcpy) with (uci_sigma US___asan_memcpy).
  eapply SRr_bind.
  { eapply (aj_intrin_at SEGS B LAWS pa_segs_low OCpy (uci_sigma US___asan_memcpy) (AMC fx) W2 (ms_regs ms) (ms_mem ms)
      CNO.CNO_STK (spZ regs) [] lyc Sc W memc mdc [] ly2 S2 _ 2 P r n (-64) (Z_to_bv 64 (BASE + 644)) HJ2 Ra0 Ra1 Ra2);
      [ lia | lia | lia | exact Qsp | reflexivity | lia | rewrite HSTK; unfold ESTACK; lia | exact Qgp | exact Qtp | exact Rra
      | apply ret_ok_codeptr_v; [lia | reflexivity]
      | intros a Ha; split;
        [ right; right; left; exists P, (n + 1); split; [exact HinP | split; [exact HfP | rewrite ?Hreq; lia]]
        | unfold ESTACK; lia ]
      | eapply (amem_range_of_block SEGS B LAWS _ _ _ _ _ _ _ _ _ (proj1 HJ2) HinP); rewrite ?Hreq; lia
      | eapply (range_addressable_of_block SEGS B LAWS _ _ _ _ _ _ _ _ _ (proj1 HJ2) HinP); rewrite ?Hreq; lia
      | intros Hn0; eapply (shadow_hull_vis_of_block SEGS B LAWS _ _ _ _ _ _ _ _ _ (proj1 HJ2) HinP); rewrite ?Hreq; lia
      | split; [lia|]; split; [lia|]; split;
        [ intros a Ha; split;
          [ apply (aview_some_of_apresent SEGS);
            destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ (proj1 HJ2) HinA2) as (_ & _ & _ & _ & Hp & _);
            exact (proj1 (Hp a ltac:(lia)))
          | unfold ESTACK; lia ]
        | split; [lia|]; split;
          [ eapply (amem_range_of_block SEGS B LAWS _ _ _ _ _ _ _ _ _ (proj1 HJ2) HinA2); lia
          | split;
            [ eapply (range_addressable_of_block SEGS B LAWS _ _ _ _ _ _ _ _ _ (proj1 HJ2) HinA2); lia
            | intros Hn0; eapply (shadow_hull_vis_of_block SEGS B LAWS _ _ _ _ _ _ _ _ _ (proj1 HJ2) HinA2); lia ] ] ] ]. }
  intros W3 c3 _ (-> & regs3 & mem3 & md3 & -> & HJ3 & HP3 & HR3 & Hcp3 & Hkeep3 & Hpres3).
  (* 7. Back from memcpy at +0x70: [P, P + n) holds the reply bytes. *)
  pose proof HJ2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & G2 & _).
  assert (CP : forall i, 0 <= i < n -> aview SEGS (w_H W2) mem3 (P + i) = aview SEGS (w_H W) memc (r + i)).
  { intros i Hi. rewrite (Hcp3 i Hi). replace (r + i) with (bA + (r + i - bA)) by lia.
    apply (G2 bA nA (r + i - bA) HinA HinA2); [lia | intros (rg & Hrg & _); destruct Hrg]. }
  clear G2 Hcp3.
  pose proof HJ3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HJ3pres & _).
  jafter_call_keep_pi HS 72%nat regs3 (mrestrict (w_H W2) mem3) HP3 [0%nat] HS2.
  match type of HS2 with ?tq -> _ => assert (HRK : tq) end.
  { cbn [ms_mem restrict]. apply Forall_cons; [|apply Forall_nil].
    split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite Usp; intros a Ha;
      [ apply (mbyte_of_aview SEGS); apply Hkeep3; [lia | lia | unfold ESTACK; lia]
      | intros _; apply (apresent_writable SEGS); apply HJ3pres; lia ]. }
  specialize (HS2 HRK). clear HS HRK. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
  lazymatch type of HS with st_ok_pi _ _ (havoc ?Eo 72 ?ws) _ _ =>
    assert (HEI3 : img_env VAL A_LIM (havoc Eo 72 ws)) by (apply img_env_havoc; [assumption | cbv; lia]) end.
  cno_env HS. cno_usp HS E2. cno_shok HS.
  clear HP3 HR3 Hkeep3 Hpres3 HJ2 HJ3pres Ra0 Ra1 Ra2 Rra Rsp1 Qgp Qtp Qsp. cno_tidy HS.
  (* 8. +0x70 .. +0x7c, memcpy (Q, r, n). *)
  paj_run_tok RUN HS HJ3 SHOK Bspan; [cno_awr Usp |].
  cno_keepC HFr CP.
  clear HF HFr HG. cno_env HS. cno_usp HS E2. cno_tidy HS.
  cno_regv HS (10%bv : bv 5) Ra0. cno_regv HS (11%bv : bv 5) Ra1. cno_regv HS (12%bv : bv 5) Ra2.
  cno_regv HS (1%bv : bv 5) Rra. cno_regv HS (2%bv : bv 5) Rsp1.
  cno_regv HS (3%bv : bv 5) Qgp. cno_regv HS (4%bv : bv 5) Qtp.
  assert (Qsp : spZ (ms_regs ms) = spZ regs + -64) by (unfold spZ at 1; rewrite Rsp1; apply unsigned_lit_small; lia).
  pose proof HJ3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & G3 & _).
  pmkst HS.
  change (pa_sigma US___asan_memcpy) with (uci_sigma US___asan_memcpy).
  eapply SRr_bind.
  { eapply (aj_intrin_at SEGS B LAWS pa_segs_low OCpy (uci_sigma US___asan_memcpy) (AMC fx) W2 (ms_regs ms) (ms_mem ms)
      CNO.CNO_STK (spZ regs) [] lyc Sc W memc mdc [] ly2 S2 _ 2 Q r n (-64) (Z_to_bv 64 (BASE + 660)) HJ3 Ra0 Ra1 Ra2);
      [ lia | lia | lia | exact Qsp | reflexivity | lia | rewrite HSTK; unfold ESTACK; lia | exact Qgp | exact Qtp | exact Rra
      | apply ret_ok_codeptr_v; [lia | reflexivity]
      | intros a Ha; split;
        [ right; right; left; exists Q, (n + 1); split; [exact HinQ | split; [exact HfQ | rewrite ?Hreq; lia]]
        | unfold ESTACK; lia ]
      | eapply (amem_range_of_block SEGS B LAWS _ _ _ _ _ _ _ _ _ (proj1 HJ3) HinQ); rewrite ?Hreq; lia
      | eapply (range_addressable_of_block SEGS B LAWS _ _ _ _ _ _ _ _ _ (proj1 HJ3) HinQ); rewrite ?Hreq; lia
      | intros Hn0; eapply (shadow_hull_vis_of_block SEGS B LAWS _ _ _ _ _ _ _ _ _ (proj1 HJ3) HinQ); rewrite ?Hreq; lia
      | split; [lia|]; split; [lia|]; split;
        [ intros a Ha; split;
          [ apply (aview_some_of_apresent SEGS);
            destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ (proj1 HJ3) HinA2) as (_ & _ & _ & _ & Hp & _);
            exact (proj1 (Hp a ltac:(lia)))
          | unfold ESTACK; lia ]
        | split; [lia|]; split;
          [ eapply (amem_range_of_block SEGS B LAWS _ _ _ _ _ _ _ _ _ (proj1 HJ3) HinA2); lia
          | split;
            [ eapply (range_addressable_of_block SEGS B LAWS _ _ _ _ _ _ _ _ _ (proj1 HJ3) HinA2); lia
            | intros Hn0; eapply (shadow_hull_vis_of_block SEGS B LAWS _ _ _ _ _ _ _ _ _ (proj1 HJ3) HinA2); lia ] ] ] ]. }
  intros W4 c4 _ (-> & regs4 & mem4 & md4 & -> & HJ4 & HP4 & HR4 & Hcp4 & Hkeep4 & Hpres4).
  (* 9. Back from memcpy at +0x80: [Q, Q + n) holds the reply bytes; [P, P + n) is kept. *)
  assert (CQ : forall i, 0 <= i < n -> aview SEGS (w_H W2) mem4 (Q + i) = aview SEGS (w_H W) memc (r + i)).
  { intros i Hi. rewrite (Hcp4 i Hi). replace (r + i) with (bA + (r + i - bA)) by lia.
    apply (G3 bA nA (r + i - bA) HinA HinA2); [lia | intros (rg & Hrg & _); destruct Hrg]. }
  assert (CP4 : forall i, 0 <= i < n -> aview SEGS (w_H W2) mem4 (P + i) = aview SEGS (w_H W) memc (r + i)).
  { intros i Hi. rewrite Hkeep4 by (unfold ESTACK; lia). exact (CP i Hi). }
  clear CP G3 Hcp4. rename CP4 into CP.
  pose proof HJ4 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HJ4pres & _).
  jafter_call_keep_pi HS 88%nat regs4 (mrestrict (w_H W2) mem4) HP4 [0%nat] HS2.
  match type of HS2 with ?tq -> _ => assert (HRK : tq) end.
  { cbn [ms_mem restrict]. apply Forall_cons; [|apply Forall_nil].
    split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite Usp; intros a Ha;
      [ apply (mbyte_of_aview SEGS); apply Hkeep4; [lia | lia | unfold ESTACK; lia]
      | intros _; apply (apresent_writable SEGS); apply HJ4pres; lia ]. }
  specialize (HS2 HRK). clear HS HRK. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
  lazymatch type of HS with st_ok_pi _ _ (havoc ?Eo 88 ?ws) _ _ =>
    assert (HEI4 : img_env VAL A_LIM (havoc Eo 88 ws)) by (apply img_env_havoc; [assumption | cbv; lia]) end.
  cno_env HS. cno_usp HS E2. cno_shok HS.
  clear HP4 HR4 Hkeep4 Hpres4 HJ3 HJ4pres Ra0 Ra1 Ra2 Rra Rsp1 Qgp Qtp Qsp. cno_tidy HS.
  rename HJ4 into HJ2.
  Unshelve.
  (* n = 0: no copy; the content facts hold for the empty ranges. *)
  2: apply Z.eqb_eq in Hc.
  2: rewrite Z.add_0_r in Hc.
  2: lazymatch goal with HS : st_ok_pi _ _ _ _ (restrict (w_H ?Wx) ?msx) |- _ =>
       assert (CP : forall i, 0 <= i < n -> aview SEGS (w_H Wx) (ms_mem msx) (P + i) = aview SEGS (w_H W) memc (r + i))
         by (intros i Hi; lia);
       assert (CQ : forall i, 0 <= i < n -> aview SEGS (w_H Wx) (ms_mem msx) (Q + i) = aview SEGS (w_H W) memc (r + i))
         by (intros i Hi; lia) end.
  all: rename Hc into Hpath.
  (* 10. Both paths at +0x80: a0 = P + n, named by the fresh slot 104; P[n] becomes a 1-byte writable region with its
     shadow entry. *)
  all: paj_run_to_tok RUNTO HS HJ2 SHOK Bspan 664; [cno_awr Usp |].
  all: cno_keepC HFr CP; cno_keepC HFr CQ.
  all: clear HF HFr HG; cno_env HS; cno_usp HS E2; cno_tidy HS.
  all: lazymatch goal with HS : st_ok_pi _ _ ?Ex ?ssx ?msr |- _ =>
    pose proof (cnoW_st_ok_ewset Ex ssx msr 104 (Z_to_bv 64 (P + n)) HS ltac:(vm_compute; reflexivity)) as HS1;
    assert (HEIx : img_env VAL A_LIM (ewset Ex 104 (Z_to_bv 64 (P + n)))) by (apply cnoW_img_env_ewset; [assumption | cbv; lia]);
    assert (E104 : ew (ewset Ex 104 (Z_to_bv 64 (P + n))) 104 = Z_to_bv 64 (P + n)) by apply ew_ewset_same;
    clear HS; rename HS1 into HS end.
  all: cno_env HS; cno_usp HS E2.
  all: cno_reg HS (10%bv : bv 5) Ra0.
  all: lazymatch goal with HS : st_ok_pi _ _ ?Ex ?ssx ?msr |- _ =>
    assert (Ha0 : getr (ms_regs msr) 10 = sv_denot Ex (SOff 104 0))
      by (cbn [ms_regs restrict]; rewrite Ra0, cnoW_den0, E104; rewrite (cnoW_add_val Ex 11 44 n P E11 EP) by lia; f_equal; lia);
    pose proof (cnoW_set_reg Ex ssx msr 10%bv (SOff 104 0) HS ltac:(intros Hq; apply (f_equal bv_unsigned) in Hq; vm_compute in Hq; discriminate) Ha0) as HS1;
    clear HS Ra0 Ha0; rename HS1 into HS end.
  all: destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ (proj1 HJ2) HinP) as (_ & _ & _ & _ & HPp & _).
  all: rewrite ?Hreq in HPp.
  all: lazymatch goal with HS : st_ok_pi _ _ ?Ex ?ssx (restrict (w_H ?Wq) ?msx) |- _ =>
    assert (HRP : region_ok SEGS Ex (ms_mem (restrict (w_H Wq) msx)) (YP09.mkRegion (Some 104%nat) 0 1 0 1 []));
    [ unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val restrict ms_mem];
      rewrite Ub104; split; [lia|]; split; [lia|]; split; [|apply Forall_nil];
      intros o Ho; apply (apresent_writable SEGS); exact (proj1 (HPp (P + n + o) ltac:(lia)))
    | ];
    pose proof (st_ok_pi_add_region Ex ssx _ (YP09.mkRegion (Some 104%nat) 0 1 0 1 []) HS eq_refl HRP) as HS1 end.
  all: match type of HS1 with ?A -> _ => assert (HDJ : A);
    [ lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
      cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
      rewrite Ub104, Usp; repeat split; lia
    | specialize (HS1 HDJ); clear HS HDJ HRP HPp; rename HS1 into HS ] end.
  all: lazymatch goal with HS : st_ok_pi _ _ ?Ex ?ssx ?msr |- _ =>
    pose proof (st_ok_pi_add_fact Ex ssx msr 104 (PTR 0) HS
      ltac:(unfold afact_ok, PTR; cbn [af_lo af_hi af_al2]; rewrite Ub104; rewrite Z.pow_0_r, Z.mod_1_r; lia)) as HS1;
    clear HS; rename HS1 into HS end.
  all: lazymatch goal with HS : st_ok_pi _ _ ?Ex _ (restrict (w_H ?Wq) ?msx) |- _ =>
    try (match goal with H : sh_ok _ _ _ _ _ |- _ => clear H end);
    assert (SHOK : sh_ok SEGS (SOff 32 0) [mkSHE 104 0 1] Ex (mrestrict (w_H Wq) (ms_mem msx)));
    [ apply Forall_cons; [|apply Forall_nil];
      apply (shent_ok_of_range SEGS (w_H Wq) (ms_mem msx) Ex (SOff 32 0) 104 (P + n) 1 (P + n) 0 1);
      [ eapply (range_addressable_of_block SEGS B LAWS _ _ _ _ _ _ _ _ _ (proj1 HJ2) HinP); rewrite ?Hreq; lia
      | rewrite (cnoW_U Ex 32 SB 0 E32) by (unfold SB; lia); unfold SB, SHADOW_OFF; lia
      | rewrite (cnoW_U Ex 104 (P + n) 0 E104) by lia; lia
      | lia | lia
      | intros xx Hxx; cbn [Z.min Z.max] in Hxx; unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HPapp;
        unfold SHADOW_OFF; lia ]
    | ] end.
  (* 11. The shadow check of P[n] (a partial granule takes the slow path at +0x118), the store P[n] = '0', and
     a0 = Q + n at +0xa0. *)
  all: cno_norm HS.
  all: paj_run_to_tok RUNTO HS HJ2 SHOK Bspan 692; [cno_awr2 Usp P Q (n + 1) HinP HfP HinQ HfQ Hreq |].
  all: cno_keepC HFr CP; cno_keepC HFr CQ.
  all: clear HF HFr HG; cno_env HS; cno_usp HS E2; cno_tidy HS.
  (* 12. a0 = Q + n at +0xa0, named by the fresh slot 105; Q[n] becomes a 1-byte writable region. *)
  all: lazymatch goal with HS : st_ok_pi _ _ ?Ex ?ssx ?msr |- _ =>
    pose proof (cnoW_st_ok_ewset Ex ssx msr 105 (Z_to_bv 64 (Q + n)) HS ltac:(vm_compute; reflexivity)) as HS1;
    assert (HEIx : img_env VAL A_LIM (ewset Ex 105 (Z_to_bv 64 (Q + n)))) by (apply cnoW_img_env_ewset; [assumption | cbv; lia]);
    assert (E105 : ew (ewset Ex 105 (Z_to_bv 64 (Q + n))) 105 = Z_to_bv 64 (Q + n)) by apply ew_ewset_same;
    clear HS; rename HS1 into HS end.
  all: cno_env HS; cno_usp HS E2.
  all: cno_reg HS (10%bv : bv 5) Ra0.
  all: lazymatch goal with HS : st_ok_pi _ _ ?Ex ?ssx ?msr |- _ =>
    assert (Ha0 : getr (ms_regs msr) 10 = sv_denot Ex (SOff 105 0))
      by (cbn [ms_regs restrict]; rewrite Ra0, cnoW_den0, E105; rewrite (cnoW_add_val Ex 11 60 n Q E11 EQ) by lia; f_equal; lia);
    pose proof (cnoW_set_reg Ex ssx msr 10%bv (SOff 105 0) HS ltac:(intros Hq; apply (f_equal bv_unsigned) in Hq; vm_compute in Hq; discriminate) Ha0) as HS1;
    clear HS Ra0 Ha0; rename HS1 into HS end.
  all: destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ (proj1 HJ2) HinQ) as (_ & _ & _ & _ & HQp & _).
  all: rewrite ?Hreq in HQp.
  all: lazymatch goal with HS : st_ok_pi _ _ ?Ex ?ssx (restrict (w_H ?Wq) ?msx) |- _ =>
    assert (HRQ : region_ok SEGS Ex (ms_mem (restrict (w_H Wq) msx)) (YP09.mkRegion (Some 105%nat) 0 1 0 1 []));
    [ unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val restrict ms_mem];
      rewrite Ub105; split; [lia|]; split; [lia|]; split; [|apply Forall_nil];
      intros o Ho; apply (apresent_writable SEGS); exact (proj1 (HQp (Q + n + o) ltac:(lia)))
    | ];
    pose proof (st_ok_pi_add_region Ex ssx _ (YP09.mkRegion (Some 105%nat) 0 1 0 1 []) HS eq_refl HRQ) as HS1 end.
  all: match type of HS1 with ?A -> _ => assert (HDJ : A);
    [ lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
      cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
      rewrite Ub105, Usp; repeat split; lia
    | specialize (HS1 HDJ); clear HS HDJ HRQ HQp; rename HS1 into HS ] end.
  all: lazymatch goal with HS : st_ok_pi _ _ ?Ex ?ssx ?msr |- _ =>
    pose proof (st_ok_pi_add_fact Ex ssx msr 105 (PTR 0) HS
      ltac:(unfold afact_ok, PTR; cbn [af_lo af_hi af_al2]; rewrite Ub105; rewrite Z.pow_0_r, Z.mod_1_r; lia)) as HS1;
    clear HS; rename HS1 into HS end.
  all: lazymatch goal with HS : st_ok_pi _ _ ?Ex _ (restrict (w_H ?Wq) ?msx) |- _ =>
    try (match goal with H : sh_ok _ _ _ _ _ |- _ => clear H end);
    assert (SHOK : sh_ok SEGS (SOff 32 0) [mkSHE 105 0 1; mkSHE 104 0 1] Ex (mrestrict (w_H Wq) (ms_mem msx)));
    [ apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]];
      [ apply (shent_ok_of_range SEGS (w_H Wq) (ms_mem msx) Ex (SOff 32 0) 105 (Q + n) 1 (Q + n) 0 1);
        [ eapply (range_addressable_of_block SEGS B LAWS _ _ _ _ _ _ _ _ _ (proj1 HJ2) HinQ); rewrite ?Hreq; lia
        | rewrite (cnoW_U Ex 32 SB 0 E32) by (unfold SB; lia); unfold SB, SHADOW_OFF; lia
        | rewrite (cnoW_U Ex 105 (Q + n) 0 E105) by lia; lia
        | lia | lia
        | intros xx Hxx; cbn [Z.min Z.max] in Hxx; unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HQapp;
          unfold SHADOW_OFF; lia ]
      | apply (shent_ok_of_range SEGS (w_H Wq) (ms_mem msx) Ex (SOff 32 0) 104 (P + n) 1 (P + n) 0 1);
        [ eapply (range_addressable_of_block SEGS B LAWS _ _ _ _ _ _ _ _ _ (proj1 HJ2) HinP); rewrite ?Hreq; lia
        | rewrite (cnoW_U Ex 32 SB 0 E32) by (unfold SB; lia); unfold SB, SHADOW_OFF; lia
        | rewrite (cnoW_U Ex 104 (P + n) 0 E104) by lia; lia
        | lia | lia
        | intros xx Hxx; cbn [Z.min Z.max] in Hxx; unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HPapp;
          unfold SHADOW_OFF; lia ] ]
    | ] end.
  (* 13. The shadow check of Q[n], the store Q[n] = ' ', and rp_uci_int (P, n, cur) at +0xc4. *)
  all: cno_norm HS.
  all: paj_run_tok RUN HS HJ2 SHOK Bspan; [cno_awr2 Usp P Q (n + 1) HinP HfP HinQ HfQ Hreq |].
  all: cno_keepC HFr CP; cno_keepC HFr CQ.
  all: clear HF HFr HG; cno_env HS; cno_usp HS E2; cno_tidy HS.
  (* 14. rp_uci_int (P, n, cur) at +0xc4: a0 = rp_uci_int_m of the n reply bytes (slot 116). *)
  all: cno_regv HS (10%bv : bv 5) Ra0; cno_regv HS (11%bv : bv 5) Ra1; cno_regv HS (12%bv : bv 5) Ra2;
       cno_regv HS (1%bv : bv 5) Rra; cno_regv HS (2%bv : bv 5) Rsp1; cno_regv HS (3%bv : bv 5) Qgp;
       cno_regv HS (4%bv : bv 5) Qtp.
  all: lazymatch type of Rsp1 with getr (ms_regs ?m) _ = _ =>
    assert (Qsp : spZ (ms_regs m) = spZ regs + -64) by (unfold spZ at 1; rewrite Rsp1; apply unsigned_lit_small; lia) end.
  all: pmkst HS.
  all: change (pa_sigma US_rp_uci_int) with (uci_sigma US_rp_uci_int).
  all: destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ (proj1 HJ2) HinP) as (_ & _ & _ & _ & HPp1 & _); rewrite ?Hreq in HPp1.
  all: eapply SRr_bind;
    [ eapply (cnoW_rui_at W2 (ms_regs ms) (ms_mem ms) CNO.CNO_STK (spZ regs) [] lyc Sc W memc mdc [] ly2 S2 _ 2 P n cur bs (-64)
        (Z_to_bv 64 (BASE + 732)) HJ2);
      [ exact Qsp | reflexivity | lia | unfold PR.RUI_STK, PR.RUI_FRAME, ESTACK; lia | exact Qgp | exact Qtp | exact Rra
      | apply ret_ok_codeptr_v; [lia | reflexivity] | exact Ra0 | exact Ra1 | exact Ra2 | lia | exact Hlen | exact Hcur
      | lia | lia
      | apply (cnoW_garr8_move (w_H W) (w_H W2) memc (ms_mem ms) r P); [|exact Hbytes];
        rewrite length_map, Hlen; intros i Hi; exact (CP i Hi)
      | intros x Hx; split; [apply (aview_some_of_apresent SEGS); exact (proj1 (HPp1 x ltac:(lia))) | unfold PR.RUI_STK, PR.RUI_FRAME, ESTACK; lia]
      | eapply (amem_range_of_block SEGS B LAWS _ _ _ _ _ _ _ _ _ (proj1 HJ2) HinP); rewrite ?Hreq; lia
      | eapply (range_addressable_of_block SEGS B LAWS _ _ _ _ _ _ _ _ _ (proj1 HJ2) HinP); rewrite ?Hreq; lia
      | intros Hn0; eapply (shadow_hull_vis_of_block SEGS B LAWS _ _ _ _ _ _ _ _ _ (proj1 HJ2) HinP); rewrite ?Hreq; lia
      | exact (cnoW_consts _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2 ROU ROE Hrom) ]
    | ].
  all: intros W5 c5 _ (-> & regs5 & mem5 & md5 & -> & HJ5 & HP5 & HR5 & Hkeep5 & Hpres5); clear HPp1.
  all: assert (CP5 : forall i, 0 <= i < n -> aview SEGS (w_H W2) mem5 (P + i) = aview SEGS (w_H W) memc (r + i))
         by (intros i Hi; rewrite Hkeep5 by (unfold PR.RUI_STK, PR.RUI_FRAME, ESTACK; lia); exact (CP i Hi)).
  all: assert (CQ5 : forall i, 0 <= i < n -> aview SEGS (w_H W2) mem5 (Q + i) = aview SEGS (w_H W) memc (r + i))
         by (intros i Hi; rewrite Hkeep5 by (unfold PR.RUI_STK, PR.RUI_FRAME, ESTACK; lia); exact (CQ i Hi)).
  all: clear CP CQ; rename CP5 into CP; rename CQ5 into CQ.
  all: pose proof HJ5 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HJ5pres & _).
  all: jafter_call_keep_pi HS 112%nat regs5 (mrestrict (w_H W2) mem5) HP5 [2%nat] HS2.
  all: match type of HS2 with ?tq -> _ => assert (HRK : tq) end;
    [ cbn [ms_mem restrict]; apply Forall_cons; [|apply Forall_nil];
      split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite Usp; intros a Ha;
        [ apply (mbyte_of_aview SEGS); apply Hkeep5; [lia | unfold PR.RUI_STK, PR.RUI_FRAME, ESTACK; lia]
        | intros _; apply (apresent_writable SEGS); apply HJ5pres; lia ]
    | ].
  all: specialize (HS2 HRK); clear HS HRK; rewrite <- restrict_mkst_fx in HS2; rename HS2 into HS.
  all: lazymatch type of HS with st_ok_pi _ _ (havoc ?Eo 112%nat ?ws) _ _ =>
    assert (ER1 : ew (havoc Eo 112%nat ws) 116%nat = Z_to_bv 64 (rp_uci_int_m (PR.PRc.zbytes bs) cur)) by (cbn [ew havoc]; exact HR5);
    assert (HEI5 : img_env VAL A_LIM (havoc Eo 112%nat ws)) by (apply img_env_havoc; [assumption | cbv; lia]) end.
  all: cno_env HS; cno_usp HS E2; cno_shok HS.
  all: clear HP5 HR5 Hkeep5 Hpres5 HJ2 HJ5pres Ra0 Ra1 Ra2 Rra Rsp1 Qgp Qtp Qsp; rename HJ5 into HJ2; cno_tidy HS.
  (* 15. +0xc8 .. +0xd8: s4 = the first result, rp_uci_int (Q, n, cur): the same value (slot 132). *)
  all: paj_run_tok RUN HS HJ2 SHOK Bspan; [cno_awr Usp |].
  all: cno_keepC HFr CP; cno_keepC HFr CQ.
  all: clear HF HFr HG; cno_env HS; cno_usp HS E2; cno_tidy HS.
  all: cno_regv HS (10%bv : bv 5) Ra0; cno_regv HS (11%bv : bv 5) Ra1; cno_regv HS (12%bv : bv 5) Ra2;
       cno_regv HS (1%bv : bv 5) Rra; cno_regv HS (2%bv : bv 5) Rsp1; cno_regv HS (3%bv : bv 5) Qgp;
       cno_regv HS (4%bv : bv 5) Qtp.
  all: lazymatch type of Rsp1 with getr (ms_regs ?m) _ = _ =>
    assert (Qsp : spZ (ms_regs m) = spZ regs + -64) by (unfold spZ at 1; rewrite Rsp1; apply unsigned_lit_small; lia) end.
  all: pmkst HS.
  all: change (pa_sigma US_rp_uci_int) with (uci_sigma US_rp_uci_int).
  all: destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ (proj1 HJ2) HinQ) as (_ & _ & _ & _ & HQp1 & _); rewrite ?Hreq in HQp1.
  all: eapply SRr_bind;
    [ eapply (cnoW_rui_at W2 (ms_regs ms) (ms_mem ms) CNO.CNO_STK (spZ regs) [] lyc Sc W memc mdc [] ly2 S2 _ 2 Q n cur bs (-64)
        (Z_to_bv 64 (BASE + 752)) HJ2);
      [ exact Qsp | reflexivity | lia | unfold PR.RUI_STK, PR.RUI_FRAME, ESTACK; lia | exact Qgp | exact Qtp | exact Rra
      | apply ret_ok_codeptr_v; [lia | reflexivity] | exact Ra0 | exact Ra1 | exact Ra2 | lia | exact Hlen | exact Hcur
      | lia | lia
      | apply (cnoW_garr8_move (w_H W) (w_H W2) memc (ms_mem ms) r Q); [|exact Hbytes];
        rewrite length_map, Hlen; intros i Hi; exact (CQ i Hi)
      | intros x Hx; split; [apply (aview_some_of_apresent SEGS); exact (proj1 (HQp1 x ltac:(lia))) | unfold PR.RUI_STK, PR.RUI_FRAME, ESTACK; lia]
      | eapply (amem_range_of_block SEGS B LAWS _ _ _ _ _ _ _ _ _ (proj1 HJ2) HinQ); rewrite ?Hreq; lia
      | eapply (range_addressable_of_block SEGS B LAWS _ _ _ _ _ _ _ _ _ (proj1 HJ2) HinQ); rewrite ?Hreq; lia
      | intros Hn0; eapply (shadow_hull_vis_of_block SEGS B LAWS _ _ _ _ _ _ _ _ _ (proj1 HJ2) HinQ); rewrite ?Hreq; lia
      | exact (cnoW_consts _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2 ROU ROE Hrom) ]
    | ].
  all: intros W6 c6 _ (-> & regs6 & mem6 & md6 & -> & HJ6 & HP6 & HR6 & Hkeep6 & Hpres6); clear HQp1.
  all: assert (CP6 : forall i, 0 <= i < n -> aview SEGS (w_H W2) mem6 (P + i) = aview SEGS (w_H W) memc (r + i))
         by (intros i Hi; rewrite Hkeep6 by (unfold PR.RUI_STK, PR.RUI_FRAME, ESTACK; lia); exact (CP i Hi)).
  all: assert (CQ6 : forall i, 0 <= i < n -> aview SEGS (w_H W2) mem6 (Q + i) = aview SEGS (w_H W) memc (r + i))
         by (intros i Hi; rewrite Hkeep6 by (unfold PR.RUI_STK, PR.RUI_FRAME, ESTACK; lia); exact (CQ i Hi)).
  all: clear CP CQ; rename CP6 into CP; rename CQ6 into CQ.
  all: pose proof HJ6 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HJ6pres & _).
  all: jafter_call_keep_pi HS 128%nat regs6 (mrestrict (w_H W2) mem6) HP6 [0%nat] HS2.
  all: match type of HS2 with ?tq -> _ => assert (HRK : tq) end;
    [ cbn [ms_mem restrict]; apply Forall_cons; [|apply Forall_nil];
      split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite Usp; intros a Ha;
        [ apply (mbyte_of_aview SEGS); apply Hkeep6; [lia | unfold PR.RUI_STK, PR.RUI_FRAME, ESTACK; lia]
        | intros _; apply (apresent_writable SEGS); apply HJ6pres; lia ]
    | ].
  all: specialize (HS2 HRK); clear HS HRK; rewrite <- restrict_mkst_fx in HS2; rename HS2 into HS.
  all: lazymatch type of HS with st_ok_pi _ _ (havoc ?Eo 128%nat ?ws) _ _ =>
    assert (ER2 : ew (havoc Eo 128%nat ws) 132%nat = Z_to_bv 64 (rp_uci_int_m (PR.PRc.zbytes bs) cur)) by (cbn [ew havoc]; exact HR6);
    assert (HEI6 : img_env VAL A_LIM (havoc Eo 128%nat ws)) by (apply img_env_havoc; [assumption | cbv; lia]) end.
  all: cno_env HS; cno_usp HS E2; cno_shok HS.
  all: clear HP6 HR6 Hkeep6 Hpres6 HJ2 HJ6pres Ra0 Ra1 Ra2 Rra Rsp1 Qgp Qtp Qsp; rename HJ6 into HJ2; cno_tidy HS.
  (* 16. +0xdc bne s4, a0: the two results are equal, so abort is not reached. *)
  all: psrr_branch_tok RUN BR HS SHOK Bspan.
  all: rewrite branch_ne_U, !cnoW_U0, ER1, ER2, Z.eqb_refl in Hc; cbn [negb] in Hc.
  all: try discriminate Hc.
  all: clear Hc.
  (* 17. +0xe0 .. +0xe4: free (P), the block of the first copy. *)
  all: paj_run_tok RUN HS HJ2 SHOK Bspan; [cno_awr Usp |].
  all: clear HF HFr HG; cno_env HS; cno_usp HS E2; cno_tidy HS.
  all: cno_regv HS (10%bv : bv 5) Ra0; cno_regv HS (1%bv : bv 5) Rra; cno_regv HS (2%bv : bv 5) Rsp1;
       cno_regv HS (3%bv : bv 5) Qgp; cno_regv HS (4%bv : bv 5) Qtp; cno_regv HS (8%bv : bv 5) Rs0.
  all: lazymatch type of Rsp1 with getr (ms_regs ?m) _ = _ =>
    assert (Qsp : spZ (ms_regs m) = spZ regs + -64) by (unfold spZ at 1; rewrite Rsp1; apply unsigned_lit_small; lia);
    assert (Qraz : raZ (ms_regs m) = BASE + 764) by (unfold raZ; rewrite Rra; apply unsigned_lit_small; rewrite cnoW_base; lia);
    assert (Qs0 : s0Z (ms_regs m) = bv_unsigned (w64 cur)) by (unfold s0Z; rewrite Rs0; reflexivity) end.
  all: pose proof HJ2 as (_ & HlyF & _ & _ & _ & _ & HnevF & _).
  all: assert (HtopF : ly_top ly2 = ly_top lyc) by (destruct HlyF as (_ & _ & _ & _ & _ & _ & _ & _ & Et & _); exact Et).
  all: lazymatch type of Rsp1 with getr (ms_regs ?m) _ = _ =>
    assert (Qch : chain_pre ly2 (aview SEGS (w_H W2) (ms_mem m)) (ms_regs m) [])
      by (apply cnoW_chain_nil; [rewrite Qraz, cnoW_base; lia | lia | rewrite Qsp; lia | rewrite Qs0; exact (cnoW_int_word cur Hcur)]);
    assert (Qtr : In (call_trace0 (pc_free_ra0 (as_code B)) (ms_regs m) []) (as_universe B))
      by (apply (cnoW_trace_fix _ CNO.UCI_CNO_RA_FREE1); [rewrite Qraz, cnoW_base; reflexivity | exact (proj2 (proj2 UFIX))]) end.
  all: pmkst HS.
  all: change (pa_sigma US___interceptor_trampoline_free) with (uci_sigma US___interceptor_trampoline_free).
  all: rewrite <- FREEPC.
  all: pose proof (mle_station MT Sc S1 S2 _ _ ML MLE1 MLE2) as MLE12.
  all: eapply SRr_bind;
    [ eapply (AF fx W2 _ _ CNO.CNO_STK (spZ regs) [] lyc Sc W memc mdc [] ly2 S2 _ 2 P (n + 1) (-64)
        (Z_to_bv 64 (BASE + 764)) [] HJ2 HinP Ra0);
      [ exact Qsp | reflexivity | lia | rewrite HSTK; unfold ASTACK; lia | exact Qgp | exact Qtp | exact Rra
      | apply ret_ok_codeptr_v; [lia | reflexivity] | unfold CNO.CNO_EV in Hev; lia | exact Qch | exact Qtr
      | intros Hin; exfalso; exact (HfP Hin)
      | apply (mok_station MT Sc S2 T _ (mo_free MT) ML Hmo MLE12); [exact (mo_free_nonneg MT ML)|];
        unfold CNO.uci_cno_cost in Hcost; pose proof (mo_free_nonneg MT ML); lia ]
    | ].
  all: intros W7 c7 _ (ly3 & S3 & regs7 & mem7 & md7 & -> & HJ7 & HP7 & (l1 & l2 & Hs1 & Hs2) & Hfr7 & HK7 & MLE7).
  all: clear Ra0 Rra Rsp1 Qgp Qtp Rs0 Qsp Qraz Qs0 Qch Qtr.
  (* 18. Back from free at +0xe8: the frame is kept. *)
  all: pose proof HJ7 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HJ7pres & _).
  all: jafter_call_keep_pi HS 144%nat regs7 (mrestrict (w_H W7) mem7) HP7 [0%nat] HS2.
  all: match type of HS2 with ?tq -> _ => assert (HRK : tq) end;
    [ cbn [ms_mem restrict]; apply Forall_cons; [|apply Forall_nil];
      split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite Usp; intros a Ha;
        [ apply (mbyte_of_aview SEGS); apply (proj1 HK7); [lia | lia]
        | intros _; apply (apresent_writable SEGS); apply HJ7pres; lia ]
    | ].
  all: specialize (HS2 HRK); clear HS HRK; rewrite <- restrict_mkst_fx in HS2; rename HS2 into HS.
  all: lazymatch type of HS with st_ok_pi _ _ (havoc ?Eo 144 ?ws) _ _ =>
    assert (HEI7 : img_env VAL A_LIM (havoc Eo 144 ws)) by (apply img_env_havoc; [assumption | cbv; lia]) end.
  all: cno_env HS; cno_usp HS E2; cno_shok HS.
  all: clear HP7 HK7 HJ2 HJ7pres; cno_tidy HS.
  (* 19. +0xe8 .. +0x10c: a0 = Q, the epilogue restores ra and s0 .. s5 and the caller's sp; the tail call free (Q). *)
  all: paj_run_tok RUN HS HJ7 SHOK Bspan; [cno_awr Usp |].
  all: clear HF HFr HG; cno_env HS; cno_usp HS E2; cno_tidy HS.
  all: lazymatch type of HS with st_ok _ ?Ex _ _ =>
    assert (HAEx : env_agree 32 (Ereg regs [Z_to_bv 64 SB]) Ex);
    [ destruct HAE as [HAE1 HAE2]; split;
      [ intros m Hm; rewrite <- (HAE1 m Hm); repeat first [ rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia ];
        reflexivity
      | cbn [ed havoc ewset]; first [exact HAE2 | symmetry; exact HAE2] ]
    | ] end.
  all: lazymatch type of HS with st_ok _ ?Ex ?ssx (restrict ?Hx ?msx) =>
    pose proof (aregs_preserved_of_st_ok SEGS Hx Ex ssx msx regs [Z_to_bv 64 SB] HS HAEx ltac:(vm_compute; reflexivity)) as HPR end.
  all: cno_regv HS (10%bv : bv 5) Ra0; cno_regv HS (1%bv : bv 5) Rra; cno_regv HS (2%bv : bv 5) Rsp1;
       cno_regv HS (3%bv : bv 5) Qgp; cno_regv HS (4%bv : bv 5) Qtp; cno_regv HS (8%bv : bv 5) Rs0.
  all: lazymatch type of Rsp1 with getr (ms_regs ?m) _ = _ =>
    assert (Qsp : spZ (ms_regs m) = spZ regs + 0) by (unfold spZ at 1; rewrite Rsp1, Z.add_0_r; apply unsigned_lit_small; lia);
    assert (Qraz : raZ (ms_regs m) = raZ regs) by (unfold raZ; rewrite Rra; reflexivity);
    assert (Qs0 : s0Z (ms_regs m) = s0Z regs) by (unfold s0Z; rewrite Rs0; reflexivity) end.
  all: pose proof HJ7 as (_ & Hly7 & _ & _ & _ & _ & Hnev7 & _ & G7 & _).
  all: assert (Htop7 : ly_top ly3 = ly_top lyc) by (destruct Hly7 as (_ & _ & _ & _ & _ & _ & _ & _ & Et & _); exact Et).
  all: lazymatch type of Rsp1 with getr (ms_regs ?m) _ = _ =>
    assert (Qch : chain_pre ly3 (aview SEGS (w_H W7) (ms_mem m)) (ms_regs m) ch);
    [ apply (achain_chain_pre ly3 _ (spZ regs) (s0Z regs) ch (ms_regs m));
      [ apply (achain_ly_top lyc ly3 _ _ _ _ Htop7);
        apply (achain_kept lyc (aview SEGS (w_H W) memc) _ (spZ regs) (s0Z regs) ch (spZ regs) Hch); [lia | lia |];
        intros a Ha; apply G7; lia
      | rewrite Qsp; lia | exact Qs0 | rewrite Qraz; exact Hra4 ]
    | ];
    assert (Qtr : In (call_trace0 (pc_free_ra0 (as_code B)) (ms_regs m) ch) (as_universe B))
      by (rewrite cnoW_trace_ctx, Qraz; exact (HUCTX _ HCTX)) end.
  all: pmkst HS.
  all: change (pa_sigma US___interceptor_trampoline_free) with (uci_sigma US___interceptor_trampoline_free).
  all: rewrite <- FREEPC.
  all: pose proof (mle_station MT Sc S2 S3 _ _ ML MLE12 MLE7) as MLE13.
  all: assert (HinQ3 : In (Q, n + 1) (ablocks B ly3 S3))
    by (rewrite Hs2; assert (HQin : In (Q, n + 1) (l1 ++ (P, n + 1) :: l2)) by (rewrite <- Hs1; exact HinQ);
        apply in_app_iff in HQin as [HQin | [HQin | HQin]];
        [apply in_or_app; left; exact HQin | exfalso; apply HPQ; exact HQin | apply in_or_app; right; exact HQin]).
  all: eapply SRr_bind;
    [ eapply (AF fx W7 _ _ CNO.CNO_STK (spZ regs) [] lyc Sc W memc mdc [] ly3 S3 _ 3 Q (n + 1) 0
        (getr regs 1) ch HJ7 HinQ3 Ra0);
      [ exact Qsp | reflexivity | lia | rewrite HSTK; unfold ASTACK; lia | exact Qgp | exact Qtp | exact Rra
      | exact Hra | unfold CNO.CNO_EV in Hev; lia | exact Qch | exact Qtr
      | intros Hin; exfalso; exact (HfQ Hin)
      | apply (mok_station MT Sc S3 T _ (mo_free MT) ML Hmo MLE13); [exact (mo_free_nonneg MT ML)|];
        unfold CNO.uci_cno_cost in Hcost; pose proof (mo_free_nonneg MT ML); lia ]
    | ].
  (* 20. The tail free returns to the caller: the post. *)
  all: intros W8 c8 _ (ly4 & S4 & regs8 & mem8 & md8 & -> & HJ8 & HP8 & (m1 & m2 & Hs3 & Hs4) & Hfr8 & HK8 & MLE8).
  all: apply SRr_ret. all: exists ly4, S4, regs8, mem8, md8.
  all: split; [reflexivity|].
  all: split; [exact HJ8|].
  all: split; [exact (aregs_preserved_trans _ _ _ HPR HP8)|].
  all: split; [rewrite Hs4; apply (cnoW_perm2 (ablocks B lyc Sc) l1 l2 m1 m2 (P, n + 1) (Q, n + 1));
                [rewrite <- Hs1, Hbl2, Hbl1; reflexivity | rewrite <- Hs3, Hs2; reflexivity]|].
  all: eapply mle_weaken; [exact ML | exact (mle_station MT Sc S3 S4 _ _ ML MLE13 MLE8) | unfold CNO.uci_cno_cost; lia].
Qed.
End Walk.
End W.

(* The frozen statement (lib/A/Prog/check_no_overread_cg.v uci_check_no_overread_cg_holds_stmt): the walk from a
   journal that starts at the call (ajournal_sub_init), composed back into the caller's journal (ajournal_sub); what
   the call kept is that journal's (acall_kept_of_journal), and the blocks are the caller's again (cnoW_walk's
   Permutation). *)
Theorem uci_check_no_overread_cg_holds {fx : YK11.FPState} {rc : YM05.RunCeil} (B : asyms) (MT : ameter_ops)
    (CTX : list (list Z)) :
  @CNO.uci_check_no_overread_cg_holds_stmt fx rc B MT CTX.
Proof.
  intros MALPC FREEPC CELLS ROU ROE LAWS ML UCTX UFIX AM AF AMC RUI.
  unfold CNO.uci_check_no_overread_cg.
  intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs r n cur T bs ch HJc Hra Hra4 Hgp Htp H10 H11 H12
    Hch HCTX Hal16 Hwlo Hwhi Hcur Hn Hlen Hblk Hbytes Hrom Hev Hlive Hmo Hcost.
  pose proof HJc as (HAR & _ & _ & _ & _ & _ & Hnev & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
  pose proof Hstk as (Hsp0al & _).
  assert (HSTK : CNO.CNO_STK = 16448) by reflexivity.
  assert (HJ0 : @ajournal rc AE2k.tfib_sink_head tfibsegs B CNO.CNO_STK (spZ regs) [] lyc Sc W memc mdc [] lyc Sc W memc mdc 0).
  { apply (ajournal_sub_init tfibsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k CNO.CNO_STK (spZ regs) []
      (spZ regs - sp0) HJc); [lia | rewrite Zminus_mod, Hal16, Hsp0al; reflexivity | lia | lia | lia]. }
  change (uci_sigma US_check_no_overread) with (@pa_val _ uci_listing PI_uci A_TEXT + AF_check_no_overread).
  eapply SRr_mono.
  { apply (cnoW_walk B MT LAWS CELLS ML MALPC FREEPC ROU ROE UFIX AM AF AMC RUI W regs memc lyc Sc mdc r n cur T bs ch CTX
      HJ0 Hra Hra4 Hgp Htp H10 H11 H12 Hch UCTX HCTX Hcur Hn Hlen Hblk Hbytes Hrom ltac:(lia) Hlive Hmo Hcost). }
  cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HP & Hperm & MLE).
  pose proof HJ2 as (_ & _ & _ & _ & _ & Hfrs2 & _).
  exists ly2, S2, regs2, mem2, md2.
  split; [reflexivity|].
  split.
  { change own with ([] ++ own).
    eapply (ajournal_sub tfibsegs B LAWS uci_segs_low STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k CNO.CNO_STK
      (spZ regs) [] [] ly2 S2 W2 mem2 md2 CNO.CNO_EV HJc HJ2); [lia | lia | intros a (rg & Hrg & _); destruct Hrg]. }
  split; [exact HP|].
  split; [rewrite Hfrs2; reflexivity|].
  split; [exact Hperm|].
  split.
  { eapply (acall_kept_of_journal tfibsegs B uci_segs_low CNO.CNO_STK (spZ regs) [] [] lyc Sc W memc mdc ly2 S2 W2 mem2 md2
      CNO.CNO_EV (fun _ => False) HJ2 HAR).
    - intros a (rg & Hrg & _); destruct Hrg.
    - intros b m i Hin _ _. exact (Permutation_in _ (Permutation_sym Hperm) Hin).
    - exact sink_closed_nil. }
  exact MLE.
Qed.
