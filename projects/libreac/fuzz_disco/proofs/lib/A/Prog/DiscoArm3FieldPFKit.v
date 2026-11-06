(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the generic part of proofs/cgif/cgif_file_fuzzer/lib/YC1i.v for libreac/fuzz_disco's program walk (ceil, alias_srlw_sll, req_size_pos', PTR, Bspan, region_kept_at1) over fuzz_disco's listing; cgif's create_byte_list_block walk is left out; module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/YC1i.v, with its module names changed; 463 of its 496 lines of code are new or changed and 36 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/DiscoEntHdrLib.v, with its module paths and module names changed; 326 of its 384 lines of code are new or changed and 438 lines of the source are left out. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI0s YI00 YG0v.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YCbp YE00 YE01 YO09.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YI16 YM05 YImgTop.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import
PaTable PaSym PaShadow PaRun PaStep PaJournal DiscoSyms DiscoList DiscoAddr DiscoPa DiscoPaLib DiscoBase DiscoFrame.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import YC1g YC1h YC1i YC45 YC81 DiscoACjr ACj1 DiscoACja.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Rt Require Import SnprintfDef.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import
DiscoEntryInv DiscoEntryShapes DiscoArm3 DiscoEntSeatStmt DiscoEntSeat DiscoRo DiscoEntBodyStmt.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Rt Require Import SnprintfConsts.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A Require AE2k.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import JtokIs JsonScalar.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require ReacBoxName.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require
disco_table_c reac_disco_table_age_c reac_disco_table_json_c disco_json_text disco_json_reader_model disco_json_lemmas
slot_ser_defs slot_ser_pure slot_ser_tokb disco_box_name_model.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import slot_inv.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import DiscoArm3FieldCut.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Definition PFR1_OFF : Z := 0x1e5c.
Definition PFR2_OFF : Z := 0x1e70.

Definition dsh_mac (k : Z) : Z :=
  if (k =? 216) || (k =? 217) then 0 else if k =? 218 then 2 else dsh_ser2 k.

Definition pf_mb (T : list byte) (j k : Z) : Z :=
  nth (Z.to_nat (48 * (j - 1) + k)) (map (fun b : byte => bv_unsigned b) T) 0.

Definition pf_mtext (T : list byte) (j : Z) : list Z :=
  disco_json_text.mac_text (disco_json_text.e_mac (reac_disco_table_json_c.tj_entry T (j - 1))).

Definition pfa_sr (c21 c22 c27 : Z) : list sv :=
  [SLit 0; SOff 531 0; SOff 60 0; SOff 533 0; SOff 534 0; SOff 535 0; SOff 536 0; SOff 537 0; SOff 538 0;
   SOff 60 0; SOff 540 0; SOff 529 0; SOff 542 0; SOff 543 0; SOff 544 0; SOff 545 0; SOff 546 0; SOff 547 0;
   SOff 32 0; SOff 549 0; SOff 550 0; SOff 529 c21; SOff 516 c22;
   SOff 553 0; SOff 554 0; SOff 555 0; SOff 556 0; SOff 516 c27;
   SOff 558 0; SOff 559 0; SOff 560 0; SOff 561 0].
Definition pfa_fcs (j : Z) : list YP09.chunk :=
  [YP09.mkChunk (2160 + 48 * (j - 1)) (CVal 1 (SOff 562 0));
   YP09.mkChunk (2161 + 48 * (j - 1)) (CVal 1 (SOff 563 0));
   YP09.mkChunk (2162 + 48 * (j - 1)) (CVal 1 (SOff 564 0));
   YP09.mkChunk (2163 + 48 * (j - 1)) (CVal 1 (SOff 565 0));
   YP09.mkChunk (2164 + 48 * (j - 1)) (CVal 1 (SOff 566 0));
   YP09.mkChunk (2165 + 48 * (j - 1)) (CVal 1 (SOff 567 0))].
Definition pfa_fa : list (nat * afact) :=
  [(562%nat, mkAF 0 255 0); (563%nat, mkAF 0 255 0); (564%nat, mkAF 0 255 0);
   (565%nat, mkAF 0 255 0); (566%nat, mkAF 0 255 0); (567%nat, mkAF 0 255 0)].
Definition pfa_stk : YP09.region := YP09.mkRegion (Some AT_A) (-16) 0 (-16) 0 [].
Definition pfa_rs (j : Z) : smem :=
  [YP09.mkRegion (Some AT_STK) (-104) 0 0 0 dsave_chunks;
   YP09.mkRegion (Some AT_A) 0 472 0 0 dslot_chunks;
   YP09.mkRegion (Some AT_F) 0 (fs_frame_bytes DFRAME_CLASS) 0 0 (dfhdr_chunks ++ pfa_fcs j);
   YP09.mkRegion (Some AT_SH) 0 (fs_frame_bytes DFRAME_CLASS / 8) 0 DFRAME_SH (dsh_chunks dsh_ser2);
   got_regionP; bcell_regionP 32; pfa_stk].

Lemma pfa_subregion : forall b lo hi wlo whi wlo' whi' cs,
  whi' <= wlo' \/ (wlo <= wlo' /\ whi' <= whi) ->
  subregion (YP09.mkRegion b lo hi wlo' whi' cs) (YP09.mkRegion b lo hi wlo whi cs).
Proof.
  intros b lo hi wlo whi wlo' whi' cs Hw. unfold subregion.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  split; [reflexivity|]. split; [lia|]. split; [lia|]. split; [exact Hw|]. intros c Hc. exact Hc.
Qed.
Lemma pfa_subrefl : forall r, subregion r r.
Proof. intros [b lo hi wlo whi cs]. apply pfa_subregion. lia. Qed.
Lemma pfa_submem : forall j, submem (pfa_rs j) (d_kregions dsh_ser2 [] (pfa_fcs j) ++ [pfa_stk]).
Proof.
  intros j. unfold pfa_rs, d_kregions, fshadow_region. rewrite app_nil_r. cbn [app].
  apply submem_keep; [apply pfa_subrefl|].
  apply submem_keep; [apply pfa_subregion; lia|].
  apply submem_keep; [apply pfa_subregion; lia|].
  apply submem_keep; [apply pfa_subrefl|].
  apply submem_keep; [apply pfa_subrefl|].
  apply submem_keep; [apply pfa_subrefl|].
  apply submem_keep; [apply pfa_subrefl|].
  apply submem_nil.
Qed.
Lemma pfa_inw : forall E j a, in_wrange E (pfa_rs j) a ->
  (base_val E (Some AT_SH) <= a < base_val E (Some AT_SH) + 384) \/
  (base_val E (Some AT_A) - 16 <= a < base_val E (Some AT_A)).
Proof.
  intros E j a (r & Hin & Hr). unfold pfa_rs in Hin. cbn [In] in Hin.
  destruct Hin as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]];
    unfold got_regionP, bcell_regionP, pfa_stk, DFRAME_SH in Hr; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Hr; lia.
Qed.
Lemma pfa_soff : forall E n z b, bv_unsigned (ew E n) = b -> sv_denot E (SOff n z) = Z_to_bv 64 (b + z).
Proof. intros E n z b Hb. cbn [sv_denot]. rewrite Hb. reflexivity. Qed.

Section d. Context {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg disco_listing}.
#[local] Notation SEGS := (@pa_segs _ disco_listing PI).
#[local] Notation VAL := (@pa_val _ disco_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ disco_listing PI).
#[local] Notation BASE := (@pa_val _ disco_listing PI A_TEXT).
#[local] Notation rd W mem := (mrestrict (w_H W) mem).

Definition pfa_vals (regs : bvmap 5 word) (T1 : list byte) (j : Z) : list word :=
  map (getr regs) (tl all_regs) ++ map (fun k => Z_to_bv 64 (pf_mb T1 j k)) [0; 1; 2; 3; 4; 5].

Lemma pfa_x : forall cx E (R : bvmap 5 word) T1 j (q : nat), (q < 31)%nat ->
  ew (d_env cx E (pfa_vals R T1 j)) (AT_X + q) = getr R (nth q (tl all_regs) 0%bv).
Proof.
  intros cx E R T1 j q Hq. unfold pfa_vals. rewrite d_env_x by (rewrite length_app, !length_map; cbn; lia).
  rewrite app_nth1 by (rewrite length_map; cbn; lia).
  rewrite (nth_indep _ _ (getr R 0%bv)) by (rewrite length_map; cbn; lia).
  apply map_nth.
Qed.
Lemma pfa_atom : forall cx E (R : bvmap 5 word) T1 j (q : nat), (q < 31)%nat ->
  sv_denot (d_env cx E (pfa_vals R T1 j)) (SOff (AT_X + q) 0) = getr R (nth q (tl all_regs) 0%bv).
Proof.
  intros cx E R T1 j q Hq. cbn [sv_denot]. rewrite pfa_x by exact Hq. rewrite Z.add_0_r. apply Z_to_bv_bv_unsigned.
Qed.
Lemma pfa_byte : forall cx E (R : bvmap 5 word) T1 j (q : nat), (q < 6)%nat ->
  ew (d_env cx E (pfa_vals R T1 j)) (AT_X + 31 + q) = Z_to_bv 64 (pf_mb T1 j (Z.of_nat q)).
Proof.
  intros cx E R T1 j q Hq. unfold pfa_vals. rewrite <- Nat.add_assoc.
  rewrite d_env_x by (rewrite length_app, !length_map; cbn; lia).
  rewrite app_nth2 by (rewrite length_map; cbn; lia). rewrite length_map. cbn [length tl all_regs].
  replace (31 + q - 31)%nat with q by lia.
  destruct q as [|[|[|[|[|[|q]]]]]]; try lia; reflexivity.
Qed.

Lemma pfa_regs_ok : forall cx E (R : bvmap 5 word) T1 j c21 c22 c27,
  getr R 2 = w64 (d_A cx) -> getr R 9 = w64 (d_A cx) -> getr R 11 = w64 (shadow_addr (d_FB cx)) ->
  getr R 18 = w64 SHADOW_OFF -> getr R 21 = w64 (shadow_addr (d_FB cx) + c21) ->
  getr R 22 = w64 (d_FB cx + c22) -> getr R 27 = w64 (d_FB cx + c27) ->
  ew E AT_A = w64 (d_A cx) -> ew E AT_F = w64 (d_FB cx) -> ew E AT_SH = w64 (shadow_addr (d_FB cx)) ->
  ew E 32 = w64 SHADOW_OFF ->
  0 <= d_A cx < 2 ^ 64 -> 0 <= d_FB cx < 2 ^ 64 -> 0 <= shadow_addr (d_FB cx) < 2 ^ 64 ->
  0 <= SHADOW_OFF < 2 ^ 64 ->
  regs_ok (d_env cx E (pfa_vals R T1 j)) (pfa_sr c21 c22 c27) R.
Proof.
  intros cx E R T1 j c21 c22 c27 R2 R9 R11 R18 R21 R22 R27 E60 E516 E529 E32 HA HF HSH HSO.
  set (E' := d_env cx E (pfa_vals R T1 j)).
  assert (U60 : bv_unsigned (ew E' 60) = d_A cx).
  { unfold E'. rewrite d_env_old by (unfold AT_FL; lia). change 60%nat with AT_A. rewrite E60.
    unfold w64. apply unsigned_lit_small. lia. }
  assert (U516 : bv_unsigned (ew E' 516) = d_FB cx).
  { unfold E'. rewrite d_env_old by (unfold AT_FL; lia). change 516%nat with AT_F. rewrite E516.
    unfold w64. apply unsigned_lit_small. lia. }
  assert (U529 : bv_unsigned (ew E' 529) = shadow_addr (d_FB cx)).
  { unfold E'. rewrite d_env_old by (unfold AT_FL; lia). change 529%nat with AT_SH. rewrite E529.
    unfold w64. apply unsigned_lit_small. lia. }
  assert (U32 : bv_unsigned (ew E' 32) = SHADOW_OFF).
  { unfold E'. rewrite d_env_old by (unfold AT_FL; lia). rewrite E32.
    unfold w64. apply unsigned_lit_small. exact HSO. }
  assert (S60 : sv_denot E' (SOff 60 0) = w64 (d_A cx)) by (rewrite (pfa_soff _ _ _ _ U60); unfold w64; f_equal; lia).
  assert (S529 : sv_denot E' (SOff 529 0) = w64 (shadow_addr (d_FB cx)))
    by (rewrite (pfa_soff _ _ _ _ U529); unfold w64; f_equal; lia).
  assert (S32 : sv_denot E' (SOff 32 0) = w64 SHADOW_OFF) by (rewrite (pfa_soff _ _ _ _ U32); unfold w64; f_equal; lia).
  assert (S21 : sv_denot E' (SOff 529 c21) = w64 (shadow_addr (d_FB cx) + c21))
    by (rewrite (pfa_soff _ _ _ _ U529); reflexivity).
  assert (S22 : sv_denot E' (SOff 516 c22) = w64 (d_FB cx + c22)) by (rewrite (pfa_soff _ _ _ _ U516); reflexivity).
  assert (S27 : sv_denot E' (SOff 516 c27) = w64 (d_FB cx + c27)) by (rewrite (pfa_soff _ _ _ _ U516); reflexivity).
  assert (QX : forall q, (q < 31)%nat -> sv_denot E' (SOff (AT_X + q) 0) = getr R (nth q (tl all_regs) 0%bv))
    by (intros q Hq; unfold E'; apply pfa_atom; exact Hq).
  clearbody E'.
  apply regs_ok_by_cases. intros z Hz. cbv [all_regs In] in Hz.
  repeat (destruct Hz as [<-|Hz]; [
    match goal with |- _ = sv_denot ?E (sr_get ?sr ?r) =>
      let v := eval vm_compute in (sr_get sr r) in change (sr_get sr r) with v end;
    first [ rewrite getr_zero; reflexivity
          | rewrite S60; assumption | rewrite S529; assumption | rewrite S32; assumption
          | rewrite S21; assumption | rewrite S22; assumption | rewrite S27; assumption
          | lazymatch goal with |- _ = sv_denot _ (SOff ?m 0) =>
              let q := eval vm_compute in (m - AT_X)%nat in
              let A := fresh "A" in
              assert (A : sv_denot E' (SOff m 0) = sv_denot E' (SOff (AT_X + q) 0)) by reflexivity;
              rewrite A, QX by (vm_compute; lia); reflexivity end ] | ]);
  try (exfalso; exact Hz).
Qed.

Lemma pfa_awr : forall E j STK sp0 FP bl0 blc ly (cid pos : Z) own' a sh,
  bv_unsigned (ew E 60) = a -> bv_unsigned (ew E 529) = sh ->
  sp0 - STK <= a - 16 -> a <= sp0 ->
  shadow_addr (frame_addr ly cid pos) = sh -> 384 <= fs_frame_bytes cid / 8 ->
  awr_ok E (pfa_rs j) STK sp0 FP bl0 blc ly ((cid, pos) :: own').
Proof.
  intros E j STK sp0 FP bl0 blc ly cid pos own' a sh Ha Hsh H1 H2 Hfs Hcl. unfold pfa_rs.
  apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia|].
  apply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 529%nat sh); [reflexivity | exact Hsh | |].
  { cbn [YP09.r_wlo YP09.r_whi]. unfold DFRAME_SH. intros x Hx. right; right; right. exists cid, pos.
    split; [left; reflexivity|]. right. unfold in_zr. cbn [fst snd]. rewrite Hfs. lia. }
  apply awr_ok_cons_ro; [unfold got_regionP; cbn; lia|]. apply awr_ok_cons_ro; [unfold bcell_regionP; cbn; lia|].
  apply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 60%nat (a - sp0)); [reflexivity | lia | cbn; lia | cbn; lia |].
  apply awr_ok_nil.
Qed.

Lemma pfa_chunk : forall cx E R T1 j m (q : nat) off,
  garr8 SEGS m (d_obj cx OT) (map (fun b : byte => bv_unsigned b) T1) -> length T1 = 400%nat -> 1 <= j <= 8 ->
  (q < 6)%nat -> off = 2160 + Z.of_nat q + 48 * (j - 1) ->
  YP09.chunk_ok SEGS (d_env cx E (pfa_vals R T1 j)) m (d_FB cx) (YP09.mkChunk off (CVal 1 (SOff (AT_X + 31 + q) 0))).
Proof.
  intros cx E R T1 j m q off HG HL Hj Hq ->.
  destruct (garr8_nthZ SEGS m (d_obj cx OT) _ (48 * (j - 1) + Z.of_nat q) HG ltac:(lia)
    ltac:(rewrite length_map, HL; lia)) as [Hv Hr].
  apply (chunk_ok_val SEGS _ _ (d_FB cx) _ 1%N _ (pf_mb T1 j (Z.of_nat q))).
  - cbn [sv_denot]. rewrite pfa_byte by exact Hq. unfold pf_mb. rewrite unsigned_lit_small by lia.
    rewrite Z.add_0_r. reflexivity.
  - unfold pf_mb. cbn. lia.
  - cbn. lia.
  - unfold pf_mb. replace (d_FB cx + (2160 + Z.of_nat q + 48 * (j - 1))) with (d_obj cx OT + (48 * (j - 1) + Z.of_nat q))
      by (unfold d_obj, dobj_off; lia). exact Hv.
Qed.

Lemma pfa_afact : forall cx E R T1 j m (q : nat),
  garr8 SEGS m (d_obj cx OT) (map (fun b : byte => bv_unsigned b) T1) -> length T1 = 400%nat -> 1 <= j <= 8 ->
  (q < 6)%nat -> afact_ok (d_env cx E (pfa_vals R T1 j)) (AT_X + 31 + q) (mkAF 0 255 0).
Proof.
  intros cx E R T1 j m q HG HL Hj Hq.
  destruct (garr8_nthZ SEGS m (d_obj cx OT) _ (48 * (j - 1) + Z.of_nat q) HG ltac:(lia)
    ltac:(rewrite length_map, HL; lia)) as [_ Hr].
  unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite pfa_byte by exact Hq. unfold pf_mb.
  rewrite unsigned_lit_small by lia. rewrite Z.pow_0_r, Z.mod_1_r. lia.
Qed.

Section h.
Variable B : asyms.
Variable MT : ameter_ops.
Variable XM_LIB : Z -> Z.
Variables RLO RHI : Z.
Variable tfib_K : asink_syms.

Definition pf_Rj (cx : dcx) (j : Z) (regs : bvmap 5 word) : Prop :=
  getr regs 21 = w64 (shadow_addr (d_FB cx) + 270 + 6 * (j - 1)) /\
  getr regs 22 = w64 (d_obj cx OT + 48 * (j - 1)) /\ getr regs 23 = w64 (j - 1) /\ getr regs 24 = w64 j /\
  getr regs 27 = w64 (d_obj cx OT + 48 * (j - 1) + 2).

Definition pf_Y (cx : dcx) (p count j : Z) (W : world SEGS) (m : word -> option byte) : Prop :=
  a3f_slots cx p count W m /\ 1 <= j <= p + 1 /\
  val_mem SEGS (rd W m) (d_A cx + 392) 8 (d_obj cx OO + 144 * p) /\
  val_mem SEGS (rd W m) (d_A cx + 408) 8 (2 ^ 64 - 1) /\
  garr8 SEGS (rd W m) (d_obj cx OUSED) (a3f_used p).

Definition pf_c1 (cx : dcx) (h i n now op : Z) (W0 : world SEGS) (c0 : config) (T0 T1 : list byte) (buf count : Z)
  (os : list disco_json_reader_model.jobj) (vpad : list byte) (p j : Z) : world SEGS -> config -> Prop :=
  a3f_stg B MT XM_LIB RLO RHI tfib_K cx h i n now op W0 c0 T0 T1 buf count os vpad
    (SIGMA DS___interceptor_trampoline_snprintf - BASE) (-16) dsh_mac
    (fun regs => getr regs 1 = w64 (BASE + PFR1_OFF) /\ pf_Rj cx j regs /\
       getr regs 10 = w64 (d_obj cx OMAC) /\ getr regs 11 = w64 18 /\ getr regs 12 = w64 (VAL (A_OBJ 10)) /\
       getr regs 13 = w64 (pf_mb T1 j 0) /\ getr regs 14 = w64 (pf_mb T1 j 1) /\ getr regs 15 = w64 (pf_mb T1 j 2) /\
       getr regs 16 = w64 (pf_mb T1 j 3) /\ getr regs 17 = w64 (pf_mb T1 j 4) /\
       getr regs 19 = w64 (d_obj cx OMAC))
    (fun W m => pf_Y cx p count j W m /\ val_mem SEGS (rd W m) (d_A cx - 16) 8 (pf_mb T1 j 5)).

Definition pf_c2 (cx : dcx) (h i n now op : Z) (W0 : world SEGS) (c0 : config) (T0 T1 : list byte) (buf count : Z)
  (os : list disco_json_reader_model.jobj) (vpad : list byte) (p j : Z) : world SEGS -> config -> Prop :=
  a3f_st B MT XM_LIB RLO RHI tfib_K cx h i n now op W0 c0 T0 T1 buf count os vpad AF_jtok_is dsh_mac
    (fun regs => getr regs 1 = w64 (BASE + PFR2_OFF) /\ pf_Rj cx j regs /\
       getr regs 10 = w64 (d_obj cx OO + 144 * p) /\ getr regs 11 = w64 1 /\ getr regs 12 = w64 (d_obj cx OMAC))
    (fun W m => pf_Y cx p count j W m /\ garr8 SEGS (rd W m) (d_obj cx OMAC) (pf_mtext T1 j ++ [0])).

Definition pf_c3 (cx : dcx) (h i n now op : Z) (W0 : world SEGS) (c0 : config) (T0 T1 : list byte) (buf count : Z)
  (os : list disco_json_reader_model.jobj) (vpad : list byte) (p j : Z) : world SEGS -> config -> Prop :=
  a3f_st B MT XM_LIB RLO RHI tfib_K cx h i n now op W0 c0 T0 T1 buf count os vpad PFR2_OFF dsh_mac
    (fun regs => pf_Rj cx j regs /\ getr regs 10 = w64 (if j - 1 =? p then 1 else 0))
    (fun W m => pf_Y cx p count j W m).

Definition pfA_stmt (j : Z) : Prop :=
  forall (cx : dcx) (h i n now op : Z) (W0 : world SEGS) (c0 : config) (T0 T1 : list byte) (buf count : Z)
         (os : list disco_json_reader_model.jobj) (vpad : list byte) (p : Z) (W : world SEGS) (c : config),
  f_pf B MT XM_LIB RLO RHI tfib_K cx h i n now op W0 c0 T0 T1 buf count os vpad p j W c ->
  SRr SEGS W c (pf_c1 cx h i n now op W0 c0 T0 T1 buf count os vpad p j).

Definition pfB_stmt : Prop :=
  forall (cx : dcx) (h i n now op : Z) (W0 : world SEGS) (c0 : config) (T0 T1 : list byte) (buf count : Z)
         (os : list disco_json_reader_model.jobj) (vpad : list byte) (p j : Z) (W : world SEGS) (c : config),
  pf_c1 cx h i n now op W0 c0 T0 T1 buf count os vpad p j W c ->
  SRr SEGS W c (pf_c2 cx h i n now op W0 c0 T0 T1 buf count os vpad p j).

Definition pfC_stmt : Prop :=
  forall (cx : dcx) (h i n now op : Z) (W0 : world SEGS) (c0 : config) (T0 T1 : list byte) (buf count : Z)
         (os : list disco_json_reader_model.jobj) (vpad : list byte) (p j : Z) (W : world SEGS) (c : config),
  pf_c2 cx h i n now op W0 c0 T0 T1 buf count os vpad p j W c ->
  SRr SEGS W c (pf_c3 cx h i n now op W0 c0 T0 T1 buf count os vpad p j).

Definition pfD_stmt : Prop :=
  forall (cx : dcx) (h i n now op : Z) (W0 : world SEGS) (c0 : config) (T0 T1 : list byte) (buf count : Z)
         (os : list disco_json_reader_model.jobj) (vpad : list byte) (p j : Z) (W : world SEGS) (c : config),
  pf_c3 cx h i n now op W0 c0 T0 T1 buf count os vpad p j W c ->
  SRr SEGS W c (fun W' c' =>
    (j <= p /\ f_pf B MT XM_LIB RLO RHI tfib_K cx h i n now op W0 c0 T0 T1 buf count os vpad p (j + 1) W' c') \/
    f_pfx B MT XM_LIB RLO RHI tfib_K cx h i n now op W0 c0 T0 T1 buf count os vpad p W' c').

Lemma pf_of_parts : forall p j, pfA_stmt j -> pfB_stmt -> pfC_stmt -> pfD_stmt ->
  seg_pf_pj_spec B MT XM_LIB RLO RHI tfib_K p j.
Proof.
  intros p j HA HB HC HD cx h i n now op W0 c0 T0 T1 buf count os vpad W c Hs.
  eapply SRr_bind; [exact (HA cx h i n now op W0 c0 T0 T1 buf count os vpad p W c Hs)|].
  intros W1 c1 _ H1.
  eapply SRr_bind; [exact (HB cx h i n now op W0 c0 T0 T1 buf count os vpad p j W1 c1 H1)|].
  intros W2 c2 _ H2.
  eapply SRr_bind; [exact (HC cx h i n now op W0 c0 T0 T1 buf count os vpad p j W2 c2 H2)|].
  intros W3 c3 _ H3.
  exact (HD cx h i n now op W0 c0 T0 T1 buf count os vpad p j W3 c3 H3).
Qed.


Hypothesis DSEAT : d_seat_stmt B MT XM_LIB RLO RHI tfib_K.
Hypothesis DFACTS : d_facts_stmt B MT XM_LIB RLO RHI tfib_K.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis PAL : PALib B.

Lemma pfa_seat : forall (fq : YK11.FPState) cx ly3 S3 (W : world SEGS) regs mem3 md3 k E T1 j,
  d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W mem3 md3 k -> d_E cx E ->
  Forall (region_ok SEGS E (rd W mem3)) (d_regions cx dsh_ser2) ->
  rdword (aview SEGS (w_H W) mem3) (d_FB cx + fs_frame_bytes DFRAME_CLASS - 8) =
    Some (flag_addr (c_ly cx) DFRAME_CLASS (c_fpos cx)) ->
  d_rL B cx regs -> getr regs 11 = w64 (shadow_addr (d_FB cx)) ->
  getr regs 21 = w64 (shadow_addr (d_FB cx) + 270 + 6 * (j - 1)) ->
  getr regs 22 = w64 (d_obj cx OT + 48 * (j - 1)) -> getr regs 27 = w64 (d_obj cx OT + 48 * (j - 1) + 2) ->
  garr8 SEGS (rd W mem3) (d_obj cx OT) (map (fun b : byte => bv_unsigned b) T1) -> length T1 = 400%nat ->
  1 <= j <= 8 ->
  regions_wf (d_kregions dsh_ser2 [] (pfa_fcs j) ++ [pfa_stk]) = true -> regions_wf (pfa_rs j) = true ->
  st_ok_pi (fx := fq) SEGS VAL (d_env cx E (pfa_vals regs T1 j))
    (mkSS PF_OFF (pfa_sr (270 + 6 * (j - 1)) (2160 + 48 * (j - 1)) (2162 + 48 * (j - 1))) (pfa_rs j) None
      (d_facts pfa_fa []))
    (restrict (w_H W) (YK11.mkst (fx := fq) regs (Z_to_bv 64 (BASE + PF_OFF)) mem3 (YK11.seg_rom SEGS))).
Proof.
  intros fq cx ly3 S3 W regs mem3 md3 k E T1 j HCTX HE HREG HFLAG HRL R11 R21 R22 R27 HGT HLT1 Hj Hkwf Hwf.
  pose proof HRL as (Rsp & Rgp & Rtp & Rs0 & Rs1 & Rs2 & Rs4 & Rs9).
  pose proof (d_geom B MT XM_LIB RLO RHI tfib_K LAWS cx ly3 S3 W mem3 md3 k HCTX)
    as (GS16 & GSlo & GShi & GF4096 & GFceil & GFapp & GFoff & GF32 & GFpres & GFsh & GSTK & HAR3 & HFin3 & EFA3 & EFL3).
  pose proof alloc_ceiling_lt as Hceil0.
  pose proof (d_A_range cx ltac:(unfold MFRAME, LLVMF_STK in *; lia)) as (GA1 & GA32).
  unfold MFRAME in GA1. unfold LLVMF_STK in GSlo.
  pose proof HE as (EE & E32 & HEI & E60 & EF & ESH).
  assert (HSH : 0 <= shadow_addr (d_FB cx) < 2 ^ 63) by (unfold shadow_addr, SHADOW_OFF; lia).
  set (vals := pfa_vals regs T1 j).
  set (E' := d_env cx E vals).
  assert (Hregs : regs_ok E' (pfa_sr (270 + 6 * (j - 1)) (2160 + 48 * (j - 1)) (2162 + 48 * (j - 1))) regs).
  { apply pfa_regs_ok; try assumption; try lia.
    - unfold w64. rewrite <- Rsp. unfold spZ. symmetry. apply Z_to_bv_bv_unsigned.
    - rewrite R21. unfold w64. f_equal. lia.
    - rewrite R22. unfold w64, d_obj, dobj_off. f_equal. lia.
    - rewrite R27. unfold w64, d_obj, dobj_off. f_equal. lia.
    - unfold SHADOW_OFF. lia. }
  assert (HG : facts_ok E' (d_facts pfa_fa [])).
  { apply (DFACTS LAWS cx ly3 S3 W mem3 md3 k E vals pfa_fa [] HCTX HE); [|exact I].
    unfold pfa_fa. cbn [atoms_ok].
    repeat split; first [ apply (pfa_afact cx E regs T1 j (rd W mem3) 0 HGT HLT1 Hj); lia
                        | apply (pfa_afact cx E regs T1 j (rd W mem3) 1 HGT HLT1 Hj); lia
                        | apply (pfa_afact cx E regs T1 j (rd W mem3) 2 HGT HLT1 Hj); lia
                        | apply (pfa_afact cx E regs T1 j (rd W mem3) 3 HGT HLT1 Hj); lia
                        | apply (pfa_afact cx E regs T1 j (rd W mem3) 4 HGT HLT1 Hj); lia
                        | apply (pfa_afact cx E regs T1 j (rd W mem3) 5 HGT HLT1 Hj); lia
                        | exact I ]. }
  assert (Hfcs : Forall (YP09.chunk_ok SEGS E' (rd W mem3) (d_FB cx)) (pfa_fcs j)).
  { unfold pfa_fcs.
    apply Forall_cons; [apply (pfa_chunk cx E regs T1 j _ 0); [exact HGT | exact HLT1 | exact Hj | lia | lia]|].
    apply Forall_cons; [apply (pfa_chunk cx E regs T1 j _ 1); [exact HGT | exact HLT1 | exact Hj | lia | lia]|].
    apply Forall_cons; [apply (pfa_chunk cx E regs T1 j _ 2); [exact HGT | exact HLT1 | exact Hj | lia | lia]|].
    apply Forall_cons; [apply (pfa_chunk cx E regs T1 j _ 3); [exact HGT | exact HLT1 | exact Hj | lia | lia]|].
    apply Forall_cons; [apply (pfa_chunk cx E regs T1 j _ 4); [exact HGT | exact HLT1 | exact Hj | lia | lia]|].
    apply Forall_cons; [apply (pfa_chunk cx E regs T1 j _ 5); [exact HGT | exact HLT1 | exact Hj | lia | lia]|].
    apply Forall_nil. }
  assert (U60 : bv_unsigned (ew E' 60) = d_A cx).
  { unfold E'. rewrite d_env_old by (unfold AT_FL; lia). rewrite (E60 : ew E 60 = w64 (d_A cx)).
    unfold w64. apply unsigned_lit_small. lia. }
  assert (U2 : bv_unsigned (ew E' 2) = d_S cx).
  { unfold E'. rewrite d_env_old by (unfold AT_FL; lia). rewrite (EE 2%nat 2%bv eq_refl). reflexivity. }
  assert (U516 : bv_unsigned (ew E' 516) = d_FB cx).
  { unfold E'. rewrite d_env_old by (unfold AT_FL; lia). rewrite (EF : ew E 516 = w64 (d_FB cx)).
    unfold w64. apply unsigned_lit_small. lia. }
  assert (U529 : bv_unsigned (ew E' 529) = shadow_addr (d_FB cx)).
  { unfold E'. rewrite d_env_old by (unfold AT_FL; lia). rewrite (ESH : ew E 529 = w64 (shadow_addr (d_FB cx))).
    unfold w64. apply unsigned_lit_small. lia. }
  assert (HEI' : img_env VAL A_LIM E') by (unfold E', d_env; apply img_env_havoc_hi; [exact HEI | unfold AT_FL, A_LIM; lia]).
  pose proof (pa_obj_img 1 ltac:(vm_compute; lia)) as OB1. pose proof (pa_obj_img 66 ltac:(vm_compute; lia)) as OB66.
  assert (U241 : bv_unsigned (ew E' (A_OBJ 1)) = VAL (A_OBJ 1)) by (apply HEI'; vm_compute; lia).
  assert (U307 : bv_unsigned (ew E' (A_OBJ 66)) = VAL (A_OBJ 66)) by (apply HEI'; vm_compute; lia).
  unfold IMG_LO, IMG_TOP in OB1, OB66.
  assert (Hext : Forall (region_ok SEGS E' (rd W mem3)) [pfa_stk]).
  { apply Forall_cons; [|apply Forall_nil]. unfold pfa_stk, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. unfold AT_A. rewrite U60.
    split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
    intros o Ho. apply (apresent_writable SEGS). apply GSTK. unfold LLVMF_STK. lia. }
  assert (Hdx : Forall (fun r => all_disjoint E' r (d_kregions dsh_ser2 [] (pfa_fcs j))) [pfa_stk]).
  { apply Forall_cons; [|apply Forall_nil]. unfold d_kregions, pfa_stk, fshadow_region, got_regionP, bcell_regionP.
    cbn [all_disjoint]. unfold extent_disjoint.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. unfold AT_A, AT_STK, AT_F, AT_SH.
    rewrite U60, U2, U516, U529, U241, U307.
    change (fs_frame_bytes DFRAME_CLASS) with 4096. change (4096 / 8) with 512.
    pose proof asan_consts as (C1 & _).
    unfold shadow_addr, SHADOW_OFF in *. repeat split; lia. }
  pose proof (DSEAT LAWS PAL fq cx dsh_ser2 ly3 S3 W regs mem3 md3 k E PF_OFF
    (pfa_sr (270 + 6 * (j - 1)) (2160 + 48 * (j - 1)) (2162 + 48 * (j - 1))) vals [] (pfa_fcs j) [pfa_stk]
    (d_facts pfa_fa []) HCTX HE HREG HFLAG Hregs HG (Forall_nil _) Hfcs Hext (conj I I) Hdx Hkwf) as HS0.
  exact (st_ok_pi_submem _ _ _ (pfa_rs j) HS0 (pfa_submem j) Hwf).
Qed.
End h.
End f.
End d.
