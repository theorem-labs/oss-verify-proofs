(* lib/A/Prog/BuildAsImg.v -- a Theorem Labs lane, 2026-10-29.
   proves no function (kind: image facts). The image-A facts that pb_reac_ctrl_build_as_stmt (lib/A/Prog/
   C_reac_ctrl_build_as.v) takes as binders about the switch table CTRL_FRAMES_SWITCH (A_OBJ 20, 0x21980, 56 bytes)
   and the box catalogue BOX_CATALOGUE (A_OBJ 17, 0x9e800, 3256 bytes), proved for image A (a Theorem Labs lane 17:47Z, from
   a Theorem Labs lane's top discharge table v2): HSW_al, HCAT_al, HSW_rng, HCAT_rng (closed listing facts) and HSW_e (the
   switch-table words read through arodata_okS; it needs CtrlTSyms B for the owned-static and errno exclusions).
   Each statement is the pb_ binder's text verbatim. + HROWS of ctrl_emit_as's pb_ statement (ba_img_rows, a Theorem Labs lane
   18:41Z). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00 YI0f YI16.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YE01.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import AB1v.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require AF0m ACtlGlobs.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import
PaTable PaSym PaShadow PaStep PaRun PaJournal CtrlSyms CtrlList CtrlAddr CtrlPa CtrlImg CtrlPaLib CtrlBase CtrlRo
CtrlCallerJ C_reac_box_model_block C_ctrl_lay_block C_ctrl_emit_as C_reac_ctrl_build_as.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require reac_ctrl_build_as_c.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Section b. Context {fx : lib.Reusable.YK11.FPState} {rc : lib.Reusable.YM05.RunCeil}.
Context {SK : lib.Reusable.YI16.sink_head}.
#[local] Notation SEGS := AB1v.tfibsegs.
#[local] Notation VAL := (@pa_val _ ctrl_listing PI_ctrl).

(* ---- closed listing facts (HSW_al, HCAT_al, HSW_rng, HCAT_rng) ---- *)
Lemma ba_img_sw_al : VAL (A_OBJ A_SW) mod 8 = 0.
Proof. vm_compute. reflexivity. Qed.

Lemma ba_img_cat_al : VAL (A_OBJ A_CAT) mod 8 = 0.
Proof. vm_compute. reflexivity. Qed.

Lemma ba_img_sw_rng : IMG_LO + 64 <= VAL (A_OBJ A_SW) /\ VAL (A_OBJ A_SW) + SW_BYTES + 64 <= IMG_HI.
Proof. split; apply Z.leb_le; vm_compute; reflexivity. Qed.

Lemma ba_img_cat_rng : IMG_LO + 64 <= VAL (A_OBJ A_CAT) /\ VAL (A_OBJ A_CAT) + 11 * CAT_BYTES + 64 <= IMG_HI.
Proof. split; apply Z.leb_le; vm_compute; reflexivity. Qed.

(* ---- HSW_glob / HCAT_glob: against a Theorem Labs lane's image-A registered-globals list (lib/A/ACtlGlobs.v, a working branch
   86f27fff835; a Theorem Labs lane 17:52Z: one definition, a Theorem Labs lane's), whose two rows a Theorem Labs lane proves there. ---- *)
Lemma ba_img_sw_glob : In (VAL (A_OBJ A_SW), SW_BYTES) ACtlGlobs.ctrl_globs_A.
Proof.
  replace (VAL (A_OBJ A_SW)) with 0x21980 by (vm_compute; reflexivity). unfold SW_BYTES.
  exact ACtlGlobs.ctrl_globs_A_sw.
Qed.

Lemma ba_img_cat_glob : In (VAL (A_OBJ A_CAT), 11 * CAT_BYTES) ACtlGlobs.ctrl_globs_A.
Proof.
  replace (VAL (A_OBJ A_CAT)) with 0x9e800 by (vm_compute; reflexivity).
  replace (11 * CAT_BYTES) with 3256 by reflexivity.
  exact ACtlGlobs.ctrl_globs_A_cat.
Qed.

(* ---- HSW_e: the seven switch-table words, read through arodata_okS ---- *)
(* A decision per byte: the address lies in a read-only segment of SEGS, outside every owned-static range and the
   errno word of image A's symbol record, and SEGS holds there the byte of ba_row k's little-endian word. *)
Definition ba_ro_b (a : Z) : bool :=
  existsb (fun s => negb (seg_writable s) && (Z.of_N (seg_base s) <=? a) && (a <? Z.of_N (seg_base s) + Z.of_N (seg_size s)))
    SEGS.
Definition ba_owned_b (a : Z) : bool :=
  existsb (fun r => (fst r <=? a) && (a <? fst r + snd r)) AF0m.Tfib_owned_static.
Definition ba_byte_b (a v : Z) : bool :=
  match seg_rom SEGS (Z_to_bv 64 a) with Some b => bv_unsigned b =? v | None => false end.
Definition ba_cell_b (k : Z) (j : nat) : bool :=
  let a := VAL (A_OBJ A_SW) + 8 * k + Z.of_nat j in
  ba_ro_b a && negb (ba_owned_b a) && negb ((AF0m.TFIB_ERRNO <=? a) && (a <? AF0m.TFIB_ERRNO + 4))
  && ba_byte_b a (le_byte (reac_ctrl_build_as_c.ba_row k) 8 j).

Lemma ba_cells_ok : forallb (fun k => forallb (ba_cell_b k) (seq 0 8)) [0; 1; 2; 3; 4; 5; 6] = true.
Proof. vm_compute. reflexivity. Qed.

Lemma ba_ro_b_sound : forall a, ba_ro_b a = true ->
  exists s, In s SEGS /\ seg_writable s = false /\ Z.of_N (seg_base s) <= a < Z.of_N (seg_base s) + Z.of_N (seg_size s).
Proof.
  intros a H. unfold ba_ro_b in H. apply existsb_exists in H. destruct H as (s & Hin & Hs).
  rewrite !andb_true_iff, negb_true_iff, Z.leb_le, Z.ltb_lt in Hs. destruct Hs as [[Hw Hlo] Hhi].
  exists s. repeat split; assumption.
Qed.

Lemma ba_owned_b_sound : forall a, ba_owned_b a = false -> ~ Exists (in_zr a) AF0m.Tfib_owned_static.
Proof.
  intros a H HE. apply Exists_exists in HE. destruct HE as (r & Hin & Hr). unfold in_zr in Hr.
  assert (Hx : existsb (fun r => (fst r <=? a) && (a <? fst r + snd r)) AF0m.Tfib_owned_static = true).
  { apply existsb_exists. exists r. split; [exact Hin|]. rewrite andb_true_iff, Z.leb_le, Z.ltb_lt. lia. }
  unfold ba_owned_b in H. rewrite Hx in H. discriminate.
Qed.

Lemma ba_img_sw_e : forall (B : asyms), AF0m.CtrlTSyms B -> forall RLO RHI,
  forall k, 0 <= k <= 6 -> forall (H : word -> bool) mem,
  arodata_okS SEGS B RLO RHI (aview SEGS H mem) ->
  lib.Reusable.YI04.val_mem SEGS (mrestrict H mem) (VAL (A_OBJ A_SW) + 8 * k) 8 (reac_ctrl_build_as_c.ba_row k).
Proof.
  intros B TS RLO RHI k Hk H mem HRO j Hj.
  assert (Hc : ba_cell_b k j = true).
  { pose proof ba_cells_ok as Hall. rewrite forallb_forall in Hall.
    assert (Hkin : In k [0; 1; 2; 3; 4; 5; 6]) by (cbn; lia).
    specialize (Hall k Hkin). rewrite forallb_forall in Hall. apply Hall. apply in_seq. lia. }
  unfold ba_cell_b in Hc. rewrite !andb_true_iff, !negb_true_iff in Hc.
  destruct Hc as [[[Hro Hown] Herr] Hbyte].
  set (a := VAL (A_OBJ A_SW) + 8 * k + Z.of_nat j) in *.
  replace (VAL (A_OBJ A_SW) + 8 * k + Z.of_nat j) with a by reflexivity.
  assert (Hrd : aview SEGS H mem a = option_map (fun b : byte => bv_unsigned b) (seg_rom SEGS (Z_to_bv 64 a))).
  { apply HRO.
    - left. exact (ba_ro_b_sound a Hro).
    - rewrite (AF0m.ts_owned B TS). exact (ba_owned_b_sound a Hown).
    - rewrite (AF0m.ts_errno B TS). rewrite andb_false_iff, Z.leb_gt, Z.ltb_ge in Herr. lia. }
  unfold ba_byte_b in Hbyte. destruct (seg_rom SEGS (Z_to_bv 64 a)) as [b0|] eqn:Erom; [|discriminate].
  apply Z.eqb_eq in Hbyte.
  unfold aview in Hrd. destruct (mbyte SEGS (mrestrict H mem) a) as [b|] eqn:Eb; cbn in Hrd; [|discriminate].
  injection Hrd as Hbu. f_equal. apply bv_eq. rewrite Hbu, Hbyte, Z_to_bv_unsigned.
  unfold bv_wrap, bv_modulus. rewrite Z.mod_small; [reflexivity|]. unfold le_byte.
  split; [apply Z.mod_pos_bound; lia|].
  eapply Z.lt_le_trans; [apply Z.mod_pos_bound; lia|]. apply Z.leb_le. vm_compute. reflexivity.
Qed.
(* ---- HROWS (a binder of ctrl_emit_as's pb_ statement, C_ctrl_emit_as.v:233, verbatim with its names
   qualified as that file resolves them: A_FRAMES / ROW_BYTES from C_ctrl_lay_block, CROW from C_ctrl_emit_as):
   rows 3 .. 9 of CTRL_FRAMES (0x9f7e0, 24 bytes each) read through arodata_okS (a Theorem Labs lane 18:41Z). CTRL_FRAMES lies
   in a WRITABLE segment (.data.rel.ro, PT_LOAD 0x9e348 RW), so the read comes from arodata_okS's RELRO disjunct:
   the lemma holds at RLO = PA_RLO, RHI = PA_RHI (a Theorem Labs lane's pb_ctrl_emit_as_on takes exactly HRLO / HRHI). Per-byte
   decision over the 168 bytes, by vm_compute. ---- *)
Definition ba_rowcell_b (r : Z) (j : nat) : bool :=
  let a := VAL (A_OBJ C_ctrl_lay_block.A_FRAMES) + C_ctrl_lay_block.ROW_BYTES * r + Z.of_nat j in
  ((@pa_relro_lo _ ctrl_listing PI_ctrl <=? a) && (a <? @pa_relro_hi _ ctrl_listing PI_ctrl)) && negb (ba_owned_b a) && negb ((AF0m.TFIB_ERRNO <=? a) && (a <? AF0m.TFIB_ERRNO + 4))
  && ba_byte_b a (le_byte (nth j (map bv_unsigned (C_ctrl_emit_as.CROW r)) 0) 1 0).

Lemma ba_rowcells_ok : forallb (fun r => forallb (ba_rowcell_b r) (seq 0 24)) [3; 4; 5; 6; 7; 8; 9] = true.
Proof. vm_compute. reflexivity. Qed.

Lemma ba_img_rows : forall (B : asyms), AF0m.CtrlTSyms B -> forall RLO RHI,
  RLO = @pa_relro_lo _ ctrl_listing PI_ctrl -> RHI = @pa_relro_hi _ ctrl_listing PI_ctrl ->
  forall r, 3 <= r <= 9 -> forall (H : word -> bool) mem,
  arodata_okS SEGS B RLO RHI (aview SEGS H mem) ->
  garr8 SEGS (mrestrict H mem) (VAL (A_OBJ C_ctrl_lay_block.A_FRAMES) + C_ctrl_lay_block.ROW_BYTES * r)
    (map bv_unsigned (C_ctrl_emit_as.CROW r)).
Proof.
  intros B TS RLO RHI HRLO HRHI r Hr H mem HRO j Hj.
  rewrite length_map in Hj. assert (Hl : length (C_ctrl_emit_as.CROW r) = 24%nat) by reflexivity.
  rewrite Hl in Hj.
  split.
  2:{ rewrite (nth_indep _ 0 (bv_unsigned (Z_to_bv 8 0))) by (rewrite length_map, Hl; exact Hj).
      rewrite map_nth. apply bv_unsigned_in_range. }
  intros k Hk. assert (k = 0%nat) by lia. subst k. rewrite Z.add_0_r.
  assert (Hc : ba_rowcell_b r j = true).
  { pose proof ba_rowcells_ok as Hall. rewrite forallb_forall in Hall.
    assert (Hrin : In r [3; 4; 5; 6; 7; 8; 9]) by (cbn; lia).
    specialize (Hall r Hrin). rewrite forallb_forall in Hall. apply Hall. apply in_seq. lia. }
  unfold ba_rowcell_b in Hc. rewrite !andb_true_iff, !negb_true_iff in Hc.
  destruct Hc as [[[[Hlo Hhi] Hown] Herr] Hbyte]. apply Z.leb_le in Hlo. apply Z.ltb_lt in Hhi.
  set (a := VAL (A_OBJ C_ctrl_lay_block.A_FRAMES) + C_ctrl_lay_block.ROW_BYTES * r + Z.of_nat j) in *.
  assert (Hrd : aview SEGS H mem a = option_map (fun b : byte => bv_unsigned b) (seg_rom SEGS (Z_to_bv 64 a))).
  { apply HRO.
    - right. subst RLO RHI. split; assumption.
    - rewrite (AF0m.ts_owned B TS). exact (ba_owned_b_sound a Hown).
    - rewrite (AF0m.ts_errno B TS). rewrite andb_false_iff, Z.leb_gt, Z.ltb_ge in Herr. lia. }
  unfold ba_byte_b in Hbyte. destruct (seg_rom SEGS (Z_to_bv 64 a)) as [b0|] eqn:Erom; [|discriminate].
  apply Z.eqb_eq in Hbyte.
  unfold aview in Hrd. destruct (mbyte SEGS (mrestrict H mem) a) as [b|] eqn:Eb; cbn in Hrd; [|discriminate].
  injection Hrd as Hbu. f_equal. apply bv_eq. rewrite Hbu, Hbyte, Z_to_bv_unsigned.
  unfold bv_wrap, bv_modulus. rewrite Z.mod_small; [reflexivity|]. unfold le_byte.
  split; [apply Z.mod_pos_bound; lia|].
  eapply Z.lt_le_trans; [apply Z.mod_pos_bound; lia|]. apply Z.leb_le. vm_compute. reflexivity.
Qed.
End b.
