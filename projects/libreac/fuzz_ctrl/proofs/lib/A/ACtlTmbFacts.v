(* lib/A/ACtlTmbFacts.v -- a Theorem Labs lane, 2026-10-29.
   proves no function (kind: image facts; rule 24: no function is proved here, only closed facts of image A's own
   bytes and listing).

   The image premises of cgif's `pb_reac_box_model_block_stmt` (lib/A/Prog/C_reac_box_model_block.v:184-221, blob
   4631d95bcf7) that image A's top lib/A/ACtlAll.v must supply, at the top's instance: B := A.AD2l.CtrlB,
   SEGS := A.AB1v.tfibsegs, RLO / RHI := 0x9e380 / 0xa07c8 (PI_ctrl's pa_relro_lo / pa_relro_hi). Each
   `ctlall_<X>_stmt` is the text of the binder <X> (C_reac_box_model_block.v line in brackets), verbatim up to
   these instantiations, JE := ctlall_JE, and its names written qualified as that file resolves them (Locate):
   IMG_LO / IMG_HI / in_zs are A.Prog.CtrlRo's, pa_val A.Prog.CtrlPa's, A_OBJ A.Prog.PaTable's, garr8 / val_mem /
   mrestrict / aview / arodata_okS lib.Reusable's YI00 / YI04 / YK04 / YG0n / YE01, J13 / J14 lib.Prog.RcSynth's.
   AMEMSET / AMEMCPY (:189 / :190) are not here: SIGMA GS___asan_memset / GS___asan_memcpy are the raw runtime
   entries 0x524c4 / 0x52028 (A.Prog.CtrlAddr.ctrl_sigma), not the wrap entries of A.AD1o's oset_of_icpt /
   ocpy_of_icpt (0x52020 / 0x52024); a Theorem Labs lane supplies them (a Theorem Labs lane 22:13Z).

   JE (:197) is the jump table's seven 32-bit words at VAL (A_OBJ A_BMB_JT) = 0x219f4 (.rodata, read with pyelftools
   from the unstripped build of the pin, (internal path) sha256 78efaeda1de5: 0x64294 0x644f8
   0x644b8 0x644c4 0x6442c 0x64510 0x645a4, the values the spec comment lists, :174-176); like BMB_JOFF, k >= 6 gives
   word 6. ctlall_HJT_e checks them against the image itself: tfibsegs's bytes, by vm_compute.

   The proofs (proof parts by two child Theorem Labs lanes, folded here): the range facts and HJT_pos /
   HJT_eq by computation; HJT_e / HJ13 / HJ14 by a per-byte decision (tmb_cell_b: a non-writable segment of SEGS,
   outside as_owned_static CtrlB and the errno word, and SEGS's byte there) read through arodata_okS's segment
   disjunct (tmb_cell_read); HZS_J13 / HZS_J14 by a row of as_zero_shadow CtrlB, as image B's twin. The closing
   `Check` (FIT) applies a proof of pb_reac_box_model_block_stmt at CtrlB / RLO / RHI to the eleven facts. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YM05.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YE01 OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YG0n.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK04 OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YI04.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YI00.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11 OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YP09.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YG0f OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YO0f.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require AB1v AD2l.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require PaTable CtrlList CtrlPa CtrlImg CtrlRo.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require C_reac_box_model_block.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require RcSynth.
Import ListNotations.
Local Open Scope Z_scope.

#[local] Notation SEGS := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.AB1v.tfibsegs.
#[local] Notation CtrlB := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.AD2l.CtrlB.
#[local] Notation RLO := 0x9e380.
#[local] Notation RHI := 0xa07c8.
#[local] Notation VAL := (@lib.A.Prog.CtrlPa.pa_val _ lib.A.Prog.CtrlList.ctrl_listing lib.A.Prog.CtrlImg.PI_ctrl).
#[local] Notation A_OBJ := lib.A.Prog.PaTable.A_OBJ.
#[local] Notation IMG_LO := lib.A.Prog.CtrlRo.IMG_LO.
#[local] Notation IMG_HI := lib.A.Prog.CtrlRo.IMG_HI.
#[local] Notation A_BMB_JT := lib.A.Prog.C_reac_box_model_block.A_BMB_JT.
#[local] Notation A_JOIN_0013 := lib.A.Prog.C_reac_box_model_block.A_JOIN_0013.
#[local] Notation A_JOIN_0014 := lib.A.Prog.C_reac_box_model_block.A_JOIN_0014.

(* JE (:197): the jump table's word k. *)
Definition ctlall_JE (k : Z) : Z :=
if k =? 0 then 0x64294 else if k =? 1 then 0x644f8 else if k =? 2 then 0x644b8 else if k =? 3 then 0x644c4
else if k =? 4 then 0x6442c else if k =? 5 then 0x64510 else 0x645a4.

Section TmbFacts.
Context {rc : lib.Reusable.YM05.RunCeil}.

(* HJT_rng (:198) *)
Definition ctlall_HJT_rng_stmt : Prop :=
IMG_LO + 64 <= VAL (A_OBJ A_BMB_JT) /\ VAL (A_OBJ A_BMB_JT) + 28 + 64 <= IMG_HI.
(* HJT_pos (:199) *)
Definition ctlall_HJT_pos_stmt : Prop :=
forall k, 0 <= k <= 6 -> 0 <= ctlall_JE k < 2 ^ 31.
(* HJT_eq (:200-201) *)
Definition ctlall_HJT_eq_stmt : Prop :=
forall k, 0 <= k <= 6 ->
   VAL (A_OBJ A_BMB_JT) + ctlall_JE k = lib.A.Prog.C_reac_box_model_block.A_reac_box_model_blockP + lib.A.Prog.C_reac_box_model_block.BMB_JOFF k.
(* HJT_e (:202-204) *)
Definition ctlall_HJT_e_stmt : Prop :=
forall (H : word -> bool) mem k, 0 <= k <= 6 ->
   lib.Reusable.YE01.arodata_okS SEGS CtrlB RLO RHI (lib.Reusable.YG0n.aview SEGS H mem) ->
   lib.Reusable.YI04.val_mem SEGS (lib.Reusable.YK04.mrestrict H mem) (VAL (A_OBJ A_BMB_JT) + 4 * k) 4 (ctlall_JE k).
(* HJ13_rng (:205) *)
Definition ctlall_HJ13_rng_stmt : Prop :=
IMG_LO + 64 <= VAL (A_OBJ A_JOIN_0013) /\ VAL (A_OBJ A_JOIN_0013) + 32 + 64 <= IMG_HI.
(* HJ14_rng (:206) *)
Definition ctlall_HJ14_rng_stmt : Prop :=
IMG_LO + 64 <= VAL (A_OBJ A_JOIN_0014) /\ VAL (A_OBJ A_JOIN_0014) + 32 + 64 <= IMG_HI.
(* HJ13 (:207-209) *)
Definition ctlall_HJ13_stmt : Prop :=
forall (H : word -> bool) mem,
   lib.Reusable.YE01.arodata_okS SEGS CtrlB RLO RHI (lib.Reusable.YG0n.aview SEGS H mem) ->
   lib.Reusable.YI00.garr8 SEGS (lib.Reusable.YK04.mrestrict H mem) (VAL (A_OBJ A_JOIN_0013))
     (lib.A.Prog.C_reac_box_model_block.bmb_z lib.Prog.RcSynth.J13).
(* HJ14 (:210-212) *)
Definition ctlall_HJ14_stmt : Prop :=
forall (H : word -> bool) mem,
   lib.Reusable.YE01.arodata_okS SEGS CtrlB RLO RHI (lib.Reusable.YG0n.aview SEGS H mem) ->
   lib.Reusable.YI00.garr8 SEGS (lib.Reusable.YK04.mrestrict H mem) (VAL (A_OBJ A_JOIN_0014))
     (lib.A.Prog.C_reac_box_model_block.bmb_z lib.Prog.RcSynth.J14).
(* HZS_J13 (:219) *)
Definition ctlall_HZS_J13_stmt : Prop :=
lib.A.Prog.CtrlRo.in_zs CtrlB (VAL (A_OBJ A_JOIN_0013)) 32.
(* HZS_J14 (:220) *)
Definition ctlall_HZS_J14_stmt : Prop :=
lib.A.Prog.CtrlRo.in_zs CtrlB (VAL (A_OBJ A_JOIN_0014)) 32.

(* ---- the proofs: closed listing facts by computation, and image bytes read through arodata_okS ---- *)
(* A decision per byte at CtrlB: a lies in a NON-writable segment of SEGS (arodata_okS's segment disjunct, so the
   relro window plays no part), outside every as_owned_static row and the errno word of CtrlB, and SEGS holds there a
   byte whose value is v. *)
Definition tmb_ro_b (a : Z) : bool :=
  existsb (fun s => negb (seg_writable s) && (Z.of_N (seg_base s) <=? a) && (a <? Z.of_N (seg_base s) + Z.of_N (seg_size s)))
    SEGS.
Definition tmb_owned_b (a : Z) : bool :=
  existsb (fun r => (fst r <=? a) && (a <? fst r + snd r)) (lib.Reusable.YG0f.as_owned_static CtrlB).
Definition tmb_cell_b (a v : Z) : bool :=
  tmb_ro_b a && negb (tmb_owned_b a)
  && negb ((lib.Reusable.YG0f.as_errno CtrlB <=? a) && (a <? lib.Reusable.YG0f.as_errno CtrlB + 4))
  && match lib.Reusable.YK11.seg_rom SEGS (Z_to_bv 64 a) with Some b => bv_unsigned b =? v | None => false end.

Lemma tmb_ro_b_sound : forall a, tmb_ro_b a = true ->
  exists s, In s SEGS /\ seg_writable s = false /\ Z.of_N (seg_base s) <= a < Z.of_N (seg_base s) + Z.of_N (seg_size s).
Proof.
  intros a H. unfold tmb_ro_b in H. apply existsb_exists in H. destruct H as (s & Hin & Hs).
  rewrite !andb_true_iff, negb_true_iff, Z.leb_le, Z.ltb_lt in Hs. destruct Hs as [[Hw Hlo] Hhi].
  exists s. repeat split; assumption.
Qed.

Lemma tmb_owned_b_sound : forall a, tmb_owned_b a = false ->
  ~ Exists (lib.Reusable.YG0n.in_zr a) (lib.Reusable.YG0f.as_owned_static CtrlB).
Proof.
  intros a H HE. apply Exists_exists in HE. destruct HE as (r & Hin & Hr). unfold lib.Reusable.YG0n.in_zr in Hr.
  assert (Hx : existsb (fun r => (fst r <=? a) && (a <? fst r + snd r)) (lib.Reusable.YG0f.as_owned_static CtrlB) = true).
  { apply existsb_exists. exists r. split; [exact Hin|]. rewrite andb_true_iff, Z.leb_le, Z.ltb_lt. lia. }
  unfold tmb_owned_b in H. rewrite Hx in H. discriminate.
Qed.

(* a decided byte, read through arodata_okS at any relro window *)
Lemma tmb_cell_read : forall a v rlo rhi (H : word -> bool) mem, tmb_cell_b a v = true ->
  lib.Reusable.YE01.arodata_okS SEGS CtrlB rlo rhi (lib.Reusable.YG0n.aview SEGS H mem) ->
  0 <= v < 256 /\ lib.Reusable.YP09.mbyte SEGS (lib.Reusable.YK04.mrestrict H mem) a = Some (Z_to_bv 8 v).
Proof.
  intros a v rlo rhi H mem Hc HRO. unfold tmb_cell_b in Hc. rewrite !andb_true_iff, !negb_true_iff in Hc.
  destruct Hc as [[[Hro Hown] Herr] Hbyte].
  assert (Hrd : lib.Reusable.YG0n.aview SEGS H mem a =
    option_map (fun b : byte => bv_unsigned b) (lib.Reusable.YK11.seg_rom SEGS (Z_to_bv 64 a))).
  { apply HRO.
    - left. exact (tmb_ro_b_sound a Hro).
    - exact (tmb_owned_b_sound a Hown).
    - rewrite andb_false_iff, Z.leb_gt, Z.ltb_ge in Herr. lia. }
  destruct (lib.Reusable.YK11.seg_rom SEGS (Z_to_bv 64 a)) as [b0|] eqn:Erom; [|discriminate].
  apply Z.eqb_eq in Hbyte. subst v.
  split; [apply bv_unsigned_in_range|].
  unfold lib.Reusable.YG0n.aview in Hrd.
  destruct (lib.Reusable.YP09.mbyte SEGS (lib.Reusable.YK04.mrestrict H mem) a) as [b|] eqn:Eb; cbn in Hrd; [|discriminate].
  injection Hrd as Hbu. f_equal. apply bv_eq. rewrite Hbu, Z_to_bv_unsigned.
  unfold bv_wrap, bv_modulus. rewrite Z.mod_small; [reflexivity | apply bv_unsigned_in_range].
Qed.

Lemma tmb_le_byte_1 : forall v, 0 <= v < 256 -> lib.Reusable.YO0f.le_byte v 1 0 = v.
Proof.
  intros v Hv. unfold lib.Reusable.YO0f.le_byte. change (2 ^ (8 * Z.of_nat 1)) with 256.
  change (8 * Z.of_nat 0) with 0.
  rewrite Z.shiftr_0_r, (Z.mod_small v 256) by lia. apply Z.mod_small. lia.
Qed.

(* a byte list whose every byte is decided is garr8 at base *)
Definition tmb_block_b (base : Z) (l : list Z) : bool :=
  forallb (fun j => tmb_cell_b (base + Z.of_nat j) (nth j l 0)) (seq 0 (length l)).

Lemma tmb_garr8 : forall base l rlo rhi, tmb_block_b base l = true -> forall (H : word -> bool) mem,
  lib.Reusable.YE01.arodata_okS SEGS CtrlB rlo rhi (lib.Reusable.YG0n.aview SEGS H mem) ->
  lib.Reusable.YI00.garr8 SEGS (lib.Reusable.YK04.mrestrict H mem) base l.
Proof.
  intros base l rlo rhi Hb H mem HRO j Hj.
  unfold tmb_block_b in Hb. rewrite forallb_forall in Hb.
  assert (Hc : tmb_cell_b (base + Z.of_nat j) (nth j l 0) = true) by (apply Hb; apply in_seq; lia).
  destruct (tmb_cell_read _ _ _ _ H mem Hc HRO) as [Hrng Hrd].
  split; [|exact Hrng].
  intros k Hk. assert (k = 0%nat) by lia. subst k. change (Z.of_nat 0) with 0.
  rewrite Z.add_0_r, (tmb_le_byte_1 _ Hrng). exact Hrd.
Qed.

(* HJT_rng *)
Lemma ctlall_HJT_rng : ctlall_HJT_rng_stmt.
Proof. unfold ctlall_HJT_rng_stmt. split; apply Z.leb_le; vm_compute; reflexivity. Qed.

(* HJT_pos: the seven words are below 2 ^ 31 *)
Lemma ctlall_HJT_pos : ctlall_HJT_pos_stmt.
Proof.
  unfold ctlall_HJT_pos_stmt. intros k Hk.
  assert (Hc : k = 0 \/ k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6) by lia.
  destruct Hc as [->|[->|[->|[->|[->|[->| ->]]]]]]; (split; [apply Z.leb_le | apply Z.ltb_lt]; vm_compute; reflexivity).
Qed.

(* HJT_eq: the table's base 0x219f4 plus word k is the case's pc *)
Lemma ctlall_HJT_eq : ctlall_HJT_eq_stmt.
Proof.
  unfold ctlall_HJT_eq_stmt. intros k Hk.
  assert (Hc : k = 0 \/ k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6) by lia.
  destruct Hc as [->|[->|[->|[->|[->|[->| ->]]]]]]; apply Z.eqb_eq; vm_compute; reflexivity.
Qed.

(* HJT_e: the 4 x 7 bytes of the table, each its word's little-endian byte, decided at once *)
Lemma tmb_jt_ok : forallb (fun k => forallb (fun j =>
    tmb_cell_b (VAL (A_OBJ A_BMB_JT) + 4 * k + Z.of_nat j) (lib.Reusable.YO0f.le_byte (ctlall_JE k) 4 j))
    (seq 0 4)) [0; 1; 2; 3; 4; 5; 6] = true.
Proof. vm_compute. reflexivity. Qed.

Lemma ctlall_HJT_e : ctlall_HJT_e_stmt.
Proof.
  unfold ctlall_HJT_e_stmt. intros H mem k Hk HRO j Hj.
  pose proof tmb_jt_ok as Hall. rewrite forallb_forall in Hall.
  assert (Hkin : In k [0; 1; 2; 3; 4; 5; 6]) by (cbn; lia).
  specialize (Hall k Hkin). rewrite forallb_forall in Hall.
  assert (Hc : tmb_cell_b (VAL (A_OBJ A_BMB_JT) + 4 * k + Z.of_nat j) (lib.Reusable.YO0f.le_byte (ctlall_JE k) 4 j) = true)
    by (apply Hall; apply in_seq; lia).
  exact (proj2 (tmb_cell_read _ _ _ _ H mem Hc HRO)).
Qed.

(* HJ13_rng / HJ14_rng *)
Lemma ctlall_HJ13_rng : ctlall_HJ13_rng_stmt.
Proof. unfold ctlall_HJ13_rng_stmt. split; apply Z.leb_le; vm_compute; reflexivity. Qed.

Lemma ctlall_HJ14_rng : ctlall_HJ14_rng_stmt.
Proof. unfold ctlall_HJ14_rng_stmt. split; apply Z.leb_le; vm_compute; reflexivity. Qed.

(* HJ13 / HJ14: the 32 bytes of JOIN_0013 / JOIN_0014 (.rodata) *)
Lemma tmb_j13_ok : tmb_block_b (VAL (A_OBJ A_JOIN_0013)) (lib.A.Prog.C_reac_box_model_block.bmb_z lib.Prog.RcSynth.J13) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma tmb_j14_ok : tmb_block_b (VAL (A_OBJ A_JOIN_0014)) (lib.A.Prog.C_reac_box_model_block.bmb_z lib.Prog.RcSynth.J14) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma ctlall_HJ13 : ctlall_HJ13_stmt.
Proof. unfold ctlall_HJ13_stmt. intros H mem HRO. exact (tmb_garr8 _ _ _ _ tmb_j13_ok H mem HRO). Qed.

Lemma ctlall_HJ14 : ctlall_HJ14_stmt.
Proof. unfold ctlall_HJ14_stmt. intros H mem HRO. exact (tmb_garr8 _ _ _ _ tmb_j14_ok H mem HRO). Qed.

(* HZS_J13 / HZS_J14: each JOIN block lies in one as_zero_shadow row of CtrlB (rows (0x219e0, 0x60) and (0x21a60,
   0x20) of Tfib_zero_shadow, AF0m.v:2962-2963) *)
Lemma tmb_in_zs : forall a n,
  existsb (fun r : Z * Z => (fst r <=? a) && (a + n <=? fst r + snd r)) (lib.Reusable.YG0f.as_zero_shadow CtrlB) = true ->
  lib.A.Prog.CtrlRo.in_zs CtrlB a n.
Proof.
  intros a n H. unfold lib.A.Prog.CtrlRo.in_zs.
  apply existsb_exists in H as ([q m] & Hin & Hb). exists q, m. apply andb_true_iff in Hb as [H1 H2].
  apply Z.leb_le in H1. apply Z.leb_le in H2. cbn [fst snd] in *. split; [exact Hin | lia].
Qed.

Lemma ctlall_HZS_J13 : ctlall_HZS_J13_stmt.
Proof. unfold ctlall_HZS_J13_stmt. apply tmb_in_zs. vm_compute. reflexivity. Qed.

Lemma ctlall_HZS_J14 : ctlall_HZS_J14_stmt.
Proof. unfold ctlall_HZS_J14_stmt. apply tmb_in_zs. vm_compute. reflexivity. Qed.

End TmbFacts.

(* FIT: the eleven facts fill the binders JE .. HZS_J14 of pb_reac_box_model_block_stmt at CtrlB / RLO / RHI: for any
   P proving it, P applied to its other premises (lambda binders typed by unification), ctlall_JE and the ten lemmas
   type-checks. *)
Check (fun fx rc SK GLOBS
  (P : @lib.A.Prog.C_reac_box_model_block.pb_reac_box_model_block_stmt fx rc SK CtrlB GLOBS RLO RHI)
  RELRO ROFL TL LAWS ML AMEMSET AMEMCPY ASM0 SMP ASF FFL TLF HGM HIMGSH =>
  P RELRO ROFL TL LAWS ML AMEMSET AMEMCPY ASM0 SMP ASF FFL TLF ctlall_JE
    ctlall_HJT_rng ctlall_HJT_pos ctlall_HJT_eq ctlall_HJT_e ctlall_HJ13_rng ctlall_HJ14_rng ctlall_HJ13 ctlall_HJ14
    HGM HIMGSH ctlall_HZS_J13 ctlall_HZS_J14).
