(* lib/A/ACtlLayImg.v -- a Theorem Labs lane, 2026-10-29.
   proves no function (kind: image facts). The three image facts that a Theorem Labs lane's pb_ctrl_lay_block
   (lib/A/Prog/C_ctrl_lay_block_glue.v, a working branch 43e169975d6, blob 08a730f9dde) takes as
   Section hypotheses and that no lemma stated (rule 24, lookup a Theorem Labs lane 18:5xZ: proof-index exit 4, a
   census-1 sweep of 1081 refs finds no lemma about CTRL_FRAMES 0x9f7e0 or BOX_CATALOGUE 0x9e800):
     HFR_ro  (:442)  lay_img_fr_ro    CTRL_FRAMES   [0x9f7e0, +11 * 24):  read-only, not owned, not errno;
     HCAT_ro (:444)  lay_img_cat_ro   BOX_CATALOGUE [0x9e800, +11 * 296): read-only, not owned, not errno;
     HFR_rom (:447)  lay_img_fr_rom   rows 3 .. 9 of CTRL_FRAMES are image bytes, kind byte r.
   Each statement after its premises is the glue's binder text verbatim (its names resolve as the glue resolves
   them: the same import mix, glue :34-55, :82). The glue's B is general under A.AF0m.CtrlTSyms B (the glue's own
   CTS, :412); lay_img_fr_ro_CtrlB / lay_img_cat_ro_CtrlB are the instances at B := A.AD2l.CtrlB.

   RLO / RHI. Both objects lie in the WRITABLE PT_LOAD [0x9e348, 0xa1000) (.data.rel.ro), so in_roP's first
   disjunct (a non-writable segment, Reusable/APostBase.v:22) is false for their bytes: in_roP holds only through
   its RELRO disjunct RLO <= x < RHI. The glue's RLO / RHI are Section variables (:400), bounded only by RELRO_IMG
   (:402); the top (C_ctrl_emit_as.v:211) takes TLAY at PA_RLO / PA_RHI. So HFR_ro / HCAT_ro are stated with the
   premises `RLO = PA_RLO -> RHI = PA_RHI ->`, as a Theorem Labs lane's ba_img_rows (lib/A/Prog/BuildAsImg.v (at head lib/A/Prog/BuildAsImg.v:141; written on a working branch f1ae402bb2c))
   states them. HFR_rom names neither B nor RLO / RHI and has no premise.

   Proofs. HFR_ro / HCAT_ro by intervals: the object's range lies in [PA_RLO, PA_RHI) = [0x9e380, 0xa07c8)
   (CtrlImg.v:96-97), it misses every row of AF0m's Tfib_owned_static (computed: the rows (0x9e7d0, 0x30),
   (0x9f4b8, 0x328) and (0x9f8e8, 0x58) end or start exactly at the bounds) and the errno word 0x5db76c; the
   exclusions go through CtrlTSyms' ts_owned / ts_errno, as R7.v's r7t_cat_ro (from a working branch 8b0ff2e4e96) (at head
   lib/A/ACtlG/R7.v:786). HFR_rom with fr := C_ctrl_emit_as.CROW r: a per-byte decision over the 7 rows x 24
   bytes, evaluated by vm_compute against SEGS's seg_rom (the same reads a Theorem Labs lane's ba_rowcells_ok makes); the length and
   the kind byte are GE_row.v:31 / :35's ge_row_len / ge_row_k, proved here the same way (GE_row's closure,
   GEbase, is not loaded). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
(* The six modules that exist twice (core lib/Reusable/<X> and ctrl's lib/A/Reusable/<X>) are Required, never
   Imported; seg_rom is written lib.Reusable.YK11.seg_rom, as the glue writes it (:450). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YK11 YK1b YI04 YI16 YM05 YO09.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import
YK0h YK0i YK14 YK1a YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YN3v YI09 YI08 YI00 YI0f.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YE01.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import AB1v.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import
PaTable PaSym PaShadow PaStep PaRun PaJournal CtrlSyms CtrlList CtrlAddr CtrlPa CtrlPaLib CtrlBase CtrlRo
CtrlCallerJ C_reac_box_model_block CtrlImg C_ctrl_lay_block.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require AF0m AD2l.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require C_ctrl_emit_as.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require RcLay.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Open Scope bv_scope.
Open Scope Z_scope.

(* PI_ctrl takes the run context; the glue's Section b (:388) has the same two. *)
Section b. Context {fx : lib.Reusable.YK11.FPState} {rc : lib.Reusable.YM05.RunCeil}.

(* the glue's abbreviations (:92, :393) and the top's relro bounds (C_ctrl_emit_as.v:92-93) *)
#[local] Notation SEGS := AB1v.tfibsegs.
#[local] Notation VAL := (@pa_val _ ctrl_listing PI_ctrl).
#[local] Notation PA_RLO := (@pa_relro_lo _ ctrl_listing PI_ctrl).
#[local] Notation PA_RHI := (@pa_relro_hi _ ctrl_listing PI_ctrl).

(* ---- the listing values the proofs compute with ---- *)
Lemma lay_img_fr_val : VAL (A_OBJ A_FRAMES) = 0x9f7e0.
Proof. vm_compute. reflexivity. Qed.

Lemma lay_img_cat_val : VAL (A_OBJ A_CAT) = 0x9e800.
Proof. vm_compute. reflexivity. Qed.

Lemma lay_img_relro : PA_RLO = 0x9e380 /\ PA_RHI = 0xa07c8.
Proof. split; reflexivity. Qed.

(* An interval [lo, hi) that misses every owned-static row of AF0m (a decision, computed per object below). *)
Definition lay_owned_apart_b (lo hi : Z) : bool :=
  forallb (fun r => (fst r + snd r <=? lo) || (hi <=? fst r)) A.AF0m.Tfib_owned_static.

Lemma lay_owned_apart : forall lo hi x, lay_owned_apart_b lo hi = true -> lo <= x < hi ->
  ~ Exists (in_zr x) A.AF0m.Tfib_owned_static.
Proof.
  intros lo hi x Hc Hx Hex. apply Exists_exists in Hex as (r & Hr & Hz). unfold in_zr in Hz.
  unfold lay_owned_apart_b in Hc. rewrite forallb_forall in Hc. specialize (Hc r Hr).
  apply Bool.orb_prop in Hc as [Hc | Hc]; apply Z.leb_le in Hc; lia.
Qed.

(* ---- HFR_ro (glue :442-443) ---- *)
Lemma lay_img_fr_ro : forall (B : asyms), A.AF0m.CtrlTSyms B -> forall RLO RHI : Z,
  RLO = PA_RLO -> RHI = PA_RHI ->
  forall x, VAL (A_OBJ A_FRAMES) <= x < VAL (A_OBJ A_FRAMES) + 11 * ROW_BYTES ->
  in_roP SEGS RLO RHI x /\ ~ Exists (in_zr x) (as_owned_static B) /\ ~ (as_errno B <= x < as_errno B + 4).
Proof.
  intros B TS RLO RHI -> -> x Hx.
  rewrite lay_img_fr_val in Hx. unfold ROW_BYTES in Hx.
  destruct lay_img_relro as [ELo EHi].
  split; [right; rewrite ELo, EHi; lia|].
  split.
  - rewrite (A.AF0m.ts_owned B TS).
    apply (lay_owned_apart 0x9f7e0 (0x9f7e0 + 11 * 24)); [vm_compute; reflexivity | lia].
  - rewrite (A.AF0m.ts_errno B TS). unfold A.AF0m.TFIB_ERRNO. lia.
Qed.

(* ---- HCAT_ro (glue :444-445) ---- *)
Lemma lay_img_cat_ro : forall (B : asyms), A.AF0m.CtrlTSyms B -> forall RLO RHI : Z,
  RLO = PA_RLO -> RHI = PA_RHI ->
  forall x, VAL (A_OBJ A_CAT) <= x < VAL (A_OBJ A_CAT) + 11 * CAT_BYTES ->
  in_roP SEGS RLO RHI x /\ ~ Exists (in_zr x) (as_owned_static B) /\ ~ (as_errno B <= x < as_errno B + 4).
Proof.
  intros B TS RLO RHI -> -> x Hx.
  rewrite lay_img_cat_val in Hx. unfold CAT_BYTES in Hx.
  destruct lay_img_relro as [ELo EHi].
  split; [right; rewrite ELo, EHi; lia|].
  split.
  - rewrite (A.AF0m.ts_owned B TS).
    apply (lay_owned_apart 0x9e800 (0x9e800 + 11 * 296)); [vm_compute; reflexivity | lia].
  - rewrite (A.AF0m.ts_errno B TS). unfold A.AF0m.TFIB_ERRNO. lia.
Qed.

(* ---- HFR_rom (glue :447-450) ---- *)
(* Byte i of row r of CTRL_FRAMES: SEGS holds a byte there, and it is byte i of C_ctrl_emit_as.CROW r. *)
Definition lay_rom_b (r : Z) (i : nat) : bool :=
  match lib.Reusable.YK11.seg_rom SEGS (Z_to_bv 64 (VAL (A_OBJ A_FRAMES) + ROW_BYTES * r + Z.of_nat i)),
        nth_error (C_ctrl_emit_as.CROW r) i with
  | Some b, Some c => bv_unsigned b =? bv_unsigned c
  | _, _ => false
  end.

Lemma lay_rom_ok : forallb (fun r => forallb (lay_rom_b r) (seq 0 24)) [3; 4; 5; 6; 7; 8; 9] = true.
Proof. vm_compute. reflexivity. Qed.

(* GE_row.v:31 ge_row_len, same proof *)
Lemma lay_row_len : forall r, length (C_ctrl_emit_as.CROW r) = 24%nat.
Proof. intros r. reflexivity. Qed.

(* GE_row.v:35 ge_row_k, same proof *)
Lemma lay_row_k : forall r, 3 <= r <= 9 -> RcLay.ly_k (C_ctrl_emit_as.CROW r) = r.
Proof.
  intros r Hr.
  assert (E : r = 3 \/ r = 4 \/ r = 5 \/ r = 6 \/ r = 7 \/ r = 8 \/ r = 9) by lia.
  destruct E as [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]; reflexivity.
Qed.

Lemma lay_img_fr_rom : forall r, 3 <= r <= 9 -> exists fr : list byte,
  length fr = 24%nat /\ RcLay.ly_k fr = r /\
  forall i, (i < 24)%nat -> exists b, nth_error fr i = Some b /\
    lib.Reusable.YK11.seg_rom SEGS (Z_to_bv 64 (VAL (A_OBJ A_FRAMES) + ROW_BYTES * r + Z.of_nat i)) = Some b.
Proof.
  intros r Hr. exists (C_ctrl_emit_as.CROW r).
  split; [exact (lay_row_len r)|]. split; [exact (lay_row_k r Hr)|].
  intros i Hi.
  assert (Hc : lay_rom_b r i = true).
  { pose proof lay_rom_ok as Hall. rewrite forallb_forall in Hall.
    assert (Hrin : In r [3; 4; 5; 6; 7; 8; 9]) by (cbn; lia).
    specialize (Hall r Hrin). rewrite forallb_forall in Hall. apply Hall. apply in_seq. lia. }
  unfold lay_rom_b in Hc.
  destruct (lib.Reusable.YK11.seg_rom SEGS (Z_to_bv 64 (VAL (A_OBJ A_FRAMES) + ROW_BYTES * r + Z.of_nat i)))
    as [b|] eqn:Erom; [|discriminate].
  destruct (nth_error (C_ctrl_emit_as.CROW r) i) as [c|] eqn:Enth; [|discriminate].
  apply Z.eqb_eq in Hc. exists c. split; [reflexivity|]. f_equal. apply bv_eq. exact Hc.
Qed.

(* ---- the instances at the composition's B := CtrlB (A/AD2l.v CtrlB_syms) ---- *)
Lemma lay_img_fr_ro_CtrlB : forall RLO RHI : Z, RLO = PA_RLO -> RHI = PA_RHI ->
  forall x, VAL (A_OBJ A_FRAMES) <= x < VAL (A_OBJ A_FRAMES) + 11 * ROW_BYTES ->
  in_roP SEGS RLO RHI x /\ ~ Exists (in_zr x) (as_owned_static A.AD2l.CtrlB) /\
  ~ (as_errno A.AD2l.CtrlB <= x < as_errno A.AD2l.CtrlB + 4).
Proof. exact (lay_img_fr_ro A.AD2l.CtrlB A.AD2l.CtrlB_syms). Qed.

Lemma lay_img_cat_ro_CtrlB : forall RLO RHI : Z, RLO = PA_RLO -> RHI = PA_RHI ->
  forall x, VAL (A_OBJ A_CAT) <= x < VAL (A_OBJ A_CAT) + 11 * CAT_BYTES ->
  in_roP SEGS RLO RHI x /\ ~ Exists (in_zr x) (as_owned_static A.AD2l.CtrlB) /\
  ~ (as_errno A.AD2l.CtrlB <= x < as_errno A.AD2l.CtrlB + 4).
Proof. exact (lay_img_cat_ro A.AD2l.CtrlB A.AD2l.CtrlB_syms). Qed.
End b.
