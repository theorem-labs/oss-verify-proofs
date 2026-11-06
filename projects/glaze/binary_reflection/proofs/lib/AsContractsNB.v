(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
Require Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.glaze.binary_reflection.images.Asan OSSVerify.glaze.binary_reflection.images.AsanUbsan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module AsRtImg.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells.
Import OSSVerify.glaze.binary_reflection.images.Asan OSSVerify.glaze.binary_reflection.images.AsanUbsan.
Import ListNotations.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Abbreviation ASEGS := Asan.M.loaded_segments.
Abbreviation BSEGS := AsanUbsan.M.loaded_segments.

Definition segs_in_hull_b (segs : list Segment) (lo hi : Z) : bool :=
  forallb (fun seg => (lo <=? Z.of_N (seg_base seg)) && (Z.of_N (seg_base seg) + Z.of_N (seg_size seg) <=? hi))%bool segs.

Lemma find_segment1_none_outside : forall segs lo hi x,
  segs_in_hull_b segs lo hi = true -> (x < lo \/ hi <= x) -> find_segment segs x 1 = None.
Proof.
  induction segs as [|s l IH]; intros lo hi x Hb Hx; [reflexivity|].
  cbn [segs_in_hull_b forallb] in Hb. apply andb_true_iff in Hb as [Hs Hl].
  apply andb_true_iff in Hs as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
  (lazymatch goal with |- ?G => let G' := eval cbn [find_segment] in G in change_no_check G' end).
  replace (Z.leb (Z.of_N (seg_base s)) x && Z.leb (x + 1) (Z.of_N (seg_base s) + Z.of_N (seg_size s)))%bool with false.
  - exact (IH lo hi x Hl Hx).
  - symmetry. apply andb_false_iff. destruct Hx as [Hx|Hx]; [left | right]; apply Z.leb_gt; lia.
Qed.

Lemma segs_hull_of_b : forall segs lo hi,
  segs_in_hull_b segs lo hi = true -> forall a, find_segment segs a 1 <> None -> lo <= a < hi.
Proof.
  intros segs lo hi Hb a Ha.
  destruct (Z_lt_le_dec a lo) as [L|G]; [exfalso; apply Ha; apply (find_segment1_none_outside segs lo hi); [exact Hb | left; exact L]|].
  destruct (Z_lt_le_dec a hi) as [L2|G2]; [lia|].
  exfalso. apply Ha. apply (find_segment1_none_outside segs lo hi); [exact Hb | right; exact G2].
Qed.

Lemma asan_segs_hull : forall a, find_segment ASEGS a 1 <> None -> ia_img_lo asan_addrs <= a < ia_img_hi asan_addrs.
Proof. apply segs_hull_of_b. vm_compute. reflexivity. Qed.
Lemma both_segs_hull : forall a, find_segment BSEGS a 1 <> None -> ia_img_lo both_addrs <= a < ia_img_hi both_addrs.
Proof. apply segs_hull_of_b. vm_compute. reflexivity. Qed.

Lemma asan_segs_wx : wx_segs_nowrap ASEGS.
Proof. apply wx_segs_nowrap_of_b. vm_compute. reflexivity. Qed.
Lemma both_segs_wx : wx_segs_nowrap BSEGS.
Proof. apply wx_segs_nowrap_of_b. vm_compute. reflexivity. Qed.

Lemma asan_img_hi_AS_LO : ia_img_hi asan_addrs <= 0x7fff7000.   Proof. cbn -[Z.le]. lia. Qed.
Lemma both_img_hi_AS_LO : ia_img_hi both_addrs <= 0x7fff7000.   Proof. cbn -[Z.le]. lia. Qed.
Lemma asan_img_lo_nonneg : 0 <= ia_img_lo asan_addrs.   Proof. cbn -[Z.le]. lia. Qed.
Lemma both_img_lo_nonneg : 0 <= ia_img_lo both_addrs.   Proof. cbn -[Z.le]. lia. Qed.
End AsRtImg.
Require LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC OSSVerify.Proofs.glaze.binary_reflection.lib.Common.InstrEnc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module Bo_code_70fc4_71054.
(* [comment removed for export] *)

Import Stdlib.ZArith.ZArith.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.glaze.binary_reflection.images.AsanUbsan.

#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- @eq (option (bv 32)) (fetch_word ?s ?a) ?r =>
      apply (@bool_decide_eq_true_1 _ (@decide_rel (option (bv 32)) (option (bv 32)) (@eq (option (bv 32))) (@option_eq_dec (bv 32) (bv_eq_dec 32)) (fetch_word s a) r));
      vm_cast_no_check (@eq_refl bool true)
  | |- @eq (option (prod instr Z)) (decode_any ?w) ?r =>
      (* [comment removed for export] *)
      apply (@InstrEnc.enc_opt_inj (decode_any w) r);
      vm_cast_no_check (@eq_refl (list Z) (InstrEnc.enc_opt r))
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_70ff0 : bv 32 := @BV 32 0x00095597%Z I.
Lemma F_70ff0 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x70ff0%Z I : word) = Some W_70ff0.
Proof. vm_refl. Qed.
Lemma D_70ff0 : decode_any W_70ff0 = Some (Auipc (@BV 5 11%Z I) (@BV 20 149%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_70ff4 : bv 32 := @BV 32 0xf205b583%Z I.
Lemma F_70ff4 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x70ff4%Z I : word) = Some W_70ff4.
Proof. vm_refl. Qed.
Lemma D_70ff4 : decode_any W_70ff4 = Some (Load SZ8 true (@BV 5 11%Z I) (@BV 5 11%Z I) (@BV 12 3872%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7100c : bv 32 := @BV 32 0x00095517%Z I.
Lemma F_7100c : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x7100c%Z I : word) = Some W_7100c.
Proof. vm_refl. Qed.
Lemma D_7100c : decode_any W_7100c = Some (Auipc (@BV 5 10%Z I) (@BV 20 149%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_71010 : bv 32 := @BV 32 0xf5c53503%Z I.
Lemma F_71010 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x71010%Z I : word) = Some W_71010.
Proof. vm_refl. Qed.
Lemma D_71010 : decode_any W_71010 = Some (Load SZ8 true (@BV 5 10%Z I) (@BV 5 10%Z I) (@BV 12 3932%Z I), 4%Z).
Proof. vm_refl. Qed.
End Bo_code_70fc4_71054.
Module Bo_code_71054_71254.
(* [comment removed for export] *)

Import Stdlib.ZArith.ZArith.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.glaze.binary_reflection.images.AsanUbsan.

#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- @eq (option (bv 32)) (fetch_word ?s ?a) ?r =>
      apply (@bool_decide_eq_true_1 _ (@decide_rel (option (bv 32)) (option (bv 32)) (@eq (option (bv 32))) (@option_eq_dec (bv 32) (bv_eq_dec 32)) (fetch_word s a) r));
      vm_cast_no_check (@eq_refl bool true)
  | |- @eq (option (prod instr Z)) (decode_any ?w) ?r =>
      (* [comment removed for export] *)
      apply (@InstrEnc.enc_opt_inj (decode_any w) r);
      vm_cast_no_check (@eq_refl (list Z) (InstrEnc.enc_opt r))
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_71158 : bv 32 := @BV 32 0x00095597%Z I.
Lemma F_71158 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x71158%Z I : word) = Some W_71158.
Proof. vm_refl. Qed.
Lemma D_71158 : decode_any W_71158 = Some (Auipc (@BV 5 11%Z I) (@BV 20 149%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7115c : bv 32 := @BV 32 0xdc05b583%Z I.
Lemma F_7115c : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x7115c%Z I : word) = Some W_7115c.
Proof. vm_refl. Qed.
Lemma D_7115c : decode_any W_7115c = Some (Load SZ8 true (@BV 5 11%Z I) (@BV 5 11%Z I) (@BV 12 3520%Z I), 4%Z).
Proof. vm_refl. Qed.
End Bo_code_71054_71254.
Module Bo_code_5cfa4_5cfa8.
(* [comment removed for export] *)

Import Stdlib.ZArith.ZArith.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.glaze.binary_reflection.images.AsanUbsan.

#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- @eq (option (bv 32)) (fetch_word ?s ?a) ?r =>
      apply (@bool_decide_eq_true_1 _ (@decide_rel (option (bv 32)) (option (bv 32)) (@eq (option (bv 32))) (@option_eq_dec (bv 32) (bv_eq_dec 32)) (fetch_word s a) r));
      vm_cast_no_check (@eq_refl bool true)
  | |- @eq (option (prod instr Z)) (decode_any ?w) ?r =>
      (* [comment removed for export] *)
      apply (@InstrEnc.enc_opt_inj (decode_any w) r);
      vm_cast_no_check (@eq_refl (list Z) (InstrEnc.enc_opt r))
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.
End Bo_code_5cfa4_5cfa8.
Module Bo_code_618d8_61954.
(* [comment removed for export] *)

Import Stdlib.ZArith.ZArith.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.glaze.binary_reflection.images.AsanUbsan.

#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- @eq (option (bv 32)) (fetch_word ?s ?a) ?r =>
      apply (@bool_decide_eq_true_1 _ (@decide_rel (option (bv 32)) (option (bv 32)) (@eq (option (bv 32))) (@option_eq_dec (bv 32) (bv_eq_dec 32)) (fetch_word s a) r));
      vm_cast_no_check (@eq_refl bool true)
  | |- @eq (option (prod instr Z)) (decode_any ?w) ?r =>
      (* [comment removed for export] *)
      apply (@InstrEnc.enc_opt_inj (decode_any w) r);
      vm_cast_no_check (@eq_refl (list Z) (InstrEnc.enc_opt r))
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.
















(* [comment removed for export] *)
Definition W_618f4 : bv 32 := @BV 32 0x000a6597%Z I.
Lemma F_618f4 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x618f4%Z I : word) = Some W_618f4.
Proof. vm_refl. Qed.
Lemma D_618f4 : decode_any W_618f4 = Some (Auipc (@BV 5 11%Z I) (@BV 20 166%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_618f8 : bv 32 := @BV 32 0x4845b583%Z I.
Lemma F_618f8 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x618f8%Z I : word) = Some W_618f8.
Proof. vm_refl. Qed.
Lemma D_618f8 : decode_any W_618f8 = Some (Load SZ8 true (@BV 5 11%Z I) (@BV 5 11%Z I) (@BV 12 1156%Z I), 4%Z).
Proof. vm_refl. Qed.
























End Bo_code_618d8_61954.
Module Bo_code_78e2c_78e4c.
(* [comment removed for export] *)

Import Stdlib.ZArith.ZArith.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.glaze.binary_reflection.images.AsanUbsan.

#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- @eq (option (bv 32)) (fetch_word ?s ?a) ?r =>
      apply (@bool_decide_eq_true_1 _ (@decide_rel (option (bv 32)) (option (bv 32)) (@eq (option (bv 32))) (@option_eq_dec (bv 32) (bv_eq_dec 32)) (fetch_word s a) r));
      vm_cast_no_check (@eq_refl bool true)
  | |- @eq (option (prod instr Z)) (decode_any ?w) ?r =>
      (* [comment removed for export] *)
      apply (@InstrEnc.enc_opt_inj (decode_any w) r);
      vm_cast_no_check (@eq_refl (list Z) (InstrEnc.enc_opt r))
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.
























End Bo_code_78e2c_78e4c.
Module Bo_code_714ac_714c4.
(* [comment removed for export] *)

Import Stdlib.ZArith.ZArith.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.glaze.binary_reflection.images.AsanUbsan.

#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- @eq (option (bv 32)) (fetch_word ?s ?a) ?r =>
      apply (@bool_decide_eq_true_1 _ (@decide_rel (option (bv 32)) (option (bv 32)) (@eq (option (bv 32))) (@option_eq_dec (bv 32) (bv_eq_dec 32)) (fetch_word s a) r));
      vm_cast_no_check (@eq_refl bool true)
  | |- @eq (option (prod instr Z)) (decode_any ?w) ?r =>
      (* [comment removed for export] *)
      apply (@InstrEnc.enc_opt_inj (decode_any w) r);
      vm_cast_no_check (@eq_refl (list Z) (InstrEnc.enc_opt r))
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_714ac : bv 32 := @BV 32 0x0009c517%Z I.
Lemma F_714ac : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x714ac%Z I : word) = Some W_714ac.
Proof. vm_refl. Qed.
Lemma D_714ac : decode_any W_714ac = Some (Auipc (@BV 5 10%Z I) (@BV 20 156%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_714b0 : bv 32 := @BV 32 0x57450513%Z I.
Lemma F_714b0 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x714b0%Z I : word) = Some W_714b0.
Proof. vm_refl. Qed.
Lemma D_714b0 : decode_any W_714b0 = Some (OpImm ALU_ADD (@BV 5 10%Z I) (@BV 5 10%Z I) (@BV 12 1396%Z I), 4%Z).
Proof. vm_refl. Qed.










(* [comment removed for export] *)
Definition W_714c0 : bv 32 := @BV 32 0x0598c06f%Z I.
Lemma F_714c0 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x714c0%Z I : word) = Some W_714c0.
Proof. vm_refl. Qed.
Lemma D_714c0 : decode_any W_714c0 = Some (Jal (@BV 5 0%Z I) (@BV 21 575576%Z I), 4%Z).
Proof. vm_refl. Qed.
End Bo_code_714ac_714c4.
Module Bo_code_86540_8675c.
(* [comment removed for export] *)

Import Stdlib.ZArith.ZArith.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.glaze.binary_reflection.images.AsanUbsan.

#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- @eq (option (bv 32)) (fetch_word ?s ?a) ?r =>
      apply (@bool_decide_eq_true_1 _ (@decide_rel (option (bv 32)) (option (bv 32)) (@eq (option (bv 32))) (@option_eq_dec (bv 32) (bv_eq_dec 32)) (fetch_word s a) r));
      vm_cast_no_check (@eq_refl bool true)
  | |- @eq (option (prod instr Z)) (decode_any ?w) ?r =>
      (* [comment removed for export] *)
      apply (@InstrEnc.enc_opt_inj (decode_any w) r);
      vm_cast_no_check (@eq_refl (list Z) (InstrEnc.enc_opt r))
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_8657c : bv 32 := @BV 32 0x00080597%Z I.
Lemma F_8657c : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8657c%Z I : word) = Some W_8657c.
Proof. vm_refl. Qed.
Lemma D_8657c : decode_any W_8657c = Some (Auipc (@BV 5 11%Z I) (@BV 20 128%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_86580 : bv 32 := @BV 32 0x98c5b583%Z I.
Lemma F_86580 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x86580%Z I : word) = Some W_86580.
Proof. vm_refl. Qed.
Lemma D_86580 : decode_any W_86580 = Some (Load SZ8 true (@BV 5 11%Z I) (@BV 5 11%Z I) (@BV 12 2444%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_86590 : bv 32 := @BV 32 0x00080517%Z I.
Lemma F_86590 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x86590%Z I : word) = Some W_86590.
Proof. vm_refl. Qed.
Lemma D_86590 : decode_any W_86590 = Some (Auipc (@BV 5 10%Z I) (@BV 20 128%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_86594 : bv 32 := @BV 32 0x9d853d03%Z I.
Lemma F_86594 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x86594%Z I : word) = Some W_86594.
Proof. vm_refl. Qed.
Lemma D_86594 : decode_any W_86594 = Some (Load SZ8 true (@BV 5 26%Z I) (@BV 5 10%Z I) (@BV 12 2520%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8659c : bv 32 := @BV 32 0x00080517%Z I.
Lemma F_8659c : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8659c%Z I : word) = Some W_8659c.
Proof. vm_refl. Qed.
Lemma D_8659c : decode_any W_8659c = Some (Auipc (@BV 5 10%Z I) (@BV 20 128%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_865a4 : bv 32 := @BV 32 0x72c53a83%Z I.
Lemma F_865a4 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x865a4%Z I : word) = Some W_865a4.
Proof. vm_refl. Qed.
Lemma D_865a4 : decode_any W_865a4 = Some (Load SZ8 true (@BV 5 21%Z I) (@BV 5 10%Z I) (@BV 12 1836%Z I), 4%Z).
Proof. vm_refl. Qed.
End Bo_code_86540_8675c.
Module Bo_code_fcc70_fcc94.
(* [comment removed for export] *)

Import Stdlib.ZArith.ZArith.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.glaze.binary_reflection.images.AsanUbsan.

#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- @eq (option (bv 32)) (fetch_word ?s ?a) ?r =>
      apply (@bool_decide_eq_true_1 _ (@decide_rel (option (bv 32)) (option (bv 32)) (@eq (option (bv 32))) (@option_eq_dec (bv 32) (bv_eq_dec 32)) (fetch_word s a) r));
      vm_cast_no_check (@eq_refl bool true)
  | |- @eq (option (prod instr Z)) (decode_any ?w) ?r =>
      (* [comment removed for export] *)
      apply (@InstrEnc.enc_opt_inj (decode_any w) r);
      vm_cast_no_check (@eq_refl (list Z) (InstrEnc.enc_opt r))
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.
End Bo_code_fcc70_fcc94.
Module Bo_code_fdd24_fdd40.
(* [comment removed for export] *)

Import Stdlib.ZArith.ZArith.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.glaze.binary_reflection.images.AsanUbsan.

#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- @eq (option (bv 32)) (fetch_word ?s ?a) ?r =>
      apply (@bool_decide_eq_true_1 _ (@decide_rel (option (bv 32)) (option (bv 32)) (@eq (option (bv 32))) (@option_eq_dec (bv 32) (bv_eq_dec 32)) (fetch_word s a) r));
      vm_cast_no_check (@eq_refl bool true)
  | |- @eq (option (prod instr Z)) (decode_any ?w) ?r =>
      (* [comment removed for export] *)
      apply (@InstrEnc.enc_opt_inj (decode_any w) r);
      vm_cast_no_check (@eq_refl (list Z) (InstrEnc.enc_opt r))
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.





















End Bo_code_fdd24_fdd40.
Module Bo_code_57bdc_58228.
(* [comment removed for export] *)

Import Stdlib.ZArith.ZArith.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.glaze.binary_reflection.images.AsanUbsan.

#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- @eq (option (bv 32)) (fetch_word ?s ?a) ?r =>
      apply (@bool_decide_eq_true_1 _ (@decide_rel (option (bv 32)) (option (bv 32)) (@eq (option (bv 32))) (@option_eq_dec (bv 32) (bv_eq_dec 32)) (fetch_word s a) r));
      vm_cast_no_check (@eq_refl bool true)
  | |- @eq (option (prod instr Z)) (decode_any ?w) ?r =>
      (* [comment removed for export] *)
      apply (@InstrEnc.enc_opt_inj (decode_any w) r);
      vm_cast_no_check (@eq_refl (list Z) (InstrEnc.enc_opt r))
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_57bf4 : bv 32 := @BV 32 0x000af517%Z I.
Lemma F_57bf4 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x57bf4%Z I : word) = Some W_57bf4.
Proof. vm_refl. Qed.
Lemma D_57bf4 : decode_any W_57bf4 = Some (Auipc (@BV 5 10%Z I) (@BV 20 175%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_57bf8 : bv 32 := @BV 32 0x0c450513%Z I.
Lemma F_57bf8 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x57bf8%Z I : word) = Some W_57bf8.
Proof. vm_refl. Qed.
Lemma D_57bf8 : decode_any W_57bf8 = Some (OpImm ALU_ADD (@BV 5 10%Z I) (@BV 5 10%Z I) (@BV 12 196%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_57d68 : bv 32 := @BV 32 0x000af517%Z I.
Lemma F_57d68 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x57d68%Z I : word) = Some W_57d68.
Proof. vm_refl. Qed.
Lemma D_57d68 : decode_any W_57d68 = Some (Auipc (@BV 5 10%Z I) (@BV 20 175%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_57d6c : bv 32 := @BV 32 0xf5050513%Z I.
Lemma F_57d6c : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x57d6c%Z I : word) = Some W_57d6c.
Proof. vm_refl. Qed.
Lemma D_57d6c : decode_any W_57d6c = Some (OpImm ALU_ADD (@BV 5 10%Z I) (@BV 5 10%Z I) (@BV 12 3920%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_57ef8 : bv 32 := @BV 32 0x000af517%Z I.
Lemma F_57ef8 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x57ef8%Z I : word) = Some W_57ef8.
Proof. vm_refl. Qed.
Lemma D_57ef8 : decode_any W_57ef8 = Some (Auipc (@BV 5 10%Z I) (@BV 20 175%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_57efc : bv 32 := @BV 32 0xdc050513%Z I.
Lemma F_57efc : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x57efc%Z I : word) = Some W_57efc.
Proof. vm_refl. Qed.
Lemma D_57efc : decode_any W_57efc = Some (OpImm ALU_ADD (@BV 5 10%Z I) (@BV 5 10%Z I) (@BV 12 3520%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_58094 : bv 32 := @BV 32 0x000af517%Z I.
Lemma F_58094 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x58094%Z I : word) = Some W_58094.
Proof. vm_refl. Qed.
Lemma D_58094 : decode_any W_58094 = Some (Auipc (@BV 5 10%Z I) (@BV 20 175%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_58098 : bv 32 := @BV 32 0xc2450513%Z I.
Lemma F_58098 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x58098%Z I : word) = Some W_58098.
Proof. vm_refl. Qed.
Lemma D_58098 : decode_any W_58098 = Some (OpImm ALU_ADD (@BV 5 10%Z I) (@BV 5 10%Z I) (@BV 12 3108%Z I), 4%Z).
Proof. vm_refl. Qed.
End Bo_code_57bdc_58228.
Require LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtM2S OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtXStrlenI OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtRegion OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtAMemset OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtStkLift OSSVerify.Proofs.glaze.binary_reflection.lib.AsIcptSetSh.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module AsIcptMemsetI.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsK OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsRtK OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib AsRtImg OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtM2S OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtXStrlenI.AsRtM2SI OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtRegion OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtXStrlenI.AsRtRegionI OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtAMemset.AsRtQC OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtAMemset OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtStkLift.AsRtAMemsetI OSSVerify.Proofs.glaze.binary_reflection.lib.AsIcptSetSh.AsIcptLift OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtStkLift.AsIcptMemset.
Import OSSVerify.glaze.binary_reflection.images.Asan.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Section INST.
  Context {RC : run_ceil}.
  Variable FXOK : FPState -> Prop.
  Variable AAINVH : option Z -> list (Z * Z) -> list (Z * Z) -> Z -> Z -> Z -> mem -> Model -> Prop.
  Variable fsbase : Z.
  Hypothesis HP : forall h, AAINV_props asan_addrs (AAINVH h) fsbase ASEGS.
  Hypothesis FSB0 : 0 <= fsbase.
  Hypothesis CELLS : forall h Lc FF B C K M mdl, AAINVH h Lc FF B C K M mdl ->
    Forall (fun c => cellN ASEGS M (fst (fst c)) (snd (fst c)) (snd c)) (amset_cells asan_amset_tab).

  (* [comment removed for export] *)
  Lemma amset_cells_A : amset_cells asan_amset_tab =
    [(0xffdd8, 8%nat, 0x108259); (0x108259, 1%nat, 1); (0x1011b0, 8%nat, 0xf56e4);
     (0xff270, 8%nat, 0x107578); (0x107578, 8%nat, 0x7fff8000);
     (0xff278, 8%nat, 0x108268); (0x108268, 8%nat, 0);
     (0xff280, 8%nat, 0x108270); (0x108270, 8%nat, 0);
     (0xff288, 8%nat, 0x108260); (0x108260, 8%nat, 0x7fffffffffff)].
  Proof using. reflexivity. Qed.

  Theorem C_asan_memset_A : MEMSET_AT ASEGS FXOK asan_addrs AAINVH (ia_asan_memset asan_addrs).
  Proof using CELLS FSB0 HP fsbase.
    apply (C_asan_memset ASEGS FXOK asan_addrs AAINVH fsbase HP asan_segs_hull asan_segs_wx
             asan_img_hi_AS_LO asan_img_lo_nonneg FSB0 asan_amset_tab (fun fx => @asan_amset_tab_ok fx)
             ltac:(apply bv_eq; vm_compute; reflexivity) CELLS).
    rewrite amset_cells_A. repeat apply Forall_cons; try apply Forall_nil; cbn -[Z.le Z.add Z.lt]; lia.
  Qed.
End INST.
End AsIcptMemsetI.
Module AsIcptXMemsetI.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsK OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsRtK OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib AsRtImg OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtM2S OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtXStrlenI.AsRtM2SI OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtRegion OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtXStrlenI.AsRtRegionI OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtAMemset.AsRtQC OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtAMemset OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtStkLift.AsRtXMemset OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtStkLift.AsRtXMemsetI OSSVerify.Proofs.glaze.binary_reflection.lib.AsIcptSetSh.AsIcptLift OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtStkLift.AsIcptXMemset.
Import OSSVerify.glaze.binary_reflection.images.Asan.
Import ListNotations.
Open Scope Z_scope.
#[local] Unset Lia Cache. #[local] Unset Nia Cache. #[local] Unset Nra Cache.

Section INST.
  Context {RC : run_ceil}.
  Variable FXOK : FPState -> Prop.
  Variable AAINVH : option Z -> list (Z * Z) -> list (Z * Z) -> Z -> Z -> Z -> mem -> Model -> Prop.
  Variable fsbase : Z.
  Hypothesis HP : forall h, AAINV_props asan_addrs (AAINVH h) fsbase ASEGS.
  Hypothesis FSB0 : 0 <= fsbase.
  Hypothesis CELLS : forall h Lc FF B C K M mdl, AAINVH h Lc FF B C K M mdl ->
    Forall (fun c => cellN ASEGS M (fst (fst c)) (snd (fst c)) (snd c)) (xmset_cells asan_xmset_tab).

  (* [comment removed for export] *)
  Lemma xmset_cells_A : xmset_cells asan_xmset_tab = ltac:(let x := eval cbv in (xmset_cells asan_xmset_tab) in exact x).
  Proof using. reflexivity. Qed.

  Theorem C_memset_icpt_A : MEMSET_AT ASEGS FXOK asan_addrs AAINVH (ia_memset_icpt asan_addrs).
  Proof using CELLS FSB0 HP fsbase.
    apply (C_memset_icpt ASEGS FXOK asan_addrs AAINVH fsbase HP asan_segs_hull asan_segs_wx
             asan_img_hi_AS_LO asan_img_lo_nonneg FSB0 asan_xmset_tab (fun fx => @asan_xmset_tab_ok fx)
             ltac:(apply bv_eq; vm_compute; reflexivity) CELLS).
    rewrite xmset_cells_A. repeat apply Forall_cons; try apply Forall_nil; cbn -[Z.le Z.add Z.lt]; lia.
  Qed.
End INST.
End AsIcptXMemsetI.
Module AsIcptMemcpyI.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsK OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsRtK OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib AsRtImg OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtM2S OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtXStrlenI.AsRtM2SI OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtRegion OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtXStrlenI.AsRtRegionI OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtAMemset.AsRtQC OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtAMemset OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtStkLift.AsRtAMemcpy OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtStkLift.AsRtAMemcpyI OSSVerify.Proofs.glaze.binary_reflection.lib.AsIcptSetSh.AsIcptLift OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtStkLift.AsIcptMemcpy.
Import OSSVerify.glaze.binary_reflection.images.Asan.
Import ListNotations.
Open Scope Z_scope.
#[local] Unset Lia Cache. #[local] Unset Nia Cache. #[local] Unset Nra Cache.

Section INST.
  Context {RC : run_ceil}.
  Variable FXOK : FPState -> Prop.
  Variable AAINVH : option Z -> list (Z * Z) -> list (Z * Z) -> Z -> Z -> Z -> mem -> Model -> Prop.
  Variable fsbase : Z.
  Hypothesis HP : forall h, AAINV_props asan_addrs (AAINVH h) fsbase ASEGS.
  Hypothesis FSB0 : 0 <= fsbase.
  Hypothesis CELLS : forall h Lc FF B C K M mdl, AAINVH h Lc FF B C K M mdl ->
    Forall (fun c => cellN ASEGS M (fst (fst c)) (snd (fst c)) (snd c)) (amcpy_cells asan_amcpy_tab).

  (* [comment removed for export] *)
  Lemma amcpy_cells_A : amcpy_cells asan_amcpy_tab = ltac:(let x := eval cbv in (amcpy_cells asan_amcpy_tab) in exact x).
  Proof using. reflexivity. Qed.

  Theorem C_asan_memcpy_A : MEMCPY_AT ASEGS FXOK asan_addrs AAINVH (ia_asan_memcpy asan_addrs).
  Proof using CELLS FSB0 HP fsbase.
    apply (C_asan_memcpy ASEGS FXOK asan_addrs AAINVH fsbase HP asan_segs_hull asan_segs_wx
             asan_img_hi_AS_LO asan_img_lo_nonneg FSB0 asan_amcpy_tab (fun fx => @asan_amcpy_tab_ok fx)
             ltac:(apply bv_eq; vm_compute; reflexivity) CELLS).
    rewrite amcpy_cells_A. repeat apply Forall_cons; try apply Forall_nil; cbn -[Z.le Z.add Z.lt]; lia.
  Qed.
End INST.
End AsIcptMemcpyI.
Module AsIcptXMemcpyI.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsK OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsRtK OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib AsRtImg OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtM2S OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtXStrlenI.AsRtM2SI OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtRegion OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtXStrlenI.AsRtRegionI OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtAMemset.AsRtQC OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtAMemset OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtStkLift.AsRtXMemcpy OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtStkLift.AsRtXMemcpyI OSSVerify.Proofs.glaze.binary_reflection.lib.AsIcptSetSh.AsIcptLift OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtStkLift.AsIcptXMemcpy.
Import OSSVerify.glaze.binary_reflection.images.Asan.
Import ListNotations.
Open Scope Z_scope.
#[local] Unset Lia Cache. #[local] Unset Nia Cache. #[local] Unset Nra Cache.

Section INST.
  Context {RC : run_ceil}.
  Variable FXOK : FPState -> Prop.
  Variable AAINVH : option Z -> list (Z * Z) -> list (Z * Z) -> Z -> Z -> Z -> mem -> Model -> Prop.
  Variable fsbase : Z.
  Hypothesis HP : forall h, AAINV_props asan_addrs (AAINVH h) fsbase ASEGS.
  Hypothesis FSB0 : 0 <= fsbase.
  Hypothesis CELLS : forall h Lc FF B C K M mdl, AAINVH h Lc FF B C K M mdl ->
    Forall (fun c => cellN ASEGS M (fst (fst c)) (snd (fst c)) (snd c)) (xmcpy_cells asan_xmcpy_tab).

  (* [comment removed for export] *)
  Lemma xmcpy_cells_A : xmcpy_cells asan_xmcpy_tab = ltac:(let x := eval cbv in (xmcpy_cells asan_xmcpy_tab) in exact x).
  Proof using. reflexivity. Qed.

  Theorem C_memcpy_icpt_A : MEMCPY_AT ASEGS FXOK asan_addrs AAINVH (ia_memcpy_icpt asan_addrs).
  Proof using CELLS FSB0 HP fsbase.
    apply (C_memcpy_icpt ASEGS FXOK asan_addrs AAINVH fsbase HP asan_segs_hull asan_segs_wx
             asan_img_hi_AS_LO asan_img_lo_nonneg FSB0 asan_xmcpy_tab (fun fx => @asan_xmcpy_tab_ok fx)
             ltac:(apply bv_eq; vm_compute; reflexivity) CELLS).
    rewrite xmcpy_cells_A. repeat apply Forall_cons; try apply Forall_nil; cbn -[Z.le Z.add Z.lt]; lia.
  Qed.
End INST.
End AsIcptXMemcpyI.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtAMemmove.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module AsIcptMemmoveI.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsK OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsRtK OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib AsRtImg OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtM2S OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtXStrlenI.AsRtM2SI OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtRegion OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtXStrlenI.AsRtRegionI OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtAMemset.AsRtQC OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtAMemset OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtAMemmove OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtStkLift.AsRtAMemmoveI OSSVerify.Proofs.glaze.binary_reflection.lib.AsIcptSetSh.AsIcptLift OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtStkLift.AsIcptMemmove.
Import OSSVerify.glaze.binary_reflection.images.Asan.
Import ListNotations.
Open Scope Z_scope.
#[local] Unset Lia Cache. #[local] Unset Nia Cache. #[local] Unset Nra Cache.

Section INST.
  Context {RC : run_ceil}.
  Variable FXOK : FPState -> Prop.
  Variable AAINVH : option Z -> list (Z * Z) -> list (Z * Z) -> Z -> Z -> Z -> mem -> Model -> Prop.
  Variable fsbase : Z.
  Hypothesis HP : forall h, AAINV_props asan_addrs (AAINVH h) fsbase ASEGS.
  Hypothesis FSB0 : 0 <= fsbase.
  Hypothesis CELLS : forall h Lc FF B C K M mdl, AAINVH h Lc FF B C K M mdl ->
    Forall (fun c => cellN ASEGS M (fst (fst c)) (snd (fst c)) (snd c)) (ammove_cells asan_ammove_tab).

  (* [comment removed for export] *)
  Lemma ammove_cells_A : ammove_cells asan_ammove_tab = ltac:(let x := eval cbv in (ammove_cells asan_ammove_tab) in exact x).
  Proof using. reflexivity. Qed.

  Theorem C_asan_memmove_A : MEMMOVE_AT ASEGS FXOK asan_addrs AAINVH (ia_asan_memmove asan_addrs).
  Proof using CELLS FSB0 HP fsbase.
    apply (C_asan_memmove ASEGS FXOK asan_addrs AAINVH fsbase HP asan_segs_hull asan_segs_wx
             asan_img_hi_AS_LO asan_img_lo_nonneg FSB0 asan_ammove_tab (fun fx => @asan_ammove_tab_ok fx)
             ltac:(apply bv_eq; vm_compute; reflexivity) CELLS).
    rewrite ammove_cells_A. repeat apply Forall_cons; try apply Forall_nil; cbn -[Z.le Z.add Z.lt]; lia.
  Qed.
End INST.
End AsIcptMemmoveI.
Module AsIcptXMemmoveI.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsK OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsRtK OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib AsRtImg OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtM2S OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtXStrlenI.AsRtM2SI OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtRegion OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtXStrlenI.AsRtRegionI OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtAMemset.AsRtQC OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtAMemset OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtAMemmove OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtStkLift.AsRtXMemmove OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtStkLift.AsRtXMemmoveI OSSVerify.Proofs.glaze.binary_reflection.lib.AsIcptSetSh.AsIcptLift OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtStkLift.AsIcptXMemmove.
Import OSSVerify.glaze.binary_reflection.images.Asan.
Import ListNotations.
Open Scope Z_scope.
#[local] Unset Lia Cache. #[local] Unset Nia Cache. #[local] Unset Nra Cache.

Section INST.
  Context {RC : run_ceil}.
  Variable FXOK : FPState -> Prop.
  Variable AAINVH : option Z -> list (Z * Z) -> list (Z * Z) -> Z -> Z -> Z -> mem -> Model -> Prop.
  Variable fsbase : Z.
  Hypothesis HP : forall h, AAINV_props asan_addrs (AAINVH h) fsbase ASEGS.
  Hypothesis FSB0 : 0 <= fsbase.
  Hypothesis CELLS : forall h Lc FF B C K M mdl, AAINVH h Lc FF B C K M mdl ->
    Forall (fun c => cellN ASEGS M (fst (fst c)) (snd (fst c)) (snd c)) (xmmove_cells asan_xmmove_tab).

  (* [comment removed for export] *)
  Lemma xmmove_cells_A : xmmove_cells asan_xmmove_tab = ltac:(let x := eval cbv in (xmmove_cells asan_xmmove_tab) in exact x).
  Proof using. reflexivity. Qed.

  Theorem C_memmove_icpt_A : MEMMOVE_AT ASEGS FXOK asan_addrs AAINVH (ia_memmove_icpt asan_addrs).
  Proof using CELLS FSB0 HP fsbase.
    apply (C_memmove_icpt ASEGS FXOK asan_addrs AAINVH fsbase HP asan_segs_hull asan_segs_wx
             asan_img_hi_AS_LO asan_img_lo_nonneg FSB0 asan_xmmove_tab (fun fx => @asan_xmmove_tab_ok fx)
             ltac:(apply bv_eq; vm_compute; reflexivity) CELLS).
    rewrite xmmove_cells_A. repeat apply Forall_cons; try apply Forall_nil; cbn -[Z.le Z.add Z.lt]; lia.
  Qed.
End INST.
End AsIcptXMemmoveI.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtMemchr OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtStrlen OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtTlsGA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module AsIcptStrlenI.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsK OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsRtK OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib AsRtImg OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtM2S OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtXStrlenI.AsRtM2SI OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtRegion OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtXStrlenI.AsRtRegionI OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtAMemset.AsRtQC OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtAMemset OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtMemchr OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtStrlen OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtXStrlenI.AsRtStrlenI OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtTlsGA.AsRtXStrlen OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtXStrlenI OSSVerify.Proofs.glaze.binary_reflection.lib.AsIcptSetSh.AsIcptLift OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtStkLift.AsIcptStrlen.
Import OSSVerify.glaze.binary_reflection.images.Asan.
Import ListNotations.
Open Scope Z_scope.
#[local] Unset Lia Cache. #[local] Unset Nia Cache. #[local] Unset Nra Cache.

Section INST.
  Context {RC : run_ceil}.
  Variable FXOK : FPState -> Prop.
  Variable AAINVH : option Z -> list (Z * Z) -> list (Z * Z) -> Z -> Z -> Z -> mem -> Model -> Prop.
  Variable fsbase : Z.
  Hypothesis HP : forall h, AAINV_props asan_addrs (AAINVH h) fsbase ASEGS.
  Hypothesis FSB0 : 0 <= fsbase.
  Hypothesis CELLS : forall h Lc FF B C K M mdl, AAINVH h Lc FF B C K M mdl ->
    Forall (fun c => cellN ASEGS M (fst (fst c)) (snd (fst c)) (snd c)) (xstrlen_cells asan_xstrlen_tab).

  (* [comment removed for export] *)
  Lemma xstrlen_cells_A : xstrlen_cells asan_xstrlen_tab = ltac:(let x := eval cbv in (xstrlen_cells asan_xstrlen_tab) in exact x).
  Proof using. reflexivity. Qed.

  Theorem C_strlen_icpt_A : STRLEN_AT ASEGS FXOK asan_addrs AAINVH (ia_strlen_icpt asan_addrs).
  Proof using CELLS FSB0 HP fsbase.
    apply (C_strlen_icpt ASEGS FXOK asan_addrs AAINVH fsbase HP asan_segs_hull asan_segs_wx
             asan_img_hi_AS_LO asan_img_lo_nonneg FSB0 asan_xstrlen_tab (fun fx => @asan_xstrlen_tab_ok fx)
             ltac:(apply bv_eq; vm_compute; reflexivity) CELLS). 2: (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); (lazymatch goal with |- ?G => let G' := eval unfold AS_LO in G in change_no_check G' end); lia.
    rewrite xstrlen_cells_A. repeat apply Forall_cons; try apply Forall_nil; cbn -[Z.le Z.add Z.lt]; lia.
  Qed.
End INST.
End AsIcptStrlenI.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsCodeM4 OSSVerify.Proofs.glaze.binary_reflection.lib.AsCodeM5 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtMemIsZero OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtMuslMemset OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoison OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoisonI OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtAnn.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module AsRtAnnI.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AsCodeM4 OSSVerify.Proofs.glaze.binary_reflection.lib.AsCodeM5 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtMemIsZero OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtMuslMemset OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtM2S OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtXStrlenI.AsRtM2SI OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoison OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoisonI OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtAnn.
Import OSSVerify.glaze.binary_reflection.images.Asan.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Abbreviation ASEGS := Asan.M.loaded_segments.

Definition asan_ann_base : word := 0x70554.
Definition asan_ann_g_flags : Z := 0xff268.  Definition asan_ann_p_flags : Z := 0x104d78.
Definition asan_ann_g_verb : Z := 0xff2c0.   Definition asan_ann_p_verb : Z := 0x197018.
Definition asan_ann_g_shoff : Z := 0xff270.  Definition asan_ann_p_shoff : Z := 0x107578.

Section FPGen1.
Context {fx : FPState}.

Lemma asan_anncc_code : code_ato ASEGS asan_ann_base 0 anncc_words.
Proof using. (lazymatch goal with |- ?G => let G' := eval unfold anncc_words, asan_ann_base in G in change_no_check G' end). code_ato_vm. Qed.
Lemma asan_ann_ptb : pt_base asan_poison_tab = at_ asan_ann_base (-3908).
Proof using. apply bv_eq. vm_compute. reflexivity. Qed.
Lemma asan_ann_mtb : mt_base asan_m2s_tab_6fb04 = at_ asan_ann_base (-2632).
Proof using. apply bv_eq. vm_compute. reflexivity. Qed.
Lemma asan_ann_G44 : gload ASEGS asan_ann_base 44 11 asan_ann_g_flags.
Proof using. (lazymatch goal with |- ?G => let G' := eval unfold asan_ann_base, asan_ann_g_flags in G in change_no_check G' end). gload_tac F_70578 D_70578 F_7057c D_7057c. Qed.
Lemma asan_ann_G72 : gload ASEGS asan_ann_base 72 10 asan_ann_g_verb.
Proof using. (lazymatch goal with |- ?G => let G' := eval unfold asan_ann_base, asan_ann_g_verb in G in change_no_check G' end). gload_tac F_70594 D_70594 F_70598 D_70598. Qed.
Lemma asan_ann_G404 : gload ASEGS asan_ann_base 404 11 asan_ann_g_shoff.
Proof using. (lazymatch goal with |- ?G => let G' := eval unfold asan_ann_base, asan_ann_g_shoff in G in change_no_check G' end). gload_tac F_706e0 D_706e0 F_706e4 D_706e4. Qed.
Lemma asan_ann_hbase : (bv_unsigned asan_ann_base mod 2 = 0)%Z /\ (4096 <= bv_unsigned asan_ann_base)%Z
                       /\ (bv_unsigned asan_ann_base + 4096 < 2 ^ 64)%Z.
Proof using. (lazymatch goal with |- ?G => let G' := eval unfold asan_ann_base in G in change_no_check G' end). split; [vm_compute; reflexivity | split; [vm_compute; discriminate | vm_compute; reflexivity]]. Qed.

End FPGen1.
End AsRtAnnI.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsIcptAnn.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module AsIcptAnnI.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsK OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsRtK OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib AsRtImg OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtM2S OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtXStrlenI.AsRtM2SI OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoison OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoisonI OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtAnn AsRtAnnI OSSVerify.Proofs.glaze.binary_reflection.lib.AsIcptSetSh.AsIcptLift OSSVerify.Proofs.glaze.binary_reflection.lib.AsIcptAnn.AsIcptAnnM OSSVerify.Proofs.glaze.binary_reflection.lib.AsIcptAnn.
Import OSSVerify.glaze.binary_reflection.images.Asan.
Import ListNotations.
Open Scope Z_scope.
#[local] Unset Lia Cache. #[local] Unset Nia Cache. #[local] Unset Nra Cache.

Section INST.
  Context {RC : run_ceil}.
  Variable FXOK : FPState -> Prop.
  Variable AAINVH : option Z -> list (Z * Z) -> list (Z * Z) -> Z -> Z -> Z -> mem -> Model -> Prop.
  Variable fsbase : Z.
  Hypothesis HP : forall h, AAINV_props asan_addrs (AAINVH h) fsbase ASEGS.
  Hypothesis HNM : forall h Lc FF B C K M mdl b n, AAINVH h Lc FF B C K M mdl -> In (b, n) Lc -> n <= NMAX.
  #[local] Abbreviation CELLS_L := (ann_cellsL asan_poison_tab asan_m2s_tab_6fb04 asan_ann_g_flags asan_ann_p_flags
                                       asan_ann_g_verb asan_ann_p_verb asan_ann_g_shoff asan_ann_p_shoff).
  Hypothesis CELLS : forall h Lc FF B C K M mdl, AAINVH h Lc FF B C K M mdl ->
    Forall (fun c => cellN ASEGS M (fst (fst c)) (snd (fst c)) (snd c)) CELLS_L.

  (* [comment removed for export] *)
  Lemma ann_cellsL_A : CELLS_L = ltac:(let x := eval cbv in CELLS_L in exact x).
  Proof using. reflexivity. Qed.

  Lemma asan_ann_T_entry : asan_ann_base = Z_to_bv 64 (as_annot asan_addrs).
  Proof using. apply bv_eq. vm_compute. reflexivity. Qed.
  Lemma asan_ann_mset_nz : bv_unsigned (pt_mset asan_poison_tab) <> 0.
  Proof using. cbv. discriminate. Qed.
  Lemma asan_ann_mset_ret : ret_ok (pt_mset asan_poison_tab).
  Proof using. apply ret_ok_even. vm_compute. reflexivity. Qed.

  Theorem C_annotate_A : ANNOTATE_AT ASEGS FXOK asan_addrs AAINVH (as_annot asan_addrs).
  Proof using CELLS HNM HP fsbase.
    apply (C_annotate ASEGS FXOK asan_addrs AAINVH fsbase HP asan_segs_hull asan_segs_wx asan_img_hi_AS_LO asan_img_lo_nonneg HNM
             asan_ann_base asan_poison_tab asan_m2s_tab_6fb04
             asan_ann_g_flags asan_ann_p_flags asan_ann_g_verb asan_ann_p_verb asan_ann_g_shoff asan_ann_p_shoff
             asan_anncc_code (fun fx => @asan_poison_tab_ok fx) asan_ann_ptb (fun fx => @asan_m2s_tab_ok_6fb04 fx) asan_ann_mtb
             (fun fx => @asan_ann_G44 fx) (fun fx => @asan_ann_G72 fx) (fun fx => @asan_ann_G404 fx) asan_ann_hbase
             asan_ann_mset_nz asan_ann_mset_ret asan_ann_T_entry CELLS).
    - rewrite ann_cellsL_A. repeat apply Forall_cons; try apply Forall_nil; cbn -[Z.le Z.add Z.lt]; lia.
    - split; cbv; discriminate.
  Qed.
End INST.
End AsIcptAnnI.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module AsIcptInstBtS.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsK OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtStkLift.AsAinvFacts3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsRtK OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib AsRtImg OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOps3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvHole3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtAMemset OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtStkLift.AsRtAMemsetI OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtStkLift.AsRtXMemset OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtStkLift.AsRtXMemsetI OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtStkLift.AsRtAMemcpy OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtStkLift.AsRtAMemcpyI OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtStkLift.AsRtXMemcpy OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtStkLift.AsRtXMemcpyI OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtAMemmove OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtStkLift.AsRtAMemmoveI OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtStkLift.AsRtXMemmove OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtStkLift.AsRtXMemmoveI OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtTlsGA.AsRtXStrlen OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtXStrlenI OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtStkLift.AsIcptMemset AsIcptMemsetI OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtStkLift.AsIcptXMemset AsIcptXMemsetI OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtStkLift.AsIcptMemcpy AsIcptMemcpyI OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtStkLift.AsIcptXMemcpy AsIcptXMemcpyI OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtStkLift.AsIcptMemmove AsIcptMemmoveI OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtStkLift.AsIcptXMemmove AsIcptXMemmoveI OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtStkLift.AsIcptStrlen AsIcptStrlenI OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtM2S OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtXStrlenI.AsRtM2SI OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoison OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoisonI OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtAnn AsRtAnnI OSSVerify.Proofs.glaze.binary_reflection.lib.AsIcptAnn.AsIcptAnnM OSSVerify.Proofs.glaze.binary_reflection.lib.AsIcptAnn AsIcptAnnI OSSVerify.Proofs.glaze.binary_reflection.lib.AsIcptSetSh.AsIcptLift OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d.AsAinvFreeS OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtStkLift.AsRtFakeRel.
Import OSSVerify.glaze.binary_reflection.images.Asan.
Import ListNotations.
Open Scope Z_scope.
#[local] Unset Lia Cache. #[local] Unset Nia Cache. #[local] Unset Nra Cache.

Section BT.
  Context {RC : run_ceil}.
  Variable FXOK : FPState -> Prop.
  Variable bt : as_boot.
  Hypothesis BT_IA : bt_ia bt = asan_addrs.
  Hypothesis BT_SEGS : bt_segs bt = ASEGS.
  Hypothesis BT_FS : 0 <= bt_fs bt.

  #[local] Notation AAINVH := (AAINV_HS bt).

  Lemma HP_bt : forall h, AAINV_props asan_addrs (AAINVH h) (bt_fs bt) ASEGS.
  Proof using BT_SEGS BT_IA. intros h. rewrite <- BT_IA, <- BT_SEGS. exact (AAINV_props_all bt (holes_lsopt h)). Qed.

  (* [comment removed for export] *)
  Lemma CELLS_bt : forall cs, Forall (fun c => In c (bt_consts bt)) cs ->
    forall h Lc FF B C K M mdl, AAINVH h Lc FF B C K M mdl ->
    Forall (fun c => cellN ASEGS M (fst (fst c)) (snd (fst c)) (snd c)) cs.
  Proof using BT_SEGS.
    intros cs Hcs h Lc FF B C K M mdl (st & W & R & _).
    pose proof (read_consts bt st Lc FF M mdl R) as CH. unfold cells_hold, cellZ in CH. rewrite BT_SEGS in CH.
    rewrite Forall_forall in Hcs, CH |- *. intros c Hc. exact (CH c (Hcs c Hc)).
  Qed.

  Hypothesis K_memset_icpt : Forall (fun c => In c (bt_consts bt)) (xmset_cells asan_xmset_tab).
  Hypothesis K_asan_memset : Forall (fun c => In c (bt_consts bt)) (amset_cells asan_amset_tab).
  Hypothesis K_memcpy_icpt : Forall (fun c => In c (bt_consts bt)) (xmcpy_cells asan_xmcpy_tab).
  Hypothesis K_asan_memcpy : Forall (fun c => In c (bt_consts bt)) (amcpy_cells asan_amcpy_tab).
  Hypothesis K_memmove_icpt : Forall (fun c => In c (bt_consts bt)) (xmmove_cells asan_xmmove_tab).
  Hypothesis K_asan_memmove : Forall (fun c => In c (bt_consts bt)) (ammove_cells asan_ammove_tab).
  Hypothesis K_strlen_icpt : Forall (fun c => In c (bt_consts bt)) (xstrlen_cells asan_xstrlen_tab).

  Theorem C_memset_icpt_bts : MEMSET_AT ASEGS FXOK asan_addrs AAINVH (ia_memset_icpt asan_addrs).
  Proof using K_memset_icpt BT_FS BT_SEGS BT_IA. exact (C_memset_icpt_A FXOK AAINVH (bt_fs bt) HP_bt BT_FS (CELLS_bt _ K_memset_icpt)). Qed.
  Theorem C_asan_memset_bts : MEMSET_AT ASEGS FXOK asan_addrs AAINVH (ia_asan_memset asan_addrs).
  Proof using K_asan_memset BT_FS BT_SEGS BT_IA. exact (C_asan_memset_A FXOK AAINVH (bt_fs bt) HP_bt BT_FS (CELLS_bt _ K_asan_memset)). Qed.
  Theorem C_memcpy_icpt_bts : MEMCPY_AT ASEGS FXOK asan_addrs AAINVH (ia_memcpy_icpt asan_addrs).
  Proof using K_memcpy_icpt BT_FS BT_SEGS BT_IA. exact (C_memcpy_icpt_A FXOK AAINVH (bt_fs bt) HP_bt BT_FS (CELLS_bt _ K_memcpy_icpt)). Qed.
  Theorem C_asan_memcpy_bts : MEMCPY_AT ASEGS FXOK asan_addrs AAINVH (ia_asan_memcpy asan_addrs).
  Proof using K_asan_memcpy BT_FS BT_SEGS BT_IA. exact (C_asan_memcpy_A FXOK AAINVH (bt_fs bt) HP_bt BT_FS (CELLS_bt _ K_asan_memcpy)). Qed.
  Theorem C_memmove_icpt_bts : MEMMOVE_AT ASEGS FXOK asan_addrs AAINVH (ia_memmove_icpt asan_addrs).
  Proof using K_memmove_icpt BT_FS BT_SEGS BT_IA. exact (C_memmove_icpt_A FXOK AAINVH (bt_fs bt) HP_bt BT_FS (CELLS_bt _ K_memmove_icpt)). Qed.
  Theorem C_asan_memmove_bts : MEMMOVE_AT ASEGS FXOK asan_addrs AAINVH (ia_asan_memmove asan_addrs).
  Proof using K_asan_memmove BT_FS BT_SEGS BT_IA. exact (C_asan_memmove_A FXOK AAINVH (bt_fs bt) HP_bt BT_FS (CELLS_bt _ K_asan_memmove)). Qed.
  Theorem C_strlen_icpt_bts : STRLEN_AT ASEGS FXOK asan_addrs AAINVH (ia_strlen_icpt asan_addrs).
  Proof using K_strlen_icpt BT_FS BT_SEGS BT_IA. exact (C_strlen_icpt_A FXOK AAINVH (bt_fs bt) HP_bt BT_FS (CELLS_bt _ K_strlen_icpt)). Qed.
  (* [comment removed for export] *)
  Lemma HNM_bts : forall h Lc FF B C K M mdl b n, AAINVH h Lc FF B C K M mdl -> In (b, n) Lc -> n <= NMAX.
  Proof using.
    intros h Lc FF B C K M mdl b n (st & W & _ & _) Hin.
    destruct W as (_ & _ & _ & _ & WL & _). destruct WL as (WL1 & _). destruct (WL1 b n Hin) as (X & _). lia.
  Qed.
  Hypothesis K_annotate : Forall (fun c => In c (bt_consts bt))
     (ann_cellsL asan_poison_tab asan_m2s_tab_6fb04 asan_ann_g_flags asan_ann_p_flags asan_ann_g_verb asan_ann_p_verb asan_ann_g_shoff asan_ann_p_shoff).
  Theorem C_annotate_bts : ANNOTATE_AT ASEGS FXOK asan_addrs AAINVH (as_annot asan_addrs).
  Proof using K_annotate BT_SEGS BT_IA. exact (C_annotate_A FXOK AAINVH (bt_fs bt) HP_bt HNM_bts (CELLS_bt _ K_annotate)). Qed.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma FS_NOLAZY_bt : forall st Lc FF M mdl z,
    WF bt st Lc FF -> Rep bt st Lc FF M mdl -> bt_fs bt + 0x1000 <= z < bt_fs bt + 0x9000 -> lzb mdl z = false.
  Proof using. exact (AsRtStkLift.AsAinvFacts3b.FS_NOLAZY bt). Qed.
  Lemma FS_PRIV_bt : forall st Lc FF z,
    WF bt st Lc FF -> bt_fs bt + 0x1000 <= z < bt_fs bt + 0x9000 -> rt_priv asan_addrs Lc FF z.
  Proof using BT_IA. intros st Lc FF z W Hz. rewrite <- BT_IA. exact (AsRtStkLift.AsAinvFacts3b.FS_PRIV bt st Lc FF z W Hz). Qed.
  Lemma HOFF_bt : forall h Lc FF B C K M mdl AA, AAINVH h Lc FF B C K M mdl -> H_off_segments ASEGS (HL mdl AA).
  Proof using BT_SEGS BT_IA. intros h Lc FF B C K M mdl AA AI. exact (HL_off_segments ASEGS asan_addrs (AAINVH h) (bt_fs bt) (HP_bt h) asan_segs_hull Lc FF B C K M mdl AA AI). Qed.
  Theorem C_fakerel_bts : forall {fx : FPState}, FAKEREL ASEGS FXOK asan_addrs AAINVH.
  Proof using BT_SEGS BT_IA.
    intros fx. pose proof (@C_fakerel_P RC FXOK bt (fun h => holes_lsopt h)) as X. rewrite BT_SEGS, BT_IA in X.
    exact (X asan_segs_wx HOFF_bt FS_NOLAZY_bt FS_PRIV_bt fx).
  Qed.
End BT.
End AsIcptInstBtS.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsCodeM3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsCodeM6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module AsRtTlsGAI.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtTlsGA.AsRtXStrlen OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtXStrlenI OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtTlsGA OSSVerify.Proofs.glaze.binary_reflection.lib.AsCodeM3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsCodeM5 OSSVerify.Proofs.glaze.binary_reflection.lib.AsCodeM6.
Import OSSVerify.glaze.binary_reflection.images.Asan.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Abbreviation ASEGS := Asan.M.loaded_segments.

Definition asan_tlsga_tab : tlsga_tab :=
  {| tg_hb := 0x5c534; tg_tga := 0xf5fbc; tg_pgs := 0xf7070;
     tg_c_inited := 0x108258; tg_c_rtga := 0x1010d0; tg_c_tsd := 0x106de0; tg_g_cf := 0xff260; tg_p_cf := 0x1990a8;
     tg_g_verb := 0xff2c0; tg_p_verb := 0x197018; tg_c_tlsd := 0x100020 |}.

Section FPGen1.
Context {fx : FPState}.

Lemma asan_tlsga_tab_ok : tlsga_tab_ok ASEGS asan_tlsga_tab.
Proof using.
  (lazymatch goal with |- ?G => let G' := eval unfold tlsga_tab_ok in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [tg_hb tg_tga tg_pgs tg_c_inited tg_c_rtga tg_c_tsd tg_g_cf tg_p_cf tg_g_verb tg_p_verb tg_c_tlsd asan_tlsga_tab] in G in change_no_check G' end).
  repeat match goal with |- _ /\ _ => split end.
  - (lazymatch goal with |- ?G => let G' := eval unfold tgth_words in G in change_no_check G' end). code_ato_vm.
  - (lazymatch goal with |- ?G => let G' := eval unfold tgic_words in G in change_no_check G' end). code_ato_vm.
  - (lazymatch goal with |- ?G => let G' := eval unfold tgct_words in G in change_no_check G' end). code_ato_vm.
  - (lazymatch goal with |- ?G => let G' := eval unfold tgts_words in G in change_no_check G' end). code_ato_vm.
  - (lazymatch goal with |- ?G => let G' := eval unfold tgdt_words in G in change_no_check G' end). code_ato_vm.
  - (lazymatch goal with |- ?G => let G' := eval unfold mtga_words in G in change_no_check G' end). code_ato_vm.
  - (lazymatch goal with |- ?G => let G' := eval unfold mpgs_words in G in change_no_check G' end). code_ato_vm.
  - replace (at_ (0x5c534 : word) 104072) with (0x75bbc : word) by (apply bv_eq; vm_compute; reflexivity). exact try_asan_init_run.
  - gload_tac F_60e7c D_60e7c F_60e80 D_60e80.
  - gaddr2_tac F_70a34 D_70a34 F_70a38 D_70a38.
  - gjump_tac F_70a48 D_70a48.
  - gload_tac F_85b04 D_85b04 F_85b08 D_85b08.
  - gload_tac F_85b18 D_85b18 F_85b1c D_85b1c.
  - gauipc_ld_tac F_85b24 D_85b24 F_85b2c D_85b2c.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - apply ret_ok_even. vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - lia.
Qed.
End FPGen1.
End AsRtTlsGAI.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtStkMal0 OSSVerify.Proofs.glaze.binary_reflection.lib.AsCodeM2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module AsRtStkMal0I.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtM2S OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtXStrlenI.AsRtM2SI OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtTlsGA AsRtTlsGAI OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtStkMal0 OSSVerify.Proofs.glaze.binary_reflection.lib.AsCodeM2.
Import OSSVerify.glaze.binary_reflection.images.Asan.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Abbreviation ASEGS := Asan.M.loaded_segments.

Definition asan_stk0_tab : stk_tab :=
  {| sk_base := 0x5716c; sk_tg := asan_tlsga_tab; sk_mt := asan_m2s_tab_577b0; sk_arg := 0x100010 |}.

Section FPGen1.
Context {fx : FPState}.

Lemma asan_stk0_tab_ok : stk0_tab_ok ASEGS asan_stk0_tab.
Proof using.
  (lazymatch goal with |- ?G => let G' := eval unfold stk0_tab_ok in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [sk_base sk_tg sk_mt sk_arg asan_stk0_tab] in G in change_no_check G' end).
  repeat match goal with |- _ /\ _ => split end.
  - (lazymatch goal with |- ?G => let G' := eval unfold stk0_words in G in change_no_check G' end). code_ato_vm.
  - exact asan_tlsga_tab_ok.
  - apply bv_eq. vm_compute. reflexivity.
  - exact asan_m2s_tab_ok_577b0.
  - apply bv_eq. vm_compute. reflexivity.
  - gaddr2_tac F_5717c D_5717c F_57180 D_57180.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
Qed.

End FPGen1.
End AsRtStkMal0I.
Module AsRtStkMal1I.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtM2S OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtXStrlenI.AsRtM2SI OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtTlsGA AsRtTlsGAI OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtStkMal0 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtStkLift.AsRtStkMal1 OSSVerify.Proofs.glaze.binary_reflection.lib.AsCodeM2.
Import OSSVerify.glaze.binary_reflection.images.Asan.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Abbreviation ASEGS := Asan.M.loaded_segments.

Definition asan_stk1_tab : stk_tab :=
  {| sk_base := 0x572e0; sk_tg := asan_tlsga_tab; sk_mt := asan_m2s_tab_577b0; sk_arg := 0x100010 |}.

Section FPGen1.
Context {fx : FPState}.

Lemma asan_stk1_tab_ok : stk1_tab_ok ASEGS asan_stk1_tab.
Proof using.
  (lazymatch goal with |- ?G => let G' := eval unfold stk1_tab_ok in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [sk_base sk_tg sk_mt sk_arg asan_stk1_tab] in G in change_no_check G' end).
  repeat match goal with |- _ /\ _ => split end.
  - (lazymatch goal with |- ?G => let G' := eval unfold stk1_words in G in change_no_check G' end). code_ato_vm.
  - exact asan_tlsga_tab_ok.
  - apply bv_eq. vm_compute. reflexivity.
  - exact asan_m2s_tab_ok_577b0.
  - apply bv_eq. vm_compute. reflexivity.
  - gaddr2_tac F_572f0 D_572f0 F_572f4 D_572f4.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
Qed.

End FPGen1.
End AsRtStkMal1I.
Module AsRtStkMal2I.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtM2S OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtXStrlenI.AsRtM2SI OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtTlsGA AsRtTlsGAI OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtStkMal0 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtStkLift.AsRtStkMal2 OSSVerify.Proofs.glaze.binary_reflection.lib.AsCodeM2.
Import OSSVerify.glaze.binary_reflection.images.Asan.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Abbreviation ASEGS := Asan.M.loaded_segments.

Definition asan_stk2_tab : stk_tab :=
  {| sk_base := 0x57470; sk_tg := asan_tlsga_tab; sk_mt := asan_m2s_tab_577b0; sk_arg := 0x100010 |}.

Section FPGen1.
Context {fx : FPState}.

Lemma asan_stk2_tab_ok : stk2_tab_ok ASEGS asan_stk2_tab.
Proof using.
  (lazymatch goal with |- ?G => let G' := eval unfold stk2_tab_ok in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [sk_base sk_tg sk_mt sk_arg asan_stk2_tab] in G in change_no_check G' end).
  repeat match goal with |- _ /\ _ => split end.
  - (lazymatch goal with |- ?G => let G' := eval unfold stk2_words in G in change_no_check G' end). code_ato_vm.
  - exact asan_tlsga_tab_ok.
  - apply bv_eq. vm_compute. reflexivity.
  - exact asan_m2s_tab_ok_577b0.
  - apply bv_eq. vm_compute. reflexivity.
  - gaddr2_tac F_57480 D_57480 F_57484 D_57484.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
Qed.

End FPGen1.
End AsRtStkMal2I.
Module AsRtStkMal3I.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtM2S OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtXStrlenI.AsRtM2SI OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtTlsGA AsRtTlsGAI OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtStkMal0 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtStkLift.AsRtStkMal3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsCodeM2.
Import OSSVerify.glaze.binary_reflection.images.Asan.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Abbreviation ASEGS := Asan.M.loaded_segments.

Definition asan_stk3_tab : stk_tab :=
  {| sk_base := 0x5760c; sk_tg := asan_tlsga_tab; sk_mt := asan_m2s_tab_577b0; sk_arg := 0x100010 |}.

Section FPGen1.
Context {fx : FPState}.

Lemma asan_stk3_tab_ok : stk3_tab_ok ASEGS asan_stk3_tab.
Proof using.
  (lazymatch goal with |- ?G => let G' := eval unfold stk3_tab_ok in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [sk_base sk_tg sk_mt sk_arg asan_stk3_tab] in G in change_no_check G' end).
  repeat match goal with |- _ /\ _ => split end.
  - (lazymatch goal with |- ?G => let G' := eval unfold stk3_words in G in change_no_check G' end). code_ato_vm.
  - exact asan_tlsga_tab_ok.
  - apply bv_eq. vm_compute. reflexivity.
  - exact asan_m2s_tab_ok_577b0.
  - apply bv_eq. vm_compute. reflexivity.
  - gaddr2_tac F_5761c D_5761c F_57620 D_57620.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
Qed.

End FPGen1.
End AsRtStkMal3I.
Module AsRtStkLiftI.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsK OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsRtK OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib AsRtImg OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOps3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvHole3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsIcptSetSh.AsIcptLift OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtM2S OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtXStrlenI.AsRtM2SI OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtTlsGA AsRtTlsGAI OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtStkMal0 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtStkLift.AsRtStkMal1 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtStkLift.AsRtStkMal2 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtStkLift.AsRtStkMal3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtStkLift.AsRtStkMalK AsRtStkMal0I AsRtStkMal1I AsRtStkMal2I AsRtStkMal3I OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtStkLift.AsRtStkLiftG OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtStkLift.
Import OSSVerify.glaze.binary_reflection.images.Asan.
Import ListNotations.
Open Scope Z_scope.
#[local] Unset Lia Cache. #[local] Unset Nia Cache. #[local] Unset Nra Cache.

(* [comment removed for export] *)
Definition asan_stk_cells (tctx : Z) : list (Z * nat * Z) :=
  stk_consts asan_stk0_tab (ia_tp asan_addrs) tctx 0x100010 0xfffffffffffff800 0x63a760 0x63af40 0x65bae8.

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac wd_in_nat i := lazymatch i with O => idtac | S ?j => wd_in_nat j end.
Ltac wd_in_fast :=
  let G := match goal with |- ?G => eval cbv beta in G end in
  lazymatch G with In (?a, ?n, ?v) ?L =>
    let i := eval lazy in ((fix f (l : list (Z * nat * Z)) : nat := match l with [] => O | (a', n', _) :: l' =>
                              if (Z.eqb a a' && Nat.eqb n n')%bool then O else S (f l') end) L) in
    wd_in_nat i; exact (nth_error_In L i eq_refl)
  end.

Lemma asan_stk_cells_in : forall P6 SPB M8 M10, Forall (fun c => In c (asan_consts P6 SPB M8 M10)) (asan_stk_cells M10).
Proof.
  intros P6 SPB M8 M10. (lazymatch goal with |- ?G => let G' := eval unfold asan_stk_cells, stk_consts in G in change_no_check G' end).
  repeat apply Forall_cons; try apply Forall_nil;
    first [ wd_in_fast | (lazymatch goal with |- ?G => let G' := eval unfold asan_consts in G in change_no_check G' end); (lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); repeat (first [left; reflexivity | right]) ].
Qed.

Section BT.
  Context {RC : run_ceil}.
  Variable FXOK : FPState -> Prop.
  Variable bt : as_boot.
  Hypothesis BT_IA : bt_ia bt = asan_addrs.
  Hypothesis BT_SEGS : bt_segs bt = ASEGS.
  Hypothesis BT_TP : bt_tp bt = ia_tp asan_addrs.
  Hypothesis BT_TLSFS : bt_tls_fs bt = ia_tp asan_addrs.
  Hypothesis K_stkmal : Forall (fun c => In c (bt_consts bt)) (asan_stk_cells (bt_tctx bt)).

  Lemma HOFF_P : forall (HP0 : option Z -> ast -> Prop) h Lc FF B C K M mdl AA,
    AAINVP (HP0 h) bt Lc FF B C K M mdl -> H_off_segments (bt_segs bt) (HL mdl AA).
  Proof using BT_SEGS BT_IA.
    intros HP0 h Lc FF B C K M mdl AA AI.
    assert (HULL : forall a, find_segment (bt_segs bt) a 1 <> None -> ia_img_lo (bt_ia bt) <= a < ia_img_hi (bt_ia bt))
      by (rewrite BT_SEGS, BT_IA; exact asan_segs_hull).
    exact (HL_off_segments (bt_segs bt) (bt_ia bt) (AAINVP (HP0 h) bt) (bt_fs bt) (AAINV_props_all bt (HP0 h)) HULL Lc FF B C K M mdl AA AI).
  Qed.

  (* [comment removed for export] *)
  Lemma C_stkmal_any : forall (HP0 : option Z -> ast -> Prop),
    (forall h st k v, HP0 h st -> HP0 h (set_hint st k v)) ->
    forall k, 0 <= k <= KMAXCLASS -> STKMAL ASEGS FXOK asan_addrs (fun h => AAINVP (HP0 h) bt) (bt_fs bt) k.
  Proof using K_stkmal BT_TLSFS BT_TP BT_SEGS BT_IA.
    intros HP0 HH k Hk. unfold KMAXCLASS in Hk.
    assert (GEN : forall t, (forall fx : FPState, @stkK_tab_ok fx (bt_segs bt) k t) -> sk_base t = Z_to_bv 64 (ia_stkmal (bt_ia bt) k) ->
                  sk_tg t = sk_tg asan_stk0_tab -> sk_mt t = sk_mt asan_stk0_tab -> sk_arg t = Z_to_bv 64 0x100010 ->
                  STKMAL (bt_segs bt) FXOK (bt_ia bt) (fun h => AAINVP (HP0 h) bt) (bt_fs bt) k).
    { intros t TOK TE TG MT TA.
      apply (@C_stkmal_P RC FXOK bt HP0 ltac:(rewrite BT_SEGS; exact asan_segs_wx)
               ltac:(rewrite BT_SEGS, BT_IA; exact asan_segs_hull) (HOFF_P HP0) HH k Hk t TOK TE
               0x100010 0xfffffffffffff800 0x63a760 0x63af40 0x65bae8 TA).
      - lia.
      - rewrite BT_IA. reflexivity.
      - rewrite BT_IA. exact BT_TP.
      - rewrite BT_IA. exact BT_TLSFS.
      - rewrite BT_IA. vm_compute. discriminate.
      - rewrite BT_IA. (lazymatch goal with |- ?G => let G' := eval unfold stk_consts in G in change_no_check G' end). rewrite TG, MT. exact K_stkmal. }
    rewrite <- BT_SEGS, <- BT_IA.
    assert (KC : k = 0 \/ k = 1 \/ k = 2 \/ k = 3) by lia.
    destruct KC as [-> | [-> | [-> | ->]]].
    - apply (GEN asan_stk0_tab); [| rewrite BT_IA; apply bv_eq; reflexivity | reflexivity | reflexivity | apply bv_eq; reflexivity].
      intros fx'. rewrite BT_SEGS. (lazymatch goal with |- ?G => let G' := eval unfold stkK_tab_ok in G in change_no_check G' end). repeat match goal with |- _ /\ _ => split end; intros E; first [discriminate E | exact asan_stk0_tab_ok].
    - apply (GEN asan_stk1_tab); [| rewrite BT_IA; apply bv_eq; reflexivity | reflexivity | reflexivity | apply bv_eq; reflexivity].
      intros fx'. rewrite BT_SEGS. (lazymatch goal with |- ?G => let G' := eval unfold stkK_tab_ok in G in change_no_check G' end). repeat match goal with |- _ /\ _ => split end; intros E; first [discriminate E | exact asan_stk1_tab_ok].
    - apply (GEN asan_stk2_tab); [| rewrite BT_IA; apply bv_eq; reflexivity | reflexivity | reflexivity | apply bv_eq; reflexivity].
      intros fx'. rewrite BT_SEGS. (lazymatch goal with |- ?G => let G' := eval unfold stkK_tab_ok in G in change_no_check G' end). repeat match goal with |- _ /\ _ => split end; intros E; first [discriminate E | exact asan_stk2_tab_ok].
    - apply (GEN asan_stk3_tab); [| rewrite BT_IA; apply bv_eq; reflexivity | reflexivity | reflexivity | apply bv_eq; reflexivity].
      intros fx'. rewrite BT_SEGS. (lazymatch goal with |- ?G => let G' := eval unfold stkK_tab_ok in G in change_no_check G' end). repeat match goal with |- _ /\ _ => split end; intros E; first [discriminate E | exact asan_stk3_tab_ok].
  Qed.

  Theorem C_stkmal_bt : forall k, 0 <= k <= KMAXCLASS -> STKMAL ASEGS FXOK asan_addrs (AAINV_H bt) (bt_fs bt) k.
  Proof using K_stkmal BT_TLSFS BT_TP BT_SEGS BT_IA. intros k Hk. apply (C_stkmal_any (fun h => holes_le h) ltac:(intros h st k' v H; exact H) k Hk). Qed.

  Theorem C_stkmal_bts : forall k, 0 <= k <= KMAXCLASS -> STKMAL ASEGS FXOK asan_addrs (AAINV_HS bt) (bt_fs bt) k.
  Proof using K_stkmal BT_TLSFS BT_TP BT_SEGS BT_IA. intros k Hk. apply (C_stkmal_any (fun h => holes_lsopt h) ltac:(intros h st k' v H; destruct h; exact H) k Hk). Qed.
End BT.
End AsRtStkLiftI.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFFam.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module AsContractsA.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsK OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinv3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvHole3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFFam.AsAinvHS3 AsRtImg OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtStkLift.AsRtAMemsetI OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtStkLift.AsRtXMemsetI OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtStkLift.AsRtAMemcpyI OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtStkLift.AsRtXMemcpyI OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtStkLift.AsRtAMemmoveI OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtStkLift.AsRtXMemmoveI OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtXStrlenI OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtStkLift.AsIcptMemset OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtStkLift.AsIcptXMemset OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtStkLift.AsIcptMemcpy OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtStkLift.AsIcptXMemcpy OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtStkLift.AsIcptMemmove OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtStkLift.AsIcptXMemmove OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtStkLift.AsIcptStrlen AsIcptInstBtS AsRtStkLiftI.
Import OSSVerify.glaze.binary_reflection.images.Asan.
Import ListNotations.
Open Scope Z_scope.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section ContractsA.
  Context {RC : run_ceil}.
  Variable FXOK : FPState -> Prop.
  Variable FRESH : list (Z * Z) -> list (Z * Z) -> Z -> Z -> Z -> mem -> Model -> Z -> Prop.
  Variable bt : as_boot.
  Hypothesis BT_IA : bt_ia bt = asan_addrs.
  Hypothesis BT_SEGS : bt_segs bt = ASEGS.
  Hypothesis BT_FS : 0 <= bt_fs bt.
  Hypothesis BT_TP : bt_tp bt = ia_tp asan_addrs.
  Hypothesis BT_TLSFS : bt_tls_fs bt = ia_tp asan_addrs.
  #[local] Notation AAINVH := (AAINV_HS bt).

  (* [comment removed for export] *)
  Hypothesis K_memset_icpt : Forall (fun c => In c (bt_consts bt)) (xmset_cells asan_xmset_tab).
  Hypothesis K_asan_memset : Forall (fun c => In c (bt_consts bt)) (amset_cells asan_amset_tab).
  Hypothesis K_memcpy_icpt : Forall (fun c => In c (bt_consts bt)) (xmcpy_cells asan_xmcpy_tab).
  Hypothesis K_asan_memcpy : Forall (fun c => In c (bt_consts bt)) (amcpy_cells asan_amcpy_tab).
  Hypothesis K_memmove_icpt : Forall (fun c => In c (bt_consts bt)) (xmmove_cells asan_xmmove_tab).
  Hypothesis K_asan_memmove : Forall (fun c => In c (bt_consts bt)) (ammove_cells asan_ammove_tab).
  Hypothesis K_strlen_icpt : Forall (fun c => In c (bt_consts bt)) (xstrlen_cells asan_xstrlen_tab).
  Hypothesis K_stkmal : Forall (fun c => In c (bt_consts bt)) (asan_stk_cells (bt_tctx bt)).

  (* [comment removed for export] *)
  Hypothesis W_MALLOC : MALLOC_KATW ASEGS FXOK asan_addrs AAINVH MSTK_A (ia_malloc asan_addrs) true.
  Hypothesis W_MALLOC_THUNK : MALLOC_KATW ASEGS FXOK asan_addrs AAINVH MSTK_A (ia_malloc_thunk asan_addrs) true.
  Hypothesis W_MALLOC_ALT : MALLOC_ALT ASEGS FXOK asan_addrs AAINVH FRESH MSTK_A (ia_malloc asan_addrs) true.
  Hypothesis W_MALLOC_ALT_THUNK : MALLOC_ALT ASEGS FXOK asan_addrs AAINVH FRESH MSTK_A (ia_malloc_thunk asan_addrs) true.
  Hypothesis W_FREE : FREE_KAT ASEGS FXOK asan_addrs AAINVH MSTK_A (ia_free asan_addrs).
  Hypothesis W_FREE_THUNK : FREE_KAT ASEGS FXOK asan_addrs AAINVH MSTK_A (ia_free_thunk asan_addrs).
  Hypothesis W_OPDEL : FREE_KAT ASEGS FXOK asan_addrs AAINVH MSTK_A (ia_opdel asan_addrs).
  Hypothesis W_OPDEL_SZ : FREE_KAT ASEGS FXOK asan_addrs AAINVH MSTK_A (ia_opdel_sz asan_addrs).




End ContractsA.
End AsContractsA.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsIfaceNM3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module AsContractsPRA.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsK OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsIfaceNM3.AsIfacePR3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinv3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOps3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtStkLift.AsAinvFacts3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvHole3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFFam.AsAinvHS3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFFam.AsAinvPrist3 AsRtImg OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsRtK OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtStkLift.AsRtAMemsetI OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtStkLift.AsRtXMemsetI OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtStkLift.AsRtAMemcpyI OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtStkLift.AsRtXMemcpyI OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtStkLift.AsRtAMemmoveI OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtStkLift.AsRtXMemmoveI OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtXStrlenI OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtStkLift.AsIcptMemset OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtStkLift.AsIcptXMemset OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtStkLift.AsIcptMemcpy OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtStkLift.AsIcptXMemcpy OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtStkLift.AsIcptMemmove OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtStkLift.AsIcptXMemmove OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtStkLift.AsIcptStrlen AsIcptMemsetI AsIcptXMemsetI AsIcptMemcpyI AsIcptXMemcpyI AsIcptMemmoveI AsIcptXMemmoveI AsIcptStrlenI OSSVerify.Proofs.glaze.binary_reflection.lib.AsIcptSetSh.AsIcptLift OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtStkLift.AsRtFakeRel AsIcptInstBtS AsRtStkLiftI.
Import OSSVerify.glaze.binary_reflection.images.Asan.
Import ListNotations.
Open Scope Z_scope.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section ContractsPRA.
  Context {RC : run_ceil}.
  Variable FXOK : FPState -> Prop.
  Variable bt : as_boot.
  Variable Q : ast -> Prop.                                             (* [comment removed for export] *)
  Hypothesis Q_hint : forall st k v, Q st -> Q (set_hint st k v).
  Hypothesis BT_IA : bt_ia bt = asan_addrs.
  Hypothesis BT_SEGS : bt_segs bt = ASEGS.
  Hypothesis BT_FS : 0 <= bt_fs bt.
  Hypothesis BT_TP : bt_tp bt = ia_tp asan_addrs.
  Hypothesis BT_TLSFS : bt_tls_fs bt = ia_tp asan_addrs.
  #[local] Notation AAINVH := (AAINV_QX bt Q).

  Hypothesis K_memset_icpt : Forall (fun c => In c (bt_consts bt)) (xmset_cells asan_xmset_tab).
  Hypothesis K_asan_memset : Forall (fun c => In c (bt_consts bt)) (amset_cells asan_amset_tab).
  Hypothesis K_memcpy_icpt : Forall (fun c => In c (bt_consts bt)) (xmcpy_cells asan_xmcpy_tab).
  Hypothesis K_asan_memcpy : Forall (fun c => In c (bt_consts bt)) (amcpy_cells asan_amcpy_tab).
  Hypothesis K_memmove_icpt : Forall (fun c => In c (bt_consts bt)) (xmmove_cells asan_xmmove_tab).
  Hypothesis K_asan_memmove : Forall (fun c => In c (bt_consts bt)) (ammove_cells asan_ammove_tab).
  Hypothesis K_strlen_icpt : Forall (fun c => In c (bt_consts bt)) (xstrlen_cells asan_xstrlen_tab).
  Hypothesis K_stkmal : Forall (fun c => In c (bt_consts bt)) (asan_stk_cells (bt_tctx bt)).

  (* [comment removed for export] *)
  Hypothesis W_MALLOC_SEC_PR : MALLOC_ALT_SEC ASEGS FXOK asan_addrs AAINVH MSTK_A (ia_malloc asan_addrs) true.
  Hypothesis W_MALLOC_SEC_PR_THUNK : MALLOC_ALT_SEC ASEGS FXOK asan_addrs AAINVH MSTK_A (ia_malloc_thunk asan_addrs) true.
  Hypothesis W_FREE_PR : FREE_KAT_N ASEGS FXOK asan_addrs AAINVH MSTK_A (ia_free asan_addrs).
  Hypothesis W_FREE_PR_THUNK : FREE_KAT_N ASEGS FXOK asan_addrs AAINVH MSTK_A (ia_free_thunk asan_addrs).
  Hypothesis W_OPDEL_PR : FREE_KAT_N ASEGS FXOK asan_addrs AAINVH MSTK_A (ia_opdel asan_addrs).
  Hypothesis W_OPDEL_SZ_PR : FREE_KAT_N ASEGS FXOK asan_addrs AAINVH MSTK_A (ia_opdel_sz asan_addrs).

  Lemma HP_pr_bt : forall h, AAINV_props asan_addrs (AAINVH h) (bt_fs bt) ASEGS.
  Proof. intros h. rewrite <- BT_IA, <- BT_SEGS. exact (AAINV_QX_props bt Q h). Qed.
  Lemma CELLS_pr : forall cs, Forall (fun c => In c (bt_consts bt)) cs ->
    forall h Lc FF B C K M mdl, AAINVH h Lc FF B C K M mdl ->
    Forall (fun c => cellN ASEGS M (fst (fst c)) (snd (fst c)) (snd c)) cs.
  Proof.
    intros cs Hcs h Lc FF B C K M mdl (st & W & R & _).
    pose proof (read_consts bt st Lc FF M mdl R) as CH. unfold cells_hold, cellZ in CH. rewrite BT_SEGS in CH.
    rewrite Forall_forall in Hcs, CH |- *. intros c Hc. exact (CH c (Hcs c Hc)).
  Qed.
  Lemma HOFF_pr : forall h Lc FF B C K M mdl AA, AAINVH h Lc FF B C K M mdl -> H_off_segments ASEGS (HL mdl AA).
  Proof. intros h Lc FF B C K M mdl AA AI. exact (HL_off_segments ASEGS asan_addrs (AAINVH h) (bt_fs bt) (HP_pr_bt h) asan_segs_hull Lc FF B C K M mdl AA AI). Qed.

  Definition W_STKMAL_PR : forall k, 0 <= k <= KMAXCLASS -> STKMAL ASEGS FXOK asan_addrs AAINVH (bt_fs bt) k :=
    @C_stkmal_any RC FXOK bt BT_IA BT_SEGS BT_TP BT_TLSFS K_stkmal (HP_q Q) (HP_q_hint Q Q_hint).
  Definition W_FAKEREL_PR : FAKEREL ASEGS FXOK asan_addrs AAINVH.
  Proof.
    intros h pc rs fx. pose proof (@C_fakerel_P RC FXOK bt (HP_q Q)) as X. rewrite BT_SEGS, BT_IA in X.
    exact (X asan_segs_wx HOFF_pr (FS_NOLAZY_bt bt) (FS_PRIV_bt bt BT_IA) fx h pc rs fx).
  Qed.

  Definition ASCP_A : as_contracts_pr ASEGS FXOK asan_addrs AAINVH (bt_fs bt) :=
    @ASCP ASEGS RC FXOK asan_addrs AAINVH (bt_fs bt)
        W_MALLOC_SEC_PR W_MALLOC_SEC_PR_THUNK W_FREE_PR W_FREE_PR_THUNK W_OPDEL_PR W_OPDEL_SZ_PR
        W_STKMAL_PR W_FAKEREL_PR
        (C_memcpy_icpt_A FXOK AAINVH (bt_fs bt) HP_pr_bt BT_FS (CELLS_pr _ K_memcpy_icpt)) (C_asan_memcpy_A FXOK AAINVH (bt_fs bt) HP_pr_bt BT_FS (CELLS_pr _ K_asan_memcpy))
        (C_memset_icpt_A FXOK AAINVH (bt_fs bt) HP_pr_bt BT_FS (CELLS_pr _ K_memset_icpt)) (C_asan_memset_A FXOK AAINVH (bt_fs bt) HP_pr_bt BT_FS (CELLS_pr _ K_asan_memset))
        (C_memmove_icpt_A FXOK AAINVH (bt_fs bt) HP_pr_bt BT_FS (CELLS_pr _ K_memmove_icpt)) (C_asan_memmove_A FXOK AAINVH (bt_fs bt) HP_pr_bt BT_FS (CELLS_pr _ K_asan_memmove))
        (C_strlen_icpt_A FXOK AAINVH (bt_fs bt) HP_pr_bt BT_FS (CELLS_pr _ K_strlen_icpt)).

  Definition ASCP_A_bt : as_contracts_pr ASEGS FXOK (bt_ia bt) AAINVH (bt_fs bt).
  Proof. rewrite BT_IA. exact ASCP_A. Defined.
End ContractsPRA.
End AsContractsPRA.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvBoot3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys10.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module AsContractsAtA.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsK OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsIfaceNM3.AsIfacePR3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinv3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinvGeom3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvHole3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFFam.AsAinvHS3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvBoot3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys10.AsAinvBootF3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFFam.AsAinvPrist3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFFam.AsAinvDrvHist3 AsRtImg OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtStkLift.AsRtAMemsetI OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtStkLift.AsRtXMemsetI OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtStkLift.AsRtAMemcpyI OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtStkLift.AsRtXMemcpyI OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtStkLift.AsRtAMemmoveI OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtStkLift.AsRtXMemmoveI OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtXStrlenI OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtStkLift.AsIcptMemset OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtStkLift.AsIcptXMemset OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtStkLift.AsIcptMemcpy OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtStkLift.AsIcptXMemcpy OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtStkLift.AsIcptMemmove OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtStkLift.AsIcptXMemmove OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtStkLift.AsIcptStrlen AsIcptInstBtS AsRtStkLiftI AsContractsA AsContractsPRA.
Import OSSVerify.glaze.binary_reflection.images.Asan.
Import ListNotations.
Open Scope Z_scope.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section At.
  Context {RC : run_ceil}.
  Variable FXOK : FPState -> Prop.
  Variable hv : bvars.
  #[local] Notation bt := (asan_bt hv).
  Hypothesis BF : boot_facts bt.

  Ltac in_consts_old := rewrite asan_bt_consts; unfold asan_consts; cbv zeta; repeat (first [left; reflexivity | right]).
  (* [comment removed for export] *)
  Ltac in_consts_nat i := lazymatch i with O => idtac | S ?j => in_consts_nat j end.
  Ltac in_consts_fast :=
    let G := match goal with |- ?G => eval cbv beta in G end in
    lazymatch G with In (?a, ?n, ?v) ?L =>
      let i := eval lazy in ((fix f (l : list (Z * nat * Z)) : nat := match l with [] => O | (a', n', _) :: l' =>
                                if (Z.eqb a a' && Nat.eqb n n')%bool then O else S (f l') end) L) in
      in_consts_nat i; exact (nth_error_In L i eq_refl)
    end.
  Ltac in_consts := first [in_consts_fast | in_consts_old].
  Ltac k_rows :=
    match goal with |- Forall _ ?L => let L' := eval vm_compute in L in change (Forall (fun c => In c (bt_consts bt)) L') end;
    repeat (constructor; [in_consts|]); constructor.

  Lemma K_memset_icpt_at : Forall (fun c => In c (bt_consts bt)) (xmset_cells asan_xmset_tab).   Proof. k_rows. Qed.
  Lemma K_asan_memset_at : Forall (fun c => In c (bt_consts bt)) (amset_cells asan_amset_tab).   Proof. k_rows. Qed.
  Lemma K_memcpy_icpt_at : Forall (fun c => In c (bt_consts bt)) (xmcpy_cells asan_xmcpy_tab).   Proof. k_rows. Qed.
  Lemma K_asan_memcpy_at : Forall (fun c => In c (bt_consts bt)) (amcpy_cells asan_amcpy_tab).   Proof. k_rows. Qed.
  Lemma K_memmove_icpt_at : Forall (fun c => In c (bt_consts bt)) (xmmove_cells asan_xmmove_tab). Proof. k_rows. Qed.
  Lemma K_asan_memmove_at : Forall (fun c => In c (bt_consts bt)) (ammove_cells asan_ammove_tab). Proof. k_rows. Qed.
  Lemma K_strlen_icpt_at : Forall (fun c => In c (bt_consts bt)) (xstrlen_cells asan_xstrlen_tab). Proof. k_rows. Qed.
  Lemma K_stkmal_at : Forall (fun c => In c (bt_consts bt)) (asan_stk_cells (bt_tctx bt)).
  Proof. rewrite asan_bt_consts, asan_bt_tctx. apply asan_stk_cells_in. Qed.

  Lemma BT_FS_at : 0 <= bt_fs bt.
  Proof.
    pose proof (boot_facts_ok bt BF) as (_ & WM & _). destruct WM as (RNG & _ & _ & _ & _ & _ & INFS & _).
    destruct (RNG _ _ (all_ranges_fixed bt (st0 bt) _ INFS)) as ((D1 & _) & _). lia.
  Qed.

  (* [comment removed for export] *)
  Hypothesis W_MALLOC : MALLOC_KATW ASEGS FXOK asan_addrs (AAINV_HS bt) MSTK_A (ia_malloc asan_addrs) true.
  Hypothesis W_MALLOC_THUNK : MALLOC_KATW ASEGS FXOK asan_addrs (AAINV_HS bt) MSTK_A (ia_malloc_thunk asan_addrs) true.
  Hypothesis W_MALLOC_ALT : MALLOC_ALT ASEGS FXOK asan_addrs (AAINV_HS bt) (FRESH_bt bt) MSTK_A (ia_malloc asan_addrs) true.
  Hypothesis W_MALLOC_ALT_THUNK : MALLOC_ALT ASEGS FXOK asan_addrs (AAINV_HS bt) (FRESH_bt bt) MSTK_A (ia_malloc_thunk asan_addrs) true.
  Hypothesis W_FREE : FREE_KAT ASEGS FXOK asan_addrs (AAINV_HS bt) MSTK_A (ia_free asan_addrs).
  Hypothesis W_FREE_THUNK : FREE_KAT ASEGS FXOK asan_addrs (AAINV_HS bt) MSTK_A (ia_free_thunk asan_addrs).
  Hypothesis W_OPDEL : FREE_KAT ASEGS FXOK asan_addrs (AAINV_HS bt) MSTK_A (ia_opdel asan_addrs).
  Hypothesis W_OPDEL_SZ : FREE_KAT ASEGS FXOK asan_addrs (AAINV_HS bt) MSTK_A (ia_opdel_sz asan_addrs).


  (* [comment removed for export] *)
  Hypothesis W_MALLOC_SEC_PR : MALLOC_ALT_SEC ASEGS FXOK asan_addrs (AAINV_DRX bt) MSTK_A (ia_malloc asan_addrs) true.
  Hypothesis W_MALLOC_SEC_PR_THUNK : MALLOC_ALT_SEC ASEGS FXOK asan_addrs (AAINV_DRX bt) MSTK_A (ia_malloc_thunk asan_addrs) true.
  Hypothesis W_FREE_PR : FREE_KAT_N ASEGS FXOK asan_addrs (AAINV_DRX bt) MSTK_A (ia_free asan_addrs).
  Hypothesis W_FREE_PR_THUNK : FREE_KAT_N ASEGS FXOK asan_addrs (AAINV_DRX bt) MSTK_A (ia_free_thunk asan_addrs).
  Hypothesis W_OPDEL_PR : FREE_KAT_N ASEGS FXOK asan_addrs (AAINV_DRX bt) MSTK_A (ia_opdel asan_addrs).
  Hypothesis W_OPDEL_SZ_PR : FREE_KAT_N ASEGS FXOK asan_addrs (AAINV_DRX bt) MSTK_A (ia_opdel_sz asan_addrs).

  Theorem ASCD_A_at : as_contracts_pr ASEGS FXOK (bt_ia bt) (AAINV_DRX bt) (bt_fs bt).
  Proof.
    exact (@ASCP_A_bt RC FXOK bt drv_hist drv_hist_hint eq_refl eq_refl BT_FS_at eq_refl eq_refl
             K_memset_icpt_at K_asan_memset_at K_memcpy_icpt_at K_asan_memcpy_at K_memmove_icpt_at K_asan_memmove_at K_strlen_icpt_at K_stkmal_at
             W_MALLOC_SEC_PR W_MALLOC_SEC_PR_THUNK W_FREE_PR W_FREE_PR_THUNK W_OPDEL_PR W_OPDEL_SZ_PR).
  Qed.
End At.
End AsContractsAtA.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtPoisonI OSSVerify.Proofs.glaze.binary_reflection.lib.BoCodeM2 OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtXStrlenI.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module BoRtAMemsetI.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtPoisonI.BoRtLeafI OSSVerify.Proofs.glaze.binary_reflection.lib.BoCodeM2 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtMemIsZero OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtM2S OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtXStrlenI.BoRtM2SI OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtMuslMemset OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoison OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtRegion OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtXStrlenI.BoRtRegionI OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtAMemset.AsRtQC OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtAMemset.
Import OSSVerify.glaze.binary_reflection.images.AsanUbsan.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

#[local] Abbreviation BSEGS := AsanUbsan.M.loaded_segments.

Definition both_amset_tab : amset_tab :=
  {| am_base := 0x6d678; am_rip := both_rip_tab; am_mset := 0xfc38c;
     am_g_flag := 0x106a80; am_p_flag := 0x10ee99; am_c_rms := 0x107e58 |}.

Section FPGen1.
Context {fx : FPState}.

Lemma both_amset_tab_ok : amset_tab_ok BSEGS both_amset_tab.
Proof using.
  split; (lazymatch goal with |- ?G => let G' := eval cbn [am_base am_rip am_mset am_g_flag am_p_flag am_c_rms both_amset_tab rt_base rt_m2s both_rip_tab mt_g_shoff both_m2s_tab_6fac4] in G in change_no_check G' end).
  - (lazymatch goal with |- ?G => let G' := eval unfold amset_words in G in change_no_check G' end). code_ato_vm.
  - exact both_rip_tab_ok.
  - apply bv_eq; vm_compute; reflexivity.
  - exact both_memset_code.
  - replace (at_ (0x6d678 : word) 84) with (0x6d6cc : word) by (apply bv_eq; vm_compute; reflexivity).
    (lazymatch goal with |- ?G => let G' := eval unfold qc1f_words in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [bv_eqb] in G in change_no_check G' end). code_ato_vm.
  - replace (at_ (0x6d678 : word) 416) with (0x6d818 : word) by (apply bv_eq; vm_compute; reflexivity).
    (lazymatch goal with |- ?G => let G' := eval unfold qc1s_words in G in change_no_check G' end). code_ato_vm.
  - gload_tac F_6d6a0 D_6d6a0 F_6d6a4 D_6d6a4.
  - replace (at_ (0x6d678 : word) 84) with (0x6d6cc : word) by (apply bv_eq; vm_compute; reflexivity).
    gload_tac F_6d6cc D_6d6cc F_6d6d0 D_6d6d0.
  - gload_tac F_6d708 D_6d708 F_6d70c D_6d70c.
  - replace (at_ (0x6d678 : word) 140) with (0x6d704 : word) by (apply bv_eq; vm_compute; reflexivity).
    replace (at_ (0x6d678 : word) 416) with (0x6d818 : word) by (apply bv_eq; vm_compute; reflexivity).
    eapply (gbnez_of BSEGS _ _ _ _ _ F_6d704 eq_refl D_6d704). apply bv_eq; vm_compute; reflexivity.
  - replace (at_ (0x6d678 : word) 464) with (0x6d848 : word) by (apply bv_eq; vm_compute; reflexivity).
    replace (at_ (0x6d678 : word) 144) with (0x6d708 : word) by (apply bv_eq; vm_compute; reflexivity).
    eapply (gbeqz_of BSEGS _ _ _ _ _ F_6d848 eq_refl D_6d848). apply bv_eq; vm_compute; reflexivity.
  - imm_norm. split; [vm_compute; reflexivity | lia].
  - apply ret_ok_even. vm_compute. reflexivity.
Qed.



End FPGen1.
End BoRtAMemsetI.
Module BoRtXMemsetI.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtPoisonI.BoRtLeafI OSSVerify.Proofs.glaze.binary_reflection.lib.BoCodeM2 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtMemIsZero OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtM2S OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtXStrlenI.BoRtM2SI OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtMuslMemset OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoison OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtRegion OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtXStrlenI.BoRtRegionI OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtAMemset.AsRtQC OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtAMemset OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtStkLift.AsRtXMemset.
Import OSSVerify.glaze.binary_reflection.images.AsanUbsan.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

#[local] Abbreviation BSEGS := AsanUbsan.M.loaded_segments.

Definition both_xmset_tab : xmset_tab :=
  {| xm_base := 0x6dc28; xm_rip := both_rip_tab; xm_mset := 0xfc38c;
     xm_g_flag := 0x106a80; xm_p_flag := 0x10ee99; xm_c_rms := 0x107e58 |}.

Section FPGen1.
Context {fx : FPState}.

Ltac lit a v := replace (at_ (0x6dc28 : word) a) with v by (apply bv_eq; vm_compute; reflexivity).

Lemma both_xmset_tab_ok : xmset_tab_ok BSEGS both_xmset_tab.
Proof using.
  split; (lazymatch goal with |- ?G => let G' := eval cbn [xm_base xm_rip xm_mset xm_g_flag xm_p_flag xm_c_rms both_xmset_tab rt_base rt_m2s both_rip_tab mt_g_shoff both_m2s_tab_6fac4] in G in change_no_check G' end).
  - (lazymatch goal with |- ?G => let G' := eval unfold xmset_words in G in change_no_check G' end). code_ato_vm.
  - exact both_rip_tab_ok.
  - apply bv_eq; vm_compute; reflexivity.
  - exact both_memset_code.
  - lit 88%Z (0x6dc80 : word). (lazymatch goal with |- ?G => let G' := eval unfold qc1f_words in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [bv_eqb] in G in change_no_check G' end). code_ato_vm.
  - lit 428%Z (0x6ddd4 : word). (lazymatch goal with |- ?G => let G' := eval unfold qc1s_words in G in change_no_check G' end). code_ato_vm.
  - gload_tac F_6dc54 D_6dc54 F_6dc58 D_6dc58.
  - lit 88%Z (0x6dc80 : word). gload_tac F_6dc80 D_6dc80 F_6dc84 D_6dc84.
  - gload_tac F_6dcbc D_6dcbc F_6dcc0 D_6dcc0.
  - lit 144%Z (0x6dcb8 : word). lit 428%Z (0x6ddd4 : word). eapply (gbnez_of BSEGS _ _ _ _ _ F_6dcb8 eq_refl D_6dcb8). apply bv_eq; vm_compute; reflexivity.
  - lit 476%Z (0x6de04 : word). lit 148%Z (0x6dcbc : word). eapply (gbeqz_of BSEGS _ _ _ _ _ F_6de04 eq_refl D_6de04). apply bv_eq; vm_compute; reflexivity.
  - imm_norm. split; [vm_compute; reflexivity | lia].
  - apply ret_ok_even. vm_compute. reflexivity.
Qed.



End FPGen1.
End BoRtXMemsetI.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtMemcpyBase OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtMuslMemcpy.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module BoRtAMemcpyI.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtPoisonI.BoRtLeafI OSSVerify.Proofs.glaze.binary_reflection.lib.BoCodeM2 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtMemIsZero OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtM2S OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtXStrlenI.BoRtM2SI OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtMemcpyBase OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtMuslMemcpy OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoison OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtRegion OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtXStrlenI.BoRtRegionI OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtAMemset.AsRtQC OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtAMemset OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtStkLift.AsRtAMemcpy.
Import OSSVerify.glaze.binary_reflection.images.AsanUbsan.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

#[local] Abbreviation BSEGS := AsanUbsan.M.loaded_segments.

Definition both_amcpy_tab : amcpy_tab :=
  {| ac_base := 0x6d1dc; ac_rip := both_rip_tab; ac_mcp := 0xfbf88;
     ac_g_flag := 0x106a80; ac_p_flag := 0x10ee99; ac_c_rmc := 0x107e50 |}.

Section FPGen1.
Context {fx : FPState}.

Ltac lit a v := replace (at_ (0x6d1dc : word) a) with v by (apply bv_eq; vm_compute; reflexivity).

Lemma both_amcpy_tab_ok : amcpy_tab_ok BSEGS both_amcpy_tab.
Proof using.
  split; (lazymatch goal with |- ?G => let G' := eval cbn [ac_base ac_rip ac_mcp ac_g_flag ac_p_flag ac_c_rmc both_amcpy_tab rt_base rt_m2s both_rip_tab mt_g_shoff both_m2s_tab_6fac4] in G in change_no_check G' end).
  - (lazymatch goal with |- ?G => let G' := eval unfold amcpy_words in G in change_no_check G' end). code_ato_vm.
  - exact both_rip_tab_ok.
  - apply bv_eq; vm_compute; reflexivity.
  - exact both_memcpy_code.
  - lit 112%Z (0x6d24c : word). (lazymatch goal with |- ?G => let G' := eval unfold qc2f_words in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [bv_eqb] in G in change_no_check G' end). code_ato_vm.
  - lit 856%Z (0x6d534 : word). (lazymatch goal with |- ?G => let G' := eval unfold qc2s_words in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [bv_eqb] in G in change_no_check G' end). code_ato_vm.
  - lit 184%Z (0x6d294 : word). (lazymatch goal with |- ?G => let G' := eval unfold qc2f_words in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [bv_eqb] in G in change_no_check G' end). code_ato_vm.
  - lit 1020%Z (0x6d5d8 : word). (lazymatch goal with |- ?G => let G' := eval unfold qc2s_words in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [bv_eqb] in G in change_no_check G' end). code_ato_vm.
  - gload_tac F_6d20c D_6d20c F_6d210 D_6d210.
  - lit 112%Z (0x6d24c : word). gload_tac F_6d24c D_6d24c F_6d250 D_6d250.
  - lit 184%Z (0x6d294 : word). gload_tac F_6d294 D_6d294 F_6d298 D_6d298.
  - gload_tac F_6d2cc D_6d2cc F_6d2d0 D_6d2d0.
  - lit 164%Z (0x6d280 : word). lit 856%Z (0x6d534 : word). eapply (gbnez_of BSEGS _ _ _ _ _ F_6d280 eq_refl D_6d280). apply bv_eq; vm_compute; reflexivity.
  - lit 904%Z (0x6d564 : word). lit 168%Z (0x6d284 : word). eapply (gbeqz_of BSEGS _ _ _ _ _ F_6d564 eq_refl D_6d564). apply bv_eq; vm_compute; reflexivity.
  - lit 236%Z (0x6d2c8 : word). lit 1020%Z (0x6d5d8 : word). eapply (gbnez_of BSEGS _ _ _ _ _ F_6d2c8 eq_refl D_6d2c8). apply bv_eq; vm_compute; reflexivity.
  - lit 1068%Z (0x6d608 : word). lit 240%Z (0x6d2cc : word). eapply (gbeqz_of BSEGS _ _ _ _ _ F_6d608 eq_refl D_6d608). apply bv_eq; vm_compute; reflexivity.
  - imm_norm. split; [vm_compute; reflexivity | lia].
  - apply ret_ok_even. vm_compute. reflexivity.
Qed.



End FPGen1.
End BoRtAMemcpyI.
Module BoRtXMemcpyI.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtPoisonI.BoRtLeafI OSSVerify.Proofs.glaze.binary_reflection.lib.BoCodeM2 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtMemIsZero OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtM2S OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtXStrlenI.BoRtM2SI OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtMemcpyBase OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtMuslMemcpy OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoison OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtRegion OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtXStrlenI.BoRtRegionI OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtAMemset.AsRtQC OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtAMemset OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtStkLift.AsRtXMemcpy.
Import OSSVerify.glaze.binary_reflection.images.AsanUbsan.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

#[local] Abbreviation BSEGS := AsanUbsan.M.loaded_segments.

Definition both_xmcpy_tab : xmcpy_tab :=
  {| xc_base := 0x6e3d8; xc_rip := both_rip_tab; xc_mcp := 0xfbf88;
     xc_g_flag := 0x106a80; xc_p_flag := 0x10ee99; xc_c_rmc := 0x107e50 |}.

Section FPGen1.
Context {fx : FPState}.

Ltac lit a v := replace (at_ (0x6e3d8 : word) a) with v by (apply bv_eq; vm_compute; reflexivity).

Lemma both_xmcpy_tab_ok : xmcpy_tab_ok BSEGS both_xmcpy_tab.
Proof using.
  split; (lazymatch goal with |- ?G => let G' := eval cbn [xc_base xc_rip xc_mcp xc_g_flag xc_p_flag xc_c_rmc both_xmcpy_tab rt_base rt_m2s both_rip_tab mt_g_shoff both_m2s_tab_6fac4] in G in change_no_check G' end).
  - (lazymatch goal with |- ?G => let G' := eval unfold xmcpy_words in G in change_no_check G' end). code_ato_vm.
  - exact both_rip_tab_ok.
  - apply bv_eq; vm_compute; reflexivity.
  - exact both_memcpy_code.
  - lit 116%Z (0x6e44c : word). (lazymatch goal with |- ?G => let G' := eval unfold qc2f_words in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [bv_eqb] in G in change_no_check G' end). code_ato_vm.
  - lit 868%Z (0x6e73c : word). (lazymatch goal with |- ?G => let G' := eval unfold qc2s_words in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [bv_eqb] in G in change_no_check G' end). code_ato_vm.
  - lit 188%Z (0x6e494 : word). (lazymatch goal with |- ?G => let G' := eval unfold qc2f_words in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [bv_eqb] in G in change_no_check G' end). code_ato_vm.
  - lit 1124%Z (0x6e83c : word). (lazymatch goal with |- ?G => let G' := eval unfold qc2s_words in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [bv_eqb] in G in change_no_check G' end). code_ato_vm.
  - gload_tac F_6e40c D_6e40c F_6e410 D_6e410.
  - lit 116%Z (0x6e44c : word). gload_tac F_6e44c D_6e44c F_6e450 D_6e450.
  - lit 188%Z (0x6e494 : word). gload_tac F_6e494 D_6e494 F_6e498 D_6e498.
  - gload_tac F_6e4cc D_6e4cc F_6e4d0 D_6e4d0.
  - lit 168%Z (0x6e480 : word). lit 868%Z (0x6e73c : word). eapply (gbnez_of BSEGS _ _ _ _ _ F_6e480 eq_refl D_6e480). apply bv_eq; vm_compute; reflexivity.
  - lit 916%Z (0x6e76c : word). lit 172%Z (0x6e484 : word). eapply (gbeqz_of BSEGS _ _ _ _ _ F_6e76c eq_refl D_6e76c). apply bv_eq; vm_compute; reflexivity.
  - lit 240%Z (0x6e4c8 : word). lit 1124%Z (0x6e83c : word). eapply (gbnez_of BSEGS _ _ _ _ _ F_6e4c8 eq_refl D_6e4c8). apply bv_eq; vm_compute; reflexivity.
  - lit 1172%Z (0x6e86c : word). lit 244%Z (0x6e4cc : word). eapply (gbeqz_of BSEGS _ _ _ _ _ F_6e86c eq_refl D_6e86c). apply bv_eq; vm_compute; reflexivity.
  - imm_norm. split; [vm_compute; reflexivity | lia].
  - apply ret_ok_even. vm_compute. reflexivity.
Qed.



End FPGen1.
End BoRtXMemcpyI.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtIMemmove.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module BoRtAMemmoveI.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtPoisonI.BoRtLeafI OSSVerify.Proofs.glaze.binary_reflection.lib.BoCodeM2 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtMemIsZero OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtM2S OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtXStrlenI.BoRtM2SI OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtIMemmove OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoison OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtRegion OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtXStrlenI.BoRtRegionI OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtAMemset.AsRtQC OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtAMemset OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtAMemmove.
Import OSSVerify.glaze.binary_reflection.images.AsanUbsan.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

#[local] Abbreviation BSEGS := AsanUbsan.M.loaded_segments.

Definition both_ammove_tab : ammove_tab :=
  {| mm_base := 0x6d8b8; mm_rip := both_rip_tab; mm_imm := 0x80950; mm_g_flag := 0x106a80; mm_p_flag := 0x10ee99 |}.

Section FPGen1.
Context {fx : FPState}.

Ltac lit a v := replace (at_ (0x6d8b8 : word) a) with v by (apply bv_eq; vm_compute; reflexivity).

Lemma both_ammove_tab_ok : ammove_tab_ok BSEGS both_ammove_tab.
Proof using.
  split; (lazymatch goal with |- ?G => let G' := eval cbn [mm_base mm_rip mm_imm mm_g_flag mm_p_flag both_ammove_tab rt_base rt_m2s both_rip_tab mt_g_shoff both_m2s_tab_6fac4] in G in change_no_check G' end).
  - (lazymatch goal with |- ?G => let G' := eval unfold ammove_words in G in change_no_check G' end). code_ato_vm.
  - exact both_rip_tab_ok.
  - apply bv_eq; vm_compute; reflexivity.
  - exact both_imemmove_code.
  - apply bv_eq; vm_compute; reflexivity.
  - lit 88%Z (0x6d910 : word). (lazymatch goal with |- ?G => let G' := eval unfold qc1f_words in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [bv_eqb] in G in change_no_check G' end). code_ato_vm.
  - lit 556%Z (0x6dae4 : word). (lazymatch goal with |- ?G => let G' := eval unfold qc1s_words in G in change_no_check G' end). code_ato_vm.
  - lit 164%Z (0x6d95c : word). (lazymatch goal with |- ?G => let G' := eval unfold qc1f_words in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [bv_eqb] in G in change_no_check G' end). code_ato_vm.
  - lit 720%Z (0x6db88 : word). (lazymatch goal with |- ?G => let G' := eval unfold qc1s_words in G in change_no_check G' end). code_ato_vm.
  - gload_tac F_6d8e4 D_6d8e4 F_6d8e8 D_6d8e8.
  - lit 88%Z (0x6d910 : word). gload_tac F_6d910 D_6d910 F_6d914 D_6d914.
  - lit 164%Z (0x6d95c : word). gload_tac F_6d95c D_6d95c F_6d960 D_6d960.
  - lit 144%Z (0x6d948 : word). lit 556%Z (0x6dae4 : word). eapply (gbnez_of BSEGS _ _ _ _ _ F_6d948 eq_refl D_6d948). apply bv_eq; vm_compute; reflexivity.
  - lit 604%Z (0x6db14 : word). lit 148%Z (0x6d94c : word). eapply (gbeqz_of BSEGS _ _ _ _ _ F_6db14 eq_refl D_6db14). apply bv_eq; vm_compute; reflexivity.
  - lit 220%Z (0x6d994 : word). lit 720%Z (0x6db88 : word). eapply (gbnez_of BSEGS _ _ _ _ _ F_6d994 eq_refl D_6d994). apply bv_eq; vm_compute; reflexivity.
  - lit 768%Z (0x6dbb8 : word). lit 224%Z (0x6d998 : word). eapply (gbeqz_of BSEGS _ _ _ _ _ F_6dbb8 eq_refl D_6dbb8). apply bv_eq; vm_compute; reflexivity.
  - imm_norm. split; [vm_compute; reflexivity | lia].
Qed.



End FPGen1.
End BoRtAMemmoveI.
Module BoRtXMemmoveI.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtPoisonI.BoRtLeafI OSSVerify.Proofs.glaze.binary_reflection.lib.BoCodeM2 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtMemIsZero OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtM2S OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtXStrlenI.BoRtM2SI OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtIMemmove OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoison OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtRegion OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtXStrlenI.BoRtRegionI OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtAMemset.AsRtQC OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtAMemset OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtAMemmove OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtStkLift.AsRtXMemmove.
Import OSSVerify.glaze.binary_reflection.images.AsanUbsan.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

#[local] Abbreviation BSEGS := AsanUbsan.M.loaded_segments.

Definition both_xmmove_tab : xmmove_tab :=
  {| ym_base := 0x6df18; ym_rip := both_rip_tab; ym_imm := 0x80950; ym_g_flag := 0x106a80; ym_p_flag := 0x10ee99 |}.

Section FPGen1.
Context {fx : FPState}.

Ltac lit a v := replace (at_ (0x6df18 : word) a) with v by (apply bv_eq; vm_compute; reflexivity).

Lemma both_xmmove_tab_ok : xmmove_tab_ok BSEGS both_xmmove_tab.
Proof using.
  split; (lazymatch goal with |- ?G => let G' := eval cbn [ym_base ym_rip ym_imm ym_g_flag ym_p_flag both_xmmove_tab rt_base rt_m2s both_rip_tab mt_g_shoff both_m2s_tab_6fac4] in G in change_no_check G' end).
  - (lazymatch goal with |- ?G => let G' := eval unfold xmmove_words in G in change_no_check G' end). code_ato_vm.
  - exact both_rip_tab_ok.
  - apply bv_eq; vm_compute; reflexivity.
  - exact both_imemmove_code.
  - apply bv_eq; vm_compute; reflexivity.
  - lit 92%Z (0x6df74 : word). (lazymatch goal with |- ?G => let G' := eval unfold qc1f_words in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [bv_eqb] in G in change_no_check G' end). code_ato_vm.
  - lit 564%Z (0x6e14c : word). (lazymatch goal with |- ?G => let G' := eval unfold qc1s_words in G in change_no_check G' end). code_ato_vm.
  - lit 168%Z (0x6dfc0 : word). (lazymatch goal with |- ?G => let G' := eval unfold qc1f_words in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [bv_eqb] in G in change_no_check G' end). code_ato_vm.
  - lit 820%Z (0x6e24c : word). (lazymatch goal with |- ?G => let G' := eval unfold qc1s_words in G in change_no_check G' end). code_ato_vm.
  - gload_tac F_6df48 D_6df48 F_6df4c D_6df4c.
  - lit 92%Z (0x6df74 : word). gload_tac F_6df74 D_6df74 F_6df78 D_6df78.
  - lit 168%Z (0x6dfc0 : word). gload_tac F_6dfc0 D_6dfc0 F_6dfc4 D_6dfc4.
  - lit 148%Z (0x6dfac : word). lit 564%Z (0x6e14c : word). eapply (gbnez_of BSEGS _ _ _ _ _ F_6dfac eq_refl D_6dfac). apply bv_eq; vm_compute; reflexivity.
  - lit 612%Z (0x6e17c : word). lit 152%Z (0x6dfb0 : word). eapply (gbeqz_of BSEGS _ _ _ _ _ F_6e17c eq_refl D_6e17c). apply bv_eq; vm_compute; reflexivity.
  - lit 224%Z (0x6dff8 : word). lit 820%Z (0x6e24c : word). eapply (gbnez_of BSEGS _ _ _ _ _ F_6dff8 eq_refl D_6dff8). apply bv_eq; vm_compute; reflexivity.
  - lit 868%Z (0x6e27c : word). lit 228%Z (0x6dffc : word). eapply (gbeqz_of BSEGS _ _ _ _ _ F_6e27c eq_refl D_6e27c). apply bv_eq; vm_compute; reflexivity.
  - imm_norm. split; [vm_compute; reflexivity | lia].
Qed.



End FPGen1.
End BoRtXMemmoveI.
Module BoIcptMemsetI.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsK OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsRtK OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib AsRtImg OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtM2S OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtXStrlenI.AsRtM2SI OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtRegion OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtXStrlenI.AsRtRegionI OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtAMemset.AsRtQC OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtAMemset OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtStkLift.AsRtAMemsetI OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtPoisonI.BoRtLeafI OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtXStrlenI.BoRtM2SI OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtXStrlenI.BoRtRegionI BoRtAMemsetI OSSVerify.Proofs.glaze.binary_reflection.lib.AsIcptSetSh.AsIcptLift OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtStkLift.AsIcptMemset.
Import OSSVerify.glaze.binary_reflection.images.AsanUbsan.
Import ListNotations.
Open Scope Z_scope.
#[local] Unset Lia Cache. #[local] Unset Nia Cache. #[local] Unset Nra Cache.

Section INST.
  Context {RC : run_ceil}.
  Variable FXOK : FPState -> Prop.
  Variable AAINVH : option Z -> list (Z * Z) -> list (Z * Z) -> Z -> Z -> Z -> mem -> Model -> Prop.
  Variable fsbase : Z.
  Hypothesis HP : forall h, AAINV_props both_addrs (AAINVH h) fsbase BSEGS.
  Hypothesis FSB0 : 0 <= fsbase.
  Hypothesis CELLS : forall h Lc FF B C K M mdl, AAINVH h Lc FF B C K M mdl ->
    Forall (fun c => cellN BSEGS M (fst (fst c)) (snd (fst c)) (snd c)) (amset_cells both_amset_tab).

  (* [comment removed for export] *)
  Lemma amset_cells_B : amset_cells both_amset_tab = ltac:(let x := eval cbv in (amset_cells both_amset_tab) in exact x).
  Proof using. reflexivity. Qed.

  Theorem C_asan_memset_B : MEMSET_AT BSEGS FXOK both_addrs AAINVH (ia_asan_memset both_addrs).
  Proof using CELLS FSB0 HP fsbase.
    apply (C_asan_memset BSEGS FXOK both_addrs AAINVH fsbase HP both_segs_hull both_segs_wx
             both_img_hi_AS_LO both_img_lo_nonneg FSB0 both_amset_tab (fun fx => @both_amset_tab_ok fx)
             ltac:(apply bv_eq; vm_compute; reflexivity) CELLS).
    rewrite amset_cells_B. repeat apply Forall_cons; try apply Forall_nil; cbn -[Z.le Z.add Z.lt]; lia.
  Qed.
End INST.
End BoIcptMemsetI.
Module BoIcptXMemsetI.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsK OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsRtK OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib AsRtImg OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtM2S OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtXStrlenI.AsRtM2SI OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtRegion OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtXStrlenI.AsRtRegionI OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtAMemset.AsRtQC OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtAMemset OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtStkLift.AsRtXMemset OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtStkLift.AsRtXMemsetI OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtPoisonI.BoRtLeafI OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtXStrlenI.BoRtM2SI OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtXStrlenI.BoRtRegionI BoRtXMemsetI OSSVerify.Proofs.glaze.binary_reflection.lib.AsIcptSetSh.AsIcptLift OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtStkLift.AsIcptXMemset.
Import OSSVerify.glaze.binary_reflection.images.AsanUbsan.
Import ListNotations.
Open Scope Z_scope.
#[local] Unset Lia Cache. #[local] Unset Nia Cache. #[local] Unset Nra Cache.

Section INST.
  Context {RC : run_ceil}.
  Variable FXOK : FPState -> Prop.
  Variable AAINVH : option Z -> list (Z * Z) -> list (Z * Z) -> Z -> Z -> Z -> mem -> Model -> Prop.
  Variable fsbase : Z.
  Hypothesis HP : forall h, AAINV_props both_addrs (AAINVH h) fsbase BSEGS.
  Hypothesis FSB0 : 0 <= fsbase.
  Hypothesis CELLS : forall h Lc FF B C K M mdl, AAINVH h Lc FF B C K M mdl ->
    Forall (fun c => cellN BSEGS M (fst (fst c)) (snd (fst c)) (snd c)) (xmset_cells both_xmset_tab).

  (* [comment removed for export] *)
  Lemma xmset_cells_B : xmset_cells both_xmset_tab = ltac:(let x := eval cbv in (xmset_cells both_xmset_tab) in exact x).
  Proof using. reflexivity. Qed.

  Theorem C_memset_icpt_B : MEMSET_AT BSEGS FXOK both_addrs AAINVH (ia_memset_icpt both_addrs).
  Proof using CELLS FSB0 HP fsbase.
    apply (C_memset_icpt BSEGS FXOK both_addrs AAINVH fsbase HP both_segs_hull both_segs_wx
             both_img_hi_AS_LO both_img_lo_nonneg FSB0 both_xmset_tab (fun fx => @both_xmset_tab_ok fx)
             ltac:(apply bv_eq; vm_compute; reflexivity) CELLS).
    rewrite xmset_cells_B. repeat apply Forall_cons; try apply Forall_nil; cbn -[Z.le Z.add Z.lt]; lia.
  Qed.
End INST.
End BoIcptXMemsetI.
Module BoIcptMemcpyI.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsK OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsRtK OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib AsRtImg OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtM2S OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtXStrlenI.AsRtM2SI OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtRegion OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtXStrlenI.AsRtRegionI OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtAMemset.AsRtQC OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtAMemset OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtStkLift.AsRtAMemcpy OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtStkLift.AsRtAMemcpyI OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtPoisonI.BoRtLeafI OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtXStrlenI.BoRtM2SI OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtXStrlenI.BoRtRegionI BoRtAMemcpyI OSSVerify.Proofs.glaze.binary_reflection.lib.AsIcptSetSh.AsIcptLift OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtStkLift.AsIcptMemcpy.
Import OSSVerify.glaze.binary_reflection.images.AsanUbsan.
Import ListNotations.
Open Scope Z_scope.
#[local] Unset Lia Cache. #[local] Unset Nia Cache. #[local] Unset Nra Cache.

Section INST.
  Context {RC : run_ceil}.
  Variable FXOK : FPState -> Prop.
  Variable AAINVH : option Z -> list (Z * Z) -> list (Z * Z) -> Z -> Z -> Z -> mem -> Model -> Prop.
  Variable fsbase : Z.
  Hypothesis HP : forall h, AAINV_props both_addrs (AAINVH h) fsbase BSEGS.
  Hypothesis FSB0 : 0 <= fsbase.
  Hypothesis CELLS : forall h Lc FF B C K M mdl, AAINVH h Lc FF B C K M mdl ->
    Forall (fun c => cellN BSEGS M (fst (fst c)) (snd (fst c)) (snd c)) (amcpy_cells both_amcpy_tab).

  (* [comment removed for export] *)
  Lemma amcpy_cells_B : amcpy_cells both_amcpy_tab = ltac:(let x := eval cbv in (amcpy_cells both_amcpy_tab) in exact x).
  Proof using. reflexivity. Qed.

  Theorem C_asan_memcpy_B : MEMCPY_AT BSEGS FXOK both_addrs AAINVH (ia_asan_memcpy both_addrs).
  Proof using CELLS FSB0 HP fsbase.
    apply (C_asan_memcpy BSEGS FXOK both_addrs AAINVH fsbase HP both_segs_hull both_segs_wx
             both_img_hi_AS_LO both_img_lo_nonneg FSB0 both_amcpy_tab (fun fx => @both_amcpy_tab_ok fx)
             ltac:(apply bv_eq; vm_compute; reflexivity) CELLS).
    rewrite amcpy_cells_B. repeat apply Forall_cons; try apply Forall_nil; cbn -[Z.le Z.add Z.lt]; lia.
  Qed.
End INST.
End BoIcptMemcpyI.
Module BoIcptXMemcpyI.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsK OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsRtK OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib AsRtImg OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtM2S OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtXStrlenI.AsRtM2SI OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtRegion OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtXStrlenI.AsRtRegionI OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtAMemset.AsRtQC OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtAMemset OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtStkLift.AsRtXMemcpy OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtStkLift.AsRtXMemcpyI OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtPoisonI.BoRtLeafI OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtXStrlenI.BoRtM2SI OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtXStrlenI.BoRtRegionI BoRtXMemcpyI OSSVerify.Proofs.glaze.binary_reflection.lib.AsIcptSetSh.AsIcptLift OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtStkLift.AsIcptXMemcpy.
Import OSSVerify.glaze.binary_reflection.images.AsanUbsan.
Import ListNotations.
Open Scope Z_scope.
#[local] Unset Lia Cache. #[local] Unset Nia Cache. #[local] Unset Nra Cache.

Section INST.
  Context {RC : run_ceil}.
  Variable FXOK : FPState -> Prop.
  Variable AAINVH : option Z -> list (Z * Z) -> list (Z * Z) -> Z -> Z -> Z -> mem -> Model -> Prop.
  Variable fsbase : Z.
  Hypothesis HP : forall h, AAINV_props both_addrs (AAINVH h) fsbase BSEGS.
  Hypothesis FSB0 : 0 <= fsbase.
  Hypothesis CELLS : forall h Lc FF B C K M mdl, AAINVH h Lc FF B C K M mdl ->
    Forall (fun c => cellN BSEGS M (fst (fst c)) (snd (fst c)) (snd c)) (xmcpy_cells both_xmcpy_tab).

  (* [comment removed for export] *)
  Lemma xmcpy_cells_B : xmcpy_cells both_xmcpy_tab = ltac:(let x := eval cbv in (xmcpy_cells both_xmcpy_tab) in exact x).
  Proof using. reflexivity. Qed.

  Theorem C_memcpy_icpt_B : MEMCPY_AT BSEGS FXOK both_addrs AAINVH (ia_memcpy_icpt both_addrs).
  Proof using CELLS FSB0 HP fsbase.
    apply (C_memcpy_icpt BSEGS FXOK both_addrs AAINVH fsbase HP both_segs_hull both_segs_wx
             both_img_hi_AS_LO both_img_lo_nonneg FSB0 both_xmcpy_tab (fun fx => @both_xmcpy_tab_ok fx)
             ltac:(apply bv_eq; vm_compute; reflexivity) CELLS).
    rewrite xmcpy_cells_B. repeat apply Forall_cons; try apply Forall_nil; cbn -[Z.le Z.add Z.lt]; lia.
  Qed.
End INST.
End BoIcptXMemcpyI.
Module BoIcptMemmoveI.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsK OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsRtK OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib AsRtImg OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtM2S OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtXStrlenI.AsRtM2SI OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtRegion OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtXStrlenI.AsRtRegionI OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtAMemset.AsRtQC OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtAMemset OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtAMemmove OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtStkLift.AsRtAMemmoveI OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtPoisonI.BoRtLeafI OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtXStrlenI.BoRtM2SI OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtXStrlenI.BoRtRegionI BoRtAMemmoveI OSSVerify.Proofs.glaze.binary_reflection.lib.AsIcptSetSh.AsIcptLift OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtStkLift.AsIcptMemmove.
Import OSSVerify.glaze.binary_reflection.images.AsanUbsan.
Import ListNotations.
Open Scope Z_scope.
#[local] Unset Lia Cache. #[local] Unset Nia Cache. #[local] Unset Nra Cache.

Section INST.
  Context {RC : run_ceil}.
  Variable FXOK : FPState -> Prop.
  Variable AAINVH : option Z -> list (Z * Z) -> list (Z * Z) -> Z -> Z -> Z -> mem -> Model -> Prop.
  Variable fsbase : Z.
  Hypothesis HP : forall h, AAINV_props both_addrs (AAINVH h) fsbase BSEGS.
  Hypothesis FSB0 : 0 <= fsbase.
  Hypothesis CELLS : forall h Lc FF B C K M mdl, AAINVH h Lc FF B C K M mdl ->
    Forall (fun c => cellN BSEGS M (fst (fst c)) (snd (fst c)) (snd c)) (ammove_cells both_ammove_tab).

  (* [comment removed for export] *)
  Lemma ammove_cells_B : ammove_cells both_ammove_tab = ltac:(let x := eval cbv in (ammove_cells both_ammove_tab) in exact x).
  Proof using. reflexivity. Qed.

  Theorem C_asan_memmove_B : MEMMOVE_AT BSEGS FXOK both_addrs AAINVH (ia_asan_memmove both_addrs).
  Proof using CELLS FSB0 HP fsbase.
    apply (C_asan_memmove BSEGS FXOK both_addrs AAINVH fsbase HP both_segs_hull both_segs_wx
             both_img_hi_AS_LO both_img_lo_nonneg FSB0 both_ammove_tab (fun fx => @both_ammove_tab_ok fx)
             ltac:(apply bv_eq; vm_compute; reflexivity) CELLS).
    rewrite ammove_cells_B. repeat apply Forall_cons; try apply Forall_nil; cbn -[Z.le Z.add Z.lt]; lia.
  Qed.
End INST.
End BoIcptMemmoveI.
Module BoIcptXMemmoveI.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsK OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsRtK OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib AsRtImg OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtM2S OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtXStrlenI.AsRtM2SI OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtRegion OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtXStrlenI.AsRtRegionI OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtAMemset.AsRtQC OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtAMemset OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtAMemmove OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtStkLift.AsRtXMemmove OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtStkLift.AsRtXMemmoveI OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtPoisonI.BoRtLeafI OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtXStrlenI.BoRtM2SI OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtXStrlenI.BoRtRegionI BoRtXMemmoveI OSSVerify.Proofs.glaze.binary_reflection.lib.AsIcptSetSh.AsIcptLift OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtStkLift.AsIcptXMemmove.
Import OSSVerify.glaze.binary_reflection.images.AsanUbsan.
Import ListNotations.
Open Scope Z_scope.
#[local] Unset Lia Cache. #[local] Unset Nia Cache. #[local] Unset Nra Cache.

Section INST.
  Context {RC : run_ceil}.
  Variable FXOK : FPState -> Prop.
  Variable AAINVH : option Z -> list (Z * Z) -> list (Z * Z) -> Z -> Z -> Z -> mem -> Model -> Prop.
  Variable fsbase : Z.
  Hypothesis HP : forall h, AAINV_props both_addrs (AAINVH h) fsbase BSEGS.
  Hypothesis FSB0 : 0 <= fsbase.
  Hypothesis CELLS : forall h Lc FF B C K M mdl, AAINVH h Lc FF B C K M mdl ->
    Forall (fun c => cellN BSEGS M (fst (fst c)) (snd (fst c)) (snd c)) (xmmove_cells both_xmmove_tab).

  (* [comment removed for export] *)
  Lemma xmmove_cells_B : xmmove_cells both_xmmove_tab = ltac:(let x := eval cbv in (xmmove_cells both_xmmove_tab) in exact x).
  Proof using. reflexivity. Qed.

  Theorem C_memmove_icpt_B : MEMMOVE_AT BSEGS FXOK both_addrs AAINVH (ia_memmove_icpt both_addrs).
  Proof using CELLS FSB0 HP fsbase.
    apply (C_memmove_icpt BSEGS FXOK both_addrs AAINVH fsbase HP both_segs_hull both_segs_wx
             both_img_hi_AS_LO both_img_lo_nonneg FSB0 both_xmmove_tab (fun fx => @both_xmmove_tab_ok fx)
             ltac:(apply bv_eq; vm_compute; reflexivity) CELLS).
    rewrite xmmove_cells_B. repeat apply Forall_cons; try apply Forall_nil; cbn -[Z.le Z.add Z.lt]; lia.
  Qed.
End INST.
End BoIcptXMemmoveI.
Module BoIcptStrlenI.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsK OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsRtK OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib AsRtImg OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtM2S OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtXStrlenI.AsRtM2SI OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtRegion OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtXStrlenI.AsRtRegionI OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtAMemset.AsRtQC OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtAMemset OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtMemchr OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtStrlen OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtXStrlenI.AsRtStrlenI OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtTlsGA.AsRtXStrlen OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtXStrlenI OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtPoisonI.BoRtLeafI OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtXStrlenI.BoRtM2SI OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtXStrlenI.BoRtRegionI OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtXStrlenI.BoRtStrlenI OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtXStrlenI OSSVerify.Proofs.glaze.binary_reflection.lib.AsIcptSetSh.AsIcptLift OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtStkLift.AsIcptStrlen.
Import OSSVerify.glaze.binary_reflection.images.AsanUbsan.
Import ListNotations.
Open Scope Z_scope.
#[local] Unset Lia Cache. #[local] Unset Nia Cache. #[local] Unset Nra Cache.

Section INST.
  Context {RC : run_ceil}.
  Variable FXOK : FPState -> Prop.
  Variable AAINVH : option Z -> list (Z * Z) -> list (Z * Z) -> Z -> Z -> Z -> mem -> Model -> Prop.
  Variable fsbase : Z.
  Hypothesis HP : forall h, AAINV_props both_addrs (AAINVH h) fsbase BSEGS.
  Hypothesis FSB0 : 0 <= fsbase.
  Hypothesis CELLS : forall h Lc FF B C K M mdl, AAINVH h Lc FF B C K M mdl ->
    Forall (fun c => cellN BSEGS M (fst (fst c)) (snd (fst c)) (snd c)) (xstrlen_cells both_xstrlen_tab).

  (* [comment removed for export] *)
  Lemma xstrlen_cells_B : xstrlen_cells both_xstrlen_tab = ltac:(let x := eval cbv in (xstrlen_cells both_xstrlen_tab) in exact x).
  Proof using. reflexivity. Qed.

  Theorem C_strlen_icpt_B : STRLEN_AT BSEGS FXOK both_addrs AAINVH (ia_strlen_icpt both_addrs).
  Proof using CELLS FSB0 HP fsbase.
    apply (C_strlen_icpt BSEGS FXOK both_addrs AAINVH fsbase HP both_segs_hull both_segs_wx
             both_img_hi_AS_LO both_img_lo_nonneg FSB0 both_xstrlen_tab (fun fx => @both_xstrlen_tab_ok fx)
             ltac:(apply bv_eq; vm_compute; reflexivity) CELLS). 2: (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); (lazymatch goal with |- ?G => let G' := eval unfold AS_LO in G in change_no_check G' end); lia.
    rewrite xstrlen_cells_B. repeat apply Forall_cons; try apply Forall_nil; cbn -[Z.le Z.add Z.lt]; lia.
  Qed.
End INST.
End BoIcptStrlenI.
Module BoRtAnnI.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtPoisonI.Bo_code_7006c_706b8 Bo_code_70fc4_71054 Bo_code_71054_71254 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtMemIsZero OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtMuslMemset OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtM2S OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtXStrlenI.AsRtM2SI OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtXStrlenI.BoRtM2SI OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoison OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtPoisonI OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtAnn.
Import OSSVerify.glaze.binary_reflection.images.AsanUbsan.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Abbreviation BSEGS := AsanUbsan.M.loaded_segments.

Definition both_ann_base : word := 0x70fc4.
Definition both_ann_g_flags : Z := 0x105f10.  Definition both_ann_p_flags : Z := 0x10b9b8.
Definition both_ann_g_verb : Z := 0x105f68.   Definition both_ann_p_verb : Z := 0x19dc58.
Definition both_ann_g_shoff : Z := 0x105f18.  Definition both_ann_p_shoff : Z := 0x10e1b8.

Section FPGen1.
Context {fx : FPState}.

Lemma both_anncc_code : code_ato BSEGS both_ann_base 0 anncc_words.
Proof using. (lazymatch goal with |- ?G => let G' := eval unfold anncc_words, both_ann_base in G in change_no_check G' end). code_ato_vm. Qed.
Lemma both_ann_ptb : pt_base both_poison_tab = at_ both_ann_base (-3908).
Proof using. apply bv_eq. vm_compute. reflexivity. Qed.
Lemma both_ann_mtb : mt_base both_m2s_tab_6fac4 = at_ both_ann_base (-2632).
Proof using. apply bv_eq. vm_compute. reflexivity. Qed.
Lemma both_ann_G44 : gload BSEGS both_ann_base 44 11 both_ann_g_flags.
Proof using. (lazymatch goal with |- ?G => let G' := eval unfold both_ann_base, both_ann_g_flags in G in change_no_check G' end). gload_tac F_70ff0 D_70ff0 F_70ff4 D_70ff4. Qed.
Lemma both_ann_G72 : gload BSEGS both_ann_base 72 10 both_ann_g_verb.
Proof using. (lazymatch goal with |- ?G => let G' := eval unfold both_ann_base, both_ann_g_verb in G in change_no_check G' end). gload_tac F_7100c D_7100c F_71010 D_71010. Qed.
Lemma both_ann_G404 : gload BSEGS both_ann_base 404 11 both_ann_g_shoff.
Proof using. (lazymatch goal with |- ?G => let G' := eval unfold both_ann_base, both_ann_g_shoff in G in change_no_check G' end). gload_tac F_71158 D_71158 F_7115c D_7115c. Qed.
Lemma both_ann_hbase : (bv_unsigned both_ann_base mod 2 = 0)%Z /\ (4096 <= bv_unsigned both_ann_base)%Z
                       /\ (bv_unsigned both_ann_base + 4096 < 2 ^ 64)%Z.
Proof using. (lazymatch goal with |- ?G => let G' := eval unfold both_ann_base in G in change_no_check G' end). split; [vm_compute; reflexivity | split; [vm_compute; discriminate | vm_compute; reflexivity]]. Qed.

End FPGen1.
End BoRtAnnI.
Module BoIcptAnnI.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsK OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsRtK OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib AsRtImg OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtM2S OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtXStrlenI.AsRtM2SI OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtXStrlenI.BoRtM2SI OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoison OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtPoisonI OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtAnn BoRtAnnI OSSVerify.Proofs.glaze.binary_reflection.lib.AsIcptSetSh.AsIcptLift OSSVerify.Proofs.glaze.binary_reflection.lib.AsIcptAnn.AsIcptAnnM OSSVerify.Proofs.glaze.binary_reflection.lib.AsIcptAnn.
Import OSSVerify.glaze.binary_reflection.images.AsanUbsan.
Import ListNotations.
Open Scope Z_scope.
#[local] Unset Lia Cache. #[local] Unset Nia Cache. #[local] Unset Nra Cache.

Section INST.
  Context {RC : run_ceil}.
  Variable FXOK : FPState -> Prop.
  Variable AAINVH : option Z -> list (Z * Z) -> list (Z * Z) -> Z -> Z -> Z -> mem -> Model -> Prop.
  Variable fsbase : Z.
  Hypothesis HP : forall h, AAINV_props both_addrs (AAINVH h) fsbase BSEGS.
  Hypothesis HNM : forall h Lc FF B C K M mdl b n, AAINVH h Lc FF B C K M mdl -> In (b, n) Lc -> n <= NMAX.
  #[local] Abbreviation CELLS_L := (ann_cellsL both_poison_tab both_m2s_tab_6fac4 both_ann_g_flags both_ann_p_flags
                                       both_ann_g_verb both_ann_p_verb both_ann_g_shoff both_ann_p_shoff).
  Hypothesis CELLS : forall h Lc FF B C K M mdl, AAINVH h Lc FF B C K M mdl ->
    Forall (fun c => cellN BSEGS M (fst (fst c)) (snd (fst c)) (snd c)) CELLS_L.

  (* [comment removed for export] *)
  Lemma ann_cellsL_B : CELLS_L = ltac:(let x := eval cbv in CELLS_L in exact x).
  Proof using. reflexivity. Qed.

  Lemma both_ann_T_entry : both_ann_base = Z_to_bv 64 (as_annot both_addrs).
  Proof using. apply bv_eq. vm_compute. reflexivity. Qed.
  Lemma both_ann_mset_nz : bv_unsigned (pt_mset both_poison_tab) <> 0.
  Proof using. cbv. discriminate. Qed.
  Lemma both_ann_mset_ret : ret_ok (pt_mset both_poison_tab).
  Proof using. apply ret_ok_even. vm_compute. reflexivity. Qed.

  Theorem C_annotate_B : ANNOTATE_AT BSEGS FXOK both_addrs AAINVH (as_annot both_addrs).
  Proof using CELLS HNM HP fsbase.
    apply (C_annotate BSEGS FXOK both_addrs AAINVH fsbase HP both_segs_hull both_segs_wx both_img_hi_AS_LO both_img_lo_nonneg HNM
             both_ann_base both_poison_tab both_m2s_tab_6fac4
             both_ann_g_flags both_ann_p_flags both_ann_g_verb both_ann_p_verb both_ann_g_shoff both_ann_p_shoff
             both_anncc_code (fun fx => @both_poison_tab_ok fx) both_ann_ptb (fun fx => @both_m2s_tab_ok_6fac4 fx) both_ann_mtb
             (fun fx => @both_ann_G44 fx) (fun fx => @both_ann_G72 fx) (fun fx => @both_ann_G404 fx) both_ann_hbase
             both_ann_mset_nz both_ann_mset_ret both_ann_T_entry CELLS).
    - rewrite ann_cellsL_B. repeat apply Forall_cons; try apply Forall_nil; cbn -[Z.le Z.add Z.lt]; lia.
    - split; cbv; discriminate.
  Qed.
End INST.
End BoIcptAnnI.
Module BoIcptInstBtS.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsK OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtStkLift.AsAinvFacts3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsRtK OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib AsRtImg OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOps3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvHole3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtAMemset OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtStkLift.AsRtAMemsetI OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtStkLift.AsRtXMemset OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtStkLift.AsRtXMemsetI OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtStkLift.AsRtAMemcpy OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtStkLift.AsRtAMemcpyI OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtStkLift.AsRtXMemcpy OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtStkLift.AsRtXMemcpyI OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtAMemmove OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtStkLift.AsRtAMemmoveI OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtStkLift.AsRtXMemmove OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtStkLift.AsRtXMemmoveI OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtTlsGA.AsRtXStrlen OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtXStrlenI OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtPoisonI.BoRtLeafI OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtXStrlenI.BoRtM2SI OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtXStrlenI.BoRtRegionI BoRtAMemsetI BoRtXMemsetI BoRtAMemcpyI BoRtXMemcpyI BoRtAMemmoveI BoRtXMemmoveI OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtXStrlenI.BoRtStrlenI OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtXStrlenI OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtStkLift.AsIcptMemset BoIcptMemsetI OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtStkLift.AsIcptXMemset BoIcptXMemsetI OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtStkLift.AsIcptMemcpy BoIcptMemcpyI OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtStkLift.AsIcptXMemcpy BoIcptXMemcpyI OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtStkLift.AsIcptMemmove BoIcptMemmoveI OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtStkLift.AsIcptXMemmove BoIcptXMemmoveI OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtStkLift.AsIcptStrlen BoIcptStrlenI OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtM2S OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtXStrlenI.AsRtM2SI OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtXStrlenI.BoRtM2SI OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoison OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoisonI OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtPoisonI OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtAnn BoRtAnnI OSSVerify.Proofs.glaze.binary_reflection.lib.AsIcptAnn.AsIcptAnnM OSSVerify.Proofs.glaze.binary_reflection.lib.AsIcptAnn BoIcptAnnI.
Import OSSVerify.glaze.binary_reflection.images.AsanUbsan.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsIcptSetSh.AsIcptLift OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d.AsAinvFreeS OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtStkLift.AsRtFakeRel.
Import ListNotations.
Open Scope Z_scope.
#[local] Unset Lia Cache. #[local] Unset Nia Cache. #[local] Unset Nra Cache.

Section BT.
  Context {RC : run_ceil}.
  Variable FXOK : FPState -> Prop.
  Variable bt : as_boot.
  Hypothesis BT_IA : bt_ia bt = both_addrs.
  Hypothesis BT_SEGS : bt_segs bt = BSEGS.
  Hypothesis BT_FS : 0 <= bt_fs bt.

  #[local] Notation AAINVH := (AAINV_HS bt).

  Lemma HP_bt : forall h, AAINV_props both_addrs (AAINVH h) (bt_fs bt) BSEGS.
  Proof using BT_SEGS BT_IA. intros h. rewrite <- BT_IA, <- BT_SEGS. exact (AAINV_props_all bt (holes_lsopt h)). Qed.

  (* [comment removed for export] *)
  Lemma CELLS_bt : forall cs, Forall (fun c => In c (bt_consts bt)) cs ->
    forall h Lc FF B C K M mdl, AAINVH h Lc FF B C K M mdl ->
    Forall (fun c => cellN BSEGS M (fst (fst c)) (snd (fst c)) (snd c)) cs.
  Proof using BT_SEGS.
    intros cs Hcs h Lc FF B C K M mdl (st & W & R & _).
    pose proof (read_consts bt st Lc FF M mdl R) as CH. unfold cells_hold, cellZ in CH. rewrite BT_SEGS in CH.
    rewrite Forall_forall in Hcs, CH |- *. intros c Hc. exact (CH c (Hcs c Hc)).
  Qed.

  Hypothesis K_memset_icpt : Forall (fun c => In c (bt_consts bt)) (xmset_cells both_xmset_tab).
  Hypothesis K_asan_memset : Forall (fun c => In c (bt_consts bt)) (amset_cells both_amset_tab).
  Hypothesis K_memcpy_icpt : Forall (fun c => In c (bt_consts bt)) (xmcpy_cells both_xmcpy_tab).
  Hypothesis K_asan_memcpy : Forall (fun c => In c (bt_consts bt)) (amcpy_cells both_amcpy_tab).
  Hypothesis K_memmove_icpt : Forall (fun c => In c (bt_consts bt)) (xmmove_cells both_xmmove_tab).
  Hypothesis K_asan_memmove : Forall (fun c => In c (bt_consts bt)) (ammove_cells both_ammove_tab).
  Hypothesis K_strlen_icpt : Forall (fun c => In c (bt_consts bt)) (xstrlen_cells both_xstrlen_tab).

  Theorem C_memset_icpt_bts_B : MEMSET_AT BSEGS FXOK both_addrs AAINVH (ia_memset_icpt both_addrs).
  Proof using K_memset_icpt BT_FS BT_SEGS BT_IA. exact (C_memset_icpt_B FXOK AAINVH (bt_fs bt) HP_bt BT_FS (CELLS_bt _ K_memset_icpt)). Qed.
  Theorem C_asan_memset_bts_B : MEMSET_AT BSEGS FXOK both_addrs AAINVH (ia_asan_memset both_addrs).
  Proof using K_asan_memset BT_FS BT_SEGS BT_IA. exact (C_asan_memset_B FXOK AAINVH (bt_fs bt) HP_bt BT_FS (CELLS_bt _ K_asan_memset)). Qed.
  Theorem C_memcpy_icpt_bts_B : MEMCPY_AT BSEGS FXOK both_addrs AAINVH (ia_memcpy_icpt both_addrs).
  Proof using K_memcpy_icpt BT_FS BT_SEGS BT_IA. exact (C_memcpy_icpt_B FXOK AAINVH (bt_fs bt) HP_bt BT_FS (CELLS_bt _ K_memcpy_icpt)). Qed.
  Theorem C_asan_memcpy_bts_B : MEMCPY_AT BSEGS FXOK both_addrs AAINVH (ia_asan_memcpy both_addrs).
  Proof using K_asan_memcpy BT_FS BT_SEGS BT_IA. exact (C_asan_memcpy_B FXOK AAINVH (bt_fs bt) HP_bt BT_FS (CELLS_bt _ K_asan_memcpy)). Qed.
  Theorem C_memmove_icpt_bts_B : MEMMOVE_AT BSEGS FXOK both_addrs AAINVH (ia_memmove_icpt both_addrs).
  Proof using K_memmove_icpt BT_FS BT_SEGS BT_IA. exact (C_memmove_icpt_B FXOK AAINVH (bt_fs bt) HP_bt BT_FS (CELLS_bt _ K_memmove_icpt)). Qed.
  Theorem C_asan_memmove_bts_B : MEMMOVE_AT BSEGS FXOK both_addrs AAINVH (ia_asan_memmove both_addrs).
  Proof using K_asan_memmove BT_FS BT_SEGS BT_IA. exact (C_asan_memmove_B FXOK AAINVH (bt_fs bt) HP_bt BT_FS (CELLS_bt _ K_asan_memmove)). Qed.
  Theorem C_strlen_icpt_bts_B : STRLEN_AT BSEGS FXOK both_addrs AAINVH (ia_strlen_icpt both_addrs).
  Proof using K_strlen_icpt BT_FS BT_SEGS BT_IA. exact (C_strlen_icpt_B FXOK AAINVH (bt_fs bt) HP_bt BT_FS (CELLS_bt _ K_strlen_icpt)). Qed.
  (* [comment removed for export] *)
  Lemma HNM_bts : forall h Lc FF B C K M mdl b n, AAINVH h Lc FF B C K M mdl -> In (b, n) Lc -> n <= NMAX.
  Proof using.
    intros h Lc FF B C K M mdl b n (st & W & _ & _) Hin.
    destruct W as (_ & _ & _ & _ & WL & _). destruct WL as (WL1 & _). destruct (WL1 b n Hin) as (X & _). lia.
  Qed.
  Hypothesis K_annotate : Forall (fun c => In c (bt_consts bt))
     (ann_cellsL both_poison_tab both_m2s_tab_6fac4 both_ann_g_flags both_ann_p_flags both_ann_g_verb both_ann_p_verb both_ann_g_shoff both_ann_p_shoff).
  Theorem C_annotate_bts_B : ANNOTATE_AT BSEGS FXOK both_addrs AAINVH (as_annot both_addrs).
  Proof using K_annotate BT_SEGS BT_IA. exact (C_annotate_B FXOK AAINVH (bt_fs bt) HP_bt HNM_bts (CELLS_bt _ K_annotate)). Qed.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma FS_NOLAZY_bt : forall st Lc FF M mdl z,
    WF bt st Lc FF -> Rep bt st Lc FF M mdl -> bt_fs bt + 0x1000 <= z < bt_fs bt + 0x9000 -> lzb mdl z = false.
  Proof using. exact (AsRtStkLift.AsAinvFacts3b.FS_NOLAZY bt). Qed.
  Lemma FS_PRIV_bt : forall st Lc FF z,
    WF bt st Lc FF -> bt_fs bt + 0x1000 <= z < bt_fs bt + 0x9000 -> rt_priv both_addrs Lc FF z.
  Proof using BT_IA. intros st Lc FF z W Hz. rewrite <- BT_IA. exact (AsRtStkLift.AsAinvFacts3b.FS_PRIV bt st Lc FF z W Hz). Qed.
  Lemma HOFF_bt : forall h Lc FF B C K M mdl AA, AAINVH h Lc FF B C K M mdl -> H_off_segments BSEGS (HL mdl AA).
  Proof using BT_SEGS BT_IA. intros h Lc FF B C K M mdl AA AI. exact (HL_off_segments BSEGS both_addrs (AAINVH h) (bt_fs bt) (HP_bt h) both_segs_hull Lc FF B C K M mdl AA AI). Qed.
  Theorem C_fakerel_bts_B : forall {fx : FPState}, FAKEREL BSEGS FXOK both_addrs AAINVH.
  Proof using BT_SEGS BT_IA.
    intros fx. pose proof (@C_fakerel_P RC FXOK bt (fun h => holes_lsopt h)) as X. rewrite BT_SEGS, BT_IA in X.
    exact (X both_segs_wx HOFF_bt FS_NOLAZY_bt FS_PRIV_bt fx).
  Qed.
End BT.
End BoIcptInstBtS.
Module BoRtTlsGAI.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtTlsGA.AsRtXStrlen OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtXStrlenI OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtTlsGA Bo_code_5cfa4_5cfa8 Bo_code_618d8_61954 Bo_code_78e2c_78e4c Bo_code_714ac_714c4 Bo_code_86540_8675c Bo_code_fcc70_fcc94 Bo_code_fdd24_fdd40.
Import OSSVerify.glaze.binary_reflection.images.AsanUbsan.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Abbreviation BSEGS := AsanUbsan.M.loaded_segments.

Definition both_tlsga_tab : tlsga_tab :=
  {| tg_hb := 0x5cfa4; tg_tga := 0xfcc64; tg_pgs := 0xfdd18;
     tg_c_inited := 0x10ee98; tg_c_rtga := 0x107d78; tg_c_tsd := 0x10da20; tg_g_cf := 0x105f08; tg_p_cf := 0x19fce8;
     tg_g_verb := 0x105f68; tg_p_verb := 0x19dc58; tg_c_tlsd := 0x106cc8 |}.

Section FPGen1.
Context {fx : FPState}.

Lemma both_tlsga_tab_ok : tlsga_tab_ok BSEGS both_tlsga_tab.
Proof using.
  (lazymatch goal with |- ?G => let G' := eval unfold tlsga_tab_ok in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [tg_hb tg_tga tg_pgs tg_c_inited tg_c_rtga tg_c_tsd tg_g_cf tg_p_cf tg_g_verb tg_p_verb tg_c_tlsd both_tlsga_tab] in G in change_no_check G' end).
  repeat match goal with |- _ /\ _ => split end.
  - (lazymatch goal with |- ?G => let G' := eval unfold tgth_words in G in change_no_check G' end). code_ato_vm.
  - (lazymatch goal with |- ?G => let G' := eval unfold tgic_words in G in change_no_check G' end). code_ato_vm.
  - (lazymatch goal with |- ?G => let G' := eval unfold tgct_words in G in change_no_check G' end). code_ato_vm.
  - (lazymatch goal with |- ?G => let G' := eval unfold tgts_words in G in change_no_check G' end). code_ato_vm.
  - (lazymatch goal with |- ?G => let G' := eval unfold tgdt_words in G in change_no_check G' end). code_ato_vm.
  - (lazymatch goal with |- ?G => let G' := eval unfold mtga_words in G in change_no_check G' end). code_ato_vm.
  - (lazymatch goal with |- ?G => let G' := eval unfold mpgs_words in G in change_no_check G' end). code_ato_vm.
  - replace (at_ (0x5cfa4 : word) 104072) with (0x7662c : word) by (apply bv_eq; vm_compute; reflexivity). exact try_asan_init_run.
  - gload_tac F_618f4 D_618f4 F_618f8 D_618f8.
  - gaddr2_tac F_714ac D_714ac F_714b0 D_714b0.
  - gjump_tac F_714c0 D_714c0.
  - gload_tac F_8657c D_8657c F_86580 D_86580.
  - gload_tac F_86590 D_86590 F_86594 D_86594.
  - gauipc_ld_tac F_8659c D_8659c F_865a4 D_865a4.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - apply ret_ok_even. vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - lia.
Qed.
End FPGen1.
End BoRtTlsGAI.
Module BoRtStkMal0I.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtM2S OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtXStrlenI.BoRtM2SI OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtTlsGA BoRtTlsGAI OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtStkMal0 Bo_code_57bdc_58228.
Import OSSVerify.glaze.binary_reflection.images.AsanUbsan.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Abbreviation BSEGS := AsanUbsan.M.loaded_segments.

Definition both_stk0_tab : stk_tab :=
  {| sk_base := 0x57bdc; sk_tg := both_tlsga_tab; sk_mt := both_m2s_tab_57770; sk_arg := 0x106cb8 |}.

Section FPGen1.
Context {fx : FPState}.

Lemma both_stk0_tab_ok : stk0_tab_ok BSEGS both_stk0_tab.
Proof using.
  (lazymatch goal with |- ?G => let G' := eval unfold stk0_tab_ok in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [sk_base sk_tg sk_mt sk_arg both_stk0_tab] in G in change_no_check G' end).
  repeat match goal with |- _ /\ _ => split end.
  - (lazymatch goal with |- ?G => let G' := eval unfold stk0_words in G in change_no_check G' end). code_ato_vm.
  - exact both_tlsga_tab_ok.
  - apply bv_eq. vm_compute. reflexivity.
  - exact both_m2s_tab_ok_57770.
  - apply bv_eq. vm_compute. reflexivity.
  - gaddr2_tac F_57bf4 D_57bf4 F_57bf8 D_57bf8.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
Qed.

End FPGen1.
End BoRtStkMal0I.
Module BoRtStkMal1I.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtM2S OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtXStrlenI.BoRtM2SI OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtTlsGA BoRtTlsGAI OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtStkMal0 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtStkLift.AsRtStkMal1 Bo_code_57bdc_58228.
Import OSSVerify.glaze.binary_reflection.images.AsanUbsan.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Abbreviation BSEGS := AsanUbsan.M.loaded_segments.

Definition both_stk1_tab : stk_tab :=
  {| sk_base := 0x57d50; sk_tg := both_tlsga_tab; sk_mt := both_m2s_tab_57770; sk_arg := 0x106cb8 |}.

Section FPGen1.
Context {fx : FPState}.

Lemma both_stk1_tab_ok : stk1_tab_ok BSEGS both_stk1_tab.
Proof using.
  (lazymatch goal with |- ?G => let G' := eval unfold stk1_tab_ok in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [sk_base sk_tg sk_mt sk_arg both_stk1_tab] in G in change_no_check G' end).
  repeat match goal with |- _ /\ _ => split end.
  - (lazymatch goal with |- ?G => let G' := eval unfold stk1_words in G in change_no_check G' end). code_ato_vm.
  - exact both_tlsga_tab_ok.
  - apply bv_eq. vm_compute. reflexivity.
  - exact both_m2s_tab_ok_57770.
  - apply bv_eq. vm_compute. reflexivity.
  - gaddr2_tac F_57d68 D_57d68 F_57d6c D_57d6c.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
Qed.

End FPGen1.
End BoRtStkMal1I.
Module BoRtStkMal2I.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtM2S OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtXStrlenI.BoRtM2SI OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtTlsGA BoRtTlsGAI OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtStkMal0 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtStkLift.AsRtStkMal2 Bo_code_57bdc_58228.
Import OSSVerify.glaze.binary_reflection.images.AsanUbsan.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Abbreviation BSEGS := AsanUbsan.M.loaded_segments.

Definition both_stk2_tab : stk_tab :=
  {| sk_base := 0x57ee0; sk_tg := both_tlsga_tab; sk_mt := both_m2s_tab_57770; sk_arg := 0x106cb8 |}.

Section FPGen1.
Context {fx : FPState}.

Lemma both_stk2_tab_ok : stk2_tab_ok BSEGS both_stk2_tab.
Proof using.
  (lazymatch goal with |- ?G => let G' := eval unfold stk2_tab_ok in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [sk_base sk_tg sk_mt sk_arg both_stk2_tab] in G in change_no_check G' end).
  repeat match goal with |- _ /\ _ => split end.
  - (lazymatch goal with |- ?G => let G' := eval unfold stk2_words in G in change_no_check G' end). code_ato_vm.
  - exact both_tlsga_tab_ok.
  - apply bv_eq. vm_compute. reflexivity.
  - exact both_m2s_tab_ok_57770.
  - apply bv_eq. vm_compute. reflexivity.
  - gaddr2_tac F_57ef8 D_57ef8 F_57efc D_57efc.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
Qed.

End FPGen1.
End BoRtStkMal2I.
Module BoRtStkMal3I.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtM2S OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtXStrlenI.BoRtM2SI OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtTlsGA BoRtTlsGAI OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtStkMal0 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtStkLift.AsRtStkMal3 Bo_code_57bdc_58228.
Import OSSVerify.glaze.binary_reflection.images.AsanUbsan.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Abbreviation BSEGS := AsanUbsan.M.loaded_segments.

Definition both_stk3_tab : stk_tab :=
  {| sk_base := 0x5807c; sk_tg := both_tlsga_tab; sk_mt := both_m2s_tab_57770; sk_arg := 0x106cb8 |}.

Section FPGen1.
Context {fx : FPState}.

Lemma both_stk3_tab_ok : stk3_tab_ok BSEGS both_stk3_tab.
Proof using.
  (lazymatch goal with |- ?G => let G' := eval unfold stk3_tab_ok in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [sk_base sk_tg sk_mt sk_arg both_stk3_tab] in G in change_no_check G' end).
  repeat match goal with |- _ /\ _ => split end.
  - (lazymatch goal with |- ?G => let G' := eval unfold stk3_words in G in change_no_check G' end). code_ato_vm.
  - exact both_tlsga_tab_ok.
  - apply bv_eq. vm_compute. reflexivity.
  - exact both_m2s_tab_ok_57770.
  - apply bv_eq. vm_compute. reflexivity.
  - gaddr2_tac F_58094 D_58094 F_58098 D_58098.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
Qed.

End FPGen1.
End BoRtStkMal3I.
Module BoRtStkLiftI.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsK OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsRtK OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib AsRtImg OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOps3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvHole3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsIcptSetSh.AsIcptLift OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtM2S OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtXStrlenI.BoRtM2SI OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtTlsGA BoRtTlsGAI OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtStkMal0 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtStkLift.AsRtStkMal1 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtStkLift.AsRtStkMal2 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtStkLift.AsRtStkMal3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtStkLift.AsRtStkMalK BoRtStkMal0I BoRtStkMal1I BoRtStkMal2I BoRtStkMal3I OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtStkLift.AsRtStkLiftG OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtStkLift.
Import OSSVerify.glaze.binary_reflection.images.AsanUbsan.
Import ListNotations.
Open Scope Z_scope.
#[local] Unset Lia Cache. #[local] Unset Nia Cache. #[local] Unset Nra Cache.

(* [comment removed for export] *)
Definition both_stk_cells (tctx : Z) : list (Z * nat * Z) :=
  stk_consts both_stk0_tab (ia_tp both_addrs) tctx 0x106cb8 0xfffffffffffff800 0x6413a0 0x641b80 0x662728.

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac wd_in_nat i := lazymatch i with O => idtac | S ?j => wd_in_nat j end.
Ltac wd_in_fast :=
  let G := match goal with |- ?G => eval cbv beta in G end in
  lazymatch G with In (?a, ?n, ?v) ?L =>
    let i := eval lazy in ((fix f (l : list (Z * nat * Z)) : nat := match l with [] => O | (a', n', _) :: l' =>
                              if (Z.eqb a a' && Nat.eqb n n')%bool then O else S (f l') end) L) in
    wd_in_nat i; exact (nth_error_In L i eq_refl)
  end.

Lemma both_stk_cells_in : forall P6 SPB M8 M10, Forall (fun c => In c (both_consts P6 SPB M8 M10)) (both_stk_cells M10).
Proof.
  intros P6 SPB M8 M10. (lazymatch goal with |- ?G => let G' := eval unfold both_stk_cells, stk_consts in G in change_no_check G' end).
  repeat apply Forall_cons; try apply Forall_nil;
    first [ wd_in_fast | (lazymatch goal with |- ?G => let G' := eval unfold both_consts in G in change_no_check G' end); (lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); repeat (first [left; reflexivity | right]) ].
Qed.

Section BT.
  Context {RC : run_ceil}.
  Variable FXOK : FPState -> Prop.
  Variable bt : as_boot.
  Hypothesis BT_IA : bt_ia bt = both_addrs.
  Hypothesis BT_SEGS : bt_segs bt = BSEGS.
  Hypothesis BT_TP : bt_tp bt = ia_tp both_addrs.
  Hypothesis BT_TLSFS : bt_tls_fs bt = ia_tp both_addrs.
  Hypothesis K_stkmal : Forall (fun c => In c (bt_consts bt)) (both_stk_cells (bt_tctx bt)).

  Lemma HOFF_P : forall (HP0 : option Z -> ast -> Prop) h Lc FF B C K M mdl AA,
    AAINVP (HP0 h) bt Lc FF B C K M mdl -> H_off_segments (bt_segs bt) (HL mdl AA).
  Proof using BT_SEGS BT_IA.
    intros HP0 h Lc FF B C K M mdl AA AI.
    assert (HULL : forall a, find_segment (bt_segs bt) a 1 <> None -> ia_img_lo (bt_ia bt) <= a < ia_img_hi (bt_ia bt))
      by (rewrite BT_SEGS, BT_IA; exact both_segs_hull).
    exact (HL_off_segments (bt_segs bt) (bt_ia bt) (AAINVP (HP0 h) bt) (bt_fs bt) (AAINV_props_all bt (HP0 h)) HULL Lc FF B C K M mdl AA AI).
  Qed.

  (* [comment removed for export] *)
  Lemma C_stkmal_any : forall (HP0 : option Z -> ast -> Prop),
    (forall h st k v, HP0 h st -> HP0 h (set_hint st k v)) ->
    forall k, 0 <= k <= KMAXCLASS -> STKMAL BSEGS FXOK both_addrs (fun h => AAINVP (HP0 h) bt) (bt_fs bt) k.
  Proof using K_stkmal BT_TLSFS BT_TP BT_SEGS BT_IA.
    intros HP0 HH k Hk. unfold KMAXCLASS in Hk.
    assert (GEN : forall t, (forall fx : FPState, @stkK_tab_ok fx (bt_segs bt) k t) -> sk_base t = Z_to_bv 64 (ia_stkmal (bt_ia bt) k) ->
                  sk_tg t = sk_tg both_stk0_tab -> sk_mt t = sk_mt both_stk0_tab -> sk_arg t = Z_to_bv 64 0x106cb8 ->
                  STKMAL (bt_segs bt) FXOK (bt_ia bt) (fun h => AAINVP (HP0 h) bt) (bt_fs bt) k).
    { intros t TOK TE TG MT TA.
      apply (@C_stkmal_P RC FXOK bt HP0 ltac:(rewrite BT_SEGS; exact both_segs_wx)
               ltac:(rewrite BT_SEGS, BT_IA; exact both_segs_hull) (HOFF_P HP0) HH k Hk t TOK TE
               0x106cb8 0xfffffffffffff800 0x6413a0 0x641b80 0x662728 TA).
      - lia.
      - rewrite BT_IA. reflexivity.
      - rewrite BT_IA. exact BT_TP.
      - rewrite BT_IA. exact BT_TLSFS.
      - rewrite BT_IA. vm_compute. discriminate.
      - rewrite BT_IA. (lazymatch goal with |- ?G => let G' := eval unfold stk_consts in G in change_no_check G' end). rewrite TG, MT. exact K_stkmal. }
    rewrite <- BT_SEGS, <- BT_IA.
    assert (KC : k = 0 \/ k = 1 \/ k = 2 \/ k = 3) by lia.
    destruct KC as [-> | [-> | [-> | ->]]].
    - apply (GEN both_stk0_tab); [| rewrite BT_IA; apply bv_eq; reflexivity | reflexivity | reflexivity | apply bv_eq; reflexivity].
      intros fx'. rewrite BT_SEGS. (lazymatch goal with |- ?G => let G' := eval unfold stkK_tab_ok in G in change_no_check G' end). repeat match goal with |- _ /\ _ => split end; intros E; first [discriminate E | exact both_stk0_tab_ok].
    - apply (GEN both_stk1_tab); [| rewrite BT_IA; apply bv_eq; reflexivity | reflexivity | reflexivity | apply bv_eq; reflexivity].
      intros fx'. rewrite BT_SEGS. (lazymatch goal with |- ?G => let G' := eval unfold stkK_tab_ok in G in change_no_check G' end). repeat match goal with |- _ /\ _ => split end; intros E; first [discriminate E | exact both_stk1_tab_ok].
    - apply (GEN both_stk2_tab); [| rewrite BT_IA; apply bv_eq; reflexivity | reflexivity | reflexivity | apply bv_eq; reflexivity].
      intros fx'. rewrite BT_SEGS. (lazymatch goal with |- ?G => let G' := eval unfold stkK_tab_ok in G in change_no_check G' end). repeat match goal with |- _ /\ _ => split end; intros E; first [discriminate E | exact both_stk2_tab_ok].
    - apply (GEN both_stk3_tab); [| rewrite BT_IA; apply bv_eq; reflexivity | reflexivity | reflexivity | apply bv_eq; reflexivity].
      intros fx'. rewrite BT_SEGS. (lazymatch goal with |- ?G => let G' := eval unfold stkK_tab_ok in G in change_no_check G' end). repeat match goal with |- _ /\ _ => split end; intros E; first [discriminate E | exact both_stk3_tab_ok].
  Qed.

  Theorem C_stkmal_bt_B : forall k, 0 <= k <= KMAXCLASS -> STKMAL BSEGS FXOK both_addrs (AAINV_H bt) (bt_fs bt) k.
  Proof using K_stkmal BT_TLSFS BT_TP BT_SEGS BT_IA. intros k Hk. apply (C_stkmal_any (fun h => holes_le h) ltac:(intros h st k' v H; exact H) k Hk). Qed.

  Theorem C_stkmal_bts_B : forall k, 0 <= k <= KMAXCLASS -> STKMAL BSEGS FXOK both_addrs (AAINV_HS bt) (bt_fs bt) k.
  Proof using K_stkmal BT_TLSFS BT_TP BT_SEGS BT_IA. intros k Hk. apply (C_stkmal_any (fun h => holes_lsopt h) ltac:(intros h st k' v H; destruct h; exact H) k Hk). Qed.
End BT.
End BoRtStkLiftI.
Module AsContractsB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsK OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinv3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvHole3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFFam.AsAinvHS3 AsRtImg OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtStkLift.AsRtAMemsetI OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtStkLift.AsRtXMemsetI OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtStkLift.AsRtAMemcpyI OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtStkLift.AsRtXMemcpyI OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtStkLift.AsRtAMemmoveI OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtStkLift.AsRtXMemmoveI OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtXStrlenI OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtStkLift.AsIcptMemset OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtStkLift.AsIcptXMemset OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtStkLift.AsIcptMemcpy OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtStkLift.AsIcptXMemcpy OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtStkLift.AsIcptMemmove OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtStkLift.AsIcptXMemmove OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtStkLift.AsIcptStrlen BoIcptInstBtS BoRtStkLiftI BoRtAMemsetI BoRtXMemsetI BoRtAMemcpyI BoRtXMemcpyI BoRtAMemmoveI BoRtXMemmoveI OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtXStrlenI BoIcptMemsetI BoIcptXMemsetI BoIcptMemcpyI BoIcptXMemcpyI BoIcptMemmoveI BoIcptXMemmoveI BoIcptStrlenI.
Import OSSVerify.glaze.binary_reflection.images.AsanUbsan.
Import ListNotations.
Open Scope Z_scope.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section ContractsB.
  Context {RC : run_ceil}.
  Variable FXOK : FPState -> Prop.
  Variable FRESH : list (Z * Z) -> list (Z * Z) -> Z -> Z -> Z -> mem -> Model -> Z -> Prop.
  Variable bt : as_boot.
  Hypothesis BT_IA : bt_ia bt = both_addrs.
  Hypothesis BT_SEGS : bt_segs bt = BSEGS.
  Hypothesis BT_FS : 0 <= bt_fs bt.
  Hypothesis BT_TP : bt_tp bt = ia_tp both_addrs.
  Hypothesis BT_TLSFS : bt_tls_fs bt = ia_tp both_addrs.
  #[local] Notation AAINVH := (AAINV_HS bt).

  (* [comment removed for export] *)
  Hypothesis K_memset_icpt : Forall (fun c => In c (bt_consts bt)) (xmset_cells both_xmset_tab).
  Hypothesis K_asan_memset : Forall (fun c => In c (bt_consts bt)) (amset_cells both_amset_tab).
  Hypothesis K_memcpy_icpt : Forall (fun c => In c (bt_consts bt)) (xmcpy_cells both_xmcpy_tab).
  Hypothesis K_asan_memcpy : Forall (fun c => In c (bt_consts bt)) (amcpy_cells both_amcpy_tab).
  Hypothesis K_memmove_icpt : Forall (fun c => In c (bt_consts bt)) (xmmove_cells both_xmmove_tab).
  Hypothesis K_asan_memmove : Forall (fun c => In c (bt_consts bt)) (ammove_cells both_ammove_tab).
  Hypothesis K_strlen_icpt : Forall (fun c => In c (bt_consts bt)) (xstrlen_cells both_xstrlen_tab).
  Hypothesis K_stkmal : Forall (fun c => In c (bt_consts bt)) (both_stk_cells (bt_tctx bt)).

  (* [comment removed for export] *)
  Hypothesis W_MALLOC : MALLOC_KATW BSEGS FXOK both_addrs AAINVH MSTK_A (ia_malloc both_addrs) true.
  Hypothesis W_MALLOC_THUNK : MALLOC_KATW BSEGS FXOK both_addrs AAINVH MSTK_A (ia_malloc_thunk both_addrs) true.
  Hypothesis W_MALLOC_ALT : MALLOC_ALT BSEGS FXOK both_addrs AAINVH FRESH MSTK_A (ia_malloc both_addrs) true.
  Hypothesis W_MALLOC_ALT_THUNK : MALLOC_ALT BSEGS FXOK both_addrs AAINVH FRESH MSTK_A (ia_malloc_thunk both_addrs) true.
  Hypothesis W_FREE : FREE_KAT BSEGS FXOK both_addrs AAINVH MSTK_A (ia_free both_addrs).
  Hypothesis W_FREE_THUNK : FREE_KAT BSEGS FXOK both_addrs AAINVH MSTK_A (ia_free_thunk both_addrs).
  Hypothesis W_OPDEL : FREE_KAT BSEGS FXOK both_addrs AAINVH MSTK_A (ia_opdel both_addrs).
  Hypothesis W_OPDEL_SZ : FREE_KAT BSEGS FXOK both_addrs AAINVH MSTK_A (ia_opdel_sz both_addrs).




End ContractsB.
End AsContractsB.
Module AsContractsPRB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsK OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsIfaceNM3.AsIfacePR3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinv3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOps3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtStkLift.AsAinvFacts3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvHole3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFFam.AsAinvHS3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFFam.AsAinvPrist3 AsRtImg OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsRtK OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib BoRtAMemsetI BoRtXMemsetI BoRtAMemcpyI BoRtXMemcpyI BoRtAMemmoveI BoRtXMemmoveI OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtXStrlenI OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtStkLift.AsIcptMemset OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtStkLift.AsIcptXMemset OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtStkLift.AsIcptMemcpy OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtStkLift.AsIcptXMemcpy OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtStkLift.AsIcptMemmove OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtStkLift.AsIcptXMemmove OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtStkLift.AsIcptStrlen BoIcptMemsetI BoIcptXMemsetI BoIcptMemcpyI BoIcptXMemcpyI BoIcptMemmoveI BoIcptXMemmoveI BoIcptStrlenI OSSVerify.Proofs.glaze.binary_reflection.lib.AsIcptSetSh.AsIcptLift OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtStkLift.AsRtFakeRel BoIcptInstBtS BoRtStkLiftI.
Import OSSVerify.glaze.binary_reflection.images.AsanUbsan.
Import ListNotations.
Open Scope Z_scope.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section ContractsPRB.
  Context {RC : run_ceil}.
  Variable FXOK : FPState -> Prop.
  Variable bt : as_boot.
  Variable Q : ast -> Prop.                                             (* [comment removed for export] *)
  Hypothesis Q_hint : forall st k v, Q st -> Q (set_hint st k v).
  Hypothesis BT_IA : bt_ia bt = both_addrs.
  Hypothesis BT_SEGS : bt_segs bt = BSEGS.
  Hypothesis BT_FS : 0 <= bt_fs bt.
  Hypothesis BT_TP : bt_tp bt = ia_tp both_addrs.
  Hypothesis BT_TLSFS : bt_tls_fs bt = ia_tp both_addrs.
  #[local] Notation AAINVH := (AAINV_QX bt Q).

  Hypothesis K_memset_icpt : Forall (fun c => In c (bt_consts bt)) (xmset_cells both_xmset_tab).
  Hypothesis K_asan_memset : Forall (fun c => In c (bt_consts bt)) (amset_cells both_amset_tab).
  Hypothesis K_memcpy_icpt : Forall (fun c => In c (bt_consts bt)) (xmcpy_cells both_xmcpy_tab).
  Hypothesis K_asan_memcpy : Forall (fun c => In c (bt_consts bt)) (amcpy_cells both_amcpy_tab).
  Hypothesis K_memmove_icpt : Forall (fun c => In c (bt_consts bt)) (xmmove_cells both_xmmove_tab).
  Hypothesis K_asan_memmove : Forall (fun c => In c (bt_consts bt)) (ammove_cells both_ammove_tab).
  Hypothesis K_strlen_icpt : Forall (fun c => In c (bt_consts bt)) (xstrlen_cells both_xstrlen_tab).
  Hypothesis K_stkmal : Forall (fun c => In c (bt_consts bt)) (both_stk_cells (bt_tctx bt)).

  (* [comment removed for export] *)
  Hypothesis W_MALLOC_SEC_PR : MALLOC_ALT_SEC BSEGS FXOK both_addrs AAINVH MSTK_A (ia_malloc both_addrs) true.
  Hypothesis W_MALLOC_SEC_PR_THUNK : MALLOC_ALT_SEC BSEGS FXOK both_addrs AAINVH MSTK_A (ia_malloc_thunk both_addrs) true.
  Hypothesis W_FREE_PR : FREE_KAT_N BSEGS FXOK both_addrs AAINVH MSTK_A (ia_free both_addrs).
  Hypothesis W_FREE_PR_THUNK : FREE_KAT_N BSEGS FXOK both_addrs AAINVH MSTK_A (ia_free_thunk both_addrs).
  Hypothesis W_OPDEL_PR : FREE_KAT_N BSEGS FXOK both_addrs AAINVH MSTK_A (ia_opdel both_addrs).
  Hypothesis W_OPDEL_SZ_PR : FREE_KAT_N BSEGS FXOK both_addrs AAINVH MSTK_A (ia_opdel_sz both_addrs).

  Lemma HP_pr_bt : forall h, AAINV_props both_addrs (AAINVH h) (bt_fs bt) BSEGS.
  Proof. intros h. rewrite <- BT_IA, <- BT_SEGS. exact (AAINV_QX_props bt Q h). Qed.
  Lemma CELLS_pr : forall cs, Forall (fun c => In c (bt_consts bt)) cs ->
    forall h Lc FF B C K M mdl, AAINVH h Lc FF B C K M mdl ->
    Forall (fun c => cellN BSEGS M (fst (fst c)) (snd (fst c)) (snd c)) cs.
  Proof.
    intros cs Hcs h Lc FF B C K M mdl (st & W & R & _).
    pose proof (read_consts bt st Lc FF M mdl R) as CH. unfold cells_hold, cellZ in CH. rewrite BT_SEGS in CH.
    rewrite Forall_forall in Hcs, CH |- *. intros c Hc. exact (CH c (Hcs c Hc)).
  Qed.
  Lemma HOFF_pr : forall h Lc FF B C K M mdl AA, AAINVH h Lc FF B C K M mdl -> H_off_segments BSEGS (HL mdl AA).
  Proof. intros h Lc FF B C K M mdl AA AI. exact (HL_off_segments BSEGS both_addrs (AAINVH h) (bt_fs bt) (HP_pr_bt h) both_segs_hull Lc FF B C K M mdl AA AI). Qed.

  Definition W_STKMAL_PR : forall k, 0 <= k <= KMAXCLASS -> STKMAL BSEGS FXOK both_addrs AAINVH (bt_fs bt) k :=
    @C_stkmal_any RC FXOK bt BT_IA BT_SEGS BT_TP BT_TLSFS K_stkmal (HP_q Q) (HP_q_hint Q Q_hint).
  Definition W_FAKEREL_PR : FAKEREL BSEGS FXOK both_addrs AAINVH.
  Proof.
    intros h pc rs fx. pose proof (@C_fakerel_P RC FXOK bt (HP_q Q)) as X. rewrite BT_SEGS, BT_IA in X.
    exact (X both_segs_wx HOFF_pr (FS_NOLAZY_bt bt) (FS_PRIV_bt bt BT_IA) fx h pc rs fx).
  Qed.

  Definition ASCP_B : as_contracts_pr BSEGS FXOK both_addrs AAINVH (bt_fs bt) :=
    @ASCP BSEGS RC FXOK both_addrs AAINVH (bt_fs bt)
        W_MALLOC_SEC_PR W_MALLOC_SEC_PR_THUNK W_FREE_PR W_FREE_PR_THUNK W_OPDEL_PR W_OPDEL_SZ_PR
        W_STKMAL_PR W_FAKEREL_PR
        (C_memcpy_icpt_B FXOK AAINVH (bt_fs bt) HP_pr_bt BT_FS (CELLS_pr _ K_memcpy_icpt)) (C_asan_memcpy_B FXOK AAINVH (bt_fs bt) HP_pr_bt BT_FS (CELLS_pr _ K_asan_memcpy))
        (C_memset_icpt_B FXOK AAINVH (bt_fs bt) HP_pr_bt BT_FS (CELLS_pr _ K_memset_icpt)) (C_asan_memset_B FXOK AAINVH (bt_fs bt) HP_pr_bt BT_FS (CELLS_pr _ K_asan_memset))
        (C_memmove_icpt_B FXOK AAINVH (bt_fs bt) HP_pr_bt BT_FS (CELLS_pr _ K_memmove_icpt)) (C_asan_memmove_B FXOK AAINVH (bt_fs bt) HP_pr_bt BT_FS (CELLS_pr _ K_asan_memmove))
        (C_strlen_icpt_B FXOK AAINVH (bt_fs bt) HP_pr_bt BT_FS (CELLS_pr _ K_strlen_icpt)).

  Definition ASCP_B_bt : as_contracts_pr BSEGS FXOK (bt_ia bt) AAINVH (bt_fs bt).
  Proof. rewrite BT_IA. exact ASCP_B. Defined.
End ContractsPRB.
End AsContractsPRB.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOomCell3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module AsContractsAtB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsK OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsIfaceNM3.AsIfacePR3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinv3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinvGeom3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvHole3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFFam.AsAinvHS3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOomCell3.BoAinvBoot3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys10.AsAinvBootF3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFFam.AsAinvPrist3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFFam.AsAinvDrvHist3 AsRtImg BoRtAMemsetI BoRtXMemsetI BoRtAMemcpyI BoRtXMemcpyI BoRtAMemmoveI BoRtXMemmoveI OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtXStrlenI OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtStkLift.AsIcptMemset OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtStkLift.AsIcptXMemset OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtStkLift.AsIcptMemcpy OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtStkLift.AsIcptXMemcpy OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtStkLift.AsIcptMemmove OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtStkLift.AsIcptXMemmove OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtStkLift.AsIcptStrlen BoIcptInstBtS BoRtStkLiftI BoIcptMemsetI BoIcptXMemsetI BoIcptMemcpyI BoIcptXMemcpyI BoIcptMemmoveI BoIcptXMemmoveI BoIcptStrlenI AsContractsB AsContractsPRB.
Import OSSVerify.glaze.binary_reflection.images.AsanUbsan.
Import ListNotations.
Open Scope Z_scope.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section At.
  Context {RC : run_ceil}.
  Variable FXOK : FPState -> Prop.
  Variable hv : bvars.
  #[local] Notation bt := (both_bt hv).
  Hypothesis BF : boot_facts bt.

  Ltac in_consts_old := rewrite both_bt_consts; unfold both_consts; cbv zeta; repeat (first [left; reflexivity | right]).
  (* [comment removed for export] *)
  Ltac in_consts_nat i := lazymatch i with O => idtac | S ?j => in_consts_nat j end.
  Ltac in_consts_fast :=
    let G := match goal with |- ?G => eval cbv beta in G end in
    lazymatch G with In (?a, ?n, ?v) ?L =>
      let i := eval lazy in ((fix f (l : list (Z * nat * Z)) : nat := match l with [] => O | (a', n', _) :: l' =>
                                if (Z.eqb a a' && Nat.eqb n n')%bool then O else S (f l') end) L) in
      in_consts_nat i; exact (nth_error_In L i eq_refl)
    end.
  Ltac in_consts := first [in_consts_fast | in_consts_old].
  Ltac k_rows :=
    match goal with |- Forall _ ?L => let L' := eval vm_compute in L in change (Forall (fun c => In c (bt_consts bt)) L') end;
    repeat (constructor; [in_consts|]); constructor.

  Lemma K_memset_icpt_at : Forall (fun c => In c (bt_consts bt)) (xmset_cells both_xmset_tab).   Proof. k_rows. Qed.
  Lemma K_asan_memset_at : Forall (fun c => In c (bt_consts bt)) (amset_cells both_amset_tab).   Proof. k_rows. Qed.
  Lemma K_memcpy_icpt_at : Forall (fun c => In c (bt_consts bt)) (xmcpy_cells both_xmcpy_tab).   Proof. k_rows. Qed.
  Lemma K_asan_memcpy_at : Forall (fun c => In c (bt_consts bt)) (amcpy_cells both_amcpy_tab).   Proof. k_rows. Qed.
  Lemma K_memmove_icpt_at : Forall (fun c => In c (bt_consts bt)) (xmmove_cells both_xmmove_tab). Proof. k_rows. Qed.
  Lemma K_asan_memmove_at : Forall (fun c => In c (bt_consts bt)) (ammove_cells both_ammove_tab). Proof. k_rows. Qed.
  Lemma K_strlen_icpt_at : Forall (fun c => In c (bt_consts bt)) (xstrlen_cells both_xstrlen_tab). Proof. k_rows. Qed.
  Lemma K_stkmal_at : Forall (fun c => In c (bt_consts bt)) (both_stk_cells (bt_tctx bt)).
  Proof. rewrite both_bt_consts, both_bt_tctx. apply both_stk_cells_in. Qed.

  Lemma BT_FS_at : 0 <= bt_fs bt.
  Proof.
    pose proof (boot_facts_ok bt BF) as (_ & WM & _). destruct WM as (RNG & _ & _ & _ & _ & _ & INFS & _).
    destruct (RNG _ _ (all_ranges_fixed bt (st0 bt) _ INFS)) as ((D1 & _) & _). lia.
  Qed.

  (* [comment removed for export] *)
  Hypothesis W_MALLOC : MALLOC_KATW BSEGS FXOK both_addrs (AAINV_HS bt) MSTK_A (ia_malloc both_addrs) true.
  Hypothesis W_MALLOC_THUNK : MALLOC_KATW BSEGS FXOK both_addrs (AAINV_HS bt) MSTK_A (ia_malloc_thunk both_addrs) true.
  Hypothesis W_MALLOC_ALT : MALLOC_ALT BSEGS FXOK both_addrs (AAINV_HS bt) (FRESH_bt bt) MSTK_A (ia_malloc both_addrs) true.
  Hypothesis W_MALLOC_ALT_THUNK : MALLOC_ALT BSEGS FXOK both_addrs (AAINV_HS bt) (FRESH_bt bt) MSTK_A (ia_malloc_thunk both_addrs) true.
  Hypothesis W_FREE : FREE_KAT BSEGS FXOK both_addrs (AAINV_HS bt) MSTK_A (ia_free both_addrs).
  Hypothesis W_FREE_THUNK : FREE_KAT BSEGS FXOK both_addrs (AAINV_HS bt) MSTK_A (ia_free_thunk both_addrs).
  Hypothesis W_OPDEL : FREE_KAT BSEGS FXOK both_addrs (AAINV_HS bt) MSTK_A (ia_opdel both_addrs).
  Hypothesis W_OPDEL_SZ : FREE_KAT BSEGS FXOK both_addrs (AAINV_HS bt) MSTK_A (ia_opdel_sz both_addrs).


  (* [comment removed for export] *)
  Hypothesis W_MALLOC_SEC_PR : MALLOC_ALT_SEC BSEGS FXOK both_addrs (AAINV_DRX bt) MSTK_A (ia_malloc both_addrs) true.
  Hypothesis W_MALLOC_SEC_PR_THUNK : MALLOC_ALT_SEC BSEGS FXOK both_addrs (AAINV_DRX bt) MSTK_A (ia_malloc_thunk both_addrs) true.
  Hypothesis W_FREE_PR : FREE_KAT_N BSEGS FXOK both_addrs (AAINV_DRX bt) MSTK_A (ia_free both_addrs).
  Hypothesis W_FREE_PR_THUNK : FREE_KAT_N BSEGS FXOK both_addrs (AAINV_DRX bt) MSTK_A (ia_free_thunk both_addrs).
  Hypothesis W_OPDEL_PR : FREE_KAT_N BSEGS FXOK both_addrs (AAINV_DRX bt) MSTK_A (ia_opdel both_addrs).
  Hypothesis W_OPDEL_SZ_PR : FREE_KAT_N BSEGS FXOK both_addrs (AAINV_DRX bt) MSTK_A (ia_opdel_sz both_addrs).

  Theorem ASCD_B_at : as_contracts_pr BSEGS FXOK (bt_ia bt) (AAINV_DRX bt) (bt_fs bt).
  Proof.
    exact (@ASCP_B_bt RC FXOK bt drv_hist drv_hist_hint eq_refl eq_refl BT_FS_at eq_refl eq_refl
             K_memset_icpt_at K_asan_memset_at K_memcpy_icpt_at K_asan_memcpy_at K_memmove_icpt_at K_asan_memmove_at K_strlen_icpt_at K_stkmal_at
             W_MALLOC_SEC_PR W_MALLOC_SEC_PR_THUNK W_FREE_PR W_FREE_PR_THUNK W_OPDEL_PR W_OPDEL_SZ_PR).
  Qed.
End At.
End AsContractsAtB.
Module AsIcptInstBt.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsK OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtStkLift.AsAinvFacts3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsRtK OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib AsRtImg OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOps3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtAMemset OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtStkLift.AsRtAMemsetI OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtStkLift.AsRtXMemset OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtStkLift.AsRtXMemsetI OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtStkLift.AsRtAMemcpy OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtStkLift.AsRtAMemcpyI OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtStkLift.AsRtXMemcpy OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtStkLift.AsRtXMemcpyI OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtAMemmove OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtStkLift.AsRtAMemmoveI OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtStkLift.AsRtXMemmove OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtStkLift.AsRtXMemmoveI OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtTlsGA.AsRtXStrlen OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtXStrlenI OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtStkLift.AsIcptMemset AsIcptMemsetI OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtStkLift.AsIcptXMemset AsIcptXMemsetI OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtStkLift.AsIcptMemcpy AsIcptMemcpyI OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtStkLift.AsIcptXMemcpy AsIcptXMemcpyI OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtStkLift.AsIcptMemmove AsIcptMemmoveI OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtStkLift.AsIcptXMemmove AsIcptXMemmoveI OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtStkLift.AsIcptStrlen AsIcptStrlenI OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtM2S OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtXStrlenI.AsRtM2SI OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoison OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoisonI OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtAnn AsRtAnnI OSSVerify.Proofs.glaze.binary_reflection.lib.AsIcptAnn.AsIcptAnnM OSSVerify.Proofs.glaze.binary_reflection.lib.AsIcptAnn AsIcptAnnI OSSVerify.Proofs.glaze.binary_reflection.lib.AsIcptSetSh.AsIcptLift OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d.AsAinvFreeS OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtStkLift.AsRtFakeRel.
Import OSSVerify.glaze.binary_reflection.images.Asan.
Import ListNotations.
Open Scope Z_scope.
#[local] Unset Lia Cache. #[local] Unset Nia Cache. #[local] Unset Nra Cache.

Section BT.
  Context {RC : run_ceil}.
  Variable FXOK : FPState -> Prop.
  Variable bt : as_boot.
  Hypothesis BT_IA : bt_ia bt = asan_addrs.
  Hypothesis BT_SEGS : bt_segs bt = ASEGS.
  Hypothesis BT_FS : 0 <= bt_fs bt.

  #[local] Notation AAINVH := (AAINV_H bt).

  Lemma HP_bt : forall h, AAINV_props asan_addrs (AAINVH h) (bt_fs bt) ASEGS.
  Proof using BT_SEGS BT_IA. intros h. rewrite <- BT_IA, <- BT_SEGS. exact (AAINV_props_all bt (holes_le h)). Qed.

  (* [comment removed for export] *)
  Lemma CELLS_bt : forall cs, Forall (fun c => In c (bt_consts bt)) cs ->
    forall h Lc FF B C K M mdl, AAINVH h Lc FF B C K M mdl ->
    Forall (fun c => cellN ASEGS M (fst (fst c)) (snd (fst c)) (snd c)) cs.
  Proof using BT_SEGS.
    intros cs Hcs h Lc FF B C K M mdl (st & W & R & _).
    pose proof (read_consts bt st Lc FF M mdl R) as CH. unfold cells_hold, cellZ in CH. rewrite BT_SEGS in CH.
    rewrite Forall_forall in Hcs, CH |- *. intros c Hc. exact (CH c (Hcs c Hc)).
  Qed.

  Hypothesis K_memset_icpt : Forall (fun c => In c (bt_consts bt)) (xmset_cells asan_xmset_tab).
  Hypothesis K_asan_memset : Forall (fun c => In c (bt_consts bt)) (amset_cells asan_amset_tab).
  Hypothesis K_memcpy_icpt : Forall (fun c => In c (bt_consts bt)) (xmcpy_cells asan_xmcpy_tab).
  Hypothesis K_asan_memcpy : Forall (fun c => In c (bt_consts bt)) (amcpy_cells asan_amcpy_tab).
  Hypothesis K_memmove_icpt : Forall (fun c => In c (bt_consts bt)) (xmmove_cells asan_xmmove_tab).
  Hypothesis K_asan_memmove : Forall (fun c => In c (bt_consts bt)) (ammove_cells asan_ammove_tab).
  Hypothesis K_strlen_icpt : Forall (fun c => In c (bt_consts bt)) (xstrlen_cells asan_xstrlen_tab).

  Theorem C_memset_icpt_bt : MEMSET_AT ASEGS FXOK asan_addrs AAINVH (ia_memset_icpt asan_addrs).
  Proof using K_memset_icpt BT_FS BT_SEGS BT_IA. exact (C_memset_icpt_A FXOK AAINVH (bt_fs bt) HP_bt BT_FS (CELLS_bt _ K_memset_icpt)). Qed.
  Theorem C_asan_memset_bt : MEMSET_AT ASEGS FXOK asan_addrs AAINVH (ia_asan_memset asan_addrs).
  Proof using K_asan_memset BT_FS BT_SEGS BT_IA. exact (C_asan_memset_A FXOK AAINVH (bt_fs bt) HP_bt BT_FS (CELLS_bt _ K_asan_memset)). Qed.
  Theorem C_memcpy_icpt_bt : MEMCPY_AT ASEGS FXOK asan_addrs AAINVH (ia_memcpy_icpt asan_addrs).
  Proof using K_memcpy_icpt BT_FS BT_SEGS BT_IA. exact (C_memcpy_icpt_A FXOK AAINVH (bt_fs bt) HP_bt BT_FS (CELLS_bt _ K_memcpy_icpt)). Qed.
  Theorem C_asan_memcpy_bt : MEMCPY_AT ASEGS FXOK asan_addrs AAINVH (ia_asan_memcpy asan_addrs).
  Proof using K_asan_memcpy BT_FS BT_SEGS BT_IA. exact (C_asan_memcpy_A FXOK AAINVH (bt_fs bt) HP_bt BT_FS (CELLS_bt _ K_asan_memcpy)). Qed.
  Theorem C_memmove_icpt_bt : MEMMOVE_AT ASEGS FXOK asan_addrs AAINVH (ia_memmove_icpt asan_addrs).
  Proof using K_memmove_icpt BT_FS BT_SEGS BT_IA. exact (C_memmove_icpt_A FXOK AAINVH (bt_fs bt) HP_bt BT_FS (CELLS_bt _ K_memmove_icpt)). Qed.
  Theorem C_asan_memmove_bt : MEMMOVE_AT ASEGS FXOK asan_addrs AAINVH (ia_asan_memmove asan_addrs).
  Proof using K_asan_memmove BT_FS BT_SEGS BT_IA. exact (C_asan_memmove_A FXOK AAINVH (bt_fs bt) HP_bt BT_FS (CELLS_bt _ K_asan_memmove)). Qed.
  Theorem C_strlen_icpt_bt : STRLEN_AT ASEGS FXOK asan_addrs AAINVH (ia_strlen_icpt asan_addrs).
  Proof using K_strlen_icpt BT_FS BT_SEGS BT_IA. exact (C_strlen_icpt_A FXOK AAINVH (bt_fs bt) HP_bt BT_FS (CELLS_bt _ K_strlen_icpt)). Qed.

  Hypothesis K_annotate : Forall (fun c => In c (bt_consts bt))
     (ann_cellsL asan_poison_tab asan_m2s_tab_6fb04 asan_ann_g_flags asan_ann_p_flags asan_ann_g_verb asan_ann_p_verb asan_ann_g_shoff asan_ann_p_shoff).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma FS_NOLAZY_bt : forall st Lc FF M mdl z,
    WF bt st Lc FF -> Rep bt st Lc FF M mdl -> bt_fs bt + 0x1000 <= z < bt_fs bt + 0x9000 -> lzb mdl z = false.
  Proof using. exact (AsRtStkLift.AsAinvFacts3b.FS_NOLAZY bt). Qed.
  Lemma FS_PRIV_bt : forall st Lc FF z,
    WF bt st Lc FF -> bt_fs bt + 0x1000 <= z < bt_fs bt + 0x9000 -> rt_priv asan_addrs Lc FF z.
  Proof using BT_IA. intros st Lc FF z W Hz. rewrite <- BT_IA. exact (AsRtStkLift.AsAinvFacts3b.FS_PRIV bt st Lc FF z W Hz). Qed.
  Lemma HOFF_bt : forall h Lc FF B C K M mdl AA, AAINVH h Lc FF B C K M mdl -> H_off_segments ASEGS (HL mdl AA).
  Proof using BT_SEGS BT_IA. intros h Lc FF B C K M mdl AA AI. exact (HL_off_segments ASEGS asan_addrs (AAINVH h) (bt_fs bt) (HP_bt h) asan_segs_hull Lc FF B C K M mdl AA AI). Qed.
  Theorem C_fakerel_bt : forall {fx : FPState}, FAKEREL ASEGS FXOK asan_addrs AAINVH.
  Proof using BT_SEGS BT_IA.
    intros fx. pose proof (@C_fakerel_P RC FXOK bt (fun h => holes_le h)) as X. rewrite BT_SEGS, BT_IA in X.
    exact (X asan_segs_wx HOFF_bt FS_NOLAZY_bt FS_PRIV_bt fx).
  Qed.
End BT.
End AsIcptInstBt.
Module AsContractsNA.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsK OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsIfaceNM3.AsIfacePR3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsIfaceNM3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinv3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinvGeom3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvHole3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFFam.AsAinvHS3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvBoot3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys10.AsAinvBootF3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFFam.AsAinvPrist3 AsRtImg OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtStkLift.AsRtAMemsetI OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtStkLift.AsRtXMemsetI OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtStkLift.AsRtAMemcpyI OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtStkLift.AsRtXMemcpyI OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtStkLift.AsRtAMemmoveI OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtStkLift.AsRtXMemmoveI OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtXStrlenI OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtStkLift.AsIcptMemset OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtStkLift.AsIcptXMemset OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtStkLift.AsIcptMemcpy OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtStkLift.AsIcptXMemcpy OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtStkLift.AsIcptMemmove OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtStkLift.AsIcptXMemmove OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtStkLift.AsIcptStrlen AsIcptInstBt AsIcptInstBtS AsRtStkLiftI AsContractsAtA.
Import OSSVerify.glaze.binary_reflection.images.Asan.
Import ListNotations.
Open Scope Z_scope.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section N.
  Context {RC : run_ceil}.
  Variable FXOK : FPState -> Prop.
  Variable hv : bvars.
  #[local] Notation bt := (asan_bt hv).
  Hypothesis BF : boot_facts bt.

  (* [comment removed for export] *)
  Hypothesis W_MALLOC : MALLOC_KATW ASEGS FXOK asan_addrs (AAINV_HS bt) MSTK_A (ia_malloc asan_addrs) true.
  Hypothesis W_MALLOC_THUNK : MALLOC_KATW ASEGS FXOK asan_addrs (AAINV_HS bt) MSTK_A (ia_malloc_thunk asan_addrs) true.
  Hypothesis W_MALLOC_ALT : MALLOC_ALT ASEGS FXOK asan_addrs (AAINV_HS bt) (FRESH_bt bt) MSTK_A (ia_malloc asan_addrs) true.
  Hypothesis W_MALLOC_ALT_THUNK : MALLOC_ALT ASEGS FXOK asan_addrs (AAINV_HS bt) (FRESH_bt bt) MSTK_A (ia_malloc_thunk asan_addrs) true.
  (* [comment removed for export] *)
  Hypothesis W_FREE : FREE_KAT ASEGS FXOK asan_addrs (AAINV_H bt) MSTK_A (ia_free asan_addrs).
  Hypothesis W_FREE_THUNK : FREE_KAT ASEGS FXOK asan_addrs (AAINV_H bt) MSTK_A (ia_free_thunk asan_addrs).
  Hypothesis W_OPDEL : FREE_KAT ASEGS FXOK asan_addrs (AAINV_H bt) MSTK_A (ia_opdel asan_addrs).
  Hypothesis W_OPDEL_SZ : FREE_KAT ASEGS FXOK asan_addrs (AAINV_H bt) MSTK_A (ia_opdel_sz asan_addrs).

  (* [comment removed for export] *)
  Lemma free_n_of_weak : forall entry, FREE_KAT ASEGS FXOK asan_addrs (AAINV_H bt) MSTK_A entry -> FREE_KAT_N ASEGS FXOK asan_addrs (AAINV_HS bt) MSTK_A entry.
  Proof. intros entry FK fx R M mdl Lc Lc' FF B C K B' C' K' ret sp p PRE. exact (FK None fx R M mdl Lc Lc' FF B C K B' C' K' ret sp p PRE). Qed.

  Theorem ASCN_A_at : as_contracts_n ASEGS FXOK (bt_ia bt) (AAINV_HS bt) (FRESH_bt bt) (bt_fs bt).
  Proof.
    change (bt_ia bt) with asan_addrs.
    exact (@ASCN ASEGS RC FXOK asan_addrs (AAINV_HS bt) (FRESH_bt bt) (bt_fs bt)
             (AAINV_HS_weaken bt) W_MALLOC W_MALLOC_THUNK W_MALLOC_ALT W_MALLOC_ALT_THUNK
             (free_n_of_weak _ W_FREE) (free_n_of_weak _ W_FREE_THUNK) (free_n_of_weak _ W_OPDEL) (free_n_of_weak _ W_OPDEL_SZ)
             (@C_stkmal_bts RC FXOK bt eq_refl eq_refl eq_refl eq_refl (K_stkmal_at hv))
             (fun h pc rs fx => @C_fakerel_bts RC FXOK bt eq_refl eq_refl fx h pc rs fx)
             (C_memcpy_icpt_bts FXOK bt eq_refl eq_refl (BT_FS_at hv BF) (K_memcpy_icpt_at hv)) (C_asan_memcpy_bts FXOK bt eq_refl eq_refl (BT_FS_at hv BF) (K_asan_memcpy_at hv))
             (C_memset_icpt_bts FXOK bt eq_refl eq_refl (BT_FS_at hv BF) (K_memset_icpt_at hv)) (C_asan_memset_bts FXOK bt eq_refl eq_refl (BT_FS_at hv BF) (K_asan_memset_at hv))
             (C_memmove_icpt_bts FXOK bt eq_refl eq_refl (BT_FS_at hv BF) (K_memmove_icpt_at hv)) (C_asan_memmove_bts FXOK bt eq_refl eq_refl (BT_FS_at hv BF) (K_asan_memmove_at hv))
             (C_strlen_icpt_bts FXOK bt eq_refl eq_refl (BT_FS_at hv BF) (K_strlen_icpt_at hv))).
  Qed.

  Theorem ASCNM_A_at : as_contracts_nm ASEGS FXOK (bt_ia bt) (AAINV_H bt) (bt_fs bt).
  Proof.
    change (bt_ia bt) with asan_addrs.
    exact (@ASCNM ASEGS RC FXOK asan_addrs (AAINV_H bt) (bt_fs bt)
             W_FREE W_FREE_THUNK W_OPDEL W_OPDEL_SZ
             (@C_stkmal_bt RC FXOK bt eq_refl eq_refl eq_refl eq_refl (K_stkmal_at hv))
             (fun h pc rs fx => @AsIcptInstBt.C_fakerel_bt RC FXOK bt eq_refl eq_refl fx h pc rs fx)
             (AsIcptInstBt.C_memcpy_icpt_bt FXOK bt eq_refl eq_refl (BT_FS_at hv BF) (K_memcpy_icpt_at hv)) (AsIcptInstBt.C_asan_memcpy_bt FXOK bt eq_refl eq_refl (BT_FS_at hv BF) (K_asan_memcpy_at hv))
             (AsIcptInstBt.C_memset_icpt_bt FXOK bt eq_refl eq_refl (BT_FS_at hv BF) (K_memset_icpt_at hv)) (AsIcptInstBt.C_asan_memset_bt FXOK bt eq_refl eq_refl (BT_FS_at hv BF) (K_asan_memset_at hv))
             (AsIcptInstBt.C_memmove_icpt_bt FXOK bt eq_refl eq_refl (BT_FS_at hv BF) (K_memmove_icpt_at hv)) (AsIcptInstBt.C_asan_memmove_bt FXOK bt eq_refl eq_refl (BT_FS_at hv BF) (K_asan_memmove_at hv))
             (AsIcptInstBt.C_strlen_icpt_bt FXOK bt eq_refl eq_refl (BT_FS_at hv BF) (K_strlen_icpt_at hv))).
  Qed.
End N.
End AsContractsNA.
Module BoIcptInstBt.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsK OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtStkLift.AsAinvFacts3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsRtK OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib AsRtImg OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOps3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtAMemset OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtStkLift.AsRtAMemsetI OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtStkLift.AsRtXMemset OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtStkLift.AsRtXMemsetI OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtStkLift.AsRtAMemcpy OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtStkLift.AsRtAMemcpyI OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtStkLift.AsRtXMemcpy OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtStkLift.AsRtXMemcpyI OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtAMemmove OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtStkLift.AsRtAMemmoveI OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtStkLift.AsRtXMemmove OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtStkLift.AsRtXMemmoveI OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtTlsGA.AsRtXStrlen OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtXStrlenI OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtPoisonI.BoRtLeafI OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtXStrlenI.BoRtM2SI OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtXStrlenI.BoRtRegionI BoRtAMemsetI BoRtXMemsetI BoRtAMemcpyI BoRtXMemcpyI BoRtAMemmoveI BoRtXMemmoveI OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtXStrlenI.BoRtStrlenI OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtXStrlenI OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtStkLift.AsIcptMemset BoIcptMemsetI OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtStkLift.AsIcptXMemset BoIcptXMemsetI OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtStkLift.AsIcptMemcpy BoIcptMemcpyI OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtStkLift.AsIcptXMemcpy BoIcptXMemcpyI OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtStkLift.AsIcptMemmove BoIcptMemmoveI OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtStkLift.AsIcptXMemmove BoIcptXMemmoveI OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtStkLift.AsIcptStrlen BoIcptStrlenI OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtM2S OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtXStrlenI.AsRtM2SI OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtXStrlenI.BoRtM2SI OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoison OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoisonI OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtPoisonI OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtAnn BoRtAnnI OSSVerify.Proofs.glaze.binary_reflection.lib.AsIcptAnn.AsIcptAnnM OSSVerify.Proofs.glaze.binary_reflection.lib.AsIcptAnn BoIcptAnnI.
Import OSSVerify.glaze.binary_reflection.images.AsanUbsan.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsIcptSetSh.AsIcptLift OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d.AsAinvFreeS OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtStkLift.AsRtFakeRel.
Import ListNotations.
Open Scope Z_scope.
#[local] Unset Lia Cache. #[local] Unset Nia Cache. #[local] Unset Nra Cache.

Section BT.
  Context {RC : run_ceil}.
  Variable FXOK : FPState -> Prop.
  Variable bt : as_boot.
  Hypothesis BT_IA : bt_ia bt = both_addrs.
  Hypothesis BT_SEGS : bt_segs bt = BSEGS.
  Hypothesis BT_FS : 0 <= bt_fs bt.

  #[local] Notation AAINVH := (AAINV_H bt).

  Lemma HP_bt : forall h, AAINV_props both_addrs (AAINVH h) (bt_fs bt) BSEGS.
  Proof using BT_SEGS BT_IA. intros h. rewrite <- BT_IA, <- BT_SEGS. exact (AAINV_props_all bt (holes_le h)). Qed.

  (* [comment removed for export] *)
  Lemma CELLS_bt : forall cs, Forall (fun c => In c (bt_consts bt)) cs ->
    forall h Lc FF B C K M mdl, AAINVH h Lc FF B C K M mdl ->
    Forall (fun c => cellN BSEGS M (fst (fst c)) (snd (fst c)) (snd c)) cs.
  Proof using BT_SEGS.
    intros cs Hcs h Lc FF B C K M mdl (st & W & R & _).
    pose proof (read_consts bt st Lc FF M mdl R) as CH. unfold cells_hold, cellZ in CH. rewrite BT_SEGS in CH.
    rewrite Forall_forall in Hcs, CH |- *. intros c Hc. exact (CH c (Hcs c Hc)).
  Qed.

  Hypothesis K_memset_icpt : Forall (fun c => In c (bt_consts bt)) (xmset_cells both_xmset_tab).
  Hypothesis K_asan_memset : Forall (fun c => In c (bt_consts bt)) (amset_cells both_amset_tab).
  Hypothesis K_memcpy_icpt : Forall (fun c => In c (bt_consts bt)) (xmcpy_cells both_xmcpy_tab).
  Hypothesis K_asan_memcpy : Forall (fun c => In c (bt_consts bt)) (amcpy_cells both_amcpy_tab).
  Hypothesis K_memmove_icpt : Forall (fun c => In c (bt_consts bt)) (xmmove_cells both_xmmove_tab).
  Hypothesis K_asan_memmove : Forall (fun c => In c (bt_consts bt)) (ammove_cells both_ammove_tab).
  Hypothesis K_strlen_icpt : Forall (fun c => In c (bt_consts bt)) (xstrlen_cells both_xstrlen_tab).

  Theorem C_memset_icpt_bt : MEMSET_AT BSEGS FXOK both_addrs AAINVH (ia_memset_icpt both_addrs).
  Proof using K_memset_icpt BT_FS BT_SEGS BT_IA. exact (C_memset_icpt_B FXOK AAINVH (bt_fs bt) HP_bt BT_FS (CELLS_bt _ K_memset_icpt)). Qed.
  Theorem C_asan_memset_bt : MEMSET_AT BSEGS FXOK both_addrs AAINVH (ia_asan_memset both_addrs).
  Proof using K_asan_memset BT_FS BT_SEGS BT_IA. exact (C_asan_memset_B FXOK AAINVH (bt_fs bt) HP_bt BT_FS (CELLS_bt _ K_asan_memset)). Qed.
  Theorem C_memcpy_icpt_bt : MEMCPY_AT BSEGS FXOK both_addrs AAINVH (ia_memcpy_icpt both_addrs).
  Proof using K_memcpy_icpt BT_FS BT_SEGS BT_IA. exact (C_memcpy_icpt_B FXOK AAINVH (bt_fs bt) HP_bt BT_FS (CELLS_bt _ K_memcpy_icpt)). Qed.
  Theorem C_asan_memcpy_bt : MEMCPY_AT BSEGS FXOK both_addrs AAINVH (ia_asan_memcpy both_addrs).
  Proof using K_asan_memcpy BT_FS BT_SEGS BT_IA. exact (C_asan_memcpy_B FXOK AAINVH (bt_fs bt) HP_bt BT_FS (CELLS_bt _ K_asan_memcpy)). Qed.
  Theorem C_memmove_icpt_bt : MEMMOVE_AT BSEGS FXOK both_addrs AAINVH (ia_memmove_icpt both_addrs).
  Proof using K_memmove_icpt BT_FS BT_SEGS BT_IA. exact (C_memmove_icpt_B FXOK AAINVH (bt_fs bt) HP_bt BT_FS (CELLS_bt _ K_memmove_icpt)). Qed.
  Theorem C_asan_memmove_bt : MEMMOVE_AT BSEGS FXOK both_addrs AAINVH (ia_asan_memmove both_addrs).
  Proof using K_asan_memmove BT_FS BT_SEGS BT_IA. exact (C_asan_memmove_B FXOK AAINVH (bt_fs bt) HP_bt BT_FS (CELLS_bt _ K_asan_memmove)). Qed.
  Theorem C_strlen_icpt_bt : STRLEN_AT BSEGS FXOK both_addrs AAINVH (ia_strlen_icpt both_addrs).
  Proof using K_strlen_icpt BT_FS BT_SEGS BT_IA. exact (C_strlen_icpt_B FXOK AAINVH (bt_fs bt) HP_bt BT_FS (CELLS_bt _ K_strlen_icpt)). Qed.

  Hypothesis K_annotate : Forall (fun c => In c (bt_consts bt))
     (ann_cellsL both_poison_tab both_m2s_tab_6fac4 both_ann_g_flags both_ann_p_flags both_ann_g_verb both_ann_p_verb both_ann_g_shoff both_ann_p_shoff).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma FS_NOLAZY_bt : forall st Lc FF M mdl z,
    WF bt st Lc FF -> Rep bt st Lc FF M mdl -> bt_fs bt + 0x1000 <= z < bt_fs bt + 0x9000 -> lzb mdl z = false.
  Proof using. exact (AsRtStkLift.AsAinvFacts3b.FS_NOLAZY bt). Qed.
  Lemma FS_PRIV_bt : forall st Lc FF z,
    WF bt st Lc FF -> bt_fs bt + 0x1000 <= z < bt_fs bt + 0x9000 -> rt_priv both_addrs Lc FF z.
  Proof using BT_IA. intros st Lc FF z W Hz. rewrite <- BT_IA. exact (AsRtStkLift.AsAinvFacts3b.FS_PRIV bt st Lc FF z W Hz). Qed.
  Lemma HOFF_bt : forall h Lc FF B C K M mdl AA, AAINVH h Lc FF B C K M mdl -> H_off_segments BSEGS (HL mdl AA).
  Proof using BT_SEGS BT_IA. intros h Lc FF B C K M mdl AA AI. exact (HL_off_segments BSEGS both_addrs (AAINVH h) (bt_fs bt) (HP_bt h) both_segs_hull Lc FF B C K M mdl AA AI). Qed.
  Theorem C_fakerel_bt_B : forall {fx : FPState}, FAKEREL BSEGS FXOK both_addrs AAINVH.
  Proof using BT_SEGS BT_IA.
    intros fx. pose proof (@C_fakerel_P RC FXOK bt (fun h => holes_le h)) as X. rewrite BT_SEGS, BT_IA in X.
    exact (X both_segs_wx HOFF_bt FS_NOLAZY_bt FS_PRIV_bt fx).
  Qed.
End BT.
End BoIcptInstBt.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsIfaceNM3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFFam OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOomCell3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys10 OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtXStrlenI OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtStkLift. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsK OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsIfaceNM3.AsIfacePR3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsIfaceNM3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinv3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinvGeom3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvHole3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFFam.AsAinvHS3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOomCell3.BoAinvBoot3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys10.AsAinvBootF3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFFam.AsAinvPrist3 AsRtImg BoRtAMemsetI BoRtXMemsetI BoRtAMemcpyI BoRtXMemcpyI BoRtAMemmoveI BoRtXMemmoveI OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtXStrlenI OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtStkLift.AsIcptMemset OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtStkLift.AsIcptXMemset OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtStkLift.AsIcptMemcpy OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtStkLift.AsIcptXMemcpy OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtStkLift.AsIcptMemmove OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtStkLift.AsIcptXMemmove OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtStkLift.AsIcptStrlen BoIcptInstBt BoIcptInstBtS BoRtStkLiftI BoIcptMemsetI BoIcptXMemsetI BoIcptMemcpyI BoIcptXMemcpyI BoIcptMemmoveI BoIcptXMemmoveI BoIcptStrlenI AsContractsAtB.
From OSSVerify.glaze.binary_reflection.images Require Import AsanUbsan.
Import ListNotations.
Open Scope Z_scope.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section N.
  Context {RC : run_ceil}.
  Variable FXOK : FPState -> Prop.
  Variable hv : bvars.
  #[local] Notation bt := (both_bt hv).
  Hypothesis BF : boot_facts bt.

  (* [comment removed for export] *)
  Hypothesis W_MALLOC : MALLOC_KATW BSEGS FXOK both_addrs (AAINV_HS bt) MSTK_A (ia_malloc both_addrs) true.
  Hypothesis W_MALLOC_THUNK : MALLOC_KATW BSEGS FXOK both_addrs (AAINV_HS bt) MSTK_A (ia_malloc_thunk both_addrs) true.
  Hypothesis W_MALLOC_ALT : MALLOC_ALT BSEGS FXOK both_addrs (AAINV_HS bt) (FRESH_bt bt) MSTK_A (ia_malloc both_addrs) true.
  Hypothesis W_MALLOC_ALT_THUNK : MALLOC_ALT BSEGS FXOK both_addrs (AAINV_HS bt) (FRESH_bt bt) MSTK_A (ia_malloc_thunk both_addrs) true.
  (* [comment removed for export] *)
  Hypothesis W_FREE : FREE_KAT BSEGS FXOK both_addrs (AAINV_H bt) MSTK_A (ia_free both_addrs).
  Hypothesis W_FREE_THUNK : FREE_KAT BSEGS FXOK both_addrs (AAINV_H bt) MSTK_A (ia_free_thunk both_addrs).
  Hypothesis W_OPDEL : FREE_KAT BSEGS FXOK both_addrs (AAINV_H bt) MSTK_A (ia_opdel both_addrs).
  Hypothesis W_OPDEL_SZ : FREE_KAT BSEGS FXOK both_addrs (AAINV_H bt) MSTK_A (ia_opdel_sz both_addrs).

  (* [comment removed for export] *)
  Lemma free_n_of_weak : forall entry, FREE_KAT BSEGS FXOK both_addrs (AAINV_H bt) MSTK_A entry -> FREE_KAT_N BSEGS FXOK both_addrs (AAINV_HS bt) MSTK_A entry.
  Proof. intros entry FK fx R M mdl Lc Lc' FF B C K B' C' K' ret sp p PRE. exact (FK None fx R M mdl Lc Lc' FF B C K B' C' K' ret sp p PRE). Qed.

  Theorem ASCN_B_at : as_contracts_n BSEGS FXOK (bt_ia bt) (AAINV_HS bt) (FRESH_bt bt) (bt_fs bt).
  Proof.
    change (bt_ia bt) with both_addrs.
    exact (@ASCN BSEGS RC FXOK both_addrs (AAINV_HS bt) (FRESH_bt bt) (bt_fs bt)
             (AAINV_HS_weaken bt) W_MALLOC W_MALLOC_THUNK W_MALLOC_ALT W_MALLOC_ALT_THUNK
             (free_n_of_weak _ W_FREE) (free_n_of_weak _ W_FREE_THUNK) (free_n_of_weak _ W_OPDEL) (free_n_of_weak _ W_OPDEL_SZ)
             (@C_stkmal_bts_B RC FXOK bt eq_refl eq_refl eq_refl eq_refl (K_stkmal_at hv))
             (fun h pc rs fx => @C_fakerel_bts_B RC FXOK bt eq_refl eq_refl fx h pc rs fx)
             (C_memcpy_icpt_bts_B FXOK bt eq_refl eq_refl (BT_FS_at hv BF) (K_memcpy_icpt_at hv)) (C_asan_memcpy_bts_B FXOK bt eq_refl eq_refl (BT_FS_at hv BF) (K_asan_memcpy_at hv))
             (C_memset_icpt_bts_B FXOK bt eq_refl eq_refl (BT_FS_at hv BF) (K_memset_icpt_at hv)) (C_asan_memset_bts_B FXOK bt eq_refl eq_refl (BT_FS_at hv BF) (K_asan_memset_at hv))
             (C_memmove_icpt_bts_B FXOK bt eq_refl eq_refl (BT_FS_at hv BF) (K_memmove_icpt_at hv)) (C_asan_memmove_bts_B FXOK bt eq_refl eq_refl (BT_FS_at hv BF) (K_asan_memmove_at hv))
             (C_strlen_icpt_bts_B FXOK bt eq_refl eq_refl (BT_FS_at hv BF) (K_strlen_icpt_at hv))).
  Qed.

  Theorem ASCNM_B_at : as_contracts_nm BSEGS FXOK (bt_ia bt) (AAINV_H bt) (bt_fs bt).
  Proof.
    change (bt_ia bt) with both_addrs.
    exact (@ASCNM BSEGS RC FXOK both_addrs (AAINV_H bt) (bt_fs bt)
             W_FREE W_FREE_THUNK W_OPDEL W_OPDEL_SZ
             (@C_stkmal_bt_B RC FXOK bt eq_refl eq_refl eq_refl eq_refl (K_stkmal_at hv))
             (fun h pc rs fx => @BoIcptInstBt.C_fakerel_bt_B RC FXOK bt eq_refl eq_refl fx h pc rs fx)
             (BoIcptInstBt.C_memcpy_icpt_bt FXOK bt eq_refl eq_refl (BT_FS_at hv BF) (K_memcpy_icpt_at hv)) (BoIcptInstBt.C_asan_memcpy_bt FXOK bt eq_refl eq_refl (BT_FS_at hv BF) (K_asan_memcpy_at hv))
             (BoIcptInstBt.C_memset_icpt_bt FXOK bt eq_refl eq_refl (BT_FS_at hv BF) (K_memset_icpt_at hv)) (BoIcptInstBt.C_asan_memset_bt FXOK bt eq_refl eq_refl (BT_FS_at hv BF) (K_asan_memset_at hv))
             (BoIcptInstBt.C_memmove_icpt_bt FXOK bt eq_refl eq_refl (BT_FS_at hv BF) (K_memmove_icpt_at hv)) (BoIcptInstBt.C_asan_memmove_bt FXOK bt eq_refl eq_refl (BT_FS_at hv BF) (K_asan_memmove_at hv))
             (BoIcptInstBt.C_strlen_icpt_bt FXOK bt eq_refl eq_refl (BT_FS_at hv BF) (K_strlen_icpt_at hv))).
  Qed.
End N.
