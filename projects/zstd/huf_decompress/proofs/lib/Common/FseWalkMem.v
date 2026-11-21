(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (7 recorded proofs replaced by written proofs (map_upd_nat, nth_error_map_Znth, Forall_Znth and 4 more)). *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import FseNCount FseLemmas.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Walk.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import STRW_tac FseWalkKit.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_FseWalkMem () := "C47Corelib5Lists7ListDef3mapC47Corelib4Init5Logic8eq_ind_rC59OSSVerify5KrLib3Lib3Arr3updC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List8map_consI47Corelib4Init9Datatypes4list00K47Corelib4Init9Datatypes4list01K47Corelib4Init5Logic2eq01K47Corelib4Init9Datatypes3nat02K47Corelib4Init9Datatypes4list02I47Corelib4Init5Logic2eq00C47Corelib4Init9Datatypes8list_indC59OSSVerify5KrLib4Spec9FseNCount7upd_natC1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1Z00I47Corelib4Init9Datatypes3nat00K47Corelib4Init9Datatypes3nat01C46Stdlib5Lists4List9nth_errorC46Stdlib5Lists4List=nth_error_mapC56Stdlib6ZArith6BinInt1Z2leC47Corelib4Init9Datatypes6lengthC56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00I47Corelib4Init9Datatypes6option00C56Stdlib6ZArith6BinInt1Z6to_natC47Corelib4Init9Datatypes:option_mapC47Corelib5Lists7ListDef3nthK47Corelib4Init9Datatypes6option01C47Corelib4Init5Peano2ltC56Stdlib6ZArith6BinInt1Z3maxC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC56Stdlib6ZArith6BinInt1Z8max_specI47Corelib4Init5Logic2or00K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K47Corelib7Numbers7BinNums8positive01K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega5Tauto8GFormula06K47Corelib4Init9Datatypes6option02K47Corelib7Numbers7BinNums8positive02C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC46Stdlib9micromega;ZifyClasses;rew_iff_revC46Stdlib5Lists4List>nth_error_nth'C59OSSVerify5KrLib4Spec9FseNCount4ZnthC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses5mkrelK46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC56Stdlib6ZArith4Znat5Nat2Z6inj_ltC46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K47Corelib7Numbers7BinNums1Z01I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega:ZMicromega;ZArithProof01K47Corelib7Numbers7BinNums8positive03K46Stdlib9micromega=RingMicromega3Op201K46Stdlib9micromega=RingMicromega3Op203K46Stdlib9micromega=RingMicromega3Op205I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I47Corelib5Lists7ListDef6Forall00C46Stdlib5Lists4List2InC46Stdlib5Lists4List=Forall_forallC46Stdlib5Lists4List6nth_InC47Corelib4Init5Logic5proj1K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C45stdpp9bitvector;definitions7Z_to_bvC59OSSVerify5KrLib3Lib3Arr5u8arrC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z3addC59OSSVerify5KrLib3Lib3Mem2waC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics<write_to_memC59OSSVerify5KrLib4Spec9FseNCount4ZupdC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem<Z_to_bv8_modC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List:length_mapC59OSSVerify5KrLib3Lib3Arr;u8arr_writeC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_indc59OSSVerify5KrLib6Common:FseWalkMem;map_upd_natC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem3le1C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common:FseWalkKit7le1_litC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common:FseWalkKit4u16sC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem8bytes_atC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3mulC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=ov_read_bytesC59OSSVerify5KrLib3Lib3Mem3le2C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Common:FseWalkMemBnth_error_map_ZnthC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common:FseWalkKit:u16ro_readC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z03C45stdpp9bitvector;definitions;bv_unsignedC45stdpp9bitvector;definitions8bv_swrapC45stdpp9bitvector;definitions7bv_wrapC56Stdlib6ZArith6BinInt1Z3subC56Stdlib6ZArith6BinInt1Z7div_modC47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extC56Stdlib6ZArith6BinInt1Z7compareK46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega:ZMicromega;ZArithProof03K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega7EnvRing5PExpr04C59OSSVerify5KrLib6Common:FseWalkKit:swrap16_eqC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions@Z_to_bv_unsignedC35stdpp7tactics<f_equal_helpC59OSSVerify5KrLib3Lib3Mem4sx16C1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula07I47Corelib4Init9Datatypes:comparison00I47Corelib4Init5Logic5False00C56Stdlib6ZArith6BinInt1Z3powC59OSSVerify5KrLib3Lib3Mem4zx16C1?~~~~~~~~~~~~~~~".
Import ListNotations.
Open Scope Z_scope.

Lemma map_upd_nat : forall {X} (f : Z -> X) n v l, map f (upd_nat n v l) = upd (map f l) n (f v).
Proof. intros X f n v l. revert n. induction l as [|a l IH]; intros [|n]; cbn; try reflexivity. rewrite IH. reflexivity. Qed.

Lemma nth_error_map_Znth : forall {X} (f : Z -> X) (l : list Z) i, 0 <= i < Z.of_nat (length l) ->
  nth_error (map f l) (Z.to_nat i) = Some (f (Znth i l)).
Proof.
  intros X f l i Hi. unfold Znth. rewrite nth_error_map.
  rewrite (nth_error_nth' l 0) by lia. reflexivity.
Qed.

Lemma Forall_Znth : forall (P : Z -> Prop) (l : list Z) i, Forall P l -> 0 <= i < Z.of_nat (length l) -> P (Znth i l).
Proof. intros P l i H Hi. unfold Znth. apply (proj1 (Forall_forall _ _) H). apply nth_In. lia. Qed.

Section Mem.
Variable segs : list Segment.

Lemma u8arr_sb : forall m A (buf : list Z) i x v,
  u8arr segs m A (map (Z_to_bv 8) buf) -> 0 <= i < Z.of_nat (length buf) -> x mod 256 = v mod 256 ->
  u8arr segs (write_to_mem m (wa (A + i)) (le1 (Z_to_bv 64 x))) A (map (Z_to_bv 8) (Zupd i v buf)).
Proof.
  intros m A buf i x v ARR Hi E. rewrite le1_lit.
  unfold Zupd. rewrite map_upd_nat.
  replace (Z_to_bv 8 v) with (Z_to_bv 8 x) by (apply Z_to_bv8_mod; exact E).
  apply u8arr_write; [exact ARR| rewrite length_map; exact Hi].
Qed.

(* [comment removed for export] *)
Lemma u16_znth : forall m A (nc : list Z) i a,
  bytes_at segs m A (u16s (map (Z_to_bv 64) nc)) -> 0 <= i < Z.of_nat (length nc) -> a = wa (A + 2 * i) ->
  ov_read_bytes segs m a 2 = Some (le2 (Z_to_bv 64 (Znth i nc))).
Proof.
  intros m A nc i a NCB Hi ->. eapply (u16ro_read segs m A _ i); [exact NCB| | lia | reflexivity].
  apply nth_error_map_Znth. exact Hi.
Qed.
End Mem.

(* [comment removed for export] *)
Lemma sx16_short : forall c, - 32768 <= c < 32768 -> sx16 (Z_to_bv 64 c) = Z_to_bv 64 c.
Proof.
  intros c Hc. unfold sx16. f_equal. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with 18446744073709551616.
  rewrite swrap16_eq. Z.div_mod_to_equations. lia.
Qed.
Lemma zx16_short : forall c, - 32768 <= c < 32768 -> zx16 (Z_to_bv 64 c) = Z_to_bv 64 (c mod 65536).
Proof.
  intros c Hc. unfold zx16. f_equal. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with 18446744073709551616.
  change (2^16) with 65536. Z.div_mod_to_equations. lia.
Qed.

(* [comment removed for export] *)
Ltac u8_sok ARR i :=
  lazymatch type of ARR with u8arr ?segs ?mx ?A ?bs =>
    let a := cur_mem_addr in
    pose proof (u8arr_store_ok segs mx A bs i a ARR ltac:(rewrite ?length_map, ?Zupd_length; lia) ltac:(unfold wa; f_equal; lia)) as SOK
  end.
(* [comment removed for export] *)
Ltac u8_store ARR i v :=
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mx ?a (le1 (Z_to_bv 64 ?x))) _) =>
    lazymatch type of ARR with u8arr ?segs mx ?A (map (Z_to_bv 8) ?buf) =>
      let E := addr_expr a in
      let ARR' := fresh "ARR" in
      assert (ARR' : u8arr segs (write_to_mem mx (wa E) (le1 (Z_to_bv 64 x))) A (map (Z_to_bv 8) (Zupd i v buf)));
      [ replace (wa E) with (wa (A + i)) by (unfold wa; f_equal; lia);
        apply (u8arr_sb segs mx A buf i x v ARR); [ rewrite ?Zupd_length; lia | ]
      | clear ARR; store_done; rename ARR' into ARR ]
    end
  end.
