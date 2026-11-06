(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
Import ListNotations.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_AsanHexScan () : Init.string Init.list := ["Corelib.Strings.PrimString.string"; "Corelib.Init.Datatypes.nat"; "Corelib.Numbers.BinNums.N"; "Corelib.Init.Logic.eq"; "Corelib.Init.Datatypes.bool"; "scanN"; "Corelib.Init.Datatypes.true"; "Stdlib.NArith.BinNat.N.lt"; "Corelib.Init.Logic.not"; "Corelib.Init.Datatypes.option"; "stdpp.bitvector.definitions.bv"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.hex_byte_at"; "Stdlib.NArith.BinNat.N.add"; "Corelib.Init.Datatypes.None"; "Stdlib.NArith.BinNat.N.le"; "Stdlib.ZArith.BinInt.Z.to_N"; "Stdlib.ZArith.BinInt.Z.div"; "Corelib.Numbers.Cyclic.Int63.Uint63Axioms.to_Z"; "Corelib.Strings.PrimString.length"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.of_N"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.segment_byte_at"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.nil"].


Definition byte_ok (s : PrimString.string) (off : N) : bool :=
  match hex_byte_at s off with Some _ => true | None => false end.

(* [comment removed for export] *)
Fixpoint scanN (s : PrimString.string) (fuel : nat) (base n : N) : bool :=
  match fuel with
  | O => N.eqb n 0
  | S f =>
      if N.eqb n 0 then true
      else if N.eqb n 1 then byte_ok s base
      else let h := N.div2 n in (scanN s f base h && scanN s f (base + h) (n - h))%bool
  end.

Lemma scanN_sound : ltac2:(CDefT.buildp (gd_tbl_AsanHexScan ()) "Ps,$0.Pfuel,$1.Pbase,$2.Pn,$2.P,(3.$4.(5.R4.R3.R2.R1.)$6.)Pi,$2.P,(7.R1.R3.)(8.(3.(9.(:.&8.))(;.R7.(<.R5.R2.))(=.(:.&8.))))")
(* [comment removed for export] *).
Proof.
  intros s fuel. induction fuel as [|f IH]; intros base n H i Hi; cbn [scanN] in H.
  - apply N.eqb_eq in H. lia.
  - destruct (N.eqb_spec n 0) as [E0|Hn0]; [lia|].
    destruct (N.eqb_spec n 1) as [E1|Hn1].
    + subst n. replace i with 0%N by lia. rewrite N.add_0_r. unfold byte_ok in H.
      destruct (hex_byte_at s base); [discriminate|discriminate].
    + apply andb_prop in H as [H1 H2].
      rewrite N.div2_div in *.
      set (h := (n / 2)%N) in *.
      destruct (N.lt_ge_cases i h) as [Hl|Hge].
      * exact (IH _ _ H1 i Hl).
      * specialize (IH _ _ H2 (i - h)%N ltac:(lia)).
        replace (base + h + (i - h))%N with (base + i)%N in IH by lia. exact IH.
Qed.

(* [comment removed for export] *)
Lemma segment_byte_at_some1 : ltac2:(CDefT.buildp (gd_tbl_AsanHexScan ()) "Ps,$0.Pn,$2.Poff,$2.P,(3.$4.(5.R3.#40.~R2.)$6.)P,(>.R3.(?.(10.(11.(12.R4.))+2.)))P,(13.(14.R3.)(14.R4.))(8.(3.(9.(:.&8.))(15.(16.$0.R6.(17.$0.))R4.)(=.(:.&8.))))")
(* [comment removed for export] *).
Proof.
  intros s n off Hs Hn Hoff. cbn [segment_byte_at].
  replace (off <? Z.to_N (Uint63.to_Z (PrimString.length s) / 2))%N with true
    by (symmetry; apply N.ltb_lt; lia).
  exact (scanN_sound s 64 0 n Hs off ltac:(lia)).
Qed.
