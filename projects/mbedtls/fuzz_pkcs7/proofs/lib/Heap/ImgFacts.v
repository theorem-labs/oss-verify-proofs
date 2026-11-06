(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
(* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_ImgFacts () : Init.string Init.list := ["Corelib.Init.Datatypes.list"; "LinuxProcessSemantics.LinuxProcessSem.MemImageType.Segment"; "Corelib.Numbers.BinNums.Z"; "Corelib.Lists.ListDef.Forall"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Logic.or"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.add"; "Corelib.Init.Datatypes.fst"; "Corelib.Init.Datatypes.snd"; "seg_ivs"; "Corelib.Init.Logic.eq"; "Corelib.Init.Datatypes.option"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.find_segment"; "Corelib.Init.Datatypes.None"; "Corelib.Init.Logic.and"].


Definition seg_ivs (segs : list Segment) : list (Z * Z) :=
  map (fun s => (Z.of_N (seg_base s), Z.of_N (seg_size s))) segs.

Lemma find_segment_none_of_bounds : ltac2:(CDefT.buildp (gd_tbl_ImgFacts ()) "Psegs,(0.$1.)Pz,$2.Pn,$2.P,(3.(4.$2.$2.)Lbs,(4.$2.$2.)(5.(6.(7.R3.R2.)(8.$2.$2.R1.))(6.(7.(8.$2.$2.R1.)(9.$2.$2.R1.))R3.))(:.R3.))P,(6.+1.R2.)(;.(<.$1.)(=.R5.R4.R3.)(>.$1.))")
(* [comment removed for export] *).
Proof.
  induction segs as [|s segs IH]; intros z n HF Hn; [reflexivity|].
  cbn [seg_ivs map] in HF. inversion HF as [|bs l Hs HF']; subst. cbn [fst snd] in Hs.
  cbn [find_segment].
  destruct (Z.leb_spec0 (Z.of_N (seg_base s)) z); destruct (Z.leb_spec0 (z + n) (Z.of_N (seg_base s) + Z.of_N (seg_size s))); cbn [andb];
    try (apply IH; assumption). exfalso. lia.
Qed.

(* [comment removed for export] *)
Lemma find_segment_none_window : ltac2:(CDefT.buildp (gd_tbl_ImgFacts ()) "Psegs,(0.$1.)Plo,$2.Phi,$2.Pz,$2.Pn,$2.P,(3.(4.$2.$2.)Lbs,(4.$2.$2.)(?.(6.R5.(8.$2.$2.R1.))(6.(7.(8.$2.$2.R1.)(9.$2.$2.R1.))R4.))(:.R5.))P,(6.+1.R2.)P,(5.(6.(7.R4.R3.)R6.)(6.R5.R4.))(;.(<.$1.)(=.R8.R5.R4.)(>.$1.))")
(* [comment removed for export] *).
Proof.
  intros segs lo hi z n HF Hn Hz. apply find_segment_none_of_bounds; [|exact Hn].
  eapply Forall_impl; [|exact HF]. cbn. intros [b s] [H1 H2]. cbn in *. lia.
Qed.
