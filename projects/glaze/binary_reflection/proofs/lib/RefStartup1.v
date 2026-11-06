(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
Require Stdlib.ZArith.ZArith Stdlib.Lists.List LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType OSSVerify.glaze.binary_reflection.images.Plain OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module RefImgCells.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import OSSVerify.glaze.binary_reflection.images.Plain.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
#[local] Existing Instance fx0.
Abbreviation SEGS := Plain.M.loaded_segments.

(* [comment removed for export] *)
Lemma img_10040_4 : rdn SEGS (fun _ => None) (Z_to_bv 64 65600) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 6)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_10050_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 65616) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 65600)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_10078_4 : rdn SEGS (fun _ => None) (Z_to_bv 64 65656) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 1)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_100b0_4 : rdn SEGS (fun _ => None) (Z_to_bv 64 65712) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 1)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_100e8_4 : rdn SEGS (fun _ => None) (Z_to_bv 64 65768) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 1)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_10120_4 : rdn SEGS (fun _ => None) (Z_to_bv 64 65824) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 1)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_10158_4 : rdn SEGS (fun _ => None) (Z_to_bv 64 65880) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 1685382482)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_10190_4 : rdn SEGS (fun _ => None) (Z_to_bv 64 65936) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 1685382480)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_101c8_4 : rdn SEGS (fun _ => None) (Z_to_bv 64 65992) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 1685382481)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_101f0_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 66032) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_10200_4 : rdn SEGS (fun _ => None) (Z_to_bv 64 66048) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 4)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_10238_4 : rdn SEGS (fun _ => None) (Z_to_bv 64 66104) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 1879048195)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_71410_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 463968) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 189064)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_74568_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 476600) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_74570_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 476608) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 189324)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_74578_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 476616) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 397012)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_74580_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 476624) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 399144)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_74588_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 476632) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_74678_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 476872) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 549968)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_74680_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 476880) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 681896)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_74688_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 476888) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 681888)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_74690_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 476896) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 463976)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_74698_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 476904) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 463968)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_746a0_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 476912) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 681872)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_758f8_4 : rdn SEGS (fun _ => None) (Z_to_bv 64 481608) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 131072)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_75910_1 : rdn SEGS (fun _ => None) (Z_to_bv 64 481632) 1%nat = Some ([Z_to_bv 8 0]).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_86418_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 681272) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_86428_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 681288) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_86430_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 681296) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_867c8_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 681880) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_867f0_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 681920) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_86808_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 681944) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. vm_refl_bv. Qed.
Lemma img_745b8_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 476600) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. vm_refl_bv. Qed.
Lemma img_75948_4 : rdn SEGS (fun _ => None) (Z_to_bv 64 481608) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 131072)).
Proof. vm_refl_bv. Qed.
Lemma img_a6538_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 681272) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. vm_refl_bv. Qed.
Lemma img_a6548_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 681288) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. vm_refl_bv. Qed.
Lemma img_a6550_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 681296) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. vm_refl_bv. Qed.
Lemma img_a6798_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 681880) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. vm_refl_bv. Qed.
Lemma img_a67c0_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 681920) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. vm_refl_bv. Qed.
Lemma img_a67d8_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 681944) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. vm_refl_bv. Qed.
End RefImgCells.
Require Stdlib.micromega.Lia Stdlib.Bool.Bool LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run OSSVerify.Proofs.glaze.binary_reflection.lib.Common.SumsLib.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module RefStartupDefs.
(* [comment removed for export] *)
(* [comment removed for export] *)

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.glaze.binary_reflection.images.Plain.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.SumsLib.StartupTac OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.ArgvEnv OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.RefLayout.
Import ListNotations.
Open Scope bv_scope.

Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Existing Instance fx0.
Abbreviation RPH := Plain.M.phdrs.

(* [comment removed for export] *)
Fixpoint after_last_slash (s : list byte) (i acc : nat) : nat :=
  match s with
  | [] => acc
  | b :: s' => after_last_slash s' (S i) (if bv_eqb b (Z_to_bv 8 47) then S i else acc)
  end.
Definition progname_off (s : list byte) : nat := after_last_slash s 0 0.



Section Defs.
  Variable sp0 : word.
  Variables av ev : list (list byte).
  Variable uid : word.
  Variable hw : word.          (* [comment removed for export] *)
  Variable rdraw : EntryDraw.  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition aux_base : word := Z_to_bv 64 (bv_unsigned sp0 - 368).
  (* [comment removed for export] *)
  Definition argv_w : word := Z_to_bv 64 (bv_unsigned sp0 + 8).
  Definition envp_w : word := Z_to_bv 64 (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length av)).
  Definition auxv_w : word :=
    Z_to_bv 64 (bv_unsigned sp0 + 24 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev)).
  Definition argc_w : word := argcN av.
  (* [comment removed for export] *)
  Definition pn_w : word := cat_argv_ptr sp0 av ev 0.
  Definition progname_w : word :=
    Z_to_bv 64 (bv_unsigned pn_w + Z.of_nat (progname_off (nth 0 av []))).
  (* [comment removed for export] *)
  Definition rnd_w : word := at_random_ptr sp0 av ev.
  (* [comment removed for export] *)
  Definition rnd_bytes : list byte := at_random_bytes (ed_random rdraw).
  Definition rb (i : nat) : byte := nth i rnd_bytes (Z_to_bv 8 0).
  Definition canary_bytes : list byte := [rb 0; Z_to_bv 8 0; rb 2; rb 3; rb 4; rb 5; rb 6; rb 7].
  Definition canary_w : word := le_bytes_to_word canary_bytes.       (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition D_libc : word -> option byte :=
    wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (fun _ => None)
      (Z_to_bv 64 0x86450) (word_to_le_bytes 8 envp_w))          (* [comment removed for export] *)
      (Z_to_bv 64 0xa67b8) (word_to_le_bytes 8 auxv_w))          (* [comment removed for export] *)
      (Z_to_bv 64 0xa6818) (word_to_le_bytes 8 hw))             (* [comment removed for export] *)
      (Z_to_bv 64 0xa67e0) (word_to_le_bytes 8 (Z_to_bv 64 4096))) (* [comment removed for export] *)
      (Z_to_bv 64 0xa67a8) (word_to_le_bytes 8 pn_w))            (* [comment removed for export] *)
      (Z_to_bv 64 0xa67a0) (word_to_le_bytes 8 progname_w).      (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition J_lsm (J : word -> option byte) : word -> option byte :=
    wbytes (wbytes (wbytes (wbytes
    (wbytes (wbytes (wbytes (wbytes J
      (Z_to_bv 64 (bv_unsigned sp0 - 8)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
      (Z_to_bv 64 (bv_unsigned sp0 - 16)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
      (Z_to_bv 64 (bv_unsigned sp0 - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
      (Z_to_bv 64 (bv_unsigned sp0 - 32)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
      (Z_to_bv 64 (bv_unsigned sp0 - 40)) (word_to_le_bytes 8 (Z_to_bv 64 0x61184)))
      (Z_to_bv 64 (bv_unsigned sp0 - 48)) (word_to_le_bytes 8 argv_w))
      (Z_to_bv 64 (bv_unsigned sp0 - 56)) (word_to_le_bytes 8 argc_w))
      (Z_to_bv 64 (bv_unsigned sp0 - 64)) (word_to_le_bytes 8 (Z_to_bv 64 0x2e38c)).

  (* [comment removed for export] *)
  Definition J_aux (Jf : word -> option byte) : word -> option byte :=
    wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes
      (wbytes Jf aux_base (zeros 304))
      (Z_to_bv 64 (bv_unsigned sp0 - 344)) (word_to_le_bytes 8 (Z_to_bv 64 0x10040)))  (* [comment removed for export] *)
      (Z_to_bv 64 (bv_unsigned sp0 - 336)) (word_to_le_bytes 8 (Z_to_bv 64 56)))       (* [comment removed for export] *)
      (Z_to_bv 64 (bv_unsigned sp0 - 328)) (word_to_le_bytes 8 (Z_to_bv 64 10)))       (* [comment removed for export] *)
      (Z_to_bv 64 (bv_unsigned sp0 - 240)) (word_to_le_bytes 8 hw))                   (* [comment removed for export] *)
      (Z_to_bv 64 (bv_unsigned sp0 - 320)) (word_to_le_bytes 8 (Z_to_bv 64 4096)))     (* [comment removed for export] *)
      (Z_to_bv 64 (bv_unsigned sp0 - 280)) (word_to_le_bytes 8 uid))                  (* [comment removed for export] *)
      (Z_to_bv 64 (bv_unsigned sp0 - 272)) (word_to_le_bytes 8 uid))                  (* [comment removed for export] *)
      (Z_to_bv 64 (bv_unsigned sp0 - 184)) (word_to_le_bytes 8 (Z_to_bv 64 0)))        (* [comment removed for export] *)
      (Z_to_bv 64 (bv_unsigned sp0 - 168)) (word_to_le_bytes 8 rnd_w).                  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition D_tlsA (D : word -> option byte) : word -> option byte :=
    wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes D
      (Z_to_bv 64 0xa6548) (word_to_le_bytes 8 (Z_to_bv 64 0)))        (* [comment removed for export] *)
      (Z_to_bv 64 0xa6558) (word_to_le_bytes 8 (Z_to_bv 64 0)))        (* [comment removed for export] *)
      (Z_to_bv 64 0xa6550) (word_to_le_bytes 8 (Z_to_bv 64 8)))        (* [comment removed for export] *)
      (Z_to_bv 64 0xa67c8) (word_to_le_bytes 8 (Z_to_bv 64 0xe0)))     (* [comment removed for export] *)
      (Z_to_bv 64 0xa67d0) (word_to_le_bytes 8 (Z_to_bv 64 8)))        (* [comment removed for export] *)
      (Z_to_bv 64 0x86530) (word_to_le_bytes 8 (Z_to_bv 64 0)))        (* [comment removed for export] *)
      (Z_to_bv 64 0x86518) (word_to_le_bytes 8 (Z_to_bv 64 0x86530)))  (* [comment removed for export] *)
      (Z_to_bv 64 0x86458) (word_to_le_bytes 8 (Z_to_bv 64 0x86458)))  (* [comment removed for export] *)
      (Z_to_bv 64 0xa67b0) [Z_to_bv 8 1])                              (* [comment removed for export] *)
      (Z_to_bv 64 0x86480) (word_to_le_bytes 4 (Z_to_bv 64 2)).        (* [comment removed for export] *)

  Definition D_tlsB (tid : word) (D : word -> option byte) : word -> option byte :=
    wbytes (wbytes (wbytes (wbytes (wbytes (wbytes D
      (Z_to_bv 64 0x86478) (word_to_le_bytes 4 tid))                   (* [comment removed for export] *)
      (Z_to_bv 64 0x864f0) (word_to_le_bytes 8 (Z_to_bv 64 0xa67e8)))  (* [comment removed for export] *)
      (Z_to_bv 64 0x864d0) (word_to_le_bytes 8 (Z_to_bv 64 0x864d0)))  (* [comment removed for export] *)
      (Z_to_bv 64 0x86460) (word_to_le_bytes 8 (Z_to_bv 64 0x86458)))  (* [comment removed for export] *)
      (Z_to_bv 64 0x86468) (word_to_le_bytes 8 (Z_to_bv 64 0x86458)))  (* [comment removed for export] *)
      (Z_to_bv 64 0x86470) (word_to_le_bytes 8 (Z_to_bv 64 0)).        (* [comment removed for export] *)

  Definition D_tls (tid : word) (D : word -> option byte) : word -> option byte :=
    D_tlsB tid (D_tlsA D).

  (* [comment removed for export] *)
  Definition J_tls (J : word -> option byte) (ra s0 s1 s2 s3 s4 s5 : word) : word -> option byte :=
    wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes J
      (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 ra))
      (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 s0))
      (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1))
      (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 s2))
      (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 s3))
      (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 s4))
      (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 s5).

  (* [comment removed for export] *)
  Definition D_ssp (D : word -> option byte) : word -> option byte :=
    wbytes (wbytes (wbytes (wbytes D
      (Z_to_bv 64 0xa6790) [rb 0; rb 1; rb 2; rb 3])           (* [comment removed for export] *)
      (Z_to_bv 64 0xa6794) [rb 4; rb 5; rb 6; rb 7])           (* [comment removed for export] *)
      (Z_to_bv 64 0xa6791) [Z_to_bv 8 0])                        (* [comment removed for export] *)
      (Z_to_bv 64 0x86510) (word_to_le_bytes 8 canary_w).        (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition D_fd (D : word -> option byte) : word -> option byte :=
    wbytes D (Z_to_bv 64 0x75960) [Z_to_bv 8 1].

  (* [comment removed for export] *)
  Definition D_main (tid : word) : word -> option byte := D_fd (D_ssp (D_tls tid D_libc)).

End Defs.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Notation rnd_lo4 r := ([rb r 0; rb r 1; rb r 2; rb r 3]) (only parsing).
Notation rnd_hi4 r := ([rb r 4; rb r 5; rb r 6; rb r 7]) (only parsing).

Lemma length_rnd_lo4 : forall rdraw, length (rnd_lo4 rdraw) = 4%nat.
Proof. intros. reflexivity. Qed.
Lemma length_rnd_hi4 : forall rdraw, length (rnd_hi4 rdraw) = 4%nat.
Proof. intros. reflexivity. Qed.


(* [comment removed for export] *)
Lemma rnd_lo4_eq : forall rdraw, firstn 4 (skipn 0 (rnd_bytes rdraw)) = rnd_lo4 rdraw.
Proof. intros. reflexivity. Qed.
Lemma rnd_hi4_eq : forall rdraw, firstn 4 (skipn 4 (rnd_bytes rdraw)) = rnd_hi4 rdraw.
Proof. intros. reflexivity. Qed.

(* [comment removed for export] *)
Lemma u_lez8 : forall l, length l = 8%nat -> bv_unsigned (Z_to_bv 64 (bytes_le_to_Z l)) = bytes_le_to_Z l.
Proof.
  intros l H. pose proof (bytes_le_to_Z_nonneg l). pose proof (bytes_le_to_Z_bound l) as B.
  rewrite H in B. change (2 ^ (8 * Z.of_nat 8))%Z with (2^64)%Z in B. apply u_Z2bv; lia.
Qed.

Lemma canary_w_val : forall rdraw, bytes_le_to_Z (canary_bytes rdraw) = bv_unsigned (canary_w rdraw).
Proof. intros. unfold canary_w, le_bytes_to_word. symmetry. apply u_lez8. reflexivity. Qed.

(* [comment removed for export] *)
Lemma rdn_pointwise8 : forall segs (m : word -> option byte) (a : Z) c0 c1 c2 c3 c4 c5 c6 c7,
  (0 <= a)%Z -> (a + 8 <= 2^64)%Z ->
  m (Z_to_bv 64 a) = Some c0 -> m (Z_to_bv 64 (a+1)) = Some c1 ->
  m (Z_to_bv 64 (a+2)) = Some c2 -> m (Z_to_bv 64 (a+3)) = Some c3 ->
  m (Z_to_bv 64 (a+4)) = Some c4 -> m (Z_to_bv 64 (a+5)) = Some c5 ->
  m (Z_to_bv 64 (a+6)) = Some c6 -> m (Z_to_bv 64 (a+7)) = Some c7 ->
  rdn segs m (Z_to_bv 64 a) 8 = Some [c0; c1; c2; c3; c4; c5; c6; c7].
Proof.
  intros segs m a c0 c1 c2 c3 c4 c5 c6 c7 Ha Hn H0 H1 H2 H3 H4 H5 H6 H7.
  assert (E : forall k, (0 <= k)%Z -> (a + k + 1 < 2^64)%Z -> (Z_to_bv 64 (a + k) + 1 = Z_to_bv 64 (a + k + 1))%bv).
  { intros k Hk Hk'. apply bv_eq. rewrite u_add1 by (rewrite u_Z2bv by lia; lia). rewrite !u_Z2bv by lia. reflexivity. }
  assert (E0 : (Z_to_bv 64 a + 1 = Z_to_bv 64 (a + 1))%bv).
  { apply bv_eq. rewrite u_add1 by (rewrite u_Z2bv by lia; lia). rewrite !u_Z2bv by lia. reflexivity. }
  cbn [rdn]. rewrite H0, E0.
  rewrite H1, (E 1%Z) by lia. replace (a+1+1)%Z with (a+2)%Z by lia.
  rewrite H2, (E 2%Z) by lia. replace (a+2+1)%Z with (a+3)%Z by lia.
  rewrite H3, (E 3%Z) by lia. replace (a+3+1)%Z with (a+4)%Z by lia.
  rewrite H4, (E 4%Z) by lia. replace (a+4+1)%Z with (a+5)%Z by lia.
  rewrite H5, (E 5%Z) by lia. replace (a+5+1)%Z with (a+6)%Z by lia.
  rewrite H6, (E 6%Z) by lia. replace (a+6+1)%Z with (a+7)%Z by lia.
  rewrite H7. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma rdn_guard_canary : forall segs rdraw (D : word -> option byte) (g : Z),
  (0 <= g)%Z -> (g + 8 <= 2^64)%Z ->
  rdn segs (wbytes (wbytes (wbytes D (Z_to_bv 64 g) (rnd_lo4 rdraw)) (Z_to_bv 64 (g + 4)) (rnd_hi4 rdraw))
              (Z_to_bv 64 (g + 1)) [Z_to_bv 8 0]) (Z_to_bv 64 g) 8
  = Some (canary_bytes rdraw).
Proof.
  intros segs rdraw D g Hg Hn. unfold canary_bytes.
  apply rdn_pointwise8; [exact Hg | exact Hn | ..];
    repeat (first [ rewrite wbytes_inside by (cbn [length]; rewrite ?u_Z2bv by lia; lia)
                  | rewrite wbytes_outside by (cbn [length]; rewrite ?u_Z2bv by lia; lia) ]);
    lazymatch goal with
    | |- Some (nth (Z.to_nat ?e) _ _) = _ =>
        first [ replace (Z.to_nat e) with 0%nat by (rewrite ?u_Z2bv by lia; lia)
              | replace (Z.to_nat e) with 1%nat by (rewrite ?u_Z2bv by lia; lia)
              | replace (Z.to_nat e) with 2%nat by (rewrite ?u_Z2bv by lia; lia)
              | replace (Z.to_nat e) with 3%nat by (rewrite ?u_Z2bv by lia; lia) ]
    | |- _ => idtac
    end; reflexivity.
Qed.
End RefStartupDefs.
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.glaze.binary_reflection.images Require Import Plain.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.SumsLib OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.RefCodeM0 OSSVerify.Proofs.glaze.binary_reflection.lib.RefCodeM2. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.SumsLib.StartupTac OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.ArgvEnv OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.RefLayout RefImgCells OSSVerify.Proofs.glaze.binary_reflection.lib.RefCodeM0 OSSVerify.Proofs.glaze.binary_reflection.lib.RefCodeM2.
Import ListNotations.
Open Scope bv_scope.

From OSSVerify.Proofs.glaze.binary_reflection.lib Require Import PropExec.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.SumsLib. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.SumsLib.PuPeel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Import PuStep.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac is_Z_lit ::= ps_is_Z_lit.   (* [comment removed for export] *)
#[local] Ltac check_closed_term_fast ::= ps_check_closed.
#[local] Ltac gres ::= pu_gres.
#[local] Ltac chain_step ::= pu_chain_step.   (* [comment removed for export] *)
#[local] Ltac vnorm ::= pu_vnorm.
#[local] Ltac step_simpl ::= pu_step_simpl.
#[local] Ltac peel ::= peel_fast.
#[local] Ltac SumsLib.StartupTac.addr_norm ::= addr_norm_fast.
#[local] Existing Instance fx0.
Abbreviation SEGS := Plain.M.loaded_segments.

(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Abbreviation RPH := Plain.M.phdrs.

(* [comment removed for export] *)
Definition regs_init (sp0 : word) : bvmap 5 word :=
  regupd (regupd bvmap_empty 10 (Z_to_bv 64 0)) 2 sp0.

Section P1.
  Variable sp0 : word.
  Variables av ev : list (list byte).
  Variable uid : word.
  Variable hw : word.
  Variable rdraw : EntryDraw.
  Hypothesis Hva : valid_argv av.
  Hypothesis Hve : valid_envp ev.
  Hypothesis Hlo : (0x7fff80000000 <= bv_unsigned sp0)%Z.
  Hypothesis Hhi : (bv_unsigned sp0 <= 0x800000000000)%Z.
  Hypothesis Hal : (bv_unsigned sp0 mod 16 = 0)%Z.

  Local Notation mem0 := (wrap_mem RPH sp0 av ev uid hw rdraw) (only parsing).
  Local Notation CM := (cmem sp0 (wrap_mem RPH sp0 av ev uid hw rdraw)) (only parsing).

  Let argc : word := argcN av.
  Local Notation argvp := (Z_to_bv 64 (bv_unsigned sp0 + 8)) (only parsing).
  Let envp : word := envp_ptr sp0 av.
  Let pn : word := cat_argv_ptr sp0 av ev 0.

  Lemma u_argc : bv_unsigned argc = Z.of_nat (length av).
  Proof using Hva. exact (u_argcN av Hva). Qed.

  Lemma len_av : (1 <= Z.of_nat (length av) <= 1024)%Z.
  Proof using Hva sp0. destruct Hva as [[H1 H2] _]. lia. Qed.

  (* [comment removed for export] *)
  Definition J1 (J : word -> option byte) : word -> option byte :=
    wbytes (wbytes (wbytes (wbytes
    (wbytes (wbytes (wbytes (wbytes J
      (Z_to_bv 64 (bv_unsigned sp0 - 8)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
      (Z_to_bv 64 (bv_unsigned sp0 - 16)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
      (Z_to_bv 64 (bv_unsigned sp0 - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
      (Z_to_bv 64 (bv_unsigned sp0 - 32)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
      (Z_to_bv 64 (bv_unsigned sp0 - 40)) (word_to_le_bytes 8 (Z_to_bv 64 0x61184)))
      (Z_to_bv 64 (bv_unsigned sp0 - 48)) (word_to_le_bytes 8 argvp))
      (Z_to_bv 64 (bv_unsigned sp0 - 56)) (word_to_le_bytes 8 argc))
      (Z_to_bv 64 (bv_unsigned sp0 - 64)) (word_to_le_bytes 8 (Z_to_bv 64 0x2e38c)).

  Lemma p1_run : forall rom (J : word -> option byte),
    wfJ sp0 J ->
    exists regs',
      msteps SEGS (mkst (regs_init sp0) (0x2e240 : word) (CM J (fun _ => None)) rom)
                  (mkst regs' (0x6f1c0 : word) (CM (J1 J) (fun _ => None)) rom)
      /\ getr regs' 1 = Z_to_bv 64 0x60f04
      /\ getr regs' 2 = Z_to_bv 64 (bv_unsigned sp0 - 416)
      /\ getr regs' 3 = Z_to_bv 64 0x10800
      /\ getr regs' 4 = Z_to_bv 64 0
      /\ getr regs' 8 = pn
      /\ getr regs' 9 = envp
      /\ getr regs' 10 = Z_to_bv 64 (bv_unsigned sp0 - 368)
      /\ getr regs' 11 = Z_to_bv 64 0
      /\ getr regs' 12 = Z_to_bv 64 304
      /\ getr regs' 18 = Z_to_bv 64 0x2e38c
      /\ (forall r : reg, In r [5;19;20;21;22;23;24;25;26;27]%list -> getr regs' r = Z_to_bv 64 0).
  Proof using Hal Hhi Hlo Hve Hva.
    intros rom J HJ.
    pose proof len_av as Hlen. pose proof u_argc as Hargc.
    eexists. split.
    - unfold regs_init.
      stepn F_2e1e0 D_2e1e0.    (* [comment removed for export] *)
      stepn F_2e1e4 D_2e1e4.    (* [comment removed for export] *)
      stepn F_2e1e8 D_2e1e8.    (* [comment removed for export] *)
      stepn F_2e1ec D_2e1ec.    (* [comment removed for export] *)
      stepn F_2e1f0 D_2e1f0.    (* [comment removed for export] *)
      stepiv F_2e1f4 D_2e1f4 sp0 ltac:(gres; imm_norm; apply v_andi_m16_aligned; exact Hal).
                                (* [comment removed for export] *)
      stepn F_2e1f8 D_2e1f8.    (* [comment removed for export] *)
      (* [comment removed for export] *)
      chain_step; [reflexivity | eapply step_lw with (bs := word_to_le_bytes 4 argc) (v := argc);
        [ exact F_2e1fc | reflexivity | exact D_2e1fc
        | addr_norm; rewrite rdn_cmem_above by region_side;
          apply (rdn_low_bytes SEGS mem0 sp0 argc 4); [lia|];
          exact (read_argc_w SEGS RPH sp0 av ev uid hw rdraw Hva Hve Hhi)
        | apply bytes_le_to_Z_4_small; rewrite Hargc; lia ]
        | step_simpl]; vnorm.
      rewrite (v_lw_small argc) by (rewrite Hargc; lia).
      stepn F_2e200 D_2e200.    (* [comment removed for export] *)
      stepn F_2e204 D_2e204.    (* [comment removed for export] *)
      stepn F_2e208 D_2e208.    (* [comment removed for export] *)
      (* [comment removed for export] *)
      chain_step; [reflexivity | eapply step_ld with (v := Z_to_bv 64 0x2e38c);
        [exact F_2e20c | reflexivity | exact D_2e20c | rd_img img_74570_8 | vm_compute; reflexivity] | step_simpl]; vnorm.
      chain_step; [reflexivity | eapply step_ld with (v := Z_to_bv 64 0x60ed4);
        [exact F_2e210 | reflexivity | exact D_2e210 | rd_img img_74578_8 | vm_compute; reflexivity] | step_simpl]; vnorm.
      chain_step; [reflexivity | eapply step_ld with (v := Z_to_bv 64 0x61728);
        [exact F_2e214 | reflexivity | exact D_2e214 | rd_img img_74580_8 | vm_compute; reflexivity] | step_simpl]; vnorm.
      sv F_2e218 D_2e218 (Z_to_bv 64 (bv_unsigned sp0 + 8)).   (* [comment removed for export] *)
      stepn F_2e21c D_2e21c.    (* [comment removed for export] *)
      stepn F_2e220 D_2e220.    (* [comment removed for export] *)
      stepn F_2e224 D_2e224.    (* [comment removed for export] *)
      (* [comment removed for export] *)
      sv F_610f0 D_610f0 (Z_to_bv 64 (bv_unsigned sp0 - 32)).   (* [comment removed for export] *)
      stw F_610f4 D_610f4 (Z_to_bv 64 (bv_unsigned sp0 - 8)) (Z_to_bv 64 0) ltac:(ok_win HJ).
      stw F_610f8 D_610f8 (Z_to_bv 64 (bv_unsigned sp0 - 16)) (Z_to_bv 64 0) ltac:(ok_win HJ).
      stw F_610fc D_610fc (Z_to_bv 64 (bv_unsigned sp0 - 24)) (Z_to_bv 64 0) ltac:(ok_win HJ).
      stw F_61100 D_61100 (Z_to_bv 64 (bv_unsigned sp0 - 32)) (Z_to_bv 64 0) ltac:(ok_win HJ).
      stepn F_61104 D_61104.    (* [comment removed for export] *)
      stepn F_61108 D_61108.    (* [comment removed for export] *)
      stepn F_6110c D_6110c.    (* [comment removed for export] *)
      (* [comment removed for export] *)
      chain_step; [reflexivity | eapply step_ld with (bs := word_to_le_bytes 8 pn) (v := pn);
        [ exact F_61110 | reflexivity | exact D_61110
        | addr_norm; rewrite rdn_cmem_above by region_side;
          replace (Z_to_bv 64 (bv_unsigned sp0 + 8)) with (sp0 + nat_to_word (8 + 8 * 0))
            by (rewrite word_add_nat; f_equal; lia);
          exact (read_argv_ptr_w SEGS RPH sp0 av ev uid hw rdraw Hva Hve Hlo Hhi 0 ltac:(lia))
        | apply bytes_le_to_Z_8 ]
        | step_simpl]; vnorm.
      stepiv F_61114 D_61114 (Z_to_bv 64 (8 * Z.of_nat (length av)))
        ltac:(gres; imm_norm; rewrite <- Hargc; unfold v_slli; f_equal; rewrite Z.shiftl_mul_pow2 by lia; change (2^3)%Z with 8%Z; lia).
                                (* [comment removed for export] *)
      stepiv F_61118 D_61118 (Z_to_bv 64 (bv_unsigned sp0 + 8 + 8 * Z.of_nat (length av))) vclose.
                                (* [comment removed for export] *)
      stepiv F_6111c D_6111c envp
        ltac:(gres; imm_norm; unfold envp, envp_ptr, v_addi; unorm; f_equal; lia).
                                (* [comment removed for export] *)
      stepn F_61120 D_61120.    (* [comment removed for export] *)
      (* [comment removed for export] *)
      sv F_60e78 D_60e78 (Z_to_bv 64 (bv_unsigned sp0 - 416)).   (* [comment removed for export] *)
      stw F_60e7c D_60e7c (Z_to_bv 64 (bv_unsigned sp0 - 40)) (Z_to_bv 64 0x61184) ltac:(ok_win HJ).
      stw F_60e80 D_60e80 (Z_to_bv 64 (bv_unsigned sp0 - 48)) (Z_to_bv 64 (bv_unsigned sp0 + 8)) ltac:(ok_win HJ).
      stw F_60e84 D_60e84 (Z_to_bv 64 (bv_unsigned sp0 - 56)) argc ltac:(ok_win HJ).
      stw F_60e88 D_60e88 (Z_to_bv 64 (bv_unsigned sp0 - 64)) (Z_to_bv 64 0x2e38c) ltac:(ok_win HJ).
      stepn F_60e8c D_60e8c.    (* [comment removed for export] *)
      stepn F_60e90 D_60e90.    (* [comment removed for export] *)
      sv F_60e94 D_60e94 (Z_to_bv 64 (bv_unsigned sp0 - 368)).   (* [comment removed for export] *)
      stepn F_60e98 D_60e98.    (* [comment removed for export] *)
      stepn F_60e9c D_60e9c.    (* [comment removed for export] *)
      stepn F_60ea0 D_60ea0.    (* [comment removed for export] *)
      pu_refl.
    - repeat split; gres; try reflexivity.
      intros r Hr. cbn [In] in Hr.
      repeat match goal with H : _ \/ _ |- _ => destruct H as [<-|H] end;
        [ .. | contradiction]; gres; apply getr_empty.
  Qed.
End P1.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
