(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
Require Stdlib.ZArith.ZArith Stdlib.Lists.List LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType OSSVerify.glaze.binary_reflection.images.Ubsan OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module UbImgCells.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import OSSVerify.glaze.binary_reflection.images.Ubsan.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
#[local] Existing Instance fx0.
Abbreviation SEGS := Ubsan.M.loaded_segments.

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
Lemma img_75a80_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 482000) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 191040)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_78bd8_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 494632) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_78be0_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 494640) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 191300)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_78be8_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 494648) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 415044)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_78bf0_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 494656) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 417176)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_78bf8_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 494664) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_78ce8_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 494904) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 568000)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_78cf0_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 494912) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 699928)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_78cf8_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 494920) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 699920)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_78d00_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 494928) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 482008)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_78d08_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 494936) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 482000)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_78d10_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 494944) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 699904)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_79f68_4 : rdn SEGS (fun _ => None) (Z_to_bv 64 499640) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 131072)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_79f80_1 : rdn SEGS (fun _ => None) (Z_to_bv 64 499664) 1%nat = Some ([Z_to_bv 8 0]).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_8aa88_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 699304) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_8aa98_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 699320) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_8aaa0_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 699328) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_8ae38_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 699912) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_8ae60_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 699952) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_8ae78_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 699976) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. vm_refl_bv. Qed.
Lemma img_78c28_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 494632) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. vm_refl_bv. Qed.
Lemma img_79fb8_4 : rdn SEGS (fun _ => None) (Z_to_bv 64 499640) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 131072)).
Proof. vm_refl_bv. Qed.
Lemma img_aaba8_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 699304) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. vm_refl_bv. Qed.
Lemma img_aabb8_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 699320) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. vm_refl_bv. Qed.
Lemma img_aabc0_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 699328) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. vm_refl_bv. Qed.
Lemma img_aae08_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 699912) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. vm_refl_bv. Qed.
Lemma img_aae30_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 699952) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. vm_refl_bv. Qed.
Lemma img_aae48_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 699976) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. vm_refl_bv. Qed.
End UbImgCells.
Require Stdlib.micromega.Lia Stdlib.Bool.Bool LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run OSSVerify.Proofs.glaze.binary_reflection.lib.Common.SumsLib.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module UbStartupDefs.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.glaze.binary_reflection.images.Ubsan.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.SumsLib.StartupTac OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.ArgvEnv OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.RefLayout.
Import ListNotations.
Open Scope bv_scope.

Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Existing Instance fx0.
Abbreviation RPH := Ubsan.M.phdrs.

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
      (Z_to_bv 64 0x8aac0) (word_to_le_bytes 8 envp_w))          (* [comment removed for export] *)
      (Z_to_bv 64 0xaae28) (word_to_le_bytes 8 auxv_w))          (* [comment removed for export] *)
      (Z_to_bv 64 0xaae88) (word_to_le_bytes 8 hw))             (* [comment removed for export] *)
      (Z_to_bv 64 0xaae50) (word_to_le_bytes 8 (Z_to_bv 64 4096))) (* [comment removed for export] *)
      (Z_to_bv 64 0xaae18) (word_to_le_bytes 8 pn_w))            (* [comment removed for export] *)
      (Z_to_bv 64 0xaae10) (word_to_le_bytes 8 progname_w).      (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition J_lsm (J : word -> option byte) : word -> option byte :=
    wbytes (wbytes (wbytes (wbytes
    (wbytes (wbytes (wbytes (wbytes J
      (Z_to_bv 64 (bv_unsigned sp0 - 8)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
      (Z_to_bv 64 (bv_unsigned sp0 - 16)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
      (Z_to_bv 64 (bv_unsigned sp0 - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
      (Z_to_bv 64 (bv_unsigned sp0 - 32)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
      (Z_to_bv 64 (bv_unsigned sp0 - 40)) (word_to_le_bytes 8 (Z_to_bv 64 0x657f4)))
      (Z_to_bv 64 (bv_unsigned sp0 - 48)) (word_to_le_bytes 8 argv_w))
      (Z_to_bv 64 (bv_unsigned sp0 - 56)) (word_to_le_bytes 8 argc_w))
      (Z_to_bv 64 (bv_unsigned sp0 - 64)) (word_to_le_bytes 8 (Z_to_bv 64 0x2eb44)).

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
      (Z_to_bv 64 0xaabb8) (word_to_le_bytes 8 (Z_to_bv 64 0)))        (* [comment removed for export] *)
      (Z_to_bv 64 0xaabc8) (word_to_le_bytes 8 (Z_to_bv 64 0)))        (* [comment removed for export] *)
      (Z_to_bv 64 0xaabc0) (word_to_le_bytes 8 (Z_to_bv 64 8)))        (* [comment removed for export] *)
      (Z_to_bv 64 0xaae38) (word_to_le_bytes 8 (Z_to_bv 64 0xe0)))     (* [comment removed for export] *)
      (Z_to_bv 64 0xaae40) (word_to_le_bytes 8 (Z_to_bv 64 8)))        (* [comment removed for export] *)
      (Z_to_bv 64 0x8aba0) (word_to_le_bytes 8 (Z_to_bv 64 0)))        (* [comment removed for export] *)
      (Z_to_bv 64 0x8ab88) (word_to_le_bytes 8 (Z_to_bv 64 0x8aba0)))  (* [comment removed for export] *)
      (Z_to_bv 64 0x8aac8) (word_to_le_bytes 8 (Z_to_bv 64 0x8aac8)))  (* [comment removed for export] *)
      (Z_to_bv 64 0xaae20) [Z_to_bv 8 1])                              (* [comment removed for export] *)
      (Z_to_bv 64 0x8aaf0) (word_to_le_bytes 4 (Z_to_bv 64 2)).        (* [comment removed for export] *)

  Definition D_tlsB (tid : word) (D : word -> option byte) : word -> option byte :=
    wbytes (wbytes (wbytes (wbytes (wbytes (wbytes D
      (Z_to_bv 64 0x8aae8) (word_to_le_bytes 4 tid))                   (* [comment removed for export] *)
      (Z_to_bv 64 0x8ab60) (word_to_le_bytes 8 (Z_to_bv 64 0xaae58)))  (* [comment removed for export] *)
      (Z_to_bv 64 0x8ab40) (word_to_le_bytes 8 (Z_to_bv 64 0x8ab40)))  (* [comment removed for export] *)
      (Z_to_bv 64 0x8aad0) (word_to_le_bytes 8 (Z_to_bv 64 0x8aac8)))  (* [comment removed for export] *)
      (Z_to_bv 64 0x8aad8) (word_to_le_bytes 8 (Z_to_bv 64 0x8aac8)))  (* [comment removed for export] *)
      (Z_to_bv 64 0x8aae0) (word_to_le_bytes 8 (Z_to_bv 64 0)).        (* [comment removed for export] *)

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
      (Z_to_bv 64 0xaae00) [rb 0; rb 1; rb 2; rb 3])           (* [comment removed for export] *)
      (Z_to_bv 64 0xaae04) [rb 4; rb 5; rb 6; rb 7])           (* [comment removed for export] *)
      (Z_to_bv 64 0xaae01) [Z_to_bv 8 0])                        (* [comment removed for export] *)
      (Z_to_bv 64 0x8ab80) (word_to_le_bytes 8 canary_w).        (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition D_fd (D : word -> option byte) : word -> option byte :=
    wbytes D (Z_to_bv 64 0x79fd0) [Z_to_bv 8 1].

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
End UbStartupDefs.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.glaze.binary_reflection.images Require Import Ubsan.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.SumsLib OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.UbCodeM0 OSSVerify.Proofs.glaze.binary_reflection.lib.UbCodeM1. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.SumsLib.StartupTac OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.ArgvEnv OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.RefLayout UbImgCells OSSVerify.Proofs.glaze.binary_reflection.lib.UbCodeM0 OSSVerify.Proofs.glaze.binary_reflection.lib.UbCodeM1.
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
Abbreviation SEGS := Ubsan.M.loaded_segments.

(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Abbreviation RPH := Ubsan.M.phdrs.

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
      (Z_to_bv 64 (bv_unsigned sp0 - 40)) (word_to_le_bytes 8 (Z_to_bv 64 0x657f4)))
      (Z_to_bv 64 (bv_unsigned sp0 - 48)) (word_to_le_bytes 8 argvp))
      (Z_to_bv 64 (bv_unsigned sp0 - 56)) (word_to_le_bytes 8 argc))
      (Z_to_bv 64 (bv_unsigned sp0 - 64)) (word_to_le_bytes 8 (Z_to_bv 64 0x2eb44)).

  Lemma p1_run : forall rom (J : word -> option byte),
    wfJ sp0 J ->
    exists regs',
      msteps SEGS (mkst (regs_init sp0) (0x2e9f8 : word) (CM J (fun _ => None)) rom)
                  (mkst regs' (0x73830 : word) (CM (J1 J) (fun _ => None)) rom)
      /\ getr regs' 1 = Z_to_bv 64 0x65574
      /\ getr regs' 2 = Z_to_bv 64 (bv_unsigned sp0 - 416)
      /\ getr regs' 3 = Z_to_bv 64 0x10800
      /\ getr regs' 4 = Z_to_bv 64 0
      /\ getr regs' 8 = pn
      /\ getr regs' 9 = envp
      /\ getr regs' 10 = Z_to_bv 64 (bv_unsigned sp0 - 368)
      /\ getr regs' 11 = Z_to_bv 64 0
      /\ getr regs' 12 = Z_to_bv 64 304
      /\ getr regs' 18 = Z_to_bv 64 0x2eb44
      /\ (forall r : reg, In r [5;19;20;21;22;23;24;25;26;27]%list -> getr regs' r = Z_to_bv 64 0).
  Proof using Hal Hhi Hlo Hve Hva.
    intros rom J HJ.
    pose proof len_av as Hlen. pose proof u_argc as Hargc.
    eexists. split.
    - unfold regs_init.
      stepn F_2e998 D_2e998.    (* [comment removed for export] *)
      stepn F_2e99c D_2e99c.    (* [comment removed for export] *)
      stepn F_2e9a0 D_2e9a0.    (* [comment removed for export] *)
      stepn F_2e9a4 D_2e9a4.    (* [comment removed for export] *)
      stepn F_2e9a8 D_2e9a8.    (* [comment removed for export] *)
      stepiv F_2e9ac D_2e9ac sp0 ltac:(gres; imm_norm; apply v_andi_m16_aligned; exact Hal).
                                (* [comment removed for export] *)
      stepn F_2e9b0 D_2e9b0.    (* [comment removed for export] *)
      (* [comment removed for export] *)
      chain_step; [reflexivity | eapply step_lw with (bs := word_to_le_bytes 4 argc) (v := argc);
        [ exact F_2e9b4 | reflexivity | exact D_2e9b4
        | addr_norm; rewrite rdn_cmem_above by region_side;
          apply (rdn_low_bytes SEGS mem0 sp0 argc 4); [lia|];
          exact (read_argc_w SEGS RPH sp0 av ev uid hw rdraw Hva Hve Hhi)
        | apply bytes_le_to_Z_4_small; rewrite Hargc; lia ]
        | step_simpl]; vnorm.
      rewrite (v_lw_small argc) by (rewrite Hargc; lia).
      stepn F_2e9b8 D_2e9b8.    (* [comment removed for export] *)
      stepn F_2e9bc D_2e9bc.    (* [comment removed for export] *)
      stepn F_2e9c0 D_2e9c0.    (* [comment removed for export] *)
      (* [comment removed for export] *)
      chain_step; [reflexivity | eapply step_ld with (v := Z_to_bv 64 0x2eb44);
        [exact F_2e9c4 | reflexivity | exact D_2e9c4 | rd_img img_78be0_8 | vm_compute; reflexivity] | step_simpl]; vnorm.
      chain_step; [reflexivity | eapply step_ld with (v := Z_to_bv 64 0x65544);
        [exact F_2e9c8 | reflexivity | exact D_2e9c8 | rd_img img_78be8_8 | vm_compute; reflexivity] | step_simpl]; vnorm.
      chain_step; [reflexivity | eapply step_ld with (v := Z_to_bv 64 0x65d98);
        [exact F_2e9cc | reflexivity | exact D_2e9cc | rd_img img_78bf0_8 | vm_compute; reflexivity] | step_simpl]; vnorm.
      sv F_2e9d0 D_2e9d0 (Z_to_bv 64 (bv_unsigned sp0 + 8)).   (* [comment removed for export] *)
      stepn F_2e9d4 D_2e9d4.    (* [comment removed for export] *)
      stepn F_2e9d8 D_2e9d8.    (* [comment removed for export] *)
      stepn F_2e9dc D_2e9dc.    (* [comment removed for export] *)
      (* [comment removed for export] *)
      sv F_65760 D_65760 (Z_to_bv 64 (bv_unsigned sp0 - 32)).   (* [comment removed for export] *)
      stw F_65764 D_65764 (Z_to_bv 64 (bv_unsigned sp0 - 8)) (Z_to_bv 64 0) ltac:(ok_win HJ).
      stw F_65768 D_65768 (Z_to_bv 64 (bv_unsigned sp0 - 16)) (Z_to_bv 64 0) ltac:(ok_win HJ).
      stw F_6576c D_6576c (Z_to_bv 64 (bv_unsigned sp0 - 24)) (Z_to_bv 64 0) ltac:(ok_win HJ).
      stw F_65770 D_65770 (Z_to_bv 64 (bv_unsigned sp0 - 32)) (Z_to_bv 64 0) ltac:(ok_win HJ).
      stepn F_65774 D_65774.    (* [comment removed for export] *)
      stepn F_65778 D_65778.    (* [comment removed for export] *)
      stepn F_6577c D_6577c.    (* [comment removed for export] *)
      (* [comment removed for export] *)
      chain_step; [reflexivity | eapply step_ld with (bs := word_to_le_bytes 8 pn) (v := pn);
        [ exact F_65780 | reflexivity | exact D_65780
        | addr_norm; rewrite rdn_cmem_above by region_side;
          replace (Z_to_bv 64 (bv_unsigned sp0 + 8)) with (sp0 + nat_to_word (8 + 8 * 0))
            by (rewrite word_add_nat; f_equal; lia);
          exact (read_argv_ptr_w SEGS RPH sp0 av ev uid hw rdraw Hva Hve Hlo Hhi 0 ltac:(lia))
        | apply bytes_le_to_Z_8 ]
        | step_simpl]; vnorm.
      stepiv F_65784 D_65784 (Z_to_bv 64 (8 * Z.of_nat (length av)))
        ltac:(gres; imm_norm; rewrite <- Hargc; unfold v_slli; f_equal; rewrite Z.shiftl_mul_pow2 by lia; change (2^3)%Z with 8%Z; lia).
                                (* [comment removed for export] *)
      stepiv F_65788 D_65788 (Z_to_bv 64 (bv_unsigned sp0 + 8 + 8 * Z.of_nat (length av))) vclose.
                                (* [comment removed for export] *)
      stepiv F_6578c D_6578c envp
        ltac:(gres; imm_norm; unfold envp, envp_ptr, v_addi; unorm; f_equal; lia).
                                (* [comment removed for export] *)
      stepn F_65790 D_65790.    (* [comment removed for export] *)
      (* [comment removed for export] *)
      sv F_654e8 D_654e8 (Z_to_bv 64 (bv_unsigned sp0 - 416)).   (* [comment removed for export] *)
      stw F_654ec D_654ec (Z_to_bv 64 (bv_unsigned sp0 - 40)) (Z_to_bv 64 0x657f4) ltac:(ok_win HJ).
      stw F_654f0 D_654f0 (Z_to_bv 64 (bv_unsigned sp0 - 48)) (Z_to_bv 64 (bv_unsigned sp0 + 8)) ltac:(ok_win HJ).
      stw F_654f4 D_654f4 (Z_to_bv 64 (bv_unsigned sp0 - 56)) argc ltac:(ok_win HJ).
      stw F_654f8 D_654f8 (Z_to_bv 64 (bv_unsigned sp0 - 64)) (Z_to_bv 64 0x2eb44) ltac:(ok_win HJ).
      stepn F_654fc D_654fc.    (* [comment removed for export] *)
      stepn F_65500 D_65500.    (* [comment removed for export] *)
      sv F_65504 D_65504 (Z_to_bv 64 (bv_unsigned sp0 - 368)).   (* [comment removed for export] *)
      stepn F_65508 D_65508.    (* [comment removed for export] *)
      stepn F_6550c D_6550c.    (* [comment removed for export] *)
      stepn F_65510 D_65510.    (* [comment removed for export] *)
      pu_refl.
    - repeat split; gres; try reflexivity.
      intros r Hr. cbn [In] in Hr.
      repeat match goal with H : _ \/ _ |- _ => destruct H as [<-|H] end;
        [ .. | contradiction]; gres; apply getr_empty.
  Qed.
End P1.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
