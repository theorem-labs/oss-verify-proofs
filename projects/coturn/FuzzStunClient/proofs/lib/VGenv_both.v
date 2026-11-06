(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.coturn.FuzzStunClient.images Require Import AsanUbsan.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import PropExec.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Asan Require Import FContractAsan.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import VLinalg VState VCert VItab VItab_both VContract VDriver
     VState2 VCert2 VContract2 VDriver2 FPA_both.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Existing Instance PropExec.fx0.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition SEGSB := AsanUbsan.M.loaded_segments.

(* [comment removed for export] *)
Fixpoint build_rom (SEGS : list Segment) (a : Z) (n : nat) (acc : pmap Z) : pmap Z :=
  match n with
  | O => acc
  | S n' => build_rom SEGS (a + 1) n'
            (match seg_rom SEGS (Z_to_bv 64 a) with
             | Some b => pm_set (Z.to_pos a) (bv_unsigned b) acc
             | None => acc
             end)
  end.

(* [comment removed for export] *)
Definition A_frame : Z := fa_frame FPA_both.          (* [comment removed for export] *)
Definition A_shoff : Z := fa_shoff FPA_both.          (* [comment removed for export] *)
Definition A_tp    : Z := fa_tp FPA_both.             (* [comment removed for export] *)
Definition A_errno : Z := fa_errno FPA_both.          (* [comment removed for export] *)
Definition A_prng  : Z := fa_prng FPA_both.           (* [comment removed for export] *)
Definition A_ret   : Z := fa_ret FPA_both.            (* [comment removed for export] *)
Definition A_nmax  : Z := fa_nmax FPA_both.           (* [comment removed for export] *)
Definition A_imgend : Z := fa_imgend FPA_both.        (* [comment removed for export] *)

(* [comment removed for export] *)
Definition rom_both : pmap Z :=
  build_rom SEGSB 0x5e4280 8 (build_rom SEGSB 0x5e4260 8 (build_rom SEGSB 0x5e4240 8
  (build_rom SEGSB 0xab000 (Z.to_nat (0xab338 - 0xab000))
  (build_rom SEGSB 0xa8f20 (Z.to_nat (0xab000 - 0xa8f20))
  (build_rom SEGSB 0x21b00 (Z.to_nat (0x223bc - 0x21b00))
  (build_rom SEGSB 0x102e0 (Z.to_nat (0x10900 - 0x102e0)) pm_empty)))))).

(* [comment removed for export] *)
Definition P1_both : vparams :=
  mkVP A_frame [] [] [(A_prng, 8); (A_errno, 4)]
       [(0x10000, 0x32000); (0xa8000, 0xab000); (0xab000, 0xab338); (A_prng, A_prng + 8); (A_errno, A_errno + 4); (0x604bf0, 0x604bf8);
        (0x5e4240, 0x5e4248); (0x5e4260, 0x5e4268); (0x5e4280, 0x5e4288)]
       (fa_pristine FPA_both)
       rom_both A_nmax F_SPLO F_SPHI.

(* [comment removed for export] *)
Definition kcells_both : list (Z * (Z * Z)) :=
  map (fun c : Z * Z * Z => (fst (fst c), (snd (fst c), snd c))) (fa_kcells FPA_both).
Definition kruns_both : list (Z * (Z * Z)) :=
  map (fun r : Z * Z * Z => (fst (fst r), (fst (fst r) + snd (fst r), snd r))) (fa_gsh FPA_both).

(* [comment removed for export] *)
Definition fzones_both : list fzone :=
  [ mkFZ SP8 A_shoff (lconst (- (A_frame / 8))) (lconst 0) true
  ; mkFZ SP8 A_shoff (lconst (- (A_frame / 8) - 8)) (lconst (- (A_frame / 8))) false
  ; mkFZ SP8 A_shoff (lconst 0) (lconst 8) false
  ; mkFZ FSB 0 (lconst 0) (lconst FS_HINTS) true
  ; mkFZ FSB 0 (lconst FContractAsan.FS_FLAGS) (lconst (FContractAsan.FS_FLAGS + FS_FLAGS_LEN)) true
  ; mkFZ FSB 0 (lconst FContractAsan.FS_FRAMES) (lconst (FContractAsan.FS_FRAMES + FS_FRAMES_LEN)) true
  ; mkFZ FS8 A_shoff (lconst (FContractAsan.FS_FRAMES / 8)) (lconst (FContractAsan.FS_FRAMES / 8 + FS_FRAMES_LEN / 8)) true
  ; mkFZ FS8 A_shoff (lconst (FContractAsan.FS_FRAMES / 8 - 8)) (lconst (FContractAsan.FS_FRAMES / 8)) false
  ; mkFZ FS8 A_shoff (lconst (FContractAsan.FS_FRAMES / 8 + FS_FRAMES_LEN / 8)) (lconst (FContractAsan.FS_FRAMES / 8 + FS_FRAMES_LEN / 8 + 8)) false ].

Definition P0_both : vparams2 :=
  mkVP2 P1_both A_shoff kcells_both kruns_both fzones_both (Some (FS_LEN, 20)) 16 [] 0 A_tp A_imgend.

(* [comment removed for export] *)
Definition ctab_both : pmap contract2 :=
  pm_of_list [ (Z.to_pos 0x3ece8, C_stack_malloc 0); (Z.to_pos 0x3ee5c, C_stack_malloc 1); (Z.to_pos 0x3efec, C_stack_malloc 2)
             ; (Z.to_pos 0x3f188, C_stack_malloc 3); (Z.to_pos 0x3f334, C_stack_malloc 4)
             ; (Z.to_pos 0x56ce0, C_set_shadow 0x00); (Z.to_pos 0x56de8, C_set_shadow 0xf5); (Z.to_pos 0x56e00, C_set_shadow 0xf8)
             ; (Z.to_pos 0x542bc, C_asan_memset); (Z.to_pos 0x53e20, C_asan_memcpy)
             ; (Z.to_pos 0x44220, C_i_strlen); (Z.to_pos 0x44228, C_i_strcmp); (Z.to_pos 0x44234, C_i_bcmp); (Z.to_pos 0x442b0, C_i_strncpy)
             ; (Z.to_pos 0x9850c, CV1 C_tolower); (Z.to_pos 0xa2580, CV1 C_strtoul) ].

Definition CI_both : cimg := mkCI A_errno A_tp (-8).

Definition genv_both (ranks : bool) : genv2 :=
  mkGE2 P0_both itab_both ctab_both CI_both A_tp A_prng ranks.
