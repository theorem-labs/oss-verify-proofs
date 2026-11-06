(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.coturn.FuzzStunClient.images Require Import Asan.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import PropExec.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Asan Require Import FContractAsan.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import VLinalg VState VCert VItab VItab_asan VContract VDriver
     VState2 VCert2 VContract2 VDriver2 FPA_asan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Existing Instance PropExec.fx0.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition SEGSA := Asan.M.loaded_segments.

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
Definition A_frame : Z := fa_frame FPA_asan.          (* [comment removed for export] *)
Definition A_shoff : Z := fa_shoff FPA_asan.          (* [comment removed for export] *)
Definition A_tp    : Z := fa_tp FPA_asan.             (* [comment removed for export] *)
Definition A_errno : Z := fa_errno FPA_asan.          (* [comment removed for export] *)
Definition A_prng  : Z := fa_prng FPA_asan.           (* [comment removed for export] *)
Definition A_ret   : Z := fa_ret FPA_asan.            (* [comment removed for export] *)
Definition A_nmax  : Z := fa_nmax FPA_asan.           (* [comment removed for export] *)
Definition A_imgend : Z := fa_imgend FPA_asan.        (* [comment removed for export] *)

(* [comment removed for export] *)
Definition rom_asan : pmap Z :=
  build_rom SEGSA 0x5e5cc0 8 (build_rom SEGSA 0x5e5ca0 8 (build_rom SEGSA 0x5e5c80 8
  (build_rom SEGSA 0xacb80 (Z.to_nat (0xaccf8 - 0xacb80))
  (build_rom SEGSA 0xaa8e8 (Z.to_nat (0xabb78 - 0xaa8e8))
  (build_rom SEGSA 0x21b00 (Z.to_nat (0x22300 - 0x21b00))
  (build_rom SEGSA 0x102e0 (Z.to_nat (0x10900 - 0x102e0)) pm_empty)))))).

(* [comment removed for export] *)
Definition P1_asan : vparams :=
  mkVP A_frame [] [] [(A_prng, 8); (A_errno, 4)]
       [(0x10000, 0x32000); (0xaa000, 0xac000); (0xacb80, 0xaccf8); (A_prng, A_prng + 8); (A_errno, A_errno + 4); (0x606630, 0x606638);
        (0x5e5c80, 0x5e5c88); (0x5e5ca0, 0x5e5ca8); (0x5e5cc0, 0x5e5cc8)]
       (fa_pristine FPA_asan)
       rom_asan A_nmax F_SPLO F_SPHI.

(* [comment removed for export] *)
Definition kcells_asan : list (Z * (Z * Z)) :=
  map (fun c : Z * Z * Z => (fst (fst c), (snd (fst c), snd c))) (fa_kcells FPA_asan).
Definition kruns_asan : list (Z * (Z * Z)) :=
  map (fun r : Z * Z * Z => (fst (fst r), (fst (fst r) + snd (fst r), snd r))) (fa_gsh FPA_asan).

(* [comment removed for export] *)
Definition fzones_asan : list fzone :=
  [ mkFZ SP8 A_shoff (lconst (- (A_frame / 8))) (lconst 0) true
  ; mkFZ SP8 A_shoff (lconst (- (A_frame / 8) - 8)) (lconst (- (A_frame / 8))) false
  ; mkFZ SP8 A_shoff (lconst 0) (lconst 8) false
  ; mkFZ FSB 0 (lconst 0) (lconst FS_HINTS) true
  ; mkFZ FSB 0 (lconst FContractAsan.FS_FLAGS) (lconst (FContractAsan.FS_FLAGS + FS_FLAGS_LEN)) true
  ; mkFZ FSB 0 (lconst FContractAsan.FS_FRAMES) (lconst (FContractAsan.FS_FRAMES + FS_FRAMES_LEN)) true
  ; mkFZ FS8 A_shoff (lconst (FContractAsan.FS_FRAMES / 8)) (lconst (FContractAsan.FS_FRAMES / 8 + FS_FRAMES_LEN / 8)) true
  ; mkFZ FS8 A_shoff (lconst (FContractAsan.FS_FRAMES / 8 - 8)) (lconst (FContractAsan.FS_FRAMES / 8)) false
  ; mkFZ FS8 A_shoff (lconst (FContractAsan.FS_FRAMES / 8 + FS_FRAMES_LEN / 8)) (lconst (FContractAsan.FS_FRAMES / 8 + FS_FRAMES_LEN / 8 + 8)) false ].

Definition P0_asan : vparams2 :=
  mkVP2 P1_asan A_shoff kcells_asan kruns_asan fzones_asan (Some (FS_LEN, 20)) 16 [] 0 A_tp A_imgend.

(* [comment removed for export] *)
Definition ctab_asan : pmap contract2 :=
  pm_of_list [ (Z.to_pos 0x3ecf8, C_stack_malloc 0); (Z.to_pos 0x3ee6c, C_stack_malloc 1); (Z.to_pos 0x3effc, C_stack_malloc 2)
             ; (Z.to_pos 0x3f198, C_stack_malloc 3); (Z.to_pos 0x3f344, C_stack_malloc 4)
             ; (Z.to_pos 0x56cf0, C_set_shadow 0x00); (Z.to_pos 0x56df8, C_set_shadow 0xf5); (Z.to_pos 0x56e10, C_set_shadow 0xf8)
             ; (Z.to_pos 0x542cc, C_asan_memset); (Z.to_pos 0x53e30, C_asan_memcpy)
             ; (Z.to_pos 0x44230, C_i_strlen); (Z.to_pos 0x44238, C_i_strcmp); (Z.to_pos 0x44244, C_i_bcmp); (Z.to_pos 0x442c0, C_i_strncpy)
             ; (Z.to_pos 0x99ed0, CV1 C_tolower); (Z.to_pos 0xa3f44, CV1 C_strtoul) ].

Definition CI_asan : cimg := mkCI A_errno A_tp (-8).

Definition genv_asan (ranks : bool) : genv2 :=
  mkGE2 P0_asan itab_asan ctab_asan CI_asan A_tp A_prng ranks.
