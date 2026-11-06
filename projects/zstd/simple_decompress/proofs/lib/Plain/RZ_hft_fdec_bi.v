(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount ZdFrame.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Common Require Import KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXMem2 KXPost.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Plain Require Import PImg RZ_huf_iface.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Ltac fbi_enum FBD :=
  let BCE := fresh "BCE" in
  lazymatch type of FBD with
  | context [C4 (Z_to_bv 64 (bv_unsigned (edenot ?E ?e) + ?c))] =>
      kx_read_ranges;
      lazymatch e with context [EVar ?j] =>
        first [ kx_enum BCE E e j 1 255%nat (fun v => (1 <=? (v + c) mod 2^64) && ((v + c) mod 2^64 <=? 8))%bool
              | kx_enum BCE E e j 1 255%nat (fun v => (1 <=? (v + c) mod 2^64) && ((v + c) mod 2^64 <=? 64))%bool ] end
  | context [C4 (Z_to_bv 64 (bv_unsigned (edenot ?E ?e)))] =>
      kx_read_ranges;
      lazymatch e with context [EVar ?j] =>
        first [ kx_enum BCE E e j 1 255%nat (fun v => (1 <=? v mod 2^64) && (v mod 2^64 <=? 8))%bool
              | kx_enum BCE E e j 1 255%nat (fun v => (1 <=? v mod 2^64) && (v mod 2^64 <=? 64))%bool ] end
  | context [C4 (edenot ?E ?e)] =>
      kx_read_ranges;
      lazymatch e with context [EVar ?j] =>
        first [ kx_enum BCE E e j 1 255%nat (fun v => (1 <=? v mod 2^64) && (v mod 2^64 <=? 8))%bool
              | kx_enum BCE E e j 1 255%nat (fun v => (1 <=? v mod 2^64) && (v mod 2^64 <=? 64))%bool ] end
  end;
  cbv beta in BCE; apply andb_prop in BCE; destruct BCE as [BCE1 BCE2]; apply Z.leb_le in BCE1, BCE2.

Ltac fbi_fin3 FBD MU WM KXMI ni :=
    first
    [ (* [comment removed for export] *)
      left; do 9 eexists;
      lazymatch type of FBD with
      | context [C4 (Z_to_bv 64 ?v)] => eexists; exists (v mod 2^64); eexists
      | context [C4 (edenot ?E ?e)] => eexists; exists (bv_unsigned (edenot E e) mod 2^64); eexists
      end;
      split; [reflexivity|]; split; [exact MU|]; split; [exact WM|]; split; [exact KXMI|];
      split; [| split; [lia | lia]];
      rewrite KXS.Z_to_bv64_mod, ?Z_to_bv_bv_unsigned; unfold bitd_cells, bitd_ptr;
      lazymatch goal with |- context [if ?b then _ else _] => destruct b eqn:EB; [apply Z.leb_le in EB | apply Z.leb_gt in EB] | _ => idtac end;
      try (exfalso; lia);
      lazymatch type of FBD with rw_cells _ _ _ [_; _; _; C8 (Z_to_bv 64 ?e1); C8 (Z_to_bv 64 ?e2); C8 (Z_to_bv 64 ?e3)] =>
        lazymatch goal with |- rw_cells _ _ _ [_; _; _; C8 (Z_to_bv 64 ?g1); C8 (Z_to_bv 64 ?g2); C8 (Z_to_bv 64 ?g3)] =>
          replace g3 with e3 by lia; replace g1 with e1 by lia; try (replace g2 with e2 by lia)
        end end;
      exact FBD
    | (* [comment removed for export] *)
      right; do 8 eexists;
      destruct (rw_cells_forget psegs _ _ _ FBD) as [bs Hbs]; cbn [cells_size csize Nat.add] in Hbs;
      eexists; exists bs;
      split; [reflexivity|]; split; [exact MU|]; split; [exact WM|]; split; [exact KXMI|]; split; [exact Hbs|];
      split; [vm_compute; reflexivity | lia] ].

Definition fbi_post (gp tp s8 s9 s10 s11 x1 x5 x6 x7 x8 x17 x18 x19 x20 x21 x22 x23 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32)
    (SPV SRCI ni : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' =>
    (exists x9 x10 x11 x12 x13 x14 x15 x16 m' cont bc pad,
       ms' = MS (mkR x1 (Z_to_bv 64 (SPV + -160)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 s8 s9 s10 s11 x28 x29 x30 x31)
                F (Z_to_bv 64 0x25854) fc None m' (seg_rom psegs)
       /\ munch [(SPV - 112, SPV - 72)] m m' /\ wmono psegs m m' /\ mem_inv psegs m'
       /\ rw_cells psegs m' (SPV + -112) (bitd_cells cont (Z_to_bv 64 bc) pad (bitd_ptr SRCI ni) SRCI) /\ 1 <= bc <= 64 /\ 1 <= ni)
    \/ (exists x9 x10 x11 x12 x13 x15 x16 m' r bs,
       ms' = MS (mkR x1 (Z_to_bv 64 (SPV + -160)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 (Z_to_bv 64 r) x15 x16 x17 x18 x19 x20 x21 x22 x23 s8 s9 s10 s11 x28 x29 x30 x31)
                F (Z_to_bv 64 0x25610) fc None m' (seg_rom psegs)
       /\ munch [(SPV - 112, SPV - 72)] m m' /\ wmono psegs m m' /\ mem_inv psegs m'
       /\ rw_cells psegs m' (SPV + -112) [CB 40 bs] /\ zd_is_error r = true /\ 0 <= r < 2^64).

Lemma fd_f_bitinit : forall (gp tp s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (SPV SRC hn ni : Z) (srci jb : list byte) (m : word -> option byte)
    (x1 x5 x6 x7 x8 x10 x12 x13 x15 x16 x17 x19 x20 x21 x22 x23 x28 x29 x30 x31 : word),
  4096 <= SRC -> 0 <= hn -> 0 <= ni <= 65536 -> SRC + hn + ni < 2^47 -> 4256 <= SPV < 2^47 ->
  Z.of_nat (length srci) = ni -> (SRC + hn + ni <= SPV - 160 \/ SPV <= SRC + hn) ->
  mem_inv psegs m -> bytes_at psegs m (SRC + hn) srci -> rw_cells psegs m (SPV + -112) [CB 40 jb] ->
  evt psegs (fbi_post gp tp s8 s9 s10 s11 x1 x5 x6 x7 x8 x17 (Z_to_bv 64 SRC) x19 x20 x21 x22 x23 x28 x29 x30 x31 F fc SPV (SRC + hn) ni m)
      (MS (mkR x1 (Z_to_bv 64 (SPV + -160)) gp tp x5 x6 x7 x8 (Z_to_bv 64 (ni + hn)) x10 (Z_to_bv 64 (SRC + hn)) x12 x13 (Z_to_bv 64 ni) x15 x16 x17
               (Z_to_bv 64 SRC) x19 x20 x21 x22 x23 s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x254fc) fc None m (seg_rom psegs)).
Proof.
  intros until x31. intros R1 R2 R3 R4 R5 SL DJ MI SRCB FBD.
  assert (MU : munch [(SPV - 112, SPV - 72)] m m) by apply munch_refl.
  assert (WM : wmono psegs m m) by apply wmono_refl.
  (* [comment removed for export] *)
  destruct (Z.eq_dec ni 1) as [N1|N1]; [rewrite N1 in *|].
  1: kx_auto [0x25854; 0x25610] 200%nat
    [KZImg 0x10000 0x14000; KZRange SPV 4256 (2^47); KZRange SRC 4096 (2^47); KZRange hn 0 (2^47);
     KZRange (SRC + hn) 4096 (2^47); KZRange (SRC + hn + 1) 4096 (2^47); KZWr (SPV - 112) 40; KZDisj (SPV - 112) 40 (SRC + hn) 1]
    [(SRC + hn, 1); (0x11328, 24)].
  all: lazymatch goal with
       | N1 : _ <> 1 |- _ =>
           kx_auto_v 8 [0x25854; 0x25610] 200%nat
             [KZImg 0x10000 0x14000; KZRange SPV 4256 (2^47); KZRange SRC 4096 (2^47); KZRange hn 0 (2^47); KZRange ni 0 65536;
              KZRange (SRC + hn) 4096 (2^47); KZRange (SRC + hn + ni) 4096 (2^47); KZWr (SPV - 112) 40; KZDisj (SPV - 112) 40 (SRC + hn) ni]
             [(SRC + hn, ni); (0x11328, 24)]
       | _ => idtac
       end.
  all: try solve [exfalso; clear - N1 SL KXBR KXBR0 KXBR1; lia].
  all: kx_mem.
  all: try fbi_enum FBD.
  all: kx_abs.
  all: (apply evt_done; unfold fbi_post).
  all: fbi_fin3 FBD MU WM KXMI ni.
Qed.
