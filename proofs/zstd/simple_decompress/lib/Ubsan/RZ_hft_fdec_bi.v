(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount ZdFrame.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXMem2 KXPost.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg RZ_huf_iface RZ_hft_iface RZ_fse_decf_kit.
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
      destruct (rw_cells_forget usegs _ _ _ FBD) as [bs Hbs]; cbn [cells_size csize Nat.add] in Hbs;
      eexists; exists bs;
      split; [reflexivity|]; split; [exact MU|]; split; [exact WM|]; split; [exact KXMI|]; split; [exact Hbs|];
      split; [vm_compute; reflexivity | lia] ].

Definition fbi_post (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (SPV SRCI ni : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' =>
    (exists x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 m' cont bc pad,
       ms' = MS (mkR x1 (Z_to_bv 64 (SPV + -192)) gp tp x5 x6 x7 s0 s1 (Z_to_bv 64 ni) x11 x12 x13 x14 x15 x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
                F (Z_to_bv 64 0x2ad28) fc None m' (seg_rom usegs)
       /\ munch [(SPV - 144, SPV - 104)] m m' /\ wmono usegs m m' /\ mem_inv usegs m'
       /\ rw_cells usegs m' (SPV + -144) (bitd_cells cont (Z_to_bv 64 bc) pad (bitd_ptr SRCI ni) SRCI) /\ 1 <= bc <= 64 /\ 1 <= ni)
    \/ (exists x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 m' r bs,
       ms' = MS (mkR x1 (Z_to_bv 64 (SPV + -192)) gp tp x5 x6 x7 s0 s1 (Z_to_bv 64 r) x11 x12 x13 x14 x15 x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
                F (Z_to_bv 64 0x2b964) fc None m' (seg_rom usegs)
       /\ munch [(SPV - 144, SPV - 104)] m m' /\ wmono usegs m m' /\ mem_inv usegs m'
       /\ rw_cells usegs m' (SPV + -144) [CB 40 bs] /\ zd_is_error r = true /\ 0 <= r < 2^64).

Lemma fd_f_bitinit : bit_init_stmt_at PFSE_BITINIT ->
  forall (gp tp s0 s1 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (SPV OE SRCI ni : Z) (srci jb : list byte) (m : word -> option byte)
    (x1 x5 x6 x7 x13 x14 x15 x16 x17 x20 x28 x29 x30 x31 : word),
  4096 <= OE < 2^47 -> 4096 <= SRCI -> 0 <= ni <= 65536 -> SRCI + ni < 2^47 -> 4288 <= SPV < 2^47 -> SPV mod 16 = 0 ->
  Z.of_nat (length srci) = ni -> (SRCI + ni <= SPV - 192 \/ SPV <= SRCI) ->
  mem_inv usegs m -> bytes_at usegs m SRCI srci -> rw_cells usegs m (SPV + -144) [CB 40 jb] ->
  evt usegs (fbi_post gp tp s0 s1 (Z_to_bv 64 OE) (Z_to_bv 64 SRCI) (Z_to_bv 64 (OE + -3)) s5 s6 s7 s8 s9 s10 s11 F fc SPV SRCI ni m)
      (MS (mkR x1 (Z_to_bv 64 (SPV + -192)) gp tp x5 x6 x7 s0 s1 (Z_to_bv 64 1) (Z_to_bv 64 1) (Z_to_bv 64 ni) x13 x14 x15 x16 x17
               (Z_to_bv 64 OE) (Z_to_bv 64 SRCI) x20 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x2acec) fc None m (seg_rom usegs)).
Proof.
  intros BINIT. intros until x31. intros OER SRCL NIR SRCH SPR SPA SL DJ MI SRCB FBD.
  assert (MU : munch [(SPV - 144, SPV - 104)] m m) by apply munch_refl.
  assert (WM : wmono usegs m m) by apply wmono_refl.
  (* [comment removed for export] *)
  zstep. try (if_cases K0; zify_cond K0; [|exfalso; lia]).
  zstep. zstep. if_cases K1; zify_cond K1; [|exfalso; lia].
  zstep. zstep. zstep. zstep. if_cases K2; zify_cond K2; [|zb_refute K2].
  zstep. zstep. zstep.
  eapply evt_cut.
  { eapply (BINIT _ _ gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m (SPV + -144) SRCI ni srci jb); try eassumption; try lia. }
  unfold bit_init_post. post_call usegs m.
  zstep. zstep.
  destruct POST as [(RN & N1 & cont & bc & pad & BC1 & BC8 & FBD') | (RERR & RLT & bs & FBD')].
  - rewrite RN in *. if_cases K3; zify_cond K3; [exfalso; lia|].
    apply evt_done. unfold fbi_post. left. do 19 eexists.
    split; [reflexivity|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
    split; [exact FBD'|]. split; [exact BC1 | exact N1].
  - if_cases K3; zify_cond K3; [|exfalso; unfold zd_is_error, ZE_maxCode in RERR; apply Z.ltb_lt in RERR; lia].
    apply evt_done. unfold fbi_post. right. do 18 eexists.
    split; [reflexivity|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
    split; [exact FBD'|]. split; [exact RERR|]. pose proof RERR as RE2. unfold zd_is_error, ZE_maxCode in RE2. apply Z.ltb_lt in RE2. lia.
Qed.
