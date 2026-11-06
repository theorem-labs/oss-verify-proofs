(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib SegsA0 SegsB0.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzDefs BzModel BzTac BzInv BzTables BzContracts.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpMem.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzArr BzCStream BzDState.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock BzDK BzDU5 BzDUM BzDU11 BzDU12S BzLemmasT2 DecCutFB B0F_decV.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCStream OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDState OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock.BzDHuff OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDK OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU5 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDUM OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU11 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU12S OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzLemmasT2 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecCutFB OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.B0F_decV.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Export B0F_decRet.
From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Open Scope bv_scope.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
Section ACeilS1. Context {ACEIL__ : ACeil}.

(* [comment removed for export] *)
Definition B0F_cut_L26 (A : act14) (Q : dres -> machine_state -> Prop) (F : nat) (k : Z) (sym unz ll16_0 ll4_0 : Z -> Z) : Prop :=
  forall (L : dsv) (d : dst) (s : dstrm) (J : jk)
         (x1 x5 x6 x7 x10 x11 x16 x17 x19 x25 x28 x29 x30 x31 : word)
         (m : word -> option byte)
         (w0 w8 w16 w24 w32 w40 w48 w56 w64 w80 w88 w104 w112 w120 : word)
         (w344 w352 w360 w368 w376 w384 w392 w400 w408 w416 w424 w432 w440 w448 w456 w464 w472 w480 w496 w504 w520 w528 w712 w720 w728 w736 w744 w752 : word),
    let cx := a_cx A in let S := b_s (a_cx A) in
    dmem DI_B0 cx (a_g1 A) (a_sv A) (a_payload A) m (dvF cx J (d) s) ->
    B0FL A m w0 w8 w16 w24 w32 w40 w48 w56 w64 (Z_to_bv 64 (S + 3160)) w80 w88 (Z_to_bv 64 (S + 3152)) w104 w112 w120 ->
    B0FH A m w344 w352 w360 w368 w376 w384 w392 w400 w408 w416 w424 w432 w440 w448 w456 w464 w472 w480 (Z_to_bv 64 (sv_nblock L)) w496 w504 (Z_to_bv 64 (a_fb A)) w520 w528 w712 w720 w728 w736 w744 w752 ->
    aframe A m ->
    stk b0segs m (a_lo A) (a_P A) ->
    munch (W14 A) (a_m0 A) m -> wmono b0segs (a_m0 A) m -> mem_inv b0segs m ->
    dpureF cx (a_b0 A) (a_payload A) J (d) s ->
    smallF L d sym unz ll16_0 ll4_0 ->
    (forall q, zget (d_ll16 d) q = ll16_0 q) ->
    (forall y, zget (d_ll4 d) y = ll4_0 y) ->
    (forall q, 0 <= q < k -> zget (d_cftabCopy d) q = psum unz q)%Z ->
    (0 <= k <= 257)%Z ->
    fuel_ok F (d) s ->
    evt b0segs (Q (K_L26 F L d s k))
      (MS (mkR x1 (Z_to_bv 64 (a_P A)) (a_gp A) (a_tp A) x5 x6 x7 (a_sp A) (Z_to_bv 64 (a_P A)) x10 x11 (Z_to_bv 64 k) (Z_to_bv 64 (S + 2124)) (Z_to_bv 64 (18446744073709551615 - (S + 2124))) (Z_to_bv 64 257) x16 x17 (Z_to_bv 64 (S + 1096)) x19 (Z_to_bv 64 (S + 64036)) (Z_to_bv 64 (18446744073709551615 - (S + 1096))) (Z_to_bv 64 2147450880) (Z_to_bv 64 (S + 56)) (Z_to_bv 64 (a_shs A + 7)) x25 (Z_to_bv 64 S) (Z_to_bv 64 (a_shf A)) x28 x29 x30 x31)
          (a_F A) (Z_to_bv 64 0xb339c) (a_fc A) None m (seg_rom b0segs)).

(* [comment removed for export] *)
Definition B0F_cut_L27 (A : act14) (Q : dres -> machine_state -> Prop) (F : nat) (i : Z) (fa fb fc : Z -> Z) (sym unz ll16_0 ll4_0 : Z -> Z) : Prop :=
  forall (L : dsv) (d : dst) (s : dstrm) (J : jk)
         (x1 x5 x6 x7 x11 x12 x19 x25 x28 x29 x30 x31 : word)
         (m : word -> option byte)
         (w0 w8 w16 w24 w32 w40 w48 w56 w64 w80 w88 w96 w104 w112 w120 : word)
         (w344 w352 w360 w368 w376 w384 w392 w400 w408 w416 w424 w432 w440 w448 w456 w464 w472 w480 w496 w504 w520 w528 w712 w720 w728 w736 w744 w752 : word),
    let cx := a_cx A in let S := b_s (a_cx A) in
    dmem DI_B0 cx (a_g1 A) (a_sv A) (a_payload A) m (dvF cx J (d) s) ->
    B0FL A m w0 w8 w16 w24 w32 w40 w48 w56 w64 (Z_to_bv 64 (S + 3160)) w80 w88 w96 w104 w112 w120 ->
    B0FH A m w344 w352 w360 w368 w376 w384 w392 w400 w408 w416 w424 w432 w440 w448 w456 w464 w472 w480 (Z_to_bv 64 (sv_nblock L)) w496 w504 (Z_to_bv 64 (a_fb A)) w520 w528 w712 w720 w728 w736 w744 w752 ->
    aframe A m ->
    stk b0segs m (a_lo A) (a_P A) ->
    munch (W14 A) (a_m0 A) m -> wmono b0segs (a_m0 A) m -> mem_inv b0segs m ->
    dpureF cx (a_b0 A) (a_payload A) J (d) s ->
    smallF L d sym unz ll16_0 ll4_0 ->
    tvst unz ll16_0 ll4_0 i = (fa, fb, fc) ->
    (forall q, zget (d_ll16 d) q = fa q) ->
    (forall y, zget (d_ll4 d) y = fb y) ->
    (forall q, 0 <= q < 256 -> zget (d_cftabCopy d) q = fc q)%Z ->
    (0 <= i < sv_nblock L)%Z ->
    fuel_ok F (d) s ->
    evt b0segs (Q (K_L27 F L d s i))
      (MS (mkR x1 (Z_to_bv 64 (a_P A)) (a_gp A) (a_tp A) x5 x6 x7 (a_sp A) (Z_to_bv 64 (a_P A)) (Z_to_bv 64 (S + 3160)) x11 x12 (Z_to_bv 64 (S + 2124)) (Z_to_bv 64 (2 * i)) (Z_to_bv 64 i) (Z_to_bv 64 (a_shs A + 395)) (Z_to_bv 64 (a_shs A + 396)) (Z_to_bv 64 (S + 1096)) x19 (Z_to_bv 64 (S + 64036)) (Z_to_bv 64 (S + 3168)) (Z_to_bv 64 2147450880) (Z_to_bv 64 (S + 56)) (Z_to_bv 64 (a_shs A + 7)) x25 (Z_to_bv 64 S) (Z_to_bv 64 (a_shf A)) x28 x29 x30 x31)
          (a_F A) (Z_to_bv 64 0xb3438) (a_fc A) None m (seg_rom b0segs)).

(* [comment removed for export] *)
Definition B0F_cut_GL (A : act14) (Q : dres -> machine_state -> Prop) (F : nat) (fa fb fc : Z -> Z) (sym unz ll16_0 ll4_0 : Z -> Z) : Prop :=
  forall (L : dsv) (d : dst) (s : dstrm) (J : jk)
         (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x25 x28 x29 x30 x31 : word)
         (m : word -> option byte)
         (w0 w8 w16 w24 w32 w40 w48 w56 w64 w80 w88 w96 w104 w112 w120 : word)
         (w344 w352 w360 w368 w376 w384 w392 w400 w408 w416 w424 w432 w440 w448 w456 w464 w472 w480 w496 w504 w520 w528 w712 w720 w728 w736 w744 w752 : word),
    let cx := a_cx A in let S := b_s (a_cx A) in
    dmem DI_B0 cx (a_g1 A) (a_sv A) (a_payload A) m (dvF cx J (d) s) ->
    B0FL A m w0 w8 w16 w24 w32 w40 w48 w56 w64 (Z_to_bv 64 (S + 3160)) w80 w88 w96 w104 w112 w120 ->
    B0FH A m w344 w352 w360 w368 w376 w384 w392 w400 w408 w416 w424 w432 w440 w448 w456 w464 w472 w480 (Z_to_bv 64 (sv_nblock L)) w496 w504 (Z_to_bv 64 (a_fb A)) w520 w528 w712 w720 w728 w736 w744 w752 ->
    aframe A m ->
    stk b0segs m (a_lo A) (a_P A) ->
    munch (W14 A) (a_m0 A) m -> wmono b0segs (a_m0 A) m -> mem_inv b0segs m ->
    dpureF cx (a_b0 A) (a_payload A) J (d) s ->
    smallF L d sym unz ll16_0 ll4_0 ->
    tvst unz ll16_0 ll4_0 (sv_nblock L) = (fa, fb, fc) ->
    (forall q, zget (d_ll16 d) q = fa q) ->
    (forall y, zget (d_ll4 d) y = fb y) ->
    (forall q, 0 <= q < 256 -> zget (d_cftabCopy d) q = fc q)%Z ->
    fuel_ok F (d) s ->
    evt b0segs (Q (K_L27 F L d s (sv_nblock L)))
      (MS (mkR x1 (Z_to_bv 64 (a_P A)) (a_gp A) (a_tp A) x5 x6 x7 (a_sp A) (Z_to_bv 64 (a_P A)) x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (S + 1096)) x19 (Z_to_bv 64 (S + 64036)) (Z_to_bv 64 (S + 3168)) (Z_to_bv 64 2147450880) (Z_to_bv 64 (S + 56)) (Z_to_bv 64 (a_shs A + 7)) x25 (Z_to_bv 64 S) (Z_to_bv 64 (a_shf A)) x28 x29 x30 x31)
          (a_F A) (Z_to_bv 64 0xb3634) (a_fc A) None m (seg_rom b0segs)).

(* [comment removed for export] *)
Definition B0F_cut_PR (A : act14) (Q : dres -> machine_state -> Prop) (F : nat) (st : nat) (fa fb : Z -> Z) (i j : Z) (sym unz ll16_0 ll4_0 : Z -> Z) : Prop :=
  forall (L : dsv) (d : dst) (s : dstrm) (J : jk)
         (x1 x5 x6 x7 x10 x11 x13 x15 x16 x17 x28 x29 x30 x31 : word)
         (m : word -> option byte)
         (w0 w8 w16 w24 w32 w40 w48 w56 w64 w80 w88 w96 w104 w112 w120 : word)
         (w344 w352 w360 w368 w376 w384 w392 w400 w408 w416 w424 w432 w440 w448 w456 w464 w472 w480 w496 w504 w520 w528 w712 w720 w728 w736 w744 w752 : word),
    let cx := a_cx A in let S := b_s (a_cx A) in
    dmem DI_B0 cx (a_g1 A) (a_sv A) (a_payload A) m (dvF cx J (d) s) ->
    B0FL A m w0 w8 w16 w24 w32 w40 w48 w56 w64 (Z_to_bv 64 (S + 3160)) w80 w88 w96 w104 w112 w120 ->
    B0FH A m w344 w352 w360 w368 w376 w384 w392 w400 w408 w416 w424 w432 w440 w448 w456 w464 w472 w480 (Z_to_bv 64 (sv_nblock L)) w496 w504 (Z_to_bv 64 (a_fb A)) w520 w528 w712 w720 w728 w736 w744 w752 ->
    aframe A m ->
    stk b0segs m (a_lo A) (a_P A) ->
    munch (W14 A) (a_m0 A) m -> wmono b0segs (a_m0 A) m -> mem_inv b0segs m ->
    dpureF cx (a_b0 A) (a_payload A) J (d) s ->
    smallF L d sym unz ll16_0 ll4_0 ->
    prst unz ll16_0 ll4_0 (sv_nblock L) (d_origPtr d) st = (fa, fb, i, j) ->
    (st < ncyc sym unz (sv_nblock L) (d_origPtr d))%nat ->
    (forall q, zget (d_ll16 d) q = fa q) ->
    (forall y, zget (d_ll4 d) y = fb y) ->
    fuel_ok F (d) s ->
    evt b0segs (Q (K_PR F L d s i j (Datatypes.S (Z.to_nat (sv_nblock L)) - st)%nat))
      (MS (mkR x1 (Z_to_bv 64 (a_P A)) (a_gp A) (a_tp A) x5 x6 x7 (a_sp A) (Z_to_bv 64 (a_P A)) x10 x11 (Z_to_bv 64 i) x13 (Z_to_bv 64 j) x15 x16 x17 (Z_to_bv 64 (S + 1096)) (Z_to_bv 64 (a_shs A + 396)) (Z_to_bv 64 (S + 64036)) (Z_to_bv 64 (S + 3168)) (Z_to_bv 64 2147450880) (Z_to_bv 64 (S + 56)) (Z_to_bv 64 (a_shs A + 7)) (Z_to_bv 64 (a_shs A + 395)) (Z_to_bv 64 S) (Z_to_bv 64 (a_shf A)) x28 x29 x30 x31)
          (a_F A) (Z_to_bv 64 0xb3744) (a_fc A) None m (seg_rom b0segs)).

(* [comment removed for export] *)
Definition B0F_cut_TAIL (A : act14) (Q : dres -> machine_state -> Prop) (F : nat) (fa fb : Z -> Z) (j5 : Z) (sym unz ll16_0 ll4_0 : Z -> Z) : Prop :=
  forall (L : dsv) (d : dst) (s : dstrm) (J : jk)
         (x1 x5 x6 x7 x10 x11 x12 x13 x15 x16 x17 x23 x24 x28 x29 x30 x31 : word)
         (m : word -> option byte)
         (w0 w8 w16 w24 w32 w40 w48 w56 w64 w80 w88 w96 w104 w112 w120 : word)
         (w344 w352 w360 w368 w376 w384 w392 w400 w408 w416 w424 w432 w440 w448 w456 w464 w472 w480 w496 w504 w520 w528 w712 w728 w736 w744 w752 : word),
    let cx := a_cx A in let S := b_s (a_cx A) in
    dmem DI_B0 cx (a_g1 A) (a_sv A) (a_payload A) m (dvF cx J (d) s) ->
    B0FL A m w0 w8 w16 w24 w32 w40 w48 w56 w64 (Z_to_bv 64 (S + 3160)) w80 w88 w96 w104 w112 w120 ->
    B0FH A m w344 w352 w360 w368 w376 w384 w392 w400 w408 w416 w424 w432 w440 w448 w456 w464 w472 w480 (Z_to_bv 64 (sv_nblock L)) w496 w504 (Z_to_bv 64 (a_fb A)) w520 w528 w712 (Z_to_bv 64 (d_origPtr d)) w728 w736 w744 w752 ->
    aframe A m ->
    stk b0segs m (a_lo A) (a_P A) ->
    munch (W14 A) (a_m0 A) m -> wmono b0segs (a_m0 A) m -> mem_inv b0segs m ->
    dpureF cx (a_b0 A) (a_payload A) J (d) s ->
    smallF L d sym unz ll16_0 ll4_0 ->
    (forall q, 0 <= fa q < 65536)%Z ->
    (forall y, 0 <= fb y < 256)%Z ->
    (forall q, zget (d_ll16 d) q = fa q) ->
    (forall y, zget (d_ll4 d) y = fb y) ->
    fuel_ok F (d) s ->
    evt b0segs (Q (K_TAIL F L d s j5))
      (MS (mkR x1 (Z_to_bv 64 (a_P A)) (a_gp A) (a_tp A) x5 x6 x7 (a_sp A) (Z_to_bv 64 (a_P A)) x10 x11 x12 x13 (Z_to_bv 64 j5) x15 x16 x17 (Z_to_bv 64 (S + 1096)) (Z_to_bv 64 (a_shs A + 396)) (Z_to_bv 64 (S + 64036)) (Z_to_bv 64 (S + 3168)) (Z_to_bv 64 2147450880) x23 x24 (Z_to_bv 64 (a_shs A + 395)) (Z_to_bv 64 S) (Z_to_bv 64 (a_shf A)) x28 x29 x30 x31)
          (a_F A) (Z_to_bv 64 0xb38fc) (a_fc A) None m (seg_rom b0segs)).

(* [comment removed for export] *)
Definition B0F_cut_IDXNR (A : act14) (Q : dres -> machine_state -> Prop) (F : nat) (fa fb : Z -> Z) (j5 : Z) (sym unz ll16_0 ll4_0 : Z -> Z) : Prop :=
  forall (L : dsv) (d : dst) (s : dstrm) (J : jk)
         (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x18 x28 x29 x30 x31 : word)
         (m : word -> option byte)
         (w0 w8 w16 w24 w32 w40 w48 w56 w64 w80 w88 w96 w104 w112 w120 : word)
         (w344 w352 w360 w368 w376 w384 w392 w400 w408 w416 w424 w432 w440 w448 w456 w464 w472 w480 w496 w504 w528 w720 w728 w736 w744 w752 : word),
    let cx := a_cx A in let S := b_s (a_cx A) in
    dmem DI_B0 cx (a_g1 A) (a_sv A) (a_payload A) m (dvF cx J (d_set_nused (d_set_tPos d (d_origPtr d)) 0) s) ->
    B0FL A m w0 w8 w16 w24 w32 w40 w48 w56 w64 (Z_to_bv 64 (S + 3160)) w80 w88 w96 w104 w112 w120 ->
    B0FH A m w344 w352 w360 w368 w376 w384 w392 w400 w408 w416 w424 w432 w440 w448 w456 w464 w472 w480 (Z_to_bv 64 (sv_nblock L)) w496 w504 (Z_to_bv 64 (a_fb A)) (Z_to_bv 64 (a_shs A + 136)) w528 (Z_to_bv 64 (S + 1092)) w720 w728 w736 w744 w752 ->
    aframe A m ->
    stk b0segs m (a_lo A) (a_P A) ->
    munch (W14 A) (a_m0 A) m -> wmono b0segs (a_m0 A) m -> mem_inv b0segs m ->
    dpureF cx (a_b0 A) (a_payload A) J (d) s ->
    smallF L d sym unz ll16_0 ll4_0 ->
    (forall q, 0 <= fa q < 65536)%Z ->
    (forall y, 0 <= fb y < 256)%Z ->
    (forall q, zget (d_ll16 d) q = fa q) ->
    (forall y, zget (d_ll4 d) y = fb y) ->
    d_rand d = 0%Z ->
    fuel_ok F (d) s ->
    evt b0segs (Q (DRet BZ_OK (sv_set_j (sv_set_i L (d_origPtr d)) j5) (sft_nr d (indexIntoF (d_origPtr d) (d_cftab d)) (get_ll d (d_origPtr d))) s))
      (MS (mkR x1 (Z_to_bv 64 (a_P A)) (a_gp A) (a_tp A) x5 x6 x7 (a_sp A) (Z_to_bv 64 (a_P A)) (Z_to_bv 64 (index_into_f (bv_signed (Z_to_bv 64 (d_origPtr d))) (sv32 (zw32 (d_cftab d) 257)))) x11 x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 (a_shs A + 396)) (Z_to_bv 64 (S + 64036)) (Z_to_bv 64 (S + 3168)) (Z_to_bv 64 2147450880) (Z_to_bv 64 (S + 60)) (Z_to_bv 64 (a_shs A + 7)) (Z_to_bv 64 (a_shs A + 395)) (Z_to_bv 64 S) (Z_to_bv 64 (a_shf A)) x28 x29 x30 x31)
          (a_F A) (Z_to_bv 64 0xb3dc8) (a_fc A) None m (seg_rom b0segs)).

(* [comment removed for export] *)
Definition B0F_cut_IDXRR (A : act14) (Q : dres -> machine_state -> Prop) (F : nat) (fa fb : Z -> Z) (j5 : Z) (sym unz ll16_0 ll4_0 : Z -> Z) : Prop :=
  forall (L : dsv) (d : dst) (s : dstrm) (J : jk)
         (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x18 x28 x29 x30 x31 : word)
         (m : word -> option byte)
         (w0 w8 w16 w24 w32 w40 w48 w56 w64 w80 w88 w96 w104 : word)
         (w344 w360 w368 w376 w384 w400 w408 w416 w424 w432 w440 w448 w456 w464 w472 w480 w496 w504 w528 w720 w728 w736 w744 w752 : word),
    let cx := a_cx A in let S := b_s (a_cx A) in
    dmem DI_B0 cx (a_g1 A) (a_sv A) (a_payload A) m (dvF cx J (d_set_rTPos (d_set_rNToGo (d_set_nused (d_set_tPos d (d_origPtr d)) 0) 0) 0) s) ->
    B0FL A m w0 w8 w16 w24 w32 w40 w48 w56 w64 (Z_to_bv 64 (S + 3160)) w80 w88 w96 w104 (Z_to_bv 64 (a_shs A + 3)) (Z_to_bv 64 (S + 28)) ->
    B0FH A m w344 (Z_to_bv 64 (a_shs A + 3)) w360 w368 w376 w384 (Z_to_bv 64 (S + 24)) w400 w408 w416 w424 w432 w440 w448 w456 w464 w472 w480 (Z_to_bv 64 (sv_nblock L)) w496 w504 (Z_to_bv 64 (a_fb A)) (Z_to_bv 64 (a_shs A + 136)) w528 (Z_to_bv 64 (S + 1092)) w720 w728 w736 w744 w752 ->
    aframe A m ->
    stk b0segs m (a_lo A) (a_P A) ->
    munch (W14 A) (a_m0 A) m -> wmono b0segs (a_m0 A) m -> mem_inv b0segs m ->
    dpureF cx (a_b0 A) (a_payload A) J (d) s ->
    smallF L d sym unz ll16_0 ll4_0 ->
    (forall q, 0 <= fa q < 65536)%Z ->
    (forall y, 0 <= fb y < 256)%Z ->
    (forall q, zget (d_ll16 d) q = fa q) ->
    (forall y, zget (d_ll4 d) y = fb y) ->
    d_rand d = 1%Z ->
    fuel_ok F (d) s ->
    evt b0segs (Q (DRet BZ_OK (sv_set_j (sv_set_i L (d_origPtr d)) j5) (sft_r d (indexIntoF (d_origPtr d) (d_cftab d)) (get_ll d (d_origPtr d))) s))
      (MS (mkR x1 (Z_to_bv 64 (a_P A)) (a_gp A) (a_tp A) x5 x6 x7 (a_sp A) (Z_to_bv 64 (a_P A)) (Z_to_bv 64 (index_into_f (bv_signed (Z_to_bv 64 (d_origPtr d))) (sv32 (zw32 (d_cftab d) 257)))) x11 x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 (a_shs A + 396)) (Z_to_bv 64 (S + 64036)) (Z_to_bv 64 (S + 3168)) (Z_to_bv 64 2147450880) (Z_to_bv 64 (S + 60)) (Z_to_bv 64 (a_shs A + 7)) (Z_to_bv 64 (a_shs A + 395)) (Z_to_bv 64 S) (Z_to_bv 64 (a_shf A)) x28 x29 x30 x31)
          (a_F A) (Z_to_bv 64 0xb39d0) (a_fc A) None m (seg_rom b0segs)).

(* [comment removed for export] *)
Definition B0F_call_IDXN (A : act14) (Q : dres -> machine_state -> Prop) (F : nat) (fa fb : Z -> Z) (j5 : Z) (sym unz ll16_0 ll4_0 : Z -> Z) : Prop :=
  forall (L : dsv) (d : dst) (s : dstrm) (J : jk)
         (x5 x6 x7 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word)
         (m : word -> option byte)
         (w0 w8 w16 w24 w32 w40 w48 w56 w64 w80 w88 w96 w104 w112 w120 : word)
         (w344 w352 w360 w368 w376 w384 w392 w400 w408 w416 w424 w432 w440 w448 w456 w464 w472 w480 w496 w504 w528 w720 w728 w736 w744 w752 : word),
    let cx := a_cx A in let S := b_s (a_cx A) in
    dmem DI_B0 cx (a_g1 A) (a_sv A) (a_payload A) m (dvF cx J (d_set_nused (d_set_tPos d (d_origPtr d)) 0) s) ->
    B0FL A m w0 w8 w16 w24 w32 w40 w48 w56 w64 (Z_to_bv 64 (S + 3160)) w80 w88 w96 w104 w112 w120 ->
    B0FH A m w344 w352 w360 w368 w376 w384 w392 w400 w408 w416 w424 w432 w440 w448 w456 w464 w472 w480 (Z_to_bv 64 (sv_nblock L)) w496 w504 (Z_to_bv 64 (a_fb A)) (Z_to_bv 64 (a_shs A + 136)) w528 (Z_to_bv 64 (S + 1092)) w720 w728 w736 w744 w752 ->
    aframe A m ->
    stk b0segs m (a_lo A) (a_P A) ->
    munch (W14 A) (a_m0 A) m -> wmono b0segs (a_m0 A) m -> mem_inv b0segs m ->
    dpureF cx (a_b0 A) (a_payload A) J (d) s ->
    smallF L d sym unz ll16_0 ll4_0 ->
    (forall q, 0 <= fa q < 65536)%Z ->
    (forall y, 0 <= fb y < 256)%Z ->
    (forall q, zget (d_ll16 d) q = fa q) ->
    (forall y, zget (d_ll4 d) y = fb y) ->
    d_rand d = 0%Z ->
    fuel_ok F (d) s ->
    evt b0segs (Q (DRet BZ_OK (sv_set_j (sv_set_i L (d_origPtr d)) j5) (sft_nr d (indexIntoF (d_origPtr d) (d_cftab d)) (get_ll d (d_origPtr d))) s))
      (MS (mkR (Z_to_bv 64 0xb3dc8) (Z_to_bv 64 (a_P A)) (a_gp A) (a_tp A) x5 x6 x7 (a_sp A) (Z_to_bv 64 (a_P A)) (Z_to_bv 64 (d_origPtr d)) (Z_to_bv 64 (S + 1096)) x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (S + 1096)) (Z_to_bv 64 (a_shs A + 396)) (Z_to_bv 64 (S + 64036)) (Z_to_bv 64 (S + 3168)) (Z_to_bv 64 2147450880) (Z_to_bv 64 (S + 60)) (Z_to_bv 64 (a_shs A + 7)) (Z_to_bv 64 (a_shs A + 395)) (Z_to_bv 64 S) (Z_to_bv 64 (a_shf A)) x28 x29 x30 x31)
          (a_F A) (Z_to_bv 64 0x83de0) (a_fc A) None m (seg_rom b0segs)).

(* [comment removed for export] *)
Definition B0F_call_IDXR (A : act14) (Q : dres -> machine_state -> Prop) (F : nat) (fa fb : Z -> Z) (j5 : Z) (sym unz ll16_0 ll4_0 : Z -> Z) : Prop :=
  forall (L : dsv) (d : dst) (s : dstrm) (J : jk)
         (x5 x6 x7 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word)
         (m : word -> option byte)
         (w0 w8 w16 w24 w32 w40 w48 w56 w64 w80 w88 w96 w104 : word)
         (w344 w360 w368 w376 w384 w400 w408 w416 w424 w432 w440 w448 w456 w464 w472 w480 w496 w504 w528 w720 w728 w736 w744 w752 : word),
    let cx := a_cx A in let S := b_s (a_cx A) in
    dmem DI_B0 cx (a_g1 A) (a_sv A) (a_payload A) m (dvF cx J (d_set_rTPos (d_set_rNToGo (d_set_nused (d_set_tPos d (d_origPtr d)) 0) 0) 0) s) ->
    B0FL A m w0 w8 w16 w24 w32 w40 w48 w56 w64 (Z_to_bv 64 (S + 3160)) w80 w88 w96 w104 (Z_to_bv 64 (a_shs A + 3)) (Z_to_bv 64 (S + 28)) ->
    B0FH A m w344 (Z_to_bv 64 (a_shs A + 3)) w360 w368 w376 w384 (Z_to_bv 64 (S + 24)) w400 w408 w416 w424 w432 w440 w448 w456 w464 w472 w480 (Z_to_bv 64 (sv_nblock L)) w496 w504 (Z_to_bv 64 (a_fb A)) (Z_to_bv 64 (a_shs A + 136)) w528 (Z_to_bv 64 (S + 1092)) w720 w728 w736 w744 w752 ->
    aframe A m ->
    stk b0segs m (a_lo A) (a_P A) ->
    munch (W14 A) (a_m0 A) m -> wmono b0segs (a_m0 A) m -> mem_inv b0segs m ->
    dpureF cx (a_b0 A) (a_payload A) J (d) s ->
    smallF L d sym unz ll16_0 ll4_0 ->
    (forall q, 0 <= fa q < 65536)%Z ->
    (forall y, 0 <= fb y < 256)%Z ->
    (forall q, zget (d_ll16 d) q = fa q) ->
    (forall y, zget (d_ll4 d) y = fb y) ->
    d_rand d = 1%Z ->
    fuel_ok F (d) s ->
    evt b0segs (Q (DRet BZ_OK (sv_set_j (sv_set_i L (d_origPtr d)) j5) (sft_r d (indexIntoF (d_origPtr d) (d_cftab d)) (get_ll d (d_origPtr d))) s))
      (MS (mkR (Z_to_bv 64 0xb39d0) (Z_to_bv 64 (a_P A)) (a_gp A) (a_tp A) x5 x6 x7 (a_sp A) (Z_to_bv 64 (a_P A)) (Z_to_bv 64 (d_origPtr d)) (Z_to_bv 64 (S + 1096)) x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (S + 1096)) (Z_to_bv 64 (a_shs A + 396)) (Z_to_bv 64 (S + 64036)) (Z_to_bv 64 (S + 3168)) (Z_to_bv 64 2147450880) (Z_to_bv 64 (S + 60)) (Z_to_bv 64 (a_shs A + 7)) (Z_to_bv 64 (a_shs A + 395)) (Z_to_bv 64 S) (Z_to_bv 64 (a_shf A)) x28 x29 x30 x31)
          (a_F A) (Z_to_bv 64 0x83de0) (a_fc A) None m (seg_rom b0segs)).

End ACeilS1.
