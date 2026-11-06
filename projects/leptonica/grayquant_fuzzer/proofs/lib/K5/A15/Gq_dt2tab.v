(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.Lib Require Import Tac.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.A15 Require Import ImageA.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.Lib Require Import RzCPS NodesA SysStep Arr.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.Lib Require Import StoreFast.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.PG Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.A15 Require Import Layout.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.A15 Require Import RT_iface RT_traces RT_gaps_iface LeptTac D_kit Lept_kit Lept_iface Lept_env LeptC_kit LeptL_kit.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Notation DT2_W tv t38 t14 := [(tv, tv + 1024); (t38, t38 + 1024); (t14, t14 + 1024)]%Z (only parsing).

(* [comment removed for export] *)
Definition dt2_geom (tv t38 t14 ca : Z) : Prop :=
  0 < tv /\ tv mod 16 = 0 /\ tv + 1024 <= 2^47 /\ (tv + 1024 <= 0x7fff7000 \/ 0x10007fff8000 <= tv) /\ (tv + 1024 <= 0x10000 \/ SEGTOP_A <= tv)
  /\ 0 < t38 /\ t38 mod 16 = 0 /\ t38 + 1024 <= 2^47 /\ (t38 + 1024 <= 0x7fff7000 \/ 0x10007fff8000 <= t38) /\ (t38 + 1024 <= 0x10000 \/ SEGTOP_A <= t38)
  /\ 0 < t14 /\ t14 mod 16 = 0 /\ t14 + 1024 <= 2^47 /\ (t14 + 1024 <= 0x7fff7000 \/ 0x10007fff8000 <= t14) /\ (t14 + 1024 <= 0x10000 \/ SEGTOP_A <= t14)
  /\ (tv + 1024 <= t38 \/ t38 + 1024 <= tv) /\ (tv + 1024 <= t14 \/ t14 + 1024 <= tv) /\ (t38 + 1024 <= t14 \/ t14 + 1024 <= t38)
  /\ 0 < ca /\ ca mod 8 = 0 /\ ca + 8 <= 2^47 /\ (ca + 8 <= tv \/ tv + 1024 <= ca) /\ (ca + 8 <= t38 \/ t38 + 1024 <= ca) /\ (ca + 8 <= t14 \/ t14 + 1024 <= ca).

(* [comment removed for export] *)
Definition dt2_exit (sp gp tp s0 s2 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (sa tv t38 t14 : Z) : machine_state -> Prop :=
  fun ms' => exists (ra' a0' a1' a2' a5' a6' s3' s6' s7' t6' : word) (m' : mem) (ws1 ws2 ws3 : list word),
    ms' = MS (mkR ra' sp gp tp (Z_to_bv 64 84) (Z_to_bv 64 1) (Z_to_bv 64 127) s0 (Z_to_bv 64 sa) a0' a1' a2' (Z_to_bv 64 250) (Z_to_bv 64 2)
                  a5' a6' (Z_to_bv 64 42) s2 s3' (Z_to_bv 64 SHB) (Z_to_bv 64 5) s6' s7' (Z_to_bv 64 tv) (Z_to_bv 64 t38) s10 s11
                  (Z_to_bv 64 169) (Z_to_bv 64 212) (Z_to_bv 64 1024) t6')
             F (Z_to_bv 64 0x9e638) fc None m' (seg_rom asegs)
    /\ munch (DT2_W tv t38 t14) m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ u32arr asegs m' tv ws1 /\ Z.of_nat (length ws1) = 256 /\ acc asegs m' tv 1024
    /\ u32arr asegs m' t38 ws2 /\ Z.of_nat (length ws2) = 256 /\ acc asegs m' t38 1024
    /\ u32arr asegs m' t14 ws3 /\ Z.of_nat (length ws3) = 256 /\ acc asegs m' t14 1024
    /\ rw_cells asegs m' (sa + 152) [C8 (Z_to_bv 64 t14)].

(* [comment removed for export] *)
Lemma dt2_tail : forall (i : Z) (ra sp gp tp s0 a0 a1 s2 s7 s10 s11 : word) (v : word) (F : bvmap 5 word) (fc : bv 32) (m0 m : mem)
    (sa tv t38 t14 : Z) (ws1 ws2 ws3 : list word) (Q : machine_state -> Prop),
  0 <= i <= 255 -> dt2_geom tv t38 t14 (sa + 152) ->
  munch (DT2_W tv t38 t14) m0 m -> wmono asegs m0 m -> mem_inv asegs m ->
  u32arr asegs m tv ws1 -> Z.of_nat (length ws1) = 256 -> acc asegs m tv 1024 ->
  u32arr asegs m t38 ws2 -> Z.of_nat (length ws2) = 256 -> acc asegs m t38 1024 ->
  u32arr asegs m t14 ws3 -> Z.of_nat (length ws3) = 256 -> acc asegs m t14 1024 ->
  rw_cells asegs m (sa + 152) [C8 (Z_to_bv 64 t14)] ->
  (forall (ra' a0' a1' : word) (m' : mem) (ws3' : list word),
      munch (DT2_W tv t38 t14) m0 m' -> wmono asegs m0 m' -> mem_inv asegs m' ->
      u32arr asegs m' tv ws1 -> acc asegs m' tv 1024 -> u32arr asegs m' t38 ws2 -> acc asegs m' t38 1024 ->
      u32arr asegs m' t14 ws3' -> Z.of_nat (length ws3') = 256 -> acc asegs m' t14 1024 ->
      rw_cells asegs m' (sa + 152) [C8 (Z_to_bv 64 t14)] ->
      evt asegs Q (MS (mkR ra' sp gp tp (Z_to_bv 64 84) (Z_to_bv 64 1) (Z_to_bv 64 127) s0 (Z_to_bv 64 sa) a0' a1' (Z_to_bv 64 (i + 1)) (Z_to_bv 64 250) (Z_to_bv 64 2)
                          (Z_to_bv 64 (87 - (i + 1))) (Z_to_bv 64 (4 * (i + 1))) (Z_to_bv 64 42) s2 (Z_to_bv 64 (i + 1 + 2)) (Z_to_bv 64 SHB) (Z_to_bv 64 5)
                          (Z_to_bv 64 (3 * (i + 1) + 4)) v (Z_to_bv 64 tv) (Z_to_bv 64 t38) s10 s11 (Z_to_bv 64 169) (Z_to_bv 64 212) (Z_to_bv 64 1024)
                          (Z_to_bv 64 (3 + 253 * (i + 1))))
                     F (Z_to_bv 64 0x9e1fc) fc None m' (seg_rom asegs))) ->
  evt asegs Q (MS (mkR ra sp gp tp (Z_to_bv 64 84) (Z_to_bv 64 1) (Z_to_bv 64 127) s0 (Z_to_bv 64 sa) a0 a1 (Z_to_bv 64 i) (Z_to_bv 64 250) (Z_to_bv 64 2)
                      (Z_to_bv 64 (87 - i)) (Z_to_bv 64 (4 * i)) (Z_to_bv 64 42) s2 (Z_to_bv 64 (i + 2)) (Z_to_bv 64 SHB) (Z_to_bv 64 5)
                      (Z_to_bv 64 (3 * i + 4)) v (Z_to_bv 64 tv) (Z_to_bv 64 t38) s10 s11 (Z_to_bv 64 169) (Z_to_bv 64 212) (Z_to_bv 64 1024)
                      (Z_to_bv 64 (3 + 253 * i)))
                 F (Z_to_bv 64 0x9e1c8) fc None m (seg_rom asegs)).
Proof.
  intros i ra sp gp tp s0 a0 a1 s2 s7 s10 s11 v F fc m0 m sa tv t38 t14 ws1 ws2 ws3 Q HI GEO MU WM MI UA1 UAL1 ACC1 UA2 UAL2 ACC2 UA3 UAL3 ACC3 CA CONT.
  pose proof GEO as (V0 & V16 & VHI & VSH & VSEG & W0 & W16 & WHI & WSH & WSEG & X0 & X16 & XHI & XSH & XSEG & D12 & D13 & D23 & CA0 & CA8 & CAHI & CD1 & CD2 & CD3).
  unfold SEGTOP_A, SHB in *.
  lwalk [0x9e1e0; 0x9e36c].
  arr_sw t14 i (t14 + 4 * i).
  lwalk [0x9e1fc].
  replace (4 * i + 4) with (4 * (i + 1)) by (clear; lia).
  replace (i + 3) with (i + 1 + 2) by (clear; lia).
  replace (3 * i + 7) with (3 * (i + 1) + 4) by (clear; lia).
  replace (87 - i + -1) with (87 - (i + 1)) by (clear; lia).
  replace (3 + 253 * i + 253) with (3 + 253 * (i + 1)) by (clear; lia).
  eapply CONT; try eassumption.
  all: lazymatch goal with |- munch _ _ _ => eapply munch_trans; eassumption | |- wmono _ _ _ => eapply wmono_trans; eassumption | |- ?g => idtac "LEFT:" g end.
Qed.

(* [comment removed for export] *)
Lemma dt2_round : forall (i : Z) (ra sp gp tp s0 a0 a1 s2 s7 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m0 m : mem)
    (sa tv t38 t14 : Z) (ws1 ws2 ws3 : list word) (Q : machine_state -> Prop),
  0 <= i <= 255 -> dt2_geom tv t38 t14 (sa + 152) ->
  munch (DT2_W tv t38 t14) m0 m -> wmono asegs m0 m -> mem_inv asegs m ->
  u32arr asegs m tv ws1 -> Z.of_nat (length ws1) = 256 -> acc asegs m tv 1024 ->
  u32arr asegs m t38 ws2 -> Z.of_nat (length ws2) = 256 -> acc asegs m t38 1024 ->
  u32arr asegs m t14 ws3 -> Z.of_nat (length ws3) = 256 -> acc asegs m t14 1024 ->
  rw_cells asegs m (sa + 152) [C8 (Z_to_bv 64 t14)] ->
  (forall (ra' a0' a1' s7' : word) (m' : mem) (ws1' ws2' ws3' : list word),
      munch (DT2_W tv t38 t14) m0 m' -> wmono asegs m0 m' -> mem_inv asegs m' ->
      u32arr asegs m' tv ws1' -> Z.of_nat (length ws1') = 256 -> acc asegs m' tv 1024 ->
      u32arr asegs m' t38 ws2' -> Z.of_nat (length ws2') = 256 -> acc asegs m' t38 1024 ->
      u32arr asegs m' t14 ws3' -> Z.of_nat (length ws3') = 256 -> acc asegs m' t14 1024 ->
      rw_cells asegs m' (sa + 152) [C8 (Z_to_bv 64 t14)] ->
      evt asegs Q (MS (mkR ra' sp gp tp (Z_to_bv 64 84) (Z_to_bv 64 1) (Z_to_bv 64 127) s0 (Z_to_bv 64 sa) a0' a1' (Z_to_bv 64 (i + 1)) (Z_to_bv 64 250) (Z_to_bv 64 2)
                          (Z_to_bv 64 (87 - (i + 1))) (Z_to_bv 64 (4 * (i + 1))) (Z_to_bv 64 42) s2 (Z_to_bv 64 (i + 1 + 2)) (Z_to_bv 64 SHB) (Z_to_bv 64 5)
                          (Z_to_bv 64 (3 * (i + 1) + 4)) s7' (Z_to_bv 64 tv) (Z_to_bv 64 t38) s10 s11 (Z_to_bv 64 169) (Z_to_bv 64 212) (Z_to_bv 64 1024)
                          (Z_to_bv 64 (3 + 253 * (i + 1))))
                     F (Z_to_bv 64 0x9e1fc) fc None m' (seg_rom asegs))) ->
  evt asegs Q (MS (mkR ra sp gp tp (Z_to_bv 64 84) (Z_to_bv 64 1) (Z_to_bv 64 127) s0 (Z_to_bv 64 sa) a0 a1 (Z_to_bv 64 i) (Z_to_bv 64 250) (Z_to_bv 64 2)
                      (Z_to_bv 64 (87 - i)) (Z_to_bv 64 (4 * i)) (Z_to_bv 64 42) s2 (Z_to_bv 64 (i + 2)) (Z_to_bv 64 SHB) (Z_to_bv 64 5)
                      (Z_to_bv 64 (3 * i + 4)) s7 (Z_to_bv 64 tv) (Z_to_bv 64 t38) s10 s11 (Z_to_bv 64 169) (Z_to_bv 64 212) (Z_to_bv 64 1024)
                      (Z_to_bv 64 (3 + 253 * i)))
                 F (Z_to_bv 64 0x9e15c) fc None m (seg_rom asegs)).
Proof.
  intros i ra sp gp tp s0 a0 a1 s2 s7 s10 s11 F fc m0 m sa tv t38 t14 ws1 ws2 ws3 Q HI GEO MU WM MI UA1 UAL1 ACC1 UA2 UAL2 ACC2 UA3 UAL3 ACC3 CA CONT.
  pose proof GEO as (V0 & V16 & VHI & VSH & VSEG & W0 & W16 & WHI & WSH & WSEG & X0 & X16 & XHI & XSH & XSEG & D12 & D13 & D23 & CA0 & CA8 & CAHI & CD1 & CD2 & CD3).
  unfold SEGTOP_A, SHB in *.
  (* [comment removed for export] *)
  assert (TL : forall (ra1 a01 a11 v : word) (m1 : mem) (ws1x ws2x : list word),
      munch (DT2_W tv t38 t14) m0 m1 -> wmono asegs m0 m1 -> mem_inv asegs m1 ->
      u32arr asegs m1 tv ws1x -> Z.of_nat (length ws1x) = 256 -> acc asegs m1 tv 1024 ->
      u32arr asegs m1 t38 ws2x -> Z.of_nat (length ws2x) = 256 -> acc asegs m1 t38 1024 ->
      u32arr asegs m1 t14 ws3 -> acc asegs m1 t14 1024 -> rw_cells asegs m1 (sa + 152) [C8 (Z_to_bv 64 t14)] ->
      evt asegs Q (MS (mkR ra1 sp gp tp (Z_to_bv 64 84) (Z_to_bv 64 1) (Z_to_bv 64 127) s0 (Z_to_bv 64 sa) a01 a11 (Z_to_bv 64 i) (Z_to_bv 64 250) (Z_to_bv 64 2)
                          (Z_to_bv 64 (87 - i)) (Z_to_bv 64 (4 * i)) (Z_to_bv 64 42) s2 (Z_to_bv 64 (i + 2)) (Z_to_bv 64 2147450880) (Z_to_bv 64 5)
                          (Z_to_bv 64 (3 * i + 4)) v (Z_to_bv 64 tv) (Z_to_bv 64 t38) s10 s11 (Z_to_bv 64 169) (Z_to_bv 64 212) (Z_to_bv 64 1024)
                          (Z_to_bv 64 (3 + 253 * i)))
                     F (Z_to_bv 64 0x9e1c8) fc None m1 (seg_rom asegs))).
  { intros ra1 a01 a11 v m1 ws1x ws2x MU1 WM1 MI1 UA1x UAL1x ACC1x UA2x UAL2x ACC2x UA3x ACC3x CAx.
    eapply (dt2_tail i) with (m0 := m0) (ws1 := ws1x) (ws2 := ws2x) (ws3 := ws3); try eassumption.
    intros ra' a0' a1' m' ws3' MU' WM' MI' UA1' ACC1' UA2' ACC2' UA3' UAL3' ACC3' CA'.
    eapply CONT; eassumption. }
  clear CONT.
  lwalk [0x9e1c8].
  brfork R1.
  - (* [comment removed for export] *)
    lwalk [0x9e1a8; 0x9e1c8].
    arr_sw tv i (tv + 4 * i).
    lwalk [0x9e1c4; 0x9e1c8].
    arr_sw t38 i (t38 + 4 * i).
    eapply TL; eassumption.
  - lwalk [0x9e1c8]. brfork R2.
    + (* [comment removed for export] *)
      lwalk [0x9e1c8]. brfork R3.
      * (* [comment removed for export] *)
        lwalk [0x9e1c8]. brfork R4.
        -- (* [comment removed for export] *)
           lwalk [0x9e1c8]. brfork R5.
           ++ (* [comment removed for export] *)
              lwalk [0x9e1c8]. brfork R6.
              ** (* [comment removed for export] *)
                 lwalk [0x9e310; 0x9e1c8].
                 arr_sw tv i (tv + 4 * i).
                 lwalk [0x9e33c; 0x9e1c4; 0x9e1c8].
                 brfork R7.
                 --- (* [comment removed for export] *)
                     lwalk [0x9e1c4; 0x9e1c8].
                     arr_sw t38 i (t38 + 4 * i).
                     eapply TL; eassumption.
                 --- (* [comment removed for export] *)
                     lwalk [0x9e33c; 0x9e1c8].
                     arr_sw t38 i (t38 + 4 * i).
                     lwalk [0x9e1c8].
                     eapply TL; eassumption.
              ** (* [comment removed for export] *)
                 lwalk [0x9e2d4; 0x9e1c8].
                 arr_sw tv i (tv + 4 * i).
                 lwalk [0x9e2f4; 0x9e1c8].
                 arr_sw t38 i (t38 + 4 * i).
                 lwalk [0x9e1c8].
                 eapply TL; eassumption.
           ++ (* [comment removed for export] *)
              lwalk [0x9e28c; 0x9e1c8].
              arr_sw tv i (tv + 4 * i).
              lwalk [0x9e2b4; 0x9e1c8].
              arr_sw t38 i (t38 + 4 * i).
              lwalk [0x9e1c8].
              eapply TL; eassumption.
        -- (* [comment removed for export] *)
           lwalk [0x9e250; 0x9e1c8].
           arr_sw tv i (tv + 4 * i).
           lwalk [0x9e270; 0x9e1c8].
           arr_sw t38 i (t38 + 4 * i).
           lwalk [0x9e1c8].
           eapply TL; eassumption.
      * (* [comment removed for export] *)
        lwalk [0x9e210; 0x9e1c8].
        arr_sw tv i (tv + 4 * i).
        lwalk [0x9e234; 0x9e1c8].
        arr_sw t38 i (t38 + 4 * i).
        lwalk [0x9e1c8].
        eapply TL; eassumption.
    + (* [comment removed for export] *)
      lwalk [0x9e178; 0x9e1c8].
      arr_sw tv i (tv + 4 * i).
      lwalk [0x9e194; 0x9e1c8].
      arr_sw t38 i (t38 + 4 * i).
      lwalk [0x9e1c8].
      eapply TL; eassumption.
Qed.

(* [comment removed for export] *)
Lemma dt2_tables : forall (k : nat) (i : Z) (ra sp gp tp s0 a0 a1 s2 s7 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m0 m : mem)
    (sa tv t38 t14 : Z) (ws1 ws2 ws3 : list word),
  Z.of_nat k = 256 - i -> 0 <= i -> (1 <= k)%nat -> dt2_geom tv t38 t14 (sa + 152) ->
  munch (DT2_W tv t38 t14) m0 m -> wmono asegs m0 m -> mem_inv asegs m ->
  u32arr asegs m tv ws1 -> Z.of_nat (length ws1) = 256 -> acc asegs m tv 1024 ->
  u32arr asegs m t38 ws2 -> Z.of_nat (length ws2) = 256 -> acc asegs m t38 1024 ->
  u32arr asegs m t14 ws3 -> Z.of_nat (length ws3) = 256 -> acc asegs m t14 1024 ->
  rw_cells asegs m (sa + 152) [C8 (Z_to_bv 64 t14)] ->
  evt asegs (dt2_exit sp gp tp s0 s2 s10 s11 F fc m0 sa tv t38 t14)
    (MS (mkR ra sp gp tp (Z_to_bv 64 84) (Z_to_bv 64 1) (Z_to_bv 64 127) s0 (Z_to_bv 64 sa) a0 a1 (Z_to_bv 64 i) (Z_to_bv 64 250) (Z_to_bv 64 2)
             (Z_to_bv 64 (87 - i)) (Z_to_bv 64 (4 * i)) (Z_to_bv 64 42) s2 (Z_to_bv 64 (i + 2)) (Z_to_bv 64 SHB) (Z_to_bv 64 5)
             (Z_to_bv 64 (3 * i + 4)) s7 (Z_to_bv 64 tv) (Z_to_bv 64 t38) s10 s11 (Z_to_bv 64 169) (Z_to_bv 64 212) (Z_to_bv 64 1024)
             (Z_to_bv 64 (3 + 253 * i)))
        F (Z_to_bv 64 0x9e15c) fc None m (seg_rom asegs)).
Proof.
  induction k as [|k IH]; intros i ra sp gp tp s0 a0 a1 s2 s7 s10 s11 F fc m0 m sa tv t38 t14 ws1 ws2 ws3 HK HI HK1 GEO MU WM MI UA1 UAL1 ACC1 UA2 UAL2 ACC2 UA3 UAL3 ACC3 CA.
  { exfalso. lia. }
  eapply dt2_round with (m0 := m0); try eassumption; [clear - HK HI; lia|].
  intros ra' a0' a1' s7' m' ws1' ws2' ws3' MU' WM' MI' UA1' UAL1' ACC1' UA2' UAL2' ACC2' UA3' UAL3' ACC3' CA'.
  clear MU WM MI UA1 UAL1 ACC1 UA2 UAL2 ACC2 UA3 UAL3 ACC3 CA.
  unfold SHB in *.
  destruct k as [|k].
  - (* [comment removed for export] *)
    assert (EI : i + 1 = 256) by (clear - HK; lia).
    lwalk [0x9e638; 0x9e15c].
    apply evt_done. unfold dt2_exit.
    do 10 eexists. exists m', ws1', ws2', ws3'.
    split; [reflexivity|].
    repeat (split; [assumption|]). assumption.
  - lwalk [0x9e638; 0x9e15c].
    replace (i + 3) with (i + 1 + 2) by (clear; lia).
    eapply (IH (i + 1)) with (m0 := m0); try eassumption; clear - HK HI; lia.
Qed.
