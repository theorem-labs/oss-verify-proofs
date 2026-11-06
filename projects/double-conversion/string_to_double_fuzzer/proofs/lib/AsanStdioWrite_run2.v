(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import ImgA.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import PropExec CatExec CatSim SeqExec StepTac Hoare WalkTac StoreOk StreamSim MmapSim LibAtomic ExitSim ShapeAlg Nodes.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import AsanStdioDefs AsanStdioWrite_run1 Asan_code_10b000_10c000 Asan_code_113000_114000   .
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Section FPW_1. Context {fx : PropExec.FPState}.

Definition sw_regs_but (regs regs' : bvmap 5 word) : Prop :=
  getr regs' 2 = getr regs 2 /\ getr regs' 8 = getr regs 8 /\ getr regs' 9 = getr regs 9
  /\ getr regs' 21 = getr regs 21
  /\ getr regs' 3 = getr regs 3 /\ getr regs' 4 = getr regs 4
  /\ getr regs' 23 = getr regs 23 /\ getr regs' 24 = getr regs 24 /\ getr regs' 25 = getr regs 25
  /\ getr regs' 26 = getr regs 26 /\ getr regs' 27 = getr regs 27.

Lemma sw_c1_eq : forall regs mem rom (k : Z),
  getr regs 10 = Z_to_bv 64 k -> getr regs 22 = Z_to_bv 64 k ->
  (0 <= k < 2147483648)%Z ->
  exists regs',
    msteps ASEGS (mkst regs (0x1134fc : word) mem rom) (mkst regs' (0x113504 : word) mem rom)
    /\ getr regs' 10 = Z_to_bv 64 k /\ getr regs' 19 = getr regs 19 /\ getr regs' 20 = getr regs 20
    /\ getr regs' 18 = getr regs 18 /\ getr regs' 22 = getr regs 22
    /\ sw_regs_but regs regs'.
Proof.
  intros regs mem rom k Ha0 Hs6 K.
  eexists. split.
  - stepn F_1134fc D_1134fc.
    stepn F_10be6c D_10be6c.
    stepn F_10be70 D_10be70.
    stepb_tk F_10be74 D_10be74 ltac:(rewrite Ha0; unfold c_ltu, bv_ltu; apply Z.ltb_lt; u_norm; lia).
    stepret F_10bea0 D_10bea0 (0x113500 : word) ltac:(bveq).
    stepb_ft F_113500 D_113500 ltac:(rewrite Ha0, Hs6; apply c_eq_refl).
    apply mst_refl.
  - unfold sw_regs_but; repeat split; gres; try reflexivity. exact Ha0.
Qed.

Lemma sw_c1_ne : forall regs mem rom (k rem : Z),
  getr regs 10 = Z_to_bv 64 k -> getr regs 22 = Z_to_bv 64 rem ->
  (0 <= k < 2147483648)%Z -> (0 <= rem < 2^64)%Z -> k <> rem ->
  exists regs',
    msteps ASEGS (mkst regs (0x1134fc : word) mem rom) (mkst regs' (0x113590 : word) mem rom)
    /\ getr regs' 10 = Z_to_bv 64 k /\ getr regs' 19 = getr regs 19 /\ getr regs' 20 = getr regs 20
    /\ getr regs' 18 = getr regs 18 /\ getr regs' 22 = getr regs 22
    /\ sw_regs_but regs regs'.
Proof.
  intros regs mem rom k rem Ha0 Hs6 K REM NE.
  eexists. split.
  - stepn F_1134fc D_1134fc.
    stepn F_10be6c D_10be6c.
    stepn F_10be70 D_10be70.
    stepb_tk F_10be74 D_10be74 ltac:(rewrite Ha0; unfold c_ltu, bv_ltu; apply Z.ltb_lt; u_norm; lia).
    stepret F_10bea0 D_10bea0 (0x113500 : word) ltac:(bveq).
    stepb_tk F_113500 D_113500 ltac:(rewrite Ha0, Hs6, c_eq_Z by lia; apply Z.eqb_neq; lia).
    apply mst_refl.
  - unfold sw_regs_but; repeat split; gres; try reflexivity. exact Ha0.
Qed.

Lemma sw_c2_eq : forall regs mem rom (k : Z),
  getr regs 10 = Z_to_bv 64 k -> getr regs 22 = Z_to_bv 64 k ->
  (0 <= k < 2147483648)%Z ->
  exists regs',
    msteps ASEGS (mkst regs (0x113584 : word) mem rom) (mkst regs' (0x113504 : word) mem rom)
    /\ getr regs' 10 = Z_to_bv 64 k /\ getr regs' 19 = getr regs 20 /\ getr regs' 20 = getr regs 20
    /\ getr regs' 18 = getr regs 18 /\ getr regs' 22 = getr regs 22
    /\ sw_regs_but regs regs'.
Proof.
  intros regs mem rom k Ha0 Hs6 K.
  eexists. split.
  - stepn F_113584 D_113584.
    stepn F_10be6c D_10be6c.
    stepn F_10be70 D_10be70.
    stepb_tk F_10be74 D_10be74 ltac:(rewrite Ha0; unfold c_ltu, bv_ltu; apply Z.ltb_lt; u_norm; lia).
    stepret F_10bea0 D_10bea0 (0x113588 : word) ltac:(bveq).
    stepn F_113588 D_113588.
    stepb_tk F_11358c D_11358c ltac:(rewrite Ha0, Hs6; apply c_eq_refl).
    apply mst_refl.
  - unfold sw_regs_but; repeat split; gres; try reflexivity. exact Ha0.
Qed.

Lemma sw_c2_ne : forall regs mem rom (k rem : Z),
  getr regs 10 = Z_to_bv 64 k -> getr regs 22 = Z_to_bv 64 rem ->
  (0 <= k < 2147483648)%Z -> (0 <= rem < 2^64)%Z -> k <> rem ->
  exists regs',
    msteps ASEGS (mkst regs (0x113584 : word) mem rom) (mkst regs' (0x113590 : word) mem rom)
    /\ getr regs' 10 = Z_to_bv 64 k /\ getr regs' 19 = getr regs 20 /\ getr regs' 20 = getr regs 20
    /\ getr regs' 18 = getr regs 18 /\ getr regs' 22 = getr regs 22
    /\ sw_regs_but regs regs'.
Proof.
  intros regs mem rom k rem Ha0 Hs6 K REM NE.
  eexists. split.
  - stepn F_113584 D_113584.
    stepn F_10be6c D_10be6c.
    stepn F_10be70 D_10be70.
    stepb_tk F_10be74 D_10be74 ltac:(rewrite Ha0; unfold c_ltu, bv_ltu; apply Z.ltb_lt; u_norm; lia).
    stepret F_10bea0 D_10bea0 (0x113588 : word) ltac:(bveq).
    stepn F_113588 D_113588.
    stepb_ft F_11358c D_11358c ltac:(rewrite Ha0, Hs6, c_eq_Z by lia; apply Z.eqb_neq; lia).
    apply mst_refl.
  - unfold sw_regs_but; repeat split; gres; try reflexivity. exact Ha0.
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma sw_retry_a : forall regs mem rom (su f fd io ic cnt n0 rem : Z) (b0 : word),
  getr regs 10 = Z_to_bv 64 cnt -> getr regs 19 = Z_to_bv 64 io -> getr regs 18 = Z_to_bv 64 ic ->
  getr regs 22 = Z_to_bv 64 rem -> getr regs 9 = Z_to_bv 64 f -> getr regs 2 = Z_to_bv 64 (su - 112) ->
  (4294967296 + 112 <= su)%Z -> (su <= 0x800000000000)%Z ->
  (0x12e590 <= f)%Z -> (f + 232 <= 0x12e988)%Z ->
  (su - 104 <= io)%Z -> (io + 16 <= su - 72)%Z ->
  (1 <= ic <= 2)%Z ->
  (1 <= cnt <= n0)%Z -> (n0 < 2^62)%Z -> (cnt <= rem)%Z -> (rem < 2^62)%Z ->
  (bv_unsigned b0 + n0 <= 2^64)%Z ->
  store_ok ASEGS mem (Z_to_bv 64 (su - 112)) 112%nat = true ->
  rdn ASEGS mem (Z_to_bv 64 io) 8%nat = Some (word_to_le_bytes 8 b0) ->
  rdn ASEGS mem (Z_to_bv 64 (io + 8)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 n0)) ->
  rdn ASEGS mem (Z_to_bv 64 (f + 120)) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 fd)) ->
  (0 < fd < 2147483648)%Z ->
  exists regs',
    msteps ASEGS (mkst regs (0x113590 : word) mem rom)
      (mkst regs' (0x113580 : word)
        (wbytes (wbytes mem (Z_to_bv 64 io) (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned b0 + cnt))))
                (Z_to_bv 64 (io + 8)) (word_to_le_bytes 8 (Z_to_bv 64 (n0 - cnt)))) rom)
    /\ getr regs' 17 = Z_to_bv 64 66 /\ getr regs' 10 = Z_to_bv 64 fd
    /\ getr regs' 11 = Z_to_bv 64 io /\ getr regs' 12 = Z_to_bv 64 ic
    /\ getr regs' 18 = Z_to_bv 64 ic /\ getr regs' 19 = Z_to_bv 64 io /\ getr regs' 20 = Z_to_bv 64 io
    /\ getr regs' 22 = Z_to_bv 64 (rem - cnt)
    /\ sw_regs_but regs regs'.
Proof.
  intros regs mem rom su f fd io ic cnt n0 rem b0
         Ha0 Hs3 Hs2 Hs6 Hs1 Hsp SUlo SUhi Flo Fhi IOlo IOhi IC CNT N0 CR REM B0 SOK Mb0 Mn0 Mfd FD.
  pose proof (u64_range b0) as Hb0.
  eexists. split.
  - (* [comment removed for export] *)
    stepb_ft F_113590 D_113590 ltac:(rewrite Ha0; apply c_lts_pos_0; lia).
    (* [comment removed for export] *)
    stepLD8 F_113594 D_113594 (Z_to_bv 64 n0).
    (* [comment removed for export] *)
    stepn F_113598 D_113598. rewrite Ha0, (sltu_ge n0 cnt) by lia.
    (* [comment removed for export] *)
    stepn F_11359c D_11359c.
    stepn F_1135a0 D_1135a0. rewrite Hs3.
    (* [comment removed for export] *)
    stepLD8 F_1135a4 D_1135a4 b0.
    (* [comment removed for export] *)
    stepn F_1135a8 D_1135a8.
    stepn F_1135ac D_1135ac. rewrite v_and_0_l.
    stepn F_1135b0 D_1135b0. rewrite Ha0, (v_sub_Z cnt 0) by lia. rewrite Z.sub_0_r.
    (* [comment removed for export] *)
    stepn F_1135b4 D_1135b4. rewrite (v_add_wZ b0 cnt) by lia.
    (* [comment removed for export] *)
    stepST F_1135b8 D_1135b8 (Z_to_bv 64 io) (Z_to_bv 64 (bv_unsigned b0 + cnt)) ltac:(sok_frame SOK).
    (* [comment removed for export] *)
    stepb_tk F_1135bc D_1135bc ltac:(rewrite Ha0; unfold c_ltu, bv_ltu; u_norm; apply Z.ltb_ge; lia).
    (* [comment removed for export] *)
    stepn F_113554 D_113554.
    stepn F_113558 D_113558.
    stepn F_11355c D_11355c. rewrite Hs3, (v_add_ZZ' io 8) by lia.
    (* [comment removed for export] *)
    stepLD8 F_113560 D_113560 (Z_to_bv 64 n0).
    (* [comment removed for export] *)
    stepn F_113564 D_113564. rewrite Hs6, Ha0, (v_sub_Z rem cnt) by lia.
    (* [comment removed for export] *)
    stepLD F_113568 D_113568 (word_to_le_bytes 4 (Z_to_bv 64 fd)) (Z_to_bv 64 fd)
      ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
    rewrite (v_lw_small fd) by lia.
    (* [comment removed for export] *)
    stepn F_11356c D_11356c. rewrite Hs2, (v_subw_small_lit ic 0) by lia. rewrite Z.sub_0_r.
    (* [comment removed for export] *)
    stepn F_113570 D_113570. rewrite (v_sub_Z n0 cnt) by lia.
    stepST F_113574 D_113574 (Z_to_bv 64 (io + 8)) (Z_to_bv 64 (n0 - cnt)) ltac:(sok_frame SOK).
    (* [comment removed for export] *)
    stepn F_113578 D_113578.
    stepn F_11357c D_11357c.
    apply mst_refl.
  - unfold sw_regs_but; repeat split; gres; try reflexivity; try assumption.
Qed.


(* [comment removed for export] *)
Lemma sw_retry_b : forall regs mem rom (su f fd io cnt n0 n1 rem : Z) (b1 : word),
  getr regs 10 = Z_to_bv 64 cnt -> getr regs 19 = Z_to_bv 64 io -> getr regs 18 = Z_to_bv 64 2 ->
  getr regs 22 = Z_to_bv 64 rem -> getr regs 9 = Z_to_bv 64 f -> getr regs 2 = Z_to_bv 64 (su - 112) ->
  (4294967296 + 112 <= su)%Z -> (su <= 0x800000000000)%Z ->
  (0x12e590 <= f)%Z -> (f + 232 <= 0x12e988)%Z ->
  (su - 104 <= io)%Z -> (io + 32 <= su - 72)%Z ->
  (0 <= n0 < cnt)%Z -> (cnt <= rem)%Z -> (rem < 2^62)%Z -> (cnt - n0 <= n1)%Z -> (n1 < 2^62)%Z ->
  (bv_unsigned b1 + n1 <= 2^64)%Z ->
  store_ok ASEGS mem (Z_to_bv 64 (su - 112)) 112%nat = true ->
  rdn ASEGS mem (Z_to_bv 64 (io + 8)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 n0)) ->
  rdn ASEGS mem (Z_to_bv 64 (io + 16)) 8%nat = Some (word_to_le_bytes 8 b1) ->
  rdn ASEGS mem (Z_to_bv 64 (io + 24)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 n1)) ->
  rdn ASEGS mem (Z_to_bv 64 (f + 120)) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 fd)) ->
  (0 < fd < 2147483648)%Z ->
  exists regs',
    msteps ASEGS (mkst regs (0x113590 : word) mem rom)
      (mkst regs' (0x113580 : word)
        (wbytes (wbytes mem (Z_to_bv 64 (io + 16)) (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned b1 + (cnt - n0)))))
                (Z_to_bv 64 (io + 24)) (word_to_le_bytes 8 (Z_to_bv 64 (n1 - (cnt - n0))))) rom)
    /\ getr regs' 17 = Z_to_bv 64 66 /\ getr regs' 10 = Z_to_bv 64 fd
    /\ getr regs' 11 = Z_to_bv 64 (io + 16) /\ getr regs' 12 = Z_to_bv 64 1
    /\ getr regs' 18 = Z_to_bv 64 1 /\ getr regs' 19 = Z_to_bv 64 io /\ getr regs' 20 = Z_to_bv 64 (io + 16)
    /\ getr regs' 22 = Z_to_bv 64 (rem - cnt)
    /\ sw_regs_but regs regs'.
Proof.
  intros regs mem rom su f fd io cnt n0 n1 rem b1
         Ha0 Hs3 Hs2 Hs6 Hs1 Hsp SUlo SUhi Flo Fhi IOlo IOhi N0 CR REM N1 N1hi B1 SOK Mn0 Mb1 Mn1 Mfd FD.
  pose proof (u64_range b1) as Hb1.
  eexists. split.
  - (* [comment removed for export] *)
    stepb_ft F_113590 D_113590 ltac:(rewrite Ha0; apply c_lts_pos_0; lia).
    (* [comment removed for export] *)
    stepLD8 F_113594 D_113594 (Z_to_bv 64 n0).
    (* [comment removed for export] *)
    stepn F_113598 D_113598. rewrite Ha0, (sltu_lt n0 cnt) by lia.
    (* [comment removed for export] *)
    stepn F_11359c D_11359c.
    stepn F_1135a0 D_1135a0. rewrite Hs3, (v_add_ZZ' io 16) by lia.
    (* [comment removed for export] *)
    stepLD8 F_1135a4 D_1135a4 b1.
    (* [comment removed for export] *)
    stepn F_1135a8 D_1135a8.
    stepn F_1135ac D_1135ac. rewrite (v_and_m1_l n0) by lia.
    stepn F_1135b0 D_1135b0. rewrite Ha0, (v_sub_Z cnt n0) by lia.
    (* [comment removed for export] *)
    stepn F_1135b4 D_1135b4. rewrite (v_add_wZ b1 (cnt - n0)) by lia.
    (* [comment removed for export] *)
    stepST F_1135b8 D_1135b8 (Z_to_bv 64 (io + 16)) (Z_to_bv 64 (bv_unsigned b1 + (cnt - n0))) ltac:(sok_frame SOK).
    (* [comment removed for export] *)
    stepb_ft F_1135bc D_1135bc ltac:(rewrite Ha0; unfold c_ltu, bv_ltu; u_norm; apply Z.ltb_lt; lia).
    (* [comment removed for export] *)
    stepn F_1135c0 D_1135c0.
    stepn F_1135c4 D_1135c4.
    stepn F_113558 D_113558.
    stepn F_11355c D_11355c. rewrite Hs3, (v_add_ZZ' io 24) by lia.
    (* [comment removed for export] *)
    stepLD8 F_113560 D_113560 (Z_to_bv 64 n1).
    (* [comment removed for export] *)
    stepn F_113564 D_113564. rewrite Hs6, Ha0, (v_sub_Z rem cnt) by lia.
    (* [comment removed for export] *)
    stepLD F_113568 D_113568 (word_to_le_bytes 4 (Z_to_bv 64 fd)) (Z_to_bv 64 fd)
      ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
    rewrite (v_lw_small fd) by lia.
    (* [comment removed for export] *)
    stepn F_11356c D_11356c. rewrite Hs2. vals_lit.
    (* [comment removed for export] *)
    stepn F_113570 D_113570. rewrite (v_sub_Z n1 (cnt - n0)) by lia.
    stepST F_113574 D_113574 (Z_to_bv 64 (io + 24)) (Z_to_bv 64 (n1 - (cnt - n0))) ltac:(sok_frame SOK).
    (* [comment removed for export] *)
    stepn F_113578 D_113578.
    stepn F_11357c D_11357c.
    apply mst_refl.
  - unfold sw_regs_but; repeat split; gres; try reflexivity; try assumption.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition mem_sw2 (mem1 : word -> option byte) (f : Z) (bufp bufsz : word) :=
  wbytes (wbytes (wbytes mem1
    (Z_to_bv 64 (f + 32)) (word_to_le_bytes 8 (v_add bufp bufsz)))
    (Z_to_bv 64 (f + 40)) (word_to_le_bytes 8 bufp))
    (Z_to_bv 64 (f + 56)) (word_to_le_bytes 8 bufp).

Lemma sw_done : forall regs mem rom (su f : Z) (l bufp bufsz can ret s0v s1v s2v s3v s4v s5v s6v : word),
  getr regs 2 = Z_to_bv 64 (su - 112) ->
  getr regs 8 = l -> getr regs 9 = Z_to_bv 64 f ->
  getr regs 21 = Z_to_bv 64 0x686368 ->
  (4294967296 + 112 <= su)%Z -> (su <= 0x800000000000)%Z ->
  (0x12e590 <= f)%Z -> (f + 232 <= 0x12e988)%Z ->
  ret_ok ret ->
  rdn ASEGS mem (Z_to_bv 64 (su - 8)) 8%nat = Some (word_to_le_bytes 8 ret) ->
  rdn ASEGS mem (Z_to_bv 64 (su - 16)) 8%nat = Some (word_to_le_bytes 8 s0v) ->
  rdn ASEGS mem (Z_to_bv 64 (su - 24)) 8%nat = Some (word_to_le_bytes 8 s1v) ->
  rdn ASEGS mem (Z_to_bv 64 (su - 32)) 8%nat = Some (word_to_le_bytes 8 s2v) ->
  rdn ASEGS mem (Z_to_bv 64 (su - 40)) 8%nat = Some (word_to_le_bytes 8 s3v) ->
  rdn ASEGS mem (Z_to_bv 64 (su - 48)) 8%nat = Some (word_to_le_bytes 8 s4v) ->
  rdn ASEGS mem (Z_to_bv 64 (su - 56)) 8%nat = Some (word_to_le_bytes 8 s5v) ->
  rdn ASEGS mem (Z_to_bv 64 (su - 64)) 8%nat = Some (word_to_le_bytes 8 s6v) ->
  rdn ASEGS mem (Z_to_bv 64 (su - 72)) 8%nat = Some (word_to_le_bytes 8 can) ->
  rdn ASEGS mem (Z_to_bv 64 0x686368) 8%nat = Some (word_to_le_bytes 8 can) ->
  rdn ASEGS mem (Z_to_bv 64 (f + 88)) 8%nat = Some (word_to_le_bytes 8 bufp) ->
  rdn ASEGS mem (Z_to_bv 64 (f + 96)) 8%nat = Some (word_to_le_bytes 8 bufsz) ->
  exists regs',
    msteps ASEGS (mkst regs (0x113504 : word) mem rom)
                 (mkst regs' ret (mem_sw2 mem f bufp bufsz) rom)
    /\ getr regs' 10 = l /\ getr regs' 2 = Z_to_bv 64 su /\ getr regs' 1 = ret
    /\ getr regs' 8 = s0v /\ getr regs' 9 = s1v /\ getr regs' 18 = s2v /\ getr regs' 19 = s3v
    /\ getr regs' 20 = s4v /\ getr regs' 21 = s5v /\ getr regs' 22 = s6v
    /\ getr regs' 3 = getr regs 3 /\ getr regs' 4 = getr regs 4
    /\ getr regs' 23 = getr regs 23 /\ getr regs' 24 = getr regs 24 /\ getr regs' 25 = getr regs 25
    /\ getr regs' 26 = getr regs 26 /\ getr regs' 27 = getr regs 27.
Proof.
  intros regs mem rom su f l bufp bufsz can ret s0v s1v s2v s3v s4v s5v s6v
         Hsp Hs0 Hs1 Hs5 SUlo SUhi Flo Fhi Hret
         M8 M16 M24 M32 M40 M48 M56 M64 M72 Mcan Mbuf Mbsz.
  unfold mem_sw2. eexists. split.
  - (* [comment removed for export] *)
    stepLD F_113504 D_113504 (word_to_le_bytes 8 bufp) bufp ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_8).
    stepLD F_113508 D_113508 (word_to_le_bytes 8 bufsz) bufsz ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_8).
    stepn F_11350c D_11350c.
    (* [comment removed for export] *)
    stepST F_113510 D_113510 (Z_to_bv 64 (f + 32)) (v_add bufp bufsz) ltac:(sok_data).
    stepST F_113514 D_113514 (Z_to_bv 64 (f + 40)) bufp ltac:(sok_data).
    stepST F_113518 D_113518 (Z_to_bv 64 (f + 56)) bufp ltac:(sok_data).
    (* [comment removed for export] *)
    stepn F_11351c D_11351c. rewrite Hs0.
    stepLD F_113520 D_113520 (word_to_le_bytes 8 can) can ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_8).
    stepLD F_113524 D_113524 (word_to_le_bytes 8 can) can ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_8).
    stepb_ft F_113528 D_113528 ltac:(apply c_eq_refl).
    (* [comment removed for export] *)
    stepLD F_11352c D_11352c (word_to_le_bytes 8 ret) ret ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_8).
    stepLD F_113530 D_113530 (word_to_le_bytes 8 s0v) s0v ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_8).
    stepLD F_113534 D_113534 (word_to_le_bytes 8 s1v) s1v ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_8).
    stepLD F_113538 D_113538 (word_to_le_bytes 8 s2v) s2v ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_8).
    stepLD F_11353c D_11353c (word_to_le_bytes 8 s3v) s3v ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_8).
    stepLD F_113540 D_113540 (word_to_le_bytes 8 s4v) s4v ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_8).
    stepLD F_113544 D_113544 (word_to_le_bytes 8 s5v) s5v ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_8).
    stepLD F_113548 D_113548 (word_to_le_bytes 8 s6v) s6v ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_8).
    stepn F_11354c D_11354c. rewrite Hsp. sp_renorm.
    replace (su - 0)%Z with su by lia.
    stepret F_113550 D_113550 ret ltac:(reflexivity).
    apply mst_refl.
  - repeat split; gres; try reflexivity.
Qed.

(* [comment removed for export] *)
End FPW_1.


Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
