(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.K5.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.K5.Lib Require Import Tac.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.K5.A17 Require Import ImageA.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.K5.Lib Require Import RzCPS NodesA SysStep Arr.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.K5.Lib Require Import StoreFast.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.K5.PG Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.K5.A17 Require Import Layout.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.K5.A17 Require Import RT_iface RT_traces RT_gaps_iface LeptTac D_kit Lept_kit Lept_iface Lept_env LeptC_kit.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Lemma bytes_at_read4 : forall (m : mem) A bs (i : Z), bytes_at asegs m A bs -> 0 <= i -> i + 4 <= Z.of_nat (length bs) ->
  exists b0 b1 b2 b3 : byte, ov_read_bytes asegs m (wa (A + i)) 4 = Some [b0; b1; b2; b3].
Proof.
  intros m A bs i Hb H0 H1.
  pose proof (bytes_at_ov_read asegs m A bs (Z.to_nat i) 4 Hb ltac:(lia)) as R. rewrite Z2Nat.id in R by lia.
  remember (firstn 4 (skipn (Z.to_nat i) bs)) as l eqn:El.
  assert (L : length l = 4%nat) by (subst l; rewrite firstn_length_le; [reflexivity| rewrite length_skipn; lia]).
  destruct l as [|b0 [|b1 [|b2 [|b3 [|]]]]]; cbn in L; try discriminate. exists b0, b1, b2, b3. exact R.
Qed.

(* [comment removed for export] *)
Lemma le_bytes_roundtrip : forall bs : list byte, Z_to_le_bytes (length bs) (bytes_le_to_Z bs) = bs.
Proof.
  induction bs as [|b bs IH]; [reflexivity|]. cbn [length Z_to_le_bytes bytes_le_to_Z].
  pose proof (bv_unsigned_in_range 8 b) as Rb. unfold bv_modulus in Rb. change (2 ^ Z.of_N 8) with 256 in Rb.
  f_equal.
  - apply bv_eq. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with (2 ^ 8).
    rewrite <- Z.land_ones by lia. rewrite Z.land_lor_distr_l.
    rewrite (Z.land_ones (bv_unsigned b)) by lia. rewrite (Z.mod_small (bv_unsigned b)) by (change (2 ^ 8) with 256; lia).
    replace (Z.land (Z.shiftl (bytes_le_to_Z bs) 8) (Z.ones 8)) with 0; [apply Z.lor_0_r|].
    symmetry. apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, Z.bits_0.
    destruct (Z.ltb_spec n 8) as [L|G].
    + rewrite Z.shiftl_spec_low by lia. reflexivity.
    + rewrite Z.ones_spec_high by lia. apply andb_false_r.
  - rewrite Z.shiftr_lor, Z.shiftr_shiftl_l by lia. rewrite Z.sub_diag, Z.shiftl_0_r.
    replace (Z.shiftr (bv_unsigned b) 8) with 0; [rewrite Z.lor_0_l; exact IH|].
    symmetry. rewrite Z.shiftr_div_pow2 by lia. apply Z.div_small. change (2 ^ 8) with 256. lia.
Qed.

(* [comment removed for export] *)
Lemma bytes_at_read4w : forall (m : mem) A bs (i : Z), bytes_at asegs m A bs -> 0 <= i -> i + 4 <= Z.of_nat (length bs) ->
  exists w : word, ov_read_bytes asegs m (wa (A + i)) 4 = Some (le4 w).
Proof.
  intros m A bs i Hb H0 H1. destruct (bytes_at_read4 m A bs i Hb H0 H1) as (b0 & b1 & b2 & b3 & R).
  exists (Z_to_bv 64 (bytes_le_to_Z [b0; b1; b2; b3])). rewrite R. f_equal.
  unfold le4. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64).
  rewrite (Z_to_le_bytes_mod 4 _ 64) by lia. symmetry. exact (le_bytes_roundtrip [b0; b1; b2; b3]).
Qed.

(* [comment removed for export] *)
Lemma land4q : forall q s, 0 <= s < 4 -> Z.land (4 * q) s = 0.
Proof.
  intros q s Hs.
  assert (E : s = Z.land 3 s) by (assert (s = 0 \/ s = 1 \/ s = 2 \/ s = 3) as [->|[->|[->| ->]]] by lia; reflexivity).
  rewrite E, Z.land_assoc. replace (Z.land (4 * q) 3) with 0; [apply Z.land_0_l|].
  symmetry. change 3 with (Z.ones 2). rewrite Z.land_ones by lia. change (2 ^ 2) with 4. rewrite Z.mul_comm. apply Z.mod_mul. lia.
Qed.
Lemma lxor3_eq : forall x, Z.lxor x 3 = x + 3 - 2 * (x mod 4).
Proof.
  intros x. pose proof (Z.div_mod x 4 ltac:(lia)) as E. pose proof (Z.mod_pos_bound x 4 ltac:(lia)) as R.
  set (q := x / 4) in *. set (r := x mod 4) in *.
  rewrite E at 1. rewrite (Z.add_nocarry_lxor (4 * q) r) by (apply land4q; lia). rewrite Z.lxor_assoc.
  assert (L : Z.lxor r 3 = 3 - r) by (assert (r = 0 \/ r = 1 \/ r = 2 \/ r = 3) as [->|[->|[->| ->]]] by lia; reflexivity).
  rewrite L. rewrite <- (Z.add_nocarry_lxor (4 * q) (3 - r)) by (apply land4q; lia). lia.
Qed.

(* [comment removed for export] *)
Ltac shbr_merge_inv ru FAST OK :=
  lazymatch goal with
  | |- evt ?segs ?Q (MS ?R ?F _ ?fc ?rv ?m ?ro) =>
      eapply (evt_cut segs (fun ms' => exists u' : word,
                 ms' = MS (@bvmap_set 5 word ru u' R) F (Z_to_bv 64 FAST) fc rv m ro));
      [ destruct OK as [OK|[OK ?]];
        [ brT; apply evt_done;
          lazymatch goal with |- exists u', _ = MS (@bvmap_set 5 word ?r u' ?R') _ _ _ _ _ _ =>
            let p := eval vm_compute in (bv_key r) in
            let v := eval cbv beta iota delta [tget mkR] in (tget p R') in
            lazymatch v with Some ?x => exists x end end;
          norm_regset; reflexivity
        | brF; bsteps_to FAST; apply evt_done; eexists; norm_regset; reflexivity ]
      | let u' := fresh "u" in let E := fresh "E" in let ms := fresh "ms" in
        intros ms (u' & E); subst ms; norm_regset; clear OK ]
  end.
Ltac shbr_inv :=
  lazymatch goal with
  | |- evt ?segs ?Q (MS ?R ?F (if ?c then Z_to_bv 64 ?FAST else Z_to_bv 64 ?SLOW) ?fc ?rv ?m ?ro) =>
      let b := shbyte_of c in
      lazymatch goal with
      | K : shk m b ?X |- _ =>
          instr_at segs SLOW ltac:(fun i =>
            lazymatch i with
            | OpImm ALU_AND ?ru _ _ =>
                let S4 := eval vm_compute in (SLOW + 4)%Z in
                instr_at segs S4 ltac:(fun i2 =>
                  let szm1 := lazymatch i2 with
                              | OpImm ALU_ADD _ _ ?imm => eval vm_compute in (bv_unsigned imm)
                              | _ => constr:(0%Z) end in
                  let sz := eval vm_compute in (szm1 + 1)%Z in
                  let OK := fresh "SHOK" in
                  first [
                    match goal with
                    | ACC : acc asegs m ?a ?n |- _ =>
                        assert (OK : sh_ok b (X + sz - 1)) by (apply (shk_ok m a n X sz b ACC K); lia)
                    end
                  | fail 1 "shbr_inv: cannot prove the access addressable:" X sz ];
                  let BB := fresh "BB" in
                  assert (BB : 0 <= bv_unsigned b < 8)
                    by (pose proof (bv_unsigned_in_range 8 b); destruct OK as [?|[? ?]]; lia);
                  rewrite ?(sxb_small b) by lia;
                  shbr_merge_inv ru FAST OK; clear K BB)
            end)
      end
  end.

(* [comment removed for export] *)
Ltac shbr_x3 :=
  lazymatch goal with
  | |- evt ?segs ?Q (MS ?R ?F (if ?c then Z_to_bv 64 ?SLOW else Z_to_bv 64 ?FAST) ?fc ?rv ?m ?ro) =>
      let b := shbyte_of c in
      lazymatch goal with
      | K : shk m b ?X |- _ =>
          let KY := fresh "SHKY" in let LX := fresh "LX3" in
          pose proof (lxor3_eq X) as LX;
          assert (KY : shk m b (Z.lxor X 3))
            by (unfold shk, shad in *; replace (Z.lxor X 3 / 8) with (X / 8) by (rewrite LX; Z.div_mod_to_equations; lia); exact K);
          clear K; shbr; try clear LX
      end
  end.

(* [comment removed for export] *)
Lemma srliw_idx : forall j d, 0 <= j < 2^31 -> 0 < d -> bv_swrap 32 (bv_wrap 32 j / d) mod 18446744073709551616 = j / d.
Proof.
  intros j d Hj Hd. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 32) with (2 ^ 32). rewrite (Z.mod_small j) by lia.
  assert (R : 0 <= j / d < 2^31) by (split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; nia]).
  rewrite bv_swrap_small by (change (bv_half_modulus 32) with (2^31); lia). apply Z.mod_small. lia.
Qed.

(* [comment removed for export] *)
Lemma u32s_exists : forall (k : nat) (bs : list byte), length bs = (4 * k)%nat -> exists ws : list word, u32s ws = bs /\ length ws = k.
Proof.
  induction k as [|k IH]; intros bs L.
  - destruct bs; [exists []; split; reflexivity| discriminate].
  - destruct bs as [|b0 [|b1 [|b2 [|b3 rest]]]]; cbn [length] in L; try lia.
    destruct (IH rest ltac:(lia)) as (ws & E & Lw).
    exists (Z_to_bv 64 (bytes_le_to_Z [b0; b1; b2; b3]) :: ws). split; [| cbn [length]; lia].
    cbn [u32s]. rewrite E. change (b0 :: b1 :: b2 :: b3 :: rest) with ([b0; b1; b2; b3] ++ rest). f_equal.
    change (Mem.le4 ?v) with (le4 v).
    unfold le4. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64).
    rewrite (Z_to_le_bytes_mod 4 _ 64) by lia. exact (le_bytes_roundtrip [b0; b1; b2; b3]).
Qed.
Lemma u8arr_u32arr : forall (m : mem) A bs (k : Z), u8arr asegs m A bs -> Z.of_nat (length bs) = 4 * k ->
  exists ws : list word, u32arr asegs m A ws /\ Z.of_nat (length ws) = k.
Proof.
  intros m A bs k [Hb Hw] L. destruct (u32s_exists (Z.to_nat k) bs ltac:(lia)) as (ws & E & Lw).
  exists ws. split; [| lia]. split; [rewrite E; exact Hb|]. replace (4 * Z.of_nat (length ws)) with (Z.of_nat (length bs)) by lia. exact Hw.
Qed.
Lemma u32arr_u8arr : forall (m : mem) A ws, u32arr asegs m A ws -> u8arr asegs m A (u32s ws).
Proof. intros m A ws [Hb Hw]. split; [exact Hb|]. rewrite u32s_length. replace (Z.of_nat (4 * length ws)) with (4 * Z.of_nat (length ws)) by lia. exact Hw. Qed.
Lemma u32arr_nth : forall (ws : list word) (i : Z), 0 <= i < Z.of_nat (length ws) -> exists w, nth_error ws (Z.to_nat i) = Some w.
Proof. intros ws i Hi. destruct (nth_error ws (Z.to_nat i)) as [w|] eqn:E; [exists w; reflexivity|]. apply nth_error_None in E. lia. Qed.

(* [comment removed for export] *)
Ltac arr_sw A idx E :=
  lazymatch goal with
  | UA : u32arr asegs ?mm A ?ws, UAL : Z.of_nat (length ?ws) = _ |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    let SOK := fresh "SOK" in
    pose proof (u32arr_store_ok asegs mm A ws idx (wa E) UA ltac:(lia) ltac:(f_equal; lia)) as SOK;
    zstep;
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem mm (Z_to_bv 64 ?E') (le4 ?v)) _) =>
      let N := fresh "UA" in
      assert (N : u32arr asegs (write_to_mem mm (wa E') (le4 v)) A (upd ws (Z.to_nat idx) v))
        by (replace E' with (A + 4 * idx) by lia; apply (u32arr_write asegs mm A ws idx v UA); lia);
      clear UA; store_done; rename N into UA;
      rewrite <- (upd_length ws (Z.to_nat idx) v) in UAL;
      let ws' := fresh "aws" in set (ws' := upd ws (Z.to_nat idx) v) in *; clearbody ws'; try clear ws
    end
  end.

(* [comment removed for export] *)
Ltac lwalk1 :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) => first [ shbr | shbr0 | shbr_inv | shbr_x3 | br ]
  | |- evt _ _ (MS _ _ (Z_to_bv 64 _) _ _ _ _) => first [ shload; lstep; clear_shl | special_step | frame_step | lstep; try sb_fix; try fix_land32; shnorm ]
  end.
Ltac lwalk stops := repeat (tryif at_stop stops then fail else lwalk1).
Ltac swrap32_fix := repeat match goal with |- context [bv_swrap 32 ?z] =>
  rewrite (bv_swrap_small 32 z) by (change (bv_half_modulus 32) with (2^31); lia) end.

Ltac show_pc := lazymatch goal with |- evt _ _ (MS _ _ ?pc _ _ _ _) => idtac "PC:" pc end.
Ltac show_regs := lazymatch goal with |- evt _ _ (MS ?R _ _ _ _ _ _) => idtac "REGS:" R end.
