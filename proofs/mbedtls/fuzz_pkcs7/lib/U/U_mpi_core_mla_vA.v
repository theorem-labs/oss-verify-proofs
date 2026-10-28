(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk MpiCoreAux MpiWalkAux.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import UImg U_mpi_core_mla U_mpi_mul_int_W U_mpi_core_mla_v1.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Ltac wrvf_tac H L L1 FS FS1 i :=
  let SOK := fresh "SOK" in let H' := fresh "HX'" in
  lazymatch type of H with
  | u32arr ?sg ?mm ?A ?l =>
      pose proof (u32arr_store_ok sg mm A l i _ H ltac:(lia) ltac:(f_equal; lia)) as SOK;
      zstep;
      lazymatch goal with |- context [write_to_mem _ _ (le4 ?v)] =>
        pose proof (u32arr_write sg mm A l i v H ltac:(lia)) as H';
        lazymatch type of L with _ = ?r =>
          assert (L1 : Z.of_nat (length (upd l (Z.to_nat i) v)) = r) by (rewrite upd_length; exact L) end;
        pose proof (same_from_upd _ _ _ v FS) as FS1;
        store_done; try clear H; rename H' into H
      end
  end.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaOrc. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= orc_lia. (* [comment removed for export] *)

Tactic Notation "wrvf" constr(H) constr(L) ident(L1) constr(FS) ident(FS1) constr(i) := wrvf_tac H L L1 FS FS1 i.

(* [comment removed for export] *)
Section Walk.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : mem)
            (D dl S sl ld ls lo b : Z) (ds0 ss : list word).
  Hypothesis Hdl : 0 <= dl <= 10000.
  Hypothesis Hsl : 0 <= sl <= dl.
  Hypothesis Ln : dl <= ld /\ sl <= ls.
  Hypothesis L0 : Z.of_nat (length ds0) = ld.
  Hypothesis LS : Z.of_nat (length ss) = ls.
  Hypothesis DB : 0 < D /\ D + 4 * ld < 2^64.
  Hypothesis SB : 0 <= S /\ S + 4 * ls < 2^64.
  Hypothesis ALD : D mod 4 = 0.
  Hypothesis ALS : S mod 4 = 0.
  Hypothesis NZS : sl = 0 \/ 0 < S.
  Hypothesis SPR : 0 <= bv_unsigned sp < 2^64.
  Hypothesis LO : lo <= bv_unsigned sp - 48.
  Hypothesis SX : D + 4 * ld <= lo \/ bv_unsigned sp <= D.
  Hypothesis SSX : S + 4 * ls <= lo \/ bv_unsigned sp <= S.
  Hypothesis RA : bv_unsigned ra mod 2 = 0.
  Hypothesis HB : 0 <= b < 2^32.

  Notation POST := (mpi_core_mla_vpost usegs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc D dl ds0 sl ss b lo m).
  Notation W := [(D, D + 4 * dl); (bv_unsigned sp - 48, bv_unsigned sp)].
  Notation FRAME mm := (rw_cells usegs mm (bv_unsigned sp + -48) [C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0]).
  Notation SFACT0 := ((S = D /\ ss = ds0) \/ (bytes_at usegs m S (u32s ss) /\ (S + 4 * ls <= D \/ D + 4 * ld <= S))).
  Notation DINV mm ds := (u32arr usegs mm D ds /\ Z.of_nat (length ds) = ld
                          /\ munch W m mm /\ wmono usegs m mm /\ mem_inv usegs mm /\ stk usegs mm lo (bv_unsigned sp + -48)).
  Notation VINV ds i k c wc := (same_from (Z.to_nat i) ds ds0 /\ 0 <= c < 2^32 /\ bv_unsigned wc = sxz c
                                /\ lval ds i + 2^(32*i) * c = lval ds0 i + lval ss k * b).
  Notation SP := (Z_to_bv 64 (bv_unsigned sp + -48)).

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  #[using="Hdl Hsl Ln L0 LS DB SB ALD ALS NZS SPR LO SX SSX RA HB"] Lemma vx8_segA : forall (j : Z) (ds : list word) (mm : mem) (c : Z) (wc : word)
      (xs0 xs1 xs2 xs3 xs4 xs5 : word) (wt0 wn wt2 wa1 wa2 wa3 wa4 wa5 wa6 wa7 wt3 wt4 wt5 wt6 : word)
      (Q : machine_state -> Prop),
    0 <= j -> 8 * j + 8 <= sl ->
    wt0 = Z_to_bv 64 (S + 32 * j) -> wt2 = Z_to_bv 64 b -> wa2 = Z_to_bv 64 (S + 32 * j) ->
    wa4 = Z_to_bv 64 (D + 32 * j) -> wa5 = Z_to_bv 64 (D + 32 * j) ->
    wt3 = Z_to_bv 64 0 -> wt4 = Z_to_bv 64 0 -> wt5 = Z_to_bv 64 4 -> wt6 = Z_to_bv 64 (-5) ->
    DINV mm ds -> SFACT0 -> FRAME mm -> VINV ds (8 * j) (8 * j) c wc ->
    (forall (ds4 : list word) (m4 : mem) (c4 : Z) (wc4 ws4 wd4 ya0 ya5 ys3 ys5 : word),
       ya0 = Z_to_bv 64 (D + 32 * j + 16) -> ya5 = Z_to_bv 64 (S + 32 * j + 16) ->
       DINV m4 ds4 -> FRAME m4 -> VINV ds4 (8 * j + 4) (8 * j + 4) c4 wc4 ->
       limb32 ss (Z.to_nat (8 * j + 4)) = w32 ws4 -> limb32 ds0 (Z.to_nat (8 * j + 4)) = w32 wd4 ->
       evt usegs Q (MS (mkR ra SP gp tp wt0 wn wt2 (Z_to_bv 64 (D + 32 * j)) (Z_to_bv 64 (S + 32 * j)) ya0 wa1 (sx32 wd4)
                            wa3 wa4 ya5 wa6 wa7 wc4 ys3 (zx32 ws4) ys5 s6 s7 s8 s9 s10 s11 wt3 wt4 wt5 wt6)
                       F (Z_to_bv 64 0x23b1c) fc None m4 (seg_rom usegs))) ->
    evt usegs Q (MS (mkR ra SP gp tp wt0 wn wt2 xs0 xs1 wc wa1 wa2 wa3 wa4 wa5 wa6 wa7 xs2 xs3 xs4 xs5
                         s6 s7 s8 s9 s10 s11 wt3 wt4 wt5 wt6) F (Z_to_bv 64 0x23a00) fc None mm (seg_rom usegs))
(* [comment removed for export] *).
  Proof.
    intros j ds mm c wc xs0 xs1 xs2 xs3 xs4 xs5 wt0 wn wt2 wa1 wa2 wa3 wa4 wa5 wa6 wa7 wt3 wt4 wt5 wt6 Q Hj Hj8
      -> -> -> -> -> -> -> -> -> (HX & LX & MU & WM & MI & ST) AS FR (FS & HC & WC & VI) K.
    assert (SPOS : 0 < S) by lia.
    replace (8 * j) with (8 * j + 0) in FS, VI by lia.
    zstep. zstep. chk. zstep. zstep. chk. zstep. chk. zstep. zstep. chk. zstep. chk. zstep. chk.
    rdsf AS MU WM HX FS LX L0 LS LO SSX sl (8 * j + 0) ws0 Us0.
    rdd HX FS (8 * j + 0) wd0 Ud0.
    zstep. zstep. zstep. zstep.
    wrvf HX LX LX1 FS FS1 (8 * j + 0).
    zstep. chk. zstep. zstep. chk.
    zstep. zstep. zstep.
    rdsf AS MU WM HX FS1 LX1 L0 LS LO SSX sl (8 * j + 1) ws1 Us1.
    zstep.
    rdd HX FS1 (8 * j + 1) wd1 Ud1.
    zstep.
    absc ws0 wd0 wc b c HB HC WC c1 wc1 wv1 R1 V1 WC1.
    adv ds1 LX1 FS1 VI Ud0 Us0 V1 VI1 (8 * j + 1). clear LX V1 Ud0 Us0.
    zstep. zstep. zstep. zstep.
    wrvf HX LX1 LX2 FS1 FS2 (8 * j + 1).
    zstep. chk. zstep. zstep. chk.
    zstep. zstep. zstep.
    rdsf AS MU WM HX FS2 LX2 L0 LS LO SSX sl (8 * j + 2) ws2 Us2.
    rdd HX FS2 (8 * j + 2) wd2 Ud2.
    zstep. zstep.
    absc ws1 wd1 wc1 b c1 HB R1 WC1 c2 wc2 wv2 R2 V2 WC2.
    adv ds2 LX2 FS2 VI1 Ud1 Us1 V2 VI2 (8 * j + 2). clear LX1 FS1 VI1 V2 Ud1 Us1 WC1 R1.
    zstep. zstep. zstep. zstep.
    wrvf HX LX2 LX3 FS2 FS3 (8 * j + 2).
    zstep. chk. zstep. zstep. chk.
    zstep. zstep. zstep.
    rdsf AS MU WM HX FS3 LX3 L0 LS LO SSX sl (8 * j + 3) ws3 Us3.
    rdd HX FS3 (8 * j + 3) wd3 Ud3.
    zstep. zstep.
    absc ws2 wd2 wc2 b c2 HB R2 WC2 c3 wc3 wv3 R3 V3 WC3.
    adv ds3 LX3 FS3 VI2 Ud2 Us2 V3 VI3 (8 * j + 3). clear LX2 FS2 VI2 V3 Ud2 Us2 WC2 R2.
    zstep. zstep. zstep. zstep.
    wrvf HX LX3 LX4 FS3 FS4 (8 * j + 3).
    zstep. chk. zstep. zstep. chk.
    zstep. zstep. zstep.
    rdsf AS MU WM HX FS4 LX4 L0 LS LO SSX sl (8 * j + 4) ws4 Us4.
    rdd HX FS4 (8 * j + 4) wd4 Ud4.
    zstep. zstep.
    absc ws3 wd3 wc3 b c3 HB R3 WC3 c4 wc4 wv4 R4 V4 WC4.
    adv ds4 LX4 FS4 VI3 Ud3 Us3 V4 VI4 (8 * j + 4). clear LX3 FS3 VI3 V4 Ud3 Us3 WC3 R3.
    match goal with MUx : munch _ m ?mx, WMx : wmono _ m ?mx, MIx : mem_inv _ ?mx, STx : stk _ ?mx _ _ |- _ =>
      eapply K; [bveq | bveq | exact (conj HX (conj LX4 (conj MUx (conj WMx (conj MIx STx))))) | exact FR
                | exact (conj FS4 (conj R4 (conj WC4 VI4))) | exact Us4 | exact Ud4] end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End Walk.
