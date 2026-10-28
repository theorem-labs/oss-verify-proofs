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
  #[using="Hdl Hsl Ln L0 LS DB SB ALD ALS NZS SPR LO SX SSX RA HB"] Lemma vx8_segB : forall (j n8 : Z) (ds : list word) (mm : mem) (c : Z) (wc ws4 wd4 : word)
      (xa0 xa5 xs3 xs5 : word) (wt0 wn wt2 wa1 wa3 wa4 wa6 wa7 wt3 wt4 wt5 wt6 : word)
      (Q : machine_state -> Prop),
    0 <= j < n8 -> 8 * j + 8 <= sl ->
    xa0 = Z_to_bv 64 (D + 32 * j + 16) -> xa5 = Z_to_bv 64 (S + 32 * j + 16) ->
    wt0 = Z_to_bv 64 (S + 32 * j) -> wn = Z_to_bv 64 (n8 - j) -> wt2 = Z_to_bv 64 b -> wa4 = Z_to_bv 64 (D + 32 * j) ->
    wt6 = Z_to_bv 64 (-5) ->
    DINV mm ds -> SFACT0 -> FRAME mm -> VINV ds (8 * j + 4) (8 * j + 4) c wc ->
    limb32 ss (Z.to_nat (8 * j + 4)) = w32 ws4 -> limb32 ds0 (Z.to_nat (8 * j + 4)) = w32 wd4 ->
    (forall (ds8 : list word) (m8 : mem) (c8 : Z) (wc8 yt0 yt1 ya2 ya4 ya5 ys2 ys3 ys4 ys5 : word),
       yt0 = Z_to_bv 64 (S + 32 * j + 32) -> yt1 = Z_to_bv 64 (n8 - j - 1) -> ya2 = Z_to_bv 64 (S + 32 * j + 32) ->
       ya4 = Z_to_bv 64 (D + 32 * j + 32) -> ya5 = Z_to_bv 64 (D + 32 * j + 32) ->
       DINV m8 ds8 -> FRAME m8 -> VINV ds8 (8 * j + 8) (8 * j + 8) c8 wc8 ->
       evt usegs Q (MS (mkR ra SP gp tp yt0 yt1 wt2 (Z_to_bv 64 (D + 32 * j)) (Z_to_bv 64 (S + 32 * j)) wc8 wa1 ya2
                            wa3 ya4 ya5 wa6 wa7 ys2 ys3 ys4 ys5 s6 s7 s8 s9 s10 s11 wt3 wt4 wt5 wt6)
                       F (Z_to_bv 64 0x23c08) fc None m8 (seg_rom usegs))) ->
    evt usegs Q (MS (mkR ra SP gp tp wt0 wn wt2 (Z_to_bv 64 (D + 32 * j)) (Z_to_bv 64 (S + 32 * j)) xa0 wa1 (sx32 wd4)
                         wa3 wa4 xa5 wa6 wa7 wc xs3 (zx32 ws4) xs5 s6 s7 s8 s9 s10 s11 wt3 wt4 wt5 wt6)
                    F (Z_to_bv 64 0x23b1c) fc None mm (seg_rom usegs))
(* [comment removed for export] *).
  Proof.
    intros j n8 ds mm c wc ws4 wd4 xa0 xa5 xs3 xs5 wt0 wn wt2 wa1 wa3 wa4 wa6 wa7 wt3 wt4 wt5 wt6 Q Hj Hj8
      -> -> -> -> -> -> -> (HX & LX4 & MU & WM & MI & ST) AS FR (FS4 & R4 & WC4 & VI4) Us4 Ud4 K.
    rename c into c4. rename wc into wc4.
    assert (SPOS : 0 < S) by lia.
    zstep. zstep. zstep. zstep.
    wrvf HX LX4 LX5 FS4 FS5 (8 * j + 4).
    zstep. chk. zstep. zstep. chk.
    zstep. zstep. zstep.
    rdsf AS MU WM HX FS5 LX5 L0 LS LO SSX sl (8 * j + 5) ws5 Us5.
    rdd HX FS5 (8 * j + 5) wd5 Ud5.
    zstep. zstep.
    absc ws4 wd4 wc4 b c4 HB R4 WC4 c5 wc5 wv5 R5 V5 WC5.
    adv ds5 LX5 FS5 VI4 Ud4 Us4 V5 VI5 (8 * j + 5). clear LX4 FS4 VI4 V5 Ud4 Us4 WC4 R4.
    zstep. zstep. zstep. zstep.
    wrvf HX LX5 LX6 FS5 FS6 (8 * j + 5).
    zstep. chk. zstep. zstep. chk.
    zstep. zstep. zstep.
    rdsf AS MU WM HX FS6 LX6 L0 LS LO SSX sl (8 * j + 6) ws6 Us6.
    rdd HX FS6 (8 * j + 6) wd6 Ud6.
    zstep. zstep.
    absc ws5 wd5 wc5 b c5 HB R5 WC5 c6 wc6 wv6 R6 V6 WC6.
    adv ds6 LX6 FS6 VI5 Ud5 Us5 V6 VI6 (8 * j + 6). clear LX5 FS5 VI5 V6 Ud5 Us5 WC5 R5.
    zstep. zstep. zstep. zstep.
    wrvf HX LX6 LX7 FS6 FS7 (8 * j + 6).
    zstep. chk. zstep. zstep. chk.
    zstep. zstep. zstep. zstep.
    rdsf AS MU WM HX FS7 LX7 L0 LS LO SSX sl (8 * j + 7) ws7 Us7.
    zstep.
    rdd HX FS7 (8 * j + 7) wd7 Ud7.
    zstep. zstep. zstep. zstep.
    absc ws6 wd6 wc6 b c6 HB R6 WC6 c7 wc7 wv7 R7 V7 WC7.
    adv ds7 LX7 FS7 VI6 Ud6 Us6 V7 VI7 (8 * j + 7). clear LX6 FS6 VI6 V7 Ud6 Us6 WC6 R6.
    zstep. zstep. zstep. zstep. zstep. zstep. zstep.
    wrvf HX LX7 LX8 FS7 FS8 (8 * j + 7).
    zstep.
    absc ws7 wd7 wc7 b c7 HB R7 WC7 c8 wc8 wv8 R8 V8 WC8.
    adv ds8 LX8 FS8 VI7 Ud7 Us7 V8 VI8 (8 * j + 8). clear LX7 FS7 VI7 V8 Ud7 Us7 WC7 R7.
    zstep.
    match goal with MUx : munch _ m ?mx, WMx : wmono _ m ?mx, MIx : mem_inv _ ?mx, STx : stk _ ?mx _ _ |- _ =>
      eapply K; [bveq | bveq | bveq | bveq | bveq | exact (conj HX (conj LX8 (conj MUx (conj WMx (conj MIx STx))))) | exact FR
                | exact (conj FS8 (conj R8 (conj WC8 VI8)))] end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End Walk.
