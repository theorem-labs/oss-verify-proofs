From Stdlib Require Import ZArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import FseNCount HufPure_FseDecomp.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Fpu Sem.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Image ZBridge Arr Bytes.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.LibA Require Import ExecF StepF Shadow.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import BImg RtCells ABase AHarness_iface.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require AProg_kit.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Plain Require Import RF_huf_tbl_iface.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Plain Require RF_huf_fdw_sm RF_huf_fdw_kit RF_huf_fdw_fm RF_huf_bdt_model.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import AF_huf_tbl_iface AF_huf_tbl_iface2 AF_huf_bdt_kit.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require AKit.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import AF_huf_fdw_kit.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw HufWalkKit.
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Notation zlen l := (Z.of_nat (length l)).

Definition AHUF_RELOADI : Z := 0x8e354.
Definition AFSE_RELOADI : Z := 0x9accc.
Definition RELOADI_STACK : Z := 16.

Section CANSEC1. Context {rc : runConstT}.

Definition reload_cellsA (cont bc : word) (jp : list byte) (P S : Z) : list cell :=
  [C8 cont; C4 bc; CB 4 jp; C8 (Z_to_bv 64 P); C8 (Z_to_bv 64 S); C8 (Z_to_bv 64 (S + 8))].

Definition reload_int_postA (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (SPV BD S : Z) (bs : list Z) (bc q lo : Z) (jp : list byte) (m : amem)
    : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 : word) (m' : amem),
    ms' = MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 BD) a1 a2 a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch [(BD, BD + 40); (SPV - RELOADI_STACK, SPV)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo SPV
    /\ rw_cells bsegs m' BD
         (reload_cellsA (Z_to_bv 64 (le64v bs (q - bc / 8))) (Z_to_bv 64 (bc mod 8)) jp (S + (q - bc / 8)) S).

Definition reload_int_stmtA (E : Z) : Prop :=
  forall (RNG : footprint) (ra gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : amem) (SPV lo BD S bc q : Z) (cont : word) (jp : list byte) (bs : list Z),
  rw_cells bsegs m BD (reload_cellsA cont (Z_to_bv 64 bc) jp (S + q) S) ->
  bytes_at bsegs m S (map (Z_to_bv 8) bs) -> Forall (fun c => 0 <= c < 256) bs ->
  BD mod 8 = 0 -> SPV <= BD -> BD + 48 <= 2^47 -> ablk S (S + zlen bs) ->
  0 <= bc <= 64 -> 8 <= q -> q + 8 <= zlen bs ->
  stk bsegs m lo SPV -> ATOP + 4096 <= lo -> lo <= SPV - RELOADI_STACK ->
  mem_inv bsegs m -> artcells m -> unpoisoned m BD (BD + 40) -> unpoisoned m S (S + zlen bs) ->
  rng RNG BD 40 -> rng RNG (shad BD) 5 -> rng RNG S (zlen bs) -> rng RNG (shad S) (nshad (zlen bs + S mod 8)) ->
  rng RNG (SPV - RELOADI_STACK) RELOADI_STACK -> rng_aimg RNG -> rng_aimg_sh RNG ->
  evtF bsegs RNG (reload_int_postA ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc SPV BD S bs bc q lo jp m)
       (MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 BD) a1 a2 a3 a4 a5 a6 a7
                s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
           F (Z_to_bv 64 E) fc None m (seg_rom bsegs)).

Local Ltac acc_hint ::=
  lazymatch goal with
  | |- acc_in ?R (Z_to_bv 64 (Z.shiftr ?a 3 + ?K), 1%nat) =>
      let X := leftmost a in
      match goal with
      | H : rng R (shad ?A) ?n |- _ =>
          constr_eq X A;
          let H' := fresh "Hsh" in pose proof H as H'; unfold shad, nshad, ASHOFF in H';
          rewrite ?Z.shiftr_div_pow2 in H' |- * by lia; change (2 ^ 3) with 8 in H' |- *;
          lazymatch type of H' with rng _ ?lo ?len =>
            let B := fresh "Bsh" in
            assert (B : lo <= a / 8 + K /\ a / 8 + K + 1 <= lo + len) by (Z.div_mod_to_equations; lia)
          end;
          solve_acc_with H'
      end
  end.

Ltac zl :=
  repeat match goal with H : ?T |- _ =>
    lazymatch type of T with Prop =>
      lazymatch T with
      | _ <= _ => fail | _ < _ => fail | _ = _ :> Z => fail | _ <= _ <= _ => fail | _ <= _ < _ => fail
      | _ => clear H end end end;
  Z.div_mod_to_equations; lia.
Ltac zdec :=
  repeat match goal with
  | |- context [Z.lxor ?x ?y <? 1] =>
      replace (Z.lxor x y <? 1) with false by
        (symmetry; apply Z.ltb_ge;
         assert (0 <= Z.lxor x y) by (apply (proj2 (Z.lxor_nonneg x y)); split; intro; zl);
         assert (Z.lxor x y <> 0) by (rewrite Z.lxor_eq_0_iff; zl); lia)
  | |- context [?a =? ?b] =>
      first [ replace (a =? b) with true by (symmetry; apply Z.eqb_eq; zl)
            | replace (a =? b) with false by (symmetry; apply Z.eqb_neq; zl) ]
  | |- context [?a <? ?b] =>
      first [ replace (a <? b) with true by (symmetry; apply Z.ltb_lt; zl)
            | replace (a <? b) with false by (symmetry; apply Z.ltb_ge; zl) ]
  end.
Ltac zbr :=
  unfold zx32; rewrite ?bv_ltu_Z, ?bv_eqb_Z, ?Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; cbn [Z.of_N];
  rewrite ?Z.shiftr_div_pow2 by lia; try change (2 ^ 3) with 8;
  repeat match goal with |- context [?a mod 2 ^ ?k] =>
    rewrite (Z.mod_small a (2 ^ k)) by zl end;
  zdec; vm_compute; reflexivity.
Ltac br :=
  lazymatch goal with |- evtF _ _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
    first [ replace c with false; [cbv iota | symmetry; zbr]
          | replace c with true; [cbv iota | symmetry; zbr] ] end.

Lemma src_sh_cell : forall m lo hi a, unpoisoned m lo hi -> lo <= a -> a + 1 <= hi -> hi <= KEND ->
  exists b, rw_cells bsegs m (Z.shiftr a 3 + ASHOFF) [C1 b] /\ Z.shiftr a 3 + ASHOFF + 1 <= KHIGH
         /\ (sval b = 0 \/ (0 < sval b <= 7 /\ a mod 8 < sval b)).
Proof.
  intros m lo hi a U L H K.
  assert (A8 : Z.shiftr a 3 = a / 8) by (apply Z.shiftr_div_pow2; destruct U; lia).
  destruct U as (U0 & U1 & U2).
  destruct (U2 (Z.shiftr a 3) ltac:(lia) ltac:(rewrite A8; zl) ltac:(rewrite A8; zl)) as (b & MB & GB).
  exists b. split; [|split].
  - apply AProg_kit.c1_of_byte; [rewrite A8; unfold ASHOFF; zl | rewrite A8; unfold ASHOFF, KEND in *; zl |].
    rewrite Z.add_comm; exact MB.
  - apply AProg_kit.shad_lt_KHIGH; lia.
  - unfold gran_ok in GB. rewrite A8 in GB. destruct GB as [G0|G0]; [left; exact G0|right].
    pose proof (sval_range b) as SR.
    destruct (Z.min_spec (8 * (a / 8) + 8) hi) as [[_ E]|[_ E]]; rewrite E in G0; zl.
Qed.

Theorem huf_reload_int_proofA : reload_int_stmtA AHUF_RELOADI.
Proof.
  unfold reload_int_stmtA, AHUF_RELOADI, reload_cellsA.
  intros RNG ra gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m SPV lo BD S bc q cont jp bs
    HBD SRC BY BD8 SPB BDH HS RB Q1 Q2 STK BOT LO MI ART UB US RBD RBDs RS RSs RF RI RIS.
  unfold RELOADI_STACK in *.
  unfold artcells in ART; repeat (let H := fresh "ARc" in destruct ART as [H ART]).
  assert (KE : BD + 40 <= KEND) by (unfold KEND; lia).
  assert (BDm : forall k, k mod 8 = 0 -> (BD + k) mod 8 = 0) by (intros k Hk; rewrite Z.add_mod, BD8, Hk by lia; reflexivity).
    destruct (AProg_kit.unpoisoned8_c1_off m BD (BD + 40) BD 0 UB ltac:(lia) ltac:(lia) (BDm 0 eq_refl) KE) as [SH0 SB0]. rewrite Z.add_0_r in SH0, SB0.
  destruct (AProg_kit.unpoisoned8_c1_off m BD (BD + 40) BD 8 UB ltac:(lia) ltac:(lia) (BDm 8 eq_refl) KE) as [SH1 SB1].
  destruct (AProg_kit.unpoisoned8_c1_off m BD (BD + 40) BD 16 UB ltac:(lia) ltac:(lia) (BDm 16 eq_refl) KE) as [SH2 SB2].
  destruct (AProg_kit.unpoisoned8_c1_off m BD (BD + 40) BD 24 UB ltac:(lia) ltac:(lia) (BDm 24 eq_refl) KE) as [SH3 SB3].
  destruct (AProg_kit.unpoisoned8_c1_off m BD (BD + 40) BD 32 UB ltac:(lia) ltac:(lia) (BDm 32 eq_refl) KE) as [SH4 SB4].
  unfold ASHOFF in SH0, SH1, SH2, SH3, SH4, SB0, SB1, SB2, SB3, SB4.
  pose proof ATOP_range as AR; unfold ATOP_MIN, ATOP_MAX in AR.
  lazymatch type of SB0 with _ <= ?K => assert (KH : K <= ATOP_MIN) by (vm_compute; intro HH; discriminate HH) end.
  unfold ATOP_MIN in KH.
  assert (SL : 1 <= S) by (destruct HS as [[HS1 HS2]|[HS1 HS2]]; [unfold AIMG_HI in HS1|]; lia).
  assert (SA : S + zlen bs <= ATOP) by (destruct HS as [[HS1 HS2]|[HS1 HS2]]; unfold KLS in HS2; lia).
  assert (ZB : bv_unsigned (zx32 (Z_to_bv 64 bc)) = bc)
    by (unfold zx32; rewrite !Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; cbn [Z.of_N];
        repeat rewrite Z.mod_small by zl; reflexivity).
  assert (BS8 : Z.shiftr bc 3 = bc / 8) by (apply Z.shiftr_div_pow2; lia).
  assert (SB8 : Z.shiftr (S + q - Z.shiftr bc 3) 3 = (S + q - bc / 8) / 8) by (rewrite BS8; apply Z.shiftr_div_pow2; lia).
  destruct (proj2 (proj2 US) (Z.shiftr (S + q - Z.shiftr bc 3) 3) ltac:(zl) ltac:(rewrite SB8; zl) ltac:(rewrite SB8; zl))
    as (b1 & MB1 & GB1).
  pose proof (AProg_kit.c1_of_byte m (Z.shiftr (S + q - Z.shiftr bc 3) 3 + ASHOFF) b1
               ltac:(rewrite SB8; unfold ASHOFF; zl) ltac:(rewrite SB8; unfold ASHOFF; zl)
               ltac:(rewrite Z.add_comm; exact MB1)) as SS1.
  pose proof (AProg_kit.shad_lt_KHIGH (S + q - Z.shiftr bc 3) ltac:(rewrite BS8; zl) ltac:(rewrite BS8; unfold KEND; zl)) as SS1B.
  unfold ASHOFF in SS1, SS1B.
  assert (B1z : sval b1 = 0).
  { unfold gran_ok in GB1; rewrite SB8 in GB1.
    rewrite Z.min_l in GB1 by zl. destruct GB1 as [G0|G0]; [exact G0|].
    exfalso; zl. }
  destruct (src_sh_cell m S (S + zlen bs) (S + q - Z.shiftr bc 3 + 7) US ltac:(rewrite BS8; zl) ltac:(rewrite BS8; zl)
             ltac:(unfold KEND; zl)) as (b2 & SS2 & SS2B & GB2).
  unfold ASHOFF in SS2, SS2B.
  pose proof (munch_refl [(BD, BD + 40); (SPV + -16, SPV)] m) as MU.
  pose proof (wmono_refl bsegs m) as WMo.
  carve_frame 16%nat STK.
  repeat zstep.
  rewrite land7_mod, BD8. if_false.
  repeat first [ zstep | if_false ].
  repeat first [ zstep | if_false ].
  do 3 (repeat first [ zstep | if_false ]; br).
  repeat first [ zstep | if_false ].
  rewrite ZB.
  lazymatch goal with |- context [Z.land ?x ?M] =>
    replace (Z.land x M) with x by (symmetry; change M with (Z.ones 64); rewrite Z.land_ones by lia; apply Z.mod_small; zl) end.
  repeat first [ zstep | if_false ].
  rewrite sxb_sval, B1z. if_false.
  repeat first [ zstep | if_false ].
  rewrite sxb_sval.
  lazymatch goal with SRC' : bytes_at bsegs ?mg S (map (Z_to_bv 8) bs) |- evtF _ _ _ (MS _ _ _ _ _ ?mg _) =>
    pose proof (src_rd bsegs mg S bs (q - bc / 8 + 0) SRC' ltac:(zl)) as RX0;
    pose proof (src_rd bsegs mg S bs (q - bc / 8 + 1) SRC' ltac:(zl)) as RX1;
    pose proof (src_rd bsegs mg S bs (q - bc / 8 + 2) SRC' ltac:(zl)) as RX2;
    pose proof (src_rd bsegs mg S bs (q - bc / 8 + 3) SRC' ltac:(zl)) as RX3;
    pose proof (src_rd bsegs mg S bs (q - bc / 8 + 4) SRC' ltac:(zl)) as RX4;
    pose proof (src_rd bsegs mg S bs (q - bc / 8 + 5) SRC' ltac:(zl)) as RX5;
    pose proof (src_rd bsegs mg S bs (q - bc / 8 + 6) SRC' ltac:(zl)) as RX6;
    pose proof (src_rd bsegs mg S bs (q - bc / 8 + 7) SRC' ltac:(zl)) as RX7 end.
  rewrite ?Z.add_assoc, ?Z.add_0_r in RX0, RX1, RX2, RX3, RX4, RX5, RX6, RX7.
  destruct GB2 as [G2|G2].
  { rewrite G2. if_false. repeat first [ zstep | if_false ].
    repeat first [ zstep | if_false | if_true ].
    release_frame FR STK SPV.
    apply evtF_done. unfold reload_int_postA.
    do 11 eexists. split; [reflexivity|].
    replace (SPV - 16) with (SPV + -16) by lia.
    split; [exact MU|]. split; [exact WMo|]. split; [assumption|]. split; [exact STK|].
    lazymatch goal with H : rw_cells bsegs ?mm BD ?cs |- rw_cells bsegs ?mm BD ?cs' =>
    replace cs' with cs; [exact H|] end.
    rewrite ZB, land7_mod, BS8.
    replace (S + q - bc / 8) with (S + (q - bc / 8)) by ring.
    unfold reload_cellsA.
    lazymatch goal with |- [?a0; ?a1; ?a2; ?a3; ?a4; ?a5] = [?b0; ?b1; ?b2; ?b3; ?b4; ?b5] =>
    replace a0 with b0; [reflexivity|] end.
    do 2 f_equal. unfold le64v.
    pose proof (fun i => byte_Znth bs i BY) as BZ.
    rewrite le64_lbu_land by (apply BZ; zl).
    rewrite ?Z.add_0_r. ring.
  }
  { replace (bv_eqb (Z_to_bv 64 (sval b2)) (Z_to_bv 64 0)) with false
      by (symmetry; rewrite bv_eqb_Z, !Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; cbn [Z.of_N];
          apply Z.eqb_neq; rewrite !Z.mod_small by lia; lia).
    cbv iota. repeat first [ zstep | if_false | if_true ].
    lazymatch goal with |- evtF _ _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      assert (c = true) end.
    { unfold bv_lts. rewrite land7_mod. pose proof (sval_range b2) as SR2.
      rewrite (signed_lit_small64 (sval b2)) by lia.
      rewrite signed_lit_small64 by (pose proof (Z.mod_pos_bound (S + q - Z.shiftr bc 3 + 7) 8); lia).
      apply Z.ltb_lt. lia. }
    rewrite H. cbv iota. repeat first [ zstep | if_false | if_true ].
    release_frame FR STK SPV.
    apply evtF_done. unfold reload_int_postA.
    do 11 eexists. split; [reflexivity|].
    replace (SPV - 16) with (SPV + -16) by lia.
    split; [exact MU|]. split; [exact WMo|]. split; [assumption|]. split; [exact STK|].
    lazymatch goal with H : rw_cells bsegs ?mm BD ?cs |- rw_cells bsegs ?mm BD ?cs' =>
    replace cs' with cs; [exact H|] end.
    rewrite ZB, land7_mod, BS8.
    replace (S + q - bc / 8) with (S + (q - bc / 8)) by ring.
    unfold reload_cellsA.
    lazymatch goal with |- [?a0; ?a1; ?a2; ?a3; ?a4; ?a5] = [?b0; ?b1; ?b2; ?b3; ?b4; ?b5] =>
    replace a0 with b0; [reflexivity|] end.
    do 2 f_equal. unfold le64v.
    pose proof (fun i => byte_Znth bs i BY) as BZ.
    rewrite le64_lbu_land by (apply BZ; zl).
    rewrite ?Z.add_0_r. ring.
  }
Qed.

Theorem fse_reload_int_proofA : reload_int_stmtA AFSE_RELOADI.
Proof.
  unfold reload_int_stmtA, AFSE_RELOADI, reload_cellsA.
  intros RNG ra gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m SPV lo BD S bc q cont jp bs
    HBD SRC BY BD8 SPB BDH HS RB Q1 Q2 STK BOT LO MI ART UB US RBD RBDs RS RSs RF RI RIS.
  unfold RELOADI_STACK in *.
  unfold artcells in ART; repeat (let H := fresh "ARc" in destruct ART as [H ART]).
  assert (KE : BD + 40 <= KEND) by (unfold KEND; lia).
  assert (BDm : forall k, k mod 8 = 0 -> (BD + k) mod 8 = 0) by (intros k Hk; rewrite Z.add_mod, BD8, Hk by lia; reflexivity).
    destruct (AProg_kit.unpoisoned8_c1_off m BD (BD + 40) BD 0 UB ltac:(lia) ltac:(lia) (BDm 0 eq_refl) KE) as [SH0 SB0]. rewrite Z.add_0_r in SH0, SB0.
  destruct (AProg_kit.unpoisoned8_c1_off m BD (BD + 40) BD 8 UB ltac:(lia) ltac:(lia) (BDm 8 eq_refl) KE) as [SH1 SB1].
  destruct (AProg_kit.unpoisoned8_c1_off m BD (BD + 40) BD 16 UB ltac:(lia) ltac:(lia) (BDm 16 eq_refl) KE) as [SH2 SB2].
  destruct (AProg_kit.unpoisoned8_c1_off m BD (BD + 40) BD 24 UB ltac:(lia) ltac:(lia) (BDm 24 eq_refl) KE) as [SH3 SB3].
  destruct (AProg_kit.unpoisoned8_c1_off m BD (BD + 40) BD 32 UB ltac:(lia) ltac:(lia) (BDm 32 eq_refl) KE) as [SH4 SB4].
  unfold ASHOFF in SH0, SH1, SH2, SH3, SH4, SB0, SB1, SB2, SB3, SB4.
  pose proof ATOP_range as AR; unfold ATOP_MIN, ATOP_MAX in AR.
  lazymatch type of SB0 with _ <= ?K => assert (KH : K <= ATOP_MIN) by (vm_compute; intro HH; discriminate HH) end.
  unfold ATOP_MIN in KH.
  assert (SL : 1 <= S) by (destruct HS as [[HS1 HS2]|[HS1 HS2]]; [unfold AIMG_HI in HS1|]; lia).
  assert (SA : S + zlen bs <= ATOP) by (destruct HS as [[HS1 HS2]|[HS1 HS2]]; unfold KLS in HS2; lia).
  assert (ZB : bv_unsigned (zx32 (Z_to_bv 64 bc)) = bc)
    by (unfold zx32; rewrite !Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; cbn [Z.of_N];
        repeat rewrite Z.mod_small by zl; reflexivity).
  assert (BS8 : Z.shiftr bc 3 = bc / 8) by (apply Z.shiftr_div_pow2; lia).
  assert (SB8 : Z.shiftr (S + q - Z.shiftr bc 3) 3 = (S + q - bc / 8) / 8) by (rewrite BS8; apply Z.shiftr_div_pow2; lia).
  destruct (proj2 (proj2 US) (Z.shiftr (S + q - Z.shiftr bc 3) 3) ltac:(zl) ltac:(rewrite SB8; zl) ltac:(rewrite SB8; zl))
    as (b1 & MB1 & GB1).
  pose proof (AProg_kit.c1_of_byte m (Z.shiftr (S + q - Z.shiftr bc 3) 3 + ASHOFF) b1
               ltac:(rewrite SB8; unfold ASHOFF; zl) ltac:(rewrite SB8; unfold ASHOFF; zl)
               ltac:(rewrite Z.add_comm; exact MB1)) as SS1.
  pose proof (AProg_kit.shad_lt_KHIGH (S + q - Z.shiftr bc 3) ltac:(rewrite BS8; zl) ltac:(rewrite BS8; unfold KEND; zl)) as SS1B.
  unfold ASHOFF in SS1, SS1B.
  assert (B1z : sval b1 = 0).
  { unfold gran_ok in GB1; rewrite SB8 in GB1.
    rewrite Z.min_l in GB1 by zl. destruct GB1 as [G0|G0]; [exact G0|].
    exfalso; zl. }
  destruct (src_sh_cell m S (S + zlen bs) (S + q - Z.shiftr bc 3 + 7) US ltac:(rewrite BS8; zl) ltac:(rewrite BS8; zl)
             ltac:(unfold KEND; zl)) as (b2 & SS2 & SS2B & GB2).
  unfold ASHOFF in SS2, SS2B.
  pose proof (munch_refl [(BD, BD + 40); (SPV + -16, SPV)] m) as MU.
  pose proof (wmono_refl bsegs m) as WMo.
  carve_frame 16%nat STK.
  repeat zstep.
  rewrite land7_mod, BD8. if_false.
  repeat first [ zstep | if_false ].
  repeat first [ zstep | if_false ].
  do 3 (repeat first [ zstep | if_false ]; br).
  repeat first [ zstep | if_false ].
  rewrite ZB.
  lazymatch goal with |- context [Z.land ?x ?M] =>
    replace (Z.land x M) with x by (symmetry; change M with (Z.ones 64); rewrite Z.land_ones by lia; apply Z.mod_small; zl) end.
  repeat first [ zstep | if_false ].
  rewrite sxb_sval, B1z. if_false.
  repeat first [ zstep | if_false ].
  rewrite sxb_sval.
  lazymatch goal with SRC' : bytes_at bsegs ?mg S (map (Z_to_bv 8) bs) |- evtF _ _ _ (MS _ _ _ _ _ ?mg _) =>
    pose proof (src_rd bsegs mg S bs (q - bc / 8 + 0) SRC' ltac:(zl)) as RX0;
    pose proof (src_rd bsegs mg S bs (q - bc / 8 + 1) SRC' ltac:(zl)) as RX1;
    pose proof (src_rd bsegs mg S bs (q - bc / 8 + 2) SRC' ltac:(zl)) as RX2;
    pose proof (src_rd bsegs mg S bs (q - bc / 8 + 3) SRC' ltac:(zl)) as RX3;
    pose proof (src_rd bsegs mg S bs (q - bc / 8 + 4) SRC' ltac:(zl)) as RX4;
    pose proof (src_rd bsegs mg S bs (q - bc / 8 + 5) SRC' ltac:(zl)) as RX5;
    pose proof (src_rd bsegs mg S bs (q - bc / 8 + 6) SRC' ltac:(zl)) as RX6;
    pose proof (src_rd bsegs mg S bs (q - bc / 8 + 7) SRC' ltac:(zl)) as RX7 end.
  rewrite ?Z.add_assoc, ?Z.add_0_r in RX0, RX1, RX2, RX3, RX4, RX5, RX6, RX7.
  destruct GB2 as [G2|G2].
  { rewrite G2. if_false. repeat first [ zstep | if_false ].
    repeat first [ zstep | if_false | if_true ].
    release_frame FR STK SPV.
    apply evtF_done. unfold reload_int_postA.
    do 11 eexists. split; [reflexivity|].
    replace (SPV - 16) with (SPV + -16) by lia.
    split; [exact MU|]. split; [exact WMo|]. split; [assumption|]. split; [exact STK|].
    lazymatch goal with H : rw_cells bsegs ?mm BD ?cs |- rw_cells bsegs ?mm BD ?cs' =>
    replace cs' with cs; [exact H|] end.
    rewrite ZB, land7_mod, BS8.
    replace (S + q - bc / 8) with (S + (q - bc / 8)) by ring.
    unfold reload_cellsA.
    lazymatch goal with |- [?a0; ?a1; ?a2; ?a3; ?a4; ?a5] = [?b0; ?b1; ?b2; ?b3; ?b4; ?b5] =>
    replace a0 with b0; [reflexivity|] end.
    do 2 f_equal. unfold le64v.
    pose proof (fun i => byte_Znth bs i BY) as BZ.
    rewrite le64_lbu_land by (apply BZ; zl).
    rewrite ?Z.add_0_r. ring.
  }
  { replace (bv_eqb (Z_to_bv 64 (sval b2)) (Z_to_bv 64 0)) with false
      by (symmetry; rewrite bv_eqb_Z, !Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; cbn [Z.of_N];
          apply Z.eqb_neq; rewrite !Z.mod_small by lia; lia).
    cbv iota. repeat first [ zstep | if_false | if_true ].
    lazymatch goal with |- evtF _ _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      assert (c = true) end.
    { unfold bv_lts. rewrite land7_mod. pose proof (sval_range b2) as SR2.
      rewrite (signed_lit_small64 (sval b2)) by lia.
      rewrite signed_lit_small64 by (pose proof (Z.mod_pos_bound (S + q - Z.shiftr bc 3 + 7) 8); lia).
      apply Z.ltb_lt. lia. }
    rewrite H. cbv iota. repeat first [ zstep | if_false | if_true ].
    release_frame FR STK SPV.
    apply evtF_done. unfold reload_int_postA.
    do 11 eexists. split; [reflexivity|].
    replace (SPV - 16) with (SPV + -16) by lia.
    split; [exact MU|]. split; [exact WMo|]. split; [assumption|]. split; [exact STK|].
    lazymatch goal with H : rw_cells bsegs ?mm BD ?cs |- rw_cells bsegs ?mm BD ?cs' =>
    replace cs' with cs; [exact H|] end.
    rewrite ZB, land7_mod, BS8.
    replace (S + q - bc / 8) with (S + (q - bc / 8)) by ring.
    unfold reload_cellsA.
    lazymatch goal with |- [?a0; ?a1; ?a2; ?a3; ?a4; ?a5] = [?b0; ?b1; ?b2; ?b3; ?b4; ?b5] =>
    replace a0 with b0; [reflexivity|] end.
    do 2 f_equal. unfold le64v.
    pose proof (fun i => byte_Znth bs i BY) as BZ.
    rewrite le64_lbu_land by (apply BZ; zl).
    rewrite ?Z.add_0_r. ring.
  }
Qed.

Definition ADSYM_FAST : Z := 0x9a970.
Definition ADSYM : Z := 0x9aaec.
Definition DSYM_STACK : Z := 16.

Definition dsym_postA (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (SPV DS BD DT S o s' : Z) (d' : bitD) (jp : list byte) (lo : Z) (m : amem)
    : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 : word) (m' : amem),
    ms' = MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 o) a1 a2 a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch [(DS, DS + 16); (BD, BD + 40); (SPV - DSYM_STACK, SPV)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo SPV
    /\ rw_cells bsegs m' DS [C8 (Z_to_bv 64 s'); C8 (Z_to_bv 64 (DT + 4))]
    /\ rw_cells bsegs m' BD (bitdz_cellsA S d' jp).

Definition dsym_stmtA (E : Z) (fast : bool) : Prop :=
  forall (RNG : footprint) (ra gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : amem) (SPV lo DS BD DT S s o s' : Z) (dt : dtable) (d d' : bitD)
         (jp : list byte),
  rw_cells bsegs m DS [C8 (Z_to_bv 64 s); C8 (Z_to_bv 64 (DT + 4))] -> rw_cells bsegs m BD (bitdz_cellsA S d jp) ->
  bytes_at bsegs m (DT + 4) (concat (map fse_cell_bytes (dt_cells dt))) ->
  1 <= dt_tableLog dt <= 12 -> zlen (dt_cells dt) = 2^(dt_tableLog dt) ->
  RF_huf_fdw_sm.cells_ok (dt_tableLog dt) (dt_cells dt) ->
  0 <= bd_cont d < 2^64 -> 0 <= bd_bits d <= 2^30 ->
  decode_sym dt fast s d = Ok (o, s', d') ->
  SPV <= DS -> DS mod 8 = 0 -> DS + 16 <= BD -> BD mod 8 = 0 -> BD + 48 <= 2^47 ->
  ablk DT (DT + 4 + 4 * 2^(dt_tableLog dt)) ->
  stk bsegs m lo SPV -> ATOP + 4096 <= lo -> lo <= SPV - DSYM_STACK ->
  mem_inv bsegs m -> artcells m ->
  zshadow m DS 16 -> zshadow m BD 40 -> zshadow m DT (4 + 4 * 2^(dt_tableLog dt)) -> zshadow m ABIT_MASK 128 ->
  rng RNG DS 16 -> rng RNG (shad DS) 2 -> rng RNG BD 40 -> rng RNG (shad BD) 5 ->
  rng RNG DT (4 + 4 * 2^(dt_tableLog dt)) -> rng RNG (shad DT) (nshad (4 + 4 * 2^(dt_tableLog dt) + DT mod 8)) ->
  rng RNG (SPV - DSYM_STACK) DSYM_STACK -> rng_aimg RNG -> rng_aimg_sh RNG ->
  evtF bsegs RNG (dsym_postA ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc SPV DS BD DT S o s' d' jp lo m)
       (MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 DS) (Z_to_bv 64 BD) a2 a3 a4 a5 a6 a7
                s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
           F (Z_to_bv 64 E) fc None m (seg_rom bsegs)).


Local Ltac acc_hint ::=
  lazymatch goal with
  | |- acc_in ?R (Z_to_bv 64 (Z.shiftr ?a 3 + ?K), 1%nat) =>
      first [
      match goal with
      | H : rng R (shad ?A) (nshad (?len + ?A' mod 8)) |- _ => constr_eq A A'; apply (acc_shZ R A len a H); zl
      end |
      match goal with
      | H : rng R (shad ?A) ?n |- _ =>
          let H' := fresh "Hsh" in pose proof H as H'; unfold shad, nshad, ASHOFF in H';
          rewrite ?Z.shiftr_div_pow2 in H' |- * by lia; change (2 ^ 3) with 8 in H' |- *;
          lazymatch type of H' with rng _ ?lo ?len =>
            let B := fresh "Bsh" in
            assert (B : lo <= a / 8 + K /\ a / 8 + K + 1 <= lo + len) by zl
          end;
          solve_acc_with H'
      end ]
  end.


Lemma cell_hi_bytes : forall ns sy nb, 0 <= sy < 256 -> 0 <= nb < 256 ->
  take 2 (drop (Z.to_nat 2) (le2 (Z_to_bv 64 ns) ++ [Z_to_bv 8 sy; Z_to_bv 8 nb])) = le2 (Z_to_bv 64 (sy + 256 * nb)).
Proof.
  intros ns sy nb Hs Hn.
  pose proof (length_le2 (Z_to_bv 64 ns)) as L.
  destruct (le2 (Z_to_bv 64 ns)) as [|x0 [|x1 [|x2 r]]]; try discriminate L.
  change (Z.to_nat 2) with 2%nat. cbn [app drop take].
  unfold le2. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. cbn [Z.of_N].
  rewrite Z.mod_small by lia. cbn [Z_to_le_bytes].
  rewrite !Z.shiftr_div_pow2 by lia.
  replace ((sy + 256 * nb) / 2 ^ 8) with nb by (Z.div_mod_to_equations; lia).
  f_equal. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. cbn [Z.of_N].
  replace (sy + 256 * nb) with (sy + nb * 2 ^ 8) by lia. rewrite Z_mod_plus_full. reflexivity.
Qed.

Lemma ld16 : forall x, 0 <= x < 2^16 -> bv_unsigned (zext 64 (bv_extract 0 16 (le_bytes_to_word (le2 (Z_to_bv 64 x))))) = x.
Proof.
  intros x H. rewrite zext_extract_le2, zx16_lit by lia. rewrite Z_to_bv_unsigned.
  unfold bv_wrap, bv_modulus. cbn [Z.of_N]. apply Z.mod_small. lia.
Qed.

Lemma hw_nb : forall sy nb, 0 <= sy < 256 -> 0 <= nb < 256 -> Z.shiftr (Z.shiftl (sy + 256 * nb) 16 mod 2^64) 24 = nb.
Proof.
  intros sy nb H1 H2. rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia.
  change (2^16) with 65536. change (2^24) with 16777216.
  rewrite Z.mod_small by (change (2^64) with 18446744073709551616; lia).
  Z.div_mod_to_equations; lia.
Qed.

Lemma hw_ns : forall sy nb ns, 0 <= sy < 256 -> 0 <= nb < 256 -> 0 <= ns < 2^16 ->
  Z.lor (Z.shiftl (sy + 256 * nb) 16 mod 2^64) ns mod 2^16 = ns.
Proof.
  intros sy nb ns H1 H2 H3. rewrite Z.shiftl_mul_pow2 by lia.
  rewrite (Z.mod_small _ (2^64)) by (change (2^16) with 65536 in *; change (2^64) with 18446744073709551616; lia).
  rewrite <- (Z.land_ones _ 16) by lia. rewrite Z.land_lor_distr_l, !Z.land_ones by lia.
  rewrite Z_mod_mult, Z.lor_0_l. apply Z.mod_small; lia.
Qed.

Lemma hw_sy : forall sy nb, 0 <= sy < 256 -> Z.land (sy + 256 * nb) 255 = sy.
Proof.
  intros sy nb H1. change 255 with (Z.ones 8). rewrite Z.land_ones by lia. change (2^8) with 256.
  replace (sy + 256 * nb) with (sy + nb * 256) by ring. rewrite Z_mod_plus_full. apply Z.mod_small; lia.
Qed.

Ltac mones H k := repeat match type of H with context [Z.land ?x ?M] =>
  lazymatch M with Zpos _ => idtac end;
  let b := eval vm_compute in (M =? Z.ones k) in lazymatch b with true =>
  replace (Z.land x M) with (x mod 2^k) in H by (change M with (Z.ones k); rewrite Z.land_ones by lia; reflexivity) end end.

Lemma hw_lor : forall a b, 0 <= a -> 0 <= b < 2^16 -> Z.lor (a * 2^16) b = a * 2^16 + b.
Proof.
  intros a b Ha Hb.
  assert (L : Z.land (a * 2^16) b = 0).
  { apply Z.bits_inj_0. intros n. rewrite Z.land_spec.
    destruct (Z.lt_ge_cases n 16) as [Hn|Hn].
    - destruct (Z.lt_ge_cases n 0) as [Hn0|Hn0]; [rewrite Z.testbit_neg_r by lia; reflexivity|].
      rewrite Z.mul_pow2_bits_low by lia. reflexivity.
    - rewrite <- (Z.mod_small b (2^16)) by lia. rewrite Z.mod_pow2_bits_high by lia. apply andb_false_r. }
  rewrite <- Z.lxor_lor by exact L. rewrite Z.add_nocarry_lxor by exact L. reflexivity.
Qed.

Lemma hw_hi : forall M sy nb ns, M = Z.ones 64 -> 0 <= sy < 256 -> 0 <= nb <= 12 -> 0 <= ns < 2^16 ->
  Z.lor (Z.land (bv_unsigned (zx16 (Z_to_bv 64 (sy + 256 * nb))) ≪ 16) M) (bv_unsigned (zx16 (Z_to_bv 64 ns))) ≫ 29 = 0.
Proof.
  intros M sy nb ns -> H1 H2 H3.
  rewrite !zx16_lit by lia. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. cbn [Z.of_N].
  rewrite (Z.mod_small ns), (Z.mod_small (sy + 256 * nb)) by lia.
  rewrite Z.land_ones, Z.shiftl_mul_pow2 by lia.
  rewrite Z.mod_small by (change (2^16) with 65536 in *; change (2^64) with 18446744073709551616; lia).
  rewrite hw_lor by lia. rewrite Z.shiftr_div_pow2 by lia.
  apply Z.div_small. change (2^16) with 65536 in *. change (2^29) with 536870912. lia.
Qed.

Lemma hw_nbz : forall M sy nb, M = Z.ones 64 -> 0 <= sy < 256 -> 0 <= nb < 256 ->
  Z.land (bv_unsigned (zx16 (Z_to_bv 64 (sy + 256 * nb))) ≪ 16) M ≫ 24 = nb.
Proof.
  intros M sy nb -> H1 H2.
  rewrite zx16_lit by lia. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. cbn [Z.of_N].
  rewrite Z.mod_small by lia. rewrite Z.land_ones by lia. apply hw_nb; lia.
Qed.

Lemma shr_mod64 : forall c k, 0 <= c < 2^64 -> 0 <= k -> (c ≫ k) mod 2^64 = c ≫ k.
Proof.
  intros c k H K. apply Z.mod_small. rewrite Z.shiftr_div_pow2 by lia.
  assert (1 <= 2^k) by (change 1 with (2^0); apply Z.pow_le_mono_r; lia).
  split; [apply Z.div_pos; lia|]. apply (Z.le_lt_trans _ c); [apply Z.div_le_upper_bound; nia | lia].
Qed.

Lemma hw2_ns : forall K M sy nb ns, K = 2^16 -> M = 2^64 -> 0 <= sy < 256 -> 0 <= nb < 256 -> 0 <= ns < 2^16 ->
  Z.lor ((sy + 256 * nb) * K mod M) ns mod 2^16 = ns.
Proof.
  intros K M sy nb ns -> -> H1 H2 H3.
  rewrite (Z.mod_small _ (2^64)) by (change (2^16) with 65536 in *; change (2^64) with 18446744073709551616; lia).
  rewrite hw_lor by lia. rewrite Z.add_comm, Z_mod_plus_full. apply Z.mod_small; lia.
Qed.

Lemma hw2_sy : forall K M sy nb ns, K = 2^16 -> M = 2^64 -> 0 <= sy < 256 -> 0 <= nb < 256 -> 0 <= ns < 2^16 ->
  Z.land (Z.lor ((sy + 256 * nb) * K mod M) ns ≫ 16) 255 = sy.
Proof.
  intros K M sy nb ns -> -> H1 H2 H3.
  rewrite (Z.mod_small _ (2^64)) by (change (2^16) with 65536 in *; change (2^64) with 18446744073709551616; lia).
  rewrite hw_lor by lia. rewrite Z.shiftr_div_pow2 by lia.
  replace (((sy + 256 * nb) * 2^16 + ns) / 2^16) with (sy + 256 * nb)
    by (change (2^16) with 65536 in *; Z.div_mod_to_equations; lia).
  apply hw_sy; lia.
Qed.

Lemma mod64_of : forall x N, 0 < N -> N mod 64 = 0 -> (x mod N) mod 64 = x mod 64.
Proof.
  intros x N H1 H2. destruct (proj1 (Z.mod_divide N 64 ltac:(lia)) H2) as [k Hk].
  rewrite (Z.mod_eq x N) by lia. replace (x - N * (x / N)) with (x + (- (k * (x / N))) * 64) by (rewrite Hk; ring).
  apply Z_mod_plus_full.
Qed.

Ltac zpre := rewrite ?land64_mod, ?Z.shiftl_mul_pow2 by lia; try change (2^2) with 4.

Lemma zsh_cell : forall m X n a, zshadow m X n -> X <= a < X + n -> 0 <= a < 2^47 ->
  rw_cells bsegs m (Z.shiftr a 3 + ASHOFF) [C1 (Z_to_bv 8 0)].
Proof.
  intros m X n a Z H B.
  assert (A8 : Z.shiftr a 3 = a / 8) by (apply Z.shiftr_div_pow2; lia).
  apply AProg_kit.c1_of_byte; [rewrite A8; unfold ASHOFF; zl | rewrite A8; unfold ASHOFF; zl |].
  rewrite Z.add_comm. unfold zshadow, shad in Z. apply Z; lia.
Qed.

Theorem fse_dsym_fast_proofA : dsym_stmtA ADSYM_FAST true.
Proof.
  unfold dsym_stmtA, ADSYM_FAST, bitdz_cellsA.
  intros RNG ra gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m SPV lo DS BD DT S s o s' dt d d' jp
    HDS HBD TBB HTL HCN HCOK HC HB HDEC SPD DS8 DSBD BD8 BDH HDT STK BOT LO MI ART ZDS ZBD ZDT ZMK
    RDS RDSs RBD RBDs RDT RDTs RF RI RIS.
  unfold DSYM_STACK in *.
  destruct (RF_huf_fdw_fm.fdec_inv (dt_tableLog dt) [] dt HTL HCN HCOK s d o s' d' HDEC ltac:(lia))
    as (c & NC & HS0 & CS & CN & CNS & CNS2 & -> & -> & ->).
  unfold artcells in ART; repeat (let H := fresh "ARc" in destruct ART as [H ART]).
  pose proof (stk_lo_nonneg _ _ _ _ STK) as LO0.
  pose proof ATOP_range as AR; unfold ATOP_MIN, ATOP_MAX in AR.
  set (tl := dt_tableLog dt) in *.
  assert (P2 : 2 <= 2^tl <= 2^12) by (split; [change 2 with (2^1); apply Z.pow_le_mono_r|apply Z.pow_le_mono_r]; lia).
  assert (DTL : 1 <= DT /\ DT + 4 + 4 * 2^tl <= ATOP)
    by (destruct HDT as [[H1 H2]|[H1 H2]]; [unfold AIMG_HI in H1; unfold KLS in H2|]; lia).
  destruct DTL as [DTL1 DTL2].
  pose proof (zsh_cell m DS 16 (DS + 8) ZDS ltac:(lia) ltac:(lia)) as SH0.
  pose proof (zsh_cell m DS 16 DS ZDS ltac:(lia) ltac:(lia)) as SH1.
  pose proof (zsh_cell m DT (4 + 4 * 2^tl) (s * 4 + (DT + 4)) ZDT ltac:(lia) ltac:(lia)) as SH2.
  pose proof (zsh_cell m DT (4 + 4 * 2^tl) (s * 4 + (DT + 4) + 3) ZDT ltac:(lia) ltac:(lia)) as SH3.
  pose proof (zsh_cell m BD 40 BD ZBD ltac:(lia) ltac:(lia)) as SH4.
  pose proof (zsh_cell m BD 40 (BD + 8) ZBD ltac:(lia) ltac:(lia)) as SH5.
  pose proof (AProg_kit.shad_lt_KHIGH (DS + 8) ltac:(lia) ltac:(unfold KEND; lia)) as SB0.
  pose proof (AProg_kit.shad_lt_KHIGH DS ltac:(lia) ltac:(unfold KEND; lia)) as SB1.
  pose proof (AProg_kit.shad_lt_KHIGH (s * 4 + (DT + 4)) ltac:(lia) ltac:(unfold KEND; lia)) as SB2.
  pose proof (AProg_kit.shad_lt_KHIGH (s * 4 + (DT + 4) + 3) ltac:(lia) ltac:(unfold KEND; lia)) as SB3.
  pose proof (AProg_kit.shad_lt_KHIGH BD ltac:(lia) ltac:(unfold KEND; lia)) as SB4.
  pose proof (AProg_kit.shad_lt_KHIGH (BD + 8) ltac:(lia) ltac:(unfold KEND; lia)) as SB5.
  unfold ASHOFF in SH0, SH1, SH2, SH3, SH4, SH5, SB0, SB1, SB2, SB3, SB4, SB5.
  lazymatch type of SB0 with _ <= ?K => assert (KH : K <= ATOP_MIN) by (vm_compute; intro HH; discriminate HH) end.
  unfold ATOP_MIN in KH.
  assert (TBL : zlen (concat (map fse_cell_bytes (dt_cells dt))) = 4 * 2^tl)
    by (rewrite RF_huf_bdt_model.fse_cells_length; lia).
  pose proof (munch_refl [(DS, DS + 16); (BD, BD + 40); (SPV + -16, SPV)] m) as MU.
  pose proof (wmono_refl bsegs m) as WMo.
  carve_frame 16%nat STK.
  (repeat first [ zstep | if_false ]).
  rewrite land7_mod, DS8. if_false.
  (repeat first [ zstep | if_false ]).
  zpre. br.
  (repeat first [ zstep | if_false ]).
  br.
  (repeat first [ zstep | if_false ]).
  br.
  (repeat first [ zstep | if_false ]).
  rewrite land7_mod, BD8. if_false.
  (repeat first [ zstep | if_false ]).
  lazymatch goal with TB' : bytes_at bsegs ?mg (DT + 4) _ |- evtF _ _ _ (MS _ _ _ _ _ ?mg _) =>
    pose proof (RF_huf_fdw_kit.cell_rd_ns bsegs mg (DT + 4) (dt_cells dt) s c (wa (s * 4 + (DT + 4))) TB' NC ltac:(lia) ltac:(f_equal; lia)) as CR0;
    pose proof (RF_huf_fdw_kit.cell_rd_off bsegs mg (DT + 4) (dt_cells dt) s c 2 2 TB' NC ltac:(lia) ltac:(lia) ltac:(lia)) as CR2 end.
  replace (DT + 4 + (4 * s + 2)) with (s * 4 + (DT + 4) + 2) in CR2 by lia.
  unfold fse_cell_bytes in CR2. rewrite cell_hi_bytes in CR2 by lia.
  (repeat first [ zstep | if_false ]).
  release_frame FR STK SPV.
  assert (NS16 : 0 <= dc_newState c < 2^16) by (assert (0 < 2^dc_nbBits c) by (apply Z.pow_pos_nonneg; lia); lia).
  assert (CW : 0 <= dc_symbol c + 256 * dc_nbBits c < 2^16) by (assert (dc_nbBits c <= 12) by lia; lia).
  assert (ZB : bv_unsigned (zx32 (Z_to_bv 64 (bd_bits d))) = bd_bits d)
    by (unfold zx32; rewrite !Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; cbn [Z.of_N];
        repeat rewrite Z.mod_small by lia; reflexivity).
  rewrite ZB in HDS, HBD.
  rewrite ?zx16_lit in HDS, HBD |- * by lia. rewrite ?Z_to_bv_unsigned in HDS, HBD |- *. unfold bv_wrap, bv_modulus in HDS, HBD |- *.
  cbn [Z.of_N] in HDS, HBD |- *.
  rewrite ?(Z.mod_small (dc_newState c)), ?(Z.mod_small (dc_symbol c + 256 * dc_nbBits c)) in HDS, HBD |- * by lia.
  mones HDS 64%Z. mones HBD 64%Z. mones HDS 16%Z. rewrite ?land63_mod in HDS.
  rewrite (hw_nb (dc_symbol c) (dc_nbBits c)) in HDS, HBD by lia.
  assert (NS16' : 0 <= dc_newState c < 65536) by (change 65536 with (2^16); lia).
  rewrite (zx16_lit (dc_newState c)) in HDS by lia.
  rewrite Z_to_bv_unsigned in HDS. unfold bv_wrap, bv_modulus in HDS. cbn [Z.of_N] in HDS.
  rewrite (Z.mod_small (dc_newState c)) in HDS by lia.
  rewrite (hw_ns (dc_symbol c) (dc_nbBits c) (dc_newState c)) in HDS by lia.
  rewrite (hw_sy (dc_symbol c) (dc_nbBits c)) by lia.
  apply evtF_done. unfold dsym_postA.
  do 11 eexists. split; [reflexivity|].
  replace (SPV - 16) with (SPV + -16) by lia.
  split; [exact MU|]. split; [exact WMo|]. split; [assumption|]. split; [exact STK|].
  split.
  - lazymatch goal with H : rw_cells bsegs ?mm DS ?cs |- rw_cells bsegs ?mm DS ?cs' => replace cs' with cs; [exact H|] end.
    rewrite (Z.add_comm (dc_newState c)). unfold RF_huf_fdw_fm.lbf. reflexivity.
  - unfold bitdz_cellsA. cbn [bd_cont bd_bits bd_ptr bd_zero]. exact HBD.
Qed.

Theorem fse_dsym_proofA : dsym_stmtA ADSYM false.
Proof.
  unfold dsym_stmtA, ADSYM, bitdz_cellsA.
  intros RNG ra gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m SPV lo DS BD DT S s o s' dt d d' jp
    HDS HBD TBB HTL HCN HCOK HC HB HDEC SPD DS8 DSBD BD8 BDH HDT STK BOT LO MI ART ZDS ZBD ZDT ZMK
    RDS RDSs RBD RBDs RDT RDTs RF RI RIS.
  unfold DSYM_STACK in *.
  destruct (RF_huf_fdw_sm.dec_inv (dt_tableLog dt) [] dt HTL HCN HCOK s d o s' d' HDEC ltac:(lia))
    as (c & NC & HS0 & CS & CN & CNS & CNS2 & -> & -> & ->).
  unfold artcells in ART; repeat (let H := fresh "ARc" in destruct ART as [H ART]).
  pose proof (stk_lo_nonneg _ _ _ _ STK) as LO0.
  pose proof ATOP_range as AR; unfold ATOP_MIN, ATOP_MAX in AR.
  set (tl := dt_tableLog dt) in *.
  assert (P2 : 2 <= 2^tl <= 2^12) by (split; [change 2 with (2^1); apply Z.pow_le_mono_r|apply Z.pow_le_mono_r]; lia).
  assert (DTL : 1 <= DT /\ DT + 4 + 4 * 2^tl <= ATOP)
    by (destruct HDT as [[H1 H2]|[H1 H2]]; [unfold AIMG_HI in H1; unfold KLS in H2|]; lia).
  destruct DTL as [DTL1 DTL2].
  pose proof (zsh_cell m DS 16 (DS + 8) ZDS ltac:(lia) ltac:(lia)) as SH0.
  pose proof (zsh_cell m DS 16 DS ZDS ltac:(lia) ltac:(lia)) as SH1.
  pose proof (zsh_cell m DT (4 + 4 * 2^tl) (s * 4 + (DT + 4)) ZDT ltac:(lia) ltac:(lia)) as SH2.
  pose proof (zsh_cell m DT (4 + 4 * 2^tl) (s * 4 + (DT + 4) + 3) ZDT ltac:(lia) ltac:(lia)) as SH3.
  pose proof (zsh_cell m BD 40 BD ZBD ltac:(lia) ltac:(lia)) as SH4.
  pose proof (zsh_cell m BD 40 (BD + 8) ZBD ltac:(lia) ltac:(lia)) as SH5.
  pose proof (AProg_kit.shad_lt_KHIGH (DS + 8) ltac:(lia) ltac:(unfold KEND; lia)) as SB0.
  pose proof (AProg_kit.shad_lt_KHIGH DS ltac:(lia) ltac:(unfold KEND; lia)) as SB1.
  pose proof (AProg_kit.shad_lt_KHIGH (s * 4 + (DT + 4)) ltac:(lia) ltac:(unfold KEND; lia)) as SB2.
  pose proof (AProg_kit.shad_lt_KHIGH (s * 4 + (DT + 4) + 3) ltac:(lia) ltac:(unfold KEND; lia)) as SB3.
  pose proof (AProg_kit.shad_lt_KHIGH BD ltac:(lia) ltac:(unfold KEND; lia)) as SB4.
  pose proof (AProg_kit.shad_lt_KHIGH (BD + 8) ltac:(lia) ltac:(unfold KEND; lia)) as SB5.
  unfold ASHOFF in SH0, SH1, SH2, SH3, SH4, SH5, SB0, SB1, SB2, SB3, SB4, SB5.
  lazymatch type of SB0 with _ <= ?K => assert (KH : K <= ATOP_MIN) by (vm_compute; intro HH; discriminate HH) end.
  unfold ATOP_MIN in KH.
  assert (TBL : zlen (concat (map fse_cell_bytes (dt_cells dt))) = 4 * 2^tl)
    by (rewrite RF_huf_bdt_model.fse_cells_length; lia).
  pose proof (zsh_cell m ABIT_MASK 128 (ABIT_MASK + dc_nbBits c * 4) ZMK ltac:(unfold ABIT_MASK; lia) ltac:(unfold ABIT_MASK; lia)) as SHM.
  pose proof (AProg_kit.shad_lt_KHIGH (ABIT_MASK + dc_nbBits c * 4) ltac:(unfold ABIT_MASK; lia) ltac:(unfold ABIT_MASK, KEND; lia)) as SBM.
  pose proof (rng_mask_sh RNG RIS) as RMS.
  unfold ABIT_MASK, ASHOFF in SHM, SBM, RMS.
  pose proof (munch_refl [(DS, DS + 16); (BD, BD + 40); (SPV + -16, SPV)] m) as MU.
  pose proof (wmono_refl bsegs m) as WMo.
  carve_frame 16%nat STK.
  (repeat first [ zstep | if_false ]).
  rewrite land7_mod, DS8. if_false.
  (repeat first [ zstep | if_false ]).
  zpre. br.
  (repeat first [ zstep | if_false ]).
  br.
  (repeat first [ zstep | if_false ]).
  br.
  (repeat first [ zstep | if_false ]).
  rewrite land7_mod, BD8. if_false.
  (repeat first [ zstep | if_false ]).
  lazymatch goal with TB' : bytes_at bsegs ?mg (DT + 4) _ |- evtF _ _ _ (MS _ _ _ _ _ ?mg _) =>
    pose proof (RF_huf_fdw_kit.cell_rd_ns bsegs mg (DT + 4) (dt_cells dt) s c (wa (s * 4 + (DT + 4))) TB' NC ltac:(lia) ltac:(f_equal; lia)) as CR0;
    pose proof (RF_huf_fdw_kit.cell_rd_off bsegs mg (DT + 4) (dt_cells dt) s c 2 2 TB' NC ltac:(lia) ltac:(lia) ltac:(lia)) as CR2 end.
  replace (DT + 4 + (4 * s + 2)) with (s * 4 + (DT + 4) + 2) in CR2 by lia.
  unfold fse_cell_bytes in CR2. rewrite cell_hi_bytes in CR2 by lia.
  (repeat first [ zstep | if_false ]).
  assert (NS16 : 0 <= dc_newState c < 2^16) by (assert (0 < 2^dc_nbBits c) by (apply Z.pow_pos_nonneg; lia); lia).
  lazymatch goal with |- context [Z.lor ?A ?B ≫ 29] =>
    replace (Z.lor A B ≫ 29) with 0 by (symmetry; apply hw_hi; [vm_compute; reflexivity | lia | lia | lia]) end.
  if_false.
  (repeat first [ zstep | if_false ]).
  lazymatch goal with |- context [Z.land (bv_unsigned (zx16 (Z_to_bv 64 (dc_symbol c + 256 * dc_nbBits c))) ≪ 16) ?M ≫ 24] =>
    rewrite (hw_nbz M (dc_symbol c) (dc_nbBits c)) by (first [vm_compute; reflexivity | lia]) end.
  zpre. br.
  (repeat first [ zstep | if_false ]).
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mg _) =>
    lazymatch goal with MI' : mem_inv bsegs mg |- _ =>
      pose proof (maskA_rd mg (dc_nbBits c) MI' ltac:(lia)) as RMK end end.
  unfold ABIT_MASK in RMK. replace (4 * dc_nbBits c) with (dc_nbBits c * 4) in RMK by lia.
  (repeat first [ zstep | if_false ]).
  release_frame FR STK SPV.
  assert (CW : 0 <= dc_symbol c + 256 * dc_nbBits c < 2^16) by (assert (dc_nbBits c <= 12) by lia; lia).
  assert (P12 : 0 < 2^dc_nbBits c <= 2^12) by (split; [apply Z.pow_pos_nonneg|apply Z.pow_le_mono_r]; lia).
  rewrite (AKit.sx32_lit (bd_bits d)) in HDS, HBD by lia.
  rewrite (AKit.zx32_lit (2^dc_nbBits c - 1)) in HDS by lia.
  rewrite ?(zx16_lit (dc_newState c)), ?(zx16_lit (dc_symbol c + 256 * dc_nbBits c)) in HDS by lia.
  rewrite ?(zx16_lit (dc_newState c)), ?(zx16_lit (dc_symbol c + 256 * dc_nbBits c)) by lia.
  repeat rewrite Z_to_bv_unsigned in HDS. repeat rewrite Z_to_bv_unsigned in HBD. repeat rewrite Z_to_bv_unsigned.
  unfold bv_wrap, bv_modulus in HDS, HBD |- *. cbn [Z.of_N] in HDS, HBD |- *.
  rewrite ?(Z.mod_small (bd_bits d)), ?(Z.mod_small (dc_newState c)), ?(Z.mod_small (dc_symbol c + 256 * dc_nbBits c)),
    ?(Z.mod_small (2^dc_nbBits c - 1)) in HDS by lia.
  rewrite ?(Z.mod_small (dc_newState c)), ?(Z.mod_small (dc_symbol c + 256 * dc_nbBits c)) by lia.
  rewrite (Z.mod_small (bd_bits d)) in HBD by lia.
  mones HDS 64%Z. mones HDS 16%Z. rewrite ?land63_mod in HDS.
  rewrite (Z.mod_small (bd_bits d + dc_nbBits c)) in HDS by lia.
  rewrite shr_mod64 in HDS by (try apply Z.mod_pos_bound; lia).
  lazymatch type of HDS with context [Z.modulo (Z.lor (Z.modulo (Z.mul ?x ?K) ?M) ?n) ?P] =>
    let E := fresh "E" in
    assert (E : Z.modulo (Z.lor (Z.modulo (Z.mul x K) M) n) P = dc_newState c)
      by (apply hw2_ns; first [vm_compute; reflexivity | lia]);
    rewrite E in HDS; clear E end.
  lazymatch goal with |- context [Z.land (Z.shiftr (Z.lor (Z.modulo (Z.mul ?x ?K) ?M) ?n) ?k) ?L] =>
    let E := fresh "E" in
    assert (E : Z.land (Z.shiftr (Z.lor (Z.modulo (Z.mul x K) M) n) k) L = dc_symbol c)
      by (apply (hw2_sy K M (dc_symbol c) (dc_nbBits c) (dc_newState c)); first [vm_compute; reflexivity | lia]);
    rewrite E; clear E end.
  apply evtF_done. unfold dsym_postA.
  do 11 eexists. split; [reflexivity|].
  replace (SPV - 16) with (SPV + -16) by lia.
  split; [exact MU|]. split; [exact WMo|]. split; [assumption|]. split; [exact STK|].
  split.
  - lazymatch goal with H : rw_cells bsegs ?mm DS ?cs |- rw_cells bsegs ?mm DS ?cs' => replace cs' with cs; [exact H|] end.
    rewrite (Z.add_comm (dc_newState c)). rewrite ?land63_mod.
    rewrite (mod64_of _ (2^64)) by (vm_compute; first [reflexivity | intro HH; discriminate HH]).
    repeat match goal with |- context [(?x mod ?N) mod 64] =>
      lazymatch N with Zpos _ => idtac end; lazymatch N with 64 => fail | _ => idtac end;
      rewrite (mod64_of x N) by (vm_compute; first [reflexivity | intro HH; discriminate HH]) end.
    reflexivity.
  - unfold bitdz_cellsA. cbn [bd_cont bd_bits bd_ptr bd_zero]. exact HBD.
Qed.





End CANSEC1.
