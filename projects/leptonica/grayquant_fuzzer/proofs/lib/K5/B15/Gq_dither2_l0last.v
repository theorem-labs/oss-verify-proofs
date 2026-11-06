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
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.B15 Require Import ImageA.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.Lib Require Import RzCPS NodesA SysStep Arr.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.Lib Require Import StoreFast.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.PG Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.B15 Require Import Layout.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.B15 Require Import RT_iface RT_traces RT_gaps_iface LeptTac D_kit Lept_kit Lept_iface Lept_env LeptC_kit LeptL_kit LeptB_guard LeptB_guard2 Gq_guardx Gq_dither2_l1.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Notation D2L0_W lined nl bufs1 bufs2 n1 := [(lined, lined + nl); (bufs1, bufs1 + n1); (bufs2, bufs2 + n1)]%Z (only parsing).

(* [comment removed for export] *)
Ltac mergeZ1w2 PC r1 r2 r3 :=
  lazymatch goal with
  | |- evt ?segs ?Q (MS ?R ?F _ ?fc ?rv ?m ?ro) =>
      eapply (evt_cut segs (fun ms' => exists (z1 : Z) (u2 u3 : word),
                 ms' = MS (@bvmap_set 5 word r1 (Z_to_bv 64 z1) (@bvmap_set 5 word r2 u2 (@bvmap_set 5 word r3 u3 R))) F (Z_to_bv 64 PC) fc rv m ro));
      [ | let z := fresh "z" in let u2 := fresh "u" in let u3 := fresh "u" in let E := fresh "E" in
          let ms := fresh "ms" in intros ms (z & u2 & u3 & E); subst ms; norm_regset ]
  end.
Ltac mergeZ1w2_done := apply evt_done; do 3 eexists; norm_regset; reflexivity.

(* [comment removed for export] *)
Lemma d2l0_last : forall (ra sp gp tp t0 t1 t2 s0 s1 a1 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t5 t6 : word) F fc (m : mem)
    (lined nl bufs1 bufs2 n1 ta t38 t14 w : Z) (bs bs2 : list byte) (wl tw t38w : list word),
  d2_geom lined nl bufs1 bufs2 n1 ta t38 t14 w ->
  mem_inv asegs m -> u8arr asegs m bufs1 bs -> Z.of_nat (length bs) = n1 -> acc asegs m bufs1 n1 ->
  u8arr asegs m bufs2 bs2 -> Z.of_nat (length bs2) = n1 -> acc asegs m bufs2 n1 ->
  u32arr asegs m lined wl -> 4 * Z.of_nat (length wl) = nl -> acc asegs m lined nl ->
  u32arr asegs m ta tw -> Z.of_nat (length tw) = 256 -> acc asegs m ta 1024 ->
  u32arr asegs m t38 t38w -> Z.of_nat (length t38w) = 256 -> acc asegs m t38 1024 -> Forall tsmall t38w ->
  evt asegs (d2l_end sp gp tp F fc m (D2L0_W lined nl bufs1 bufs2 n1) lined nl bufs1 bufs2 n1)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 lined) a1 (Z_to_bv 64 bufs1) (Z_to_bv 64 bufs2) (Z_to_bv 64 ta) (Z_to_bv 64 t38) a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 SHB) (Z_to_bv 64 (w - 1)) t5 t6)
        F (Z_to_bv 64 0xa3cec) fc None m (seg_rom asegs)).
Proof.
  intros until t38w. intros GEO MI UB UBL ACCB UB2 UBL2 ACCB2 UL ULL ACCL UT UTL ACCT U38 U38L ACC38 T38S.
  pose proof GEO as (HW & WN & N4 & NHI & WL & L4 & LHI & B0 & B8 & BHI & BSH & BSEG & C0 & C8 & CHI & CSH & CSEG & L0 & LA4 & LNHI & LSH & LSEG
                   & TA0 & TA8 & TAHI & TASH & TASEG & T380 & T388 & T38HI & T38SH & T38SEG & T140 & T148 & T14HI & T14SH & T14SEG
                   & SEP1 & SEP2 & SEP12 & SEPT1 & SEPT2 & SEPT3 & SEP81 & SEP82 & SEP83 & SEP41 & SEP42 & SEP43).
  unfold SEGTOP_A, SHB in *.
  clear T140 T148 T14HI T14SH T14SEG SEP41 SEP42 SEP43.
  pose proof (munch_refl (D2L0_W lined nl bufs1 bufs2 n1) m) as MU. pose proof (wmono_refl asegs m) as WM.
  park_disj.
  pose proof (lxor3_eq (bufs1 + (w - 1))) as LX0.
  assert (IDX0 : 0 <= Z.lxor (bufs1 + (w - 1)) 3 - bufs1 < n1) by (rewrite LX0; clear - HW WN N4 B8; Z.div_mod_to_equations; lia).
  pose proof (lxor3_eq (bufs2 + (w - 1))) as LX2.
  assert (IDX2 : 0 <= Z.lxor (bufs2 + (w - 1)) 3 - bufs2 < n1) by (rewrite LX2; clear - HW WN N4 C8; Z.div_mod_to_equations; lia).
  clear LX0 LX2.
  (* [comment removed for export] *)
  lwalk [0xa3e70; 0xa3eac].
  rewrite (srliw_idx (w - 1) 16) by (clear - HW; lia).
  replace (lined + (w - 1) / 16 * 4) with (lined + 4 * ((w - 1) / 16)) by (clear; lia).
  assert (ULW : Z.of_nat (length wl) = nl / 4) by (clear - ULL L4; Z.div_mod_to_equations; lia).
  assert (JL : 0 <= (w - 1) / 16 < nl / 4) by (clear - HW WL L4; Z.div_mod_to_equations; lia).
  lwalk [0xa3e70; 0xa3eac].
  (* [comment removed for export] *)
  destruct UB as [HB WB].
  destruct (bytes_at_read1 m bufs1 bs (Z.lxor (bufs1 + (w - 1)) 3 - bufs1) HB ltac:(lia)) as (ov & R).
  replace (bufs1 + (Z.lxor (bufs1 + (w - 1)) 3 - bufs1)) with (Z.lxor (bufs1 + (w - 1)) 3) in R by lia.
  lstep. clear R.
  assert (UB : u8arr asegs m bufs1 bs) by (split; assumption).
  clear HB WB.
  pose proof (bv_unsigned_in_range 8 ov) as OVR. unfold bv_modulus in OVR. change (2 ^ Z.of_N 8) with 256 in OVR.
  set (oz := bv_unsigned ov) in *.
  lwalk [0xa3e70; 0xa3eac].
  match goal with |- context [ta + ?e * 4] => replace (ta + e * 4) with (ta + 4 * oz) by (subst oz; clear; lia) end.
  (* [comment removed for export] *)
  destruct (u32arr_nth wl ((w - 1) / 16) ltac:(lia)) as (dv & NTHD).
  pose proof (u32arr_read asegs m lined wl ((w - 1) / 16) dv _ UL NTHD ltac:(lia) eq_refl) as R.
  lstep. clear R.
  lwalk [0xa3e70; 0xa3eac].
  destruct (u32arr_nth tw oz ltac:(lia)) as (tv & NTHT).
  pose proof (u32arr_read asegs m ta tw oz tv _ UT NTHT ltac:(lia) eq_refl) as R.
  lstep. clear R.
  (* [comment removed for export] *)
  clear UT ACCT NTHT.
  lwalk [0xa3e70; 0xa3eac; 0xa3dcc].
  clear ULL.
  unpark SEP1. unpark SEP2. unpark SEP81. unpark LSH.
  arr_sw lined ((w - 1) / 16) (lined + 4 * ((w - 1) / 16)).
  park SEP1. park SEP2. park SEP81. park LSH.
  lazymatch goal with H : Z.of_nat (length ?ws) = nl / 4 |- _ => assert (ULL : 4 * Z.of_nat (length ws) = nl) by (rewrite H; clear - L4; Z.div_mod_to_equations; lia) end.
  (* [comment removed for export] *)
  lwalk [0xa3e70; 0xa3eac].
  lazymatch goal with UCx : u8arr asegs ?mm bufs2 ?bsx |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    pose proof UCx as [HB WB];
    destruct (bytes_at_read1 mm bufs2 bsx (Z.lxor (bufs2 + (w - 1)) 3 - bufs2) HB ltac:(lia)) as (bvb & R) end.
  replace (bufs2 + (Z.lxor (bufs2 + (w - 1)) 3 - bufs2)) with (Z.lxor (bufs2 + (w - 1)) 3) in R by lia.
  lstep. clear R HB WB.
  match goal with |- context [t38 + ?e * 4] => replace (t38 + e * 4) with (t38 + 4 * oz) by (subst oz; clear; lia) end.
  lwalk [0xa3e70; 0xa3eac].
  destruct (u32arr_nth t38w oz ltac:(lia)) as (pv & NTHP).
  lazymatch goal with U : u32arr asegs ?mm t38 t38w |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    pose proof (u32arr_read asegs mm t38 t38w oz pv _ U NTHP ltac:(lia) eq_refl) as R end.
  lstep. clear R.
  pose proof (proj1 (Forall_forall tsmall t38w) T38S pv (nth_error_In _ _ NTHP)) as PVS. unfold tsmall in PVS.
  pose proof (bv_unsigned_in_range 8 bvb) as BVR. unfold bv_modulus in BVR. change (2 ^ Z.of_N 8) with 256 in BVR.
  pose proof (bv_unsigned_in_range 64 (sx32 pv)) as PVR. unfold bv_modulus in PVR. change (2 ^ Z.of_N 64) with (2^64) in PVR.
  (* [comment removed for export] *)
  lazymatch goal with U : u32arr asegs ?mm t38 t38w, A : acc asegs ?mm t38 1024 |- evt _ _ (MS _ _ _ _ _ ?mm _) => clear U A end.
  lwalk [0xa3e70; 0xa3eac].
  (* [comment removed for export] *)
  mergeZ1w2 0xa3e64 (Z_to_bv 5 11) (Z_to_bv 5 12) (Z_to_bv 5 14).
  { brfork SG.
    - (* [comment removed for export] *)
      lwalk [0xa3e64; 0xa3eac]. mergeZ1w2_done.
    - (* [comment removed for export] *)
      lwalk [0xa3e64; 0xa3eac]. rewrite ?Z.add_0_r.
      brfork F1; bsteps_to 0xa3e64; mergeZ1w2_done. }
  (* [comment removed for export] *)
  lwalk [0xa3e6c; 0xa3eac].
  remember (Z.lxor (bufs2 + (w - 1)) 3 - bufs2) as ix eqn:EIX.
  unpark SEP2. unpark SEP12. unpark CSH.
  arr_sb bufs2 ix (Z.lxor (bufs2 + (w - 1)) 3).
  park SEP2. park SEP12. park CSH.
  apply evt_done. unfold d2l_end. do 28 eexists.
  lazymatch goal with |- context [MS _ _ _ _ _ ?mm _] =>
    lazymatch goal with UBx : u8arr asegs mm bufs1 ?bsx, UB2x : u8arr asegs mm bufs2 ?bs2x, ULx : u32arr asegs mm lined ?wlx |- _ => exists mm, bsx, bs2x, wlx end end.
  split; [reflexivity|].
  repeat (split; [assumption|]). assumption.
Qed.
