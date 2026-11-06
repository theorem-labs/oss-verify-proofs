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
Notation ONE := (Z_to_bv 64 1) (only parsing).

(* [comment removed for export] *)
Lemma acc_transport3 : forall (m m' : mem) l1 h1 l2 h2 l3 h3 A N,
  acc asegs m A N -> munch [(l1, h1); (l2, h2); (l3, h3)] m m' -> 0 <= A -> A + N <= 2^47 ->
  (h1 <= 0x7fff7000 \/ 0x10007fff8000 <= l1) -> (h2 <= 0x7fff7000 \/ 0x10007fff8000 <= l2) -> (h3 <= 0x7fff7000 \/ 0x10007fff8000 <= l3) ->
  acc asegs m' A N.
Proof.
  intros m m' l1 h1 l2 h2 l3 h3 A N H MU HA HN D1 D2 D3 i Hi. destruct (H i Hi) as (b & Hb & OK). exists b. split; [| exact OK].
  apply (bytes_at_transport asegs _ m m' _ _ Hb MU). pose proof (shad_range (A + i) ltac:(lia)) as R.
  cbn [disjoint_from length Z.of_nat Pos.of_succ_nat]. repeat split; try exact I; lia.
Qed.

(* [comment removed for export] *)
Lemma swrap_add_small : forall r v, 0 <= r <= 65535 -> (v <= 65535 \/ 2^64 - 65536 <= v) -> 0 <= v < 2^64 ->
  Z_to_bv 64 (bv_swrap 32 (r + v)) = Z_to_bv 64 (r + v).
Proof.
  intros r v Hr Hv Hv2. apply Z_to_bv_eqm. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  change (2 ^ Z.of_N 32) with 4294967296. change (4294967296 / 2) with 2147483648. change (2 ^ 64) with 18446744073709551616.
  destruct Hv as [Hv|Hv].
  - rewrite (Z.mod_small (r + v + 2147483648) 4294967296) by lia. replace (r + v + 2147483648 - 2147483648) with (r + v) by lia. reflexivity.
  - replace (r + v) with ((r + v - 18446744073709551616) + 1 * 18446744073709551616) by lia.
    rewrite Z_mod_plus_full.
    replace (r + v - 18446744073709551616 + 1 * 18446744073709551616 + 2147483648)
       with ((r + v - 18446744073709551616 + 2147483648) + 4294967296 * 4294967296) by lia.
    rewrite Z_mod_plus_full. rewrite (Z.mod_small (r + v - 18446744073709551616 + 2147483648) 4294967296) by lia.
    replace (r + v - 18446744073709551616 + 2147483648 - 2147483648) with (r + v - 18446744073709551616) by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Ltac shbr_inv_j :=
  lazymatch goal with
  | |- evt ?segs ?Q (MS ?R ?F (if ?c then Z_to_bv 64 ?FAST else Z_to_bv 64 ?SLOW) ?fc ?rv ?m ?ro) =>
      let b := shbyte_of c in
      lazymatch goal with
      | K : shk m b ?X |- _ =>
          instr_at segs SLOW ltac:(fun i0 =>
            lazymatch i0 with
            | Jal _ ?off =>
              let S1 := eval vm_compute in (SLOW + bv_signed off)%Z in
              instr_at segs S1 ltac:(fun i =>
                lazymatch i with
                | OpImm ALU_AND ?ru _ _ =>
                    let S4 := eval vm_compute in (S1 + 4)%Z in
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
                      | fail 1 "shbr_inv_j: cannot prove the access addressable:" X sz ];
                      let BB := fresh "BB" in
                      assert (BB : 0 <= bv_unsigned b < 8)
                        by (pose proof (bv_unsigned_in_range 8 b); destruct OK as [?|[? ?]]; lia);
                      rewrite ?(sxb_small b) by lia;
                      shbr_merge_inv ru FAST OK; clear K BB)
                end)
            end)
      end
  end.

(* [comment removed for export] *)
Ltac mergeZ1 PC r1 :=
  lazymatch goal with
  | |- evt ?segs ?Q (MS ?R ?F _ ?fc ?rv ?m ?ro) =>
      eapply (evt_cut segs (fun ms' => exists z1 : Z,
                 ms' = MS (@bvmap_set 5 word r1 (Z_to_bv 64 z1) R) F (Z_to_bv 64 PC) fc rv m ro));
      [ | let z := fresh "z" in let E := fresh "E" in
          let ms := fresh "ms" in intros ms (z & E); subst ms; norm_regset ]
  end.
Ltac mergeZ_done := apply evt_done; eexists; norm_regset; reflexivity.


(* [comment removed for export] *)
Definition d2l0_exit (sp gp tp : word) (F : bvmap 5 word) (fc : bv 32)
    (m : mem) (lined nl bufs1 bufs2 n1 ta t38 t14 w : Z) (tw t38w t14w : list word) : machine_state -> Prop :=
  fun ms' => exists (ra' t0' t1' t2' a1' a7' s3' s6' s7' s8' s9' s10' s11' : word) (m' : mem) (bs1' bs2' : list byte) (wl' : list word),
    ms' = MS (mkR ra' sp gp tp t0' t1' t2' (Z_to_bv 64 3) ONE (Z_to_bv 64 lined) a1' (Z_to_bv 64 bufs1) (Z_to_bv 64 bufs2) (Z_to_bv 64 ta) (Z_to_bv 64 t38) (Z_to_bv 64 t14) a7'
             ONE s3' (Z_to_bv 64 268435455) (Z_to_bv 64 30) s6' s7' s8' s9' s10' s11' (Z_to_bv 64 SHB) (Z_to_bv 64 (w - 1)) (Z_to_bv 64 (2 * (w - 1))) (Z_to_bv 64 (w - 1)))
             F (Z_to_bv 64 0xa3cec) fc None m' (seg_rom asegs)
    /\ munch (D2L0_W lined nl bufs1 bufs2 n1) m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ u8arr asegs m' bufs1 bs1' /\ Z.of_nat (length bs1') = n1 /\ acc asegs m' bufs1 n1
    /\ u8arr asegs m' bufs2 bs2' /\ Z.of_nat (length bs2') = n1 /\ acc asegs m' bufs2 n1
    /\ u32arr asegs m' lined wl' /\ 4 * Z.of_nat (length wl') = nl /\ acc asegs m' lined nl
    /\ u32arr asegs m' ta tw /\ u32arr asegs m' t38 t38w /\ u32arr asegs m' t14 t14w.

Lemma d2l0_pixels : forall (k : nat) (j : Z)
    (ra sp gp tp t0 t1 t2 a1 a7 s3 s6 s7 s8 s9 s10 s11 : word) F fc (m : mem)
    (lined nl bufs1 bufs2 n1 ta t38 t14 w : Z) (bs1 bs2 : list byte) (wl tw t38w t14w : list word),
  Z.of_nat k = w - 1 - j -> 0 <= j -> (1 <= k)%nat -> d2_geom lined nl bufs1 bufs2 n1 ta t38 t14 w ->
  mem_inv asegs m -> u8arr asegs m bufs1 bs1 -> Z.of_nat (length bs1) = n1 -> acc asegs m bufs1 n1 ->
  u8arr asegs m bufs2 bs2 -> Z.of_nat (length bs2) = n1 -> acc asegs m bufs2 n1 ->
  u32arr asegs m lined wl -> 4 * Z.of_nat (length wl) = nl -> acc asegs m lined nl ->
  u32arr asegs m ta tw -> Z.of_nat (length tw) = 256 -> acc asegs m ta 1024 ->
  u32arr asegs m t38 t38w -> Z.of_nat (length t38w) = 256 -> acc asegs m t38 1024 -> Forall tsmall t38w ->
  u32arr asegs m t14 t14w -> Z.of_nat (length t14w) = 256 -> acc asegs m t14 1024 -> Forall tsmall t14w ->
  evt asegs (d2l0_exit sp gp tp F fc m lined nl bufs1 bufs2 n1 ta t38 t14 w tw t38w t14w)
    (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 3) ONE (Z_to_bv 64 lined) a1 (Z_to_bv 64 bufs1) (Z_to_bv 64 bufs2) (Z_to_bv 64 ta) (Z_to_bv 64 t38) (Z_to_bv 64 t14) a7
             ONE s3 (Z_to_bv 64 268435455) (Z_to_bv 64 30) s6 s7 s8 s9 s10 s11 (Z_to_bv 64 SHB) (Z_to_bv 64 (w - 1)) (Z_to_bv 64 (2 * j)) (Z_to_bv 64 j))
        F (Z_to_bv 64 0xa39c0) fc None m (seg_rom asegs)).
Proof.
  induction k as [|k IH]; intros j ra sp gp tp t0 t1 t2 a1 a7 s3 s6 s7 s8 s9 s10 s11 F fc m lined nl bufs1 bufs2 n1 ta t38 t14 w bs1 bs2 wl tw t38w t14w
    HK HJ HK1 GEO MI UB UBL ACCB UC UCL ACCC UL ULL ACCL UT UTL ACCT U38 U38L ACC38 T38S U14 U14L ACC14 T14S.
  { lia. }
  pose proof GEO as (HW & WN & N4 & NHI & WL & L4 & LHI & B0 & B8 & BHI & BSH & BSEG & C0 & C8 & CHI & CSH & CSEG & L0 & LA4 & LNHI & LSH & LSEG
                   & TA0 & TA8 & TAHI & TASH & TASEG & T380 & T388 & T38HI & T38SH & T38SEG & T140 & T148 & T14HI & T14SH & T14SEG
                   & SEP1 & SEP2 & SEP12 & SEPT1 & SEPT2 & SEPT3 & SEP81 & SEP82 & SEP83 & SEP41 & SEP42 & SEP43).
  unfold SEGTOP_A, SHB in *.
  pose proof (munch_refl (D2L0_W lined nl bufs1 bufs2 n1) m) as MU. pose proof (wmono_refl asegs m) as WM.
  park_disj.
  (* [comment removed for export] *)
  hide UT. hide U38. hide U14. hide ACC38. hide ACC14.
  (* [comment removed for export] *)
  pose proof (lxor3_eq (bufs1 + j)) as LX0. pose proof (lxor3_eq (bufs1 + j + 1)) as LX1. pose proof (lxor3_eq (bufs2 + j)) as LX2. pose proof (lxor3_eq (bufs2 + j + 1)) as LX3.
  assert (IDX0 : 0 <= Z.lxor (bufs1 + j) 3 - bufs1 < n1) by (rewrite LX0; clear - HJ HK HW WN N4 B8; Z.div_mod_to_equations; lia).
  assert (IDX1 : 0 <= Z.lxor (bufs1 + j + 1) 3 - bufs1 < n1) by (rewrite LX1; clear - HJ HK HW WN N4 B8; Z.div_mod_to_equations; lia).
  assert (IDX2 : 0 <= Z.lxor (bufs2 + j) 3 - bufs2 < n1) by (rewrite LX2; clear - HJ HK HW WN N4 C8; Z.div_mod_to_equations; lia).
  assert (IDX3 : 0 <= Z.lxor (bufs2 + j + 1) 3 - bufs2 < n1) by (rewrite LX3; clear - HJ HK HW WN N4 C8; Z.div_mod_to_equations; lia).
  (* [comment removed for export] *)
  assert (CONT : forall (ra' t0' t1' t2' a1' a7' s3' s6' s7' s8' s9' s10' s11' : word) (mm : mem) (bs1' bs2' : list byte) (wl' : list word),
    munch (D2L0_W lined nl bufs1 bufs2 n1) m mm -> wmono asegs m mm -> mem_inv asegs mm ->
    u8arr asegs mm bufs1 bs1' -> Z.of_nat (length bs1') = n1 -> acc asegs mm bufs1 n1 ->
    u8arr asegs mm bufs2 bs2' -> Z.of_nat (length bs2') = n1 -> acc asegs mm bufs2 n1 ->
    u32arr asegs mm lined wl' -> 4 * Z.of_nat (length wl') = nl -> acc asegs mm lined nl ->
    evt asegs (d2l0_exit sp gp tp F fc m lined nl bufs1 bufs2 n1 ta t38 t14 w tw t38w t14w)
      (MS (mkR ra' sp gp tp t0' t1' t2' (Z_to_bv 64 3) ONE (Z_to_bv 64 lined) a1' (Z_to_bv 64 bufs1) (Z_to_bv 64 bufs2) (Z_to_bv 64 ta) (Z_to_bv 64 t38) (Z_to_bv 64 t14) a7'
             ONE s3' (Z_to_bv 64 268435455) (Z_to_bv 64 30) s6' s7' s8' s9' s10' s11' (Z_to_bv 64 2147450880) (Z_to_bv 64 (w - 1)) (Z_to_bv 64 (2 * j)) (Z_to_bv 64 (j + 1)))
          F (Z_to_bv 64 0xa3c38) fc None mm (seg_rom asegs))).
  { intros ra' t0' t1' t2' a1' a7' s3' s6' s7' s8' s9' s10' s11' mm bs1' bs2' wl' MU1 WM1 MI1 UB1 UBL1 ACCB1 UC1 UCL1 ACCC1 UL1 ULL1 ACCL1.
    clear MI UB UBL ACCB UC UCL ACCC UL ULL ACCL MU WM.
    lwalk [0xa39c0; 0xa3cec; 0xa3eac].
    replace (2 * j + 2) with (2 * (j + 1)) by lia.
    destruct k as [|k].
    - assert (EJ : j + 1 = w - 1) by lia. rewrite EJ in *.
      brF. lwalk [0xa39c0; 0xa3cec; 0xa3eac].
      (* [comment removed for export] *)
      lazymatch type of MU1 with munch _ _ ?mm =>
        pose proof (u32arr_transport asegs _ _ mm ta tw UT MU1 WM1 ltac:(rewrite UTL; cbn [disjoint_from]; unpark SEPT1; unpark SEPT2; unpark SEPT3; clear - SEPT1 SEPT2 SEPT3; lia)) as UTc;
        pose proof (u32arr_transport asegs _ _ mm t38 t38w U38 MU1 WM1 ltac:(rewrite U38L; cbn [disjoint_from]; unpark SEP81; unpark SEP82; unpark SEP83; clear - SEP81 SEP82 SEP83; lia)) as U38c;
        pose proof (u32arr_transport asegs _ _ mm t14 t14w U14 MU1 WM1 ltac:(rewrite U14L; cbn [disjoint_from]; unpark SEP41; unpark SEP42; unpark SEP43; clear - SEP41 SEP42 SEP43; lia)) as U14c;
        pose proof (acc_transport3 _ mm _ _ _ _ _ _ ta 1024 ACCT MU1 ltac:(lia) ltac:(lia) ltac:(unpark LSH; exact LSH) ltac:(unpark BSH; exact BSH) ltac:(unpark CSH; exact CSH)) as ACCTc;
        pose proof (acc_transport3 _ mm _ _ _ _ _ _ t38 1024 ACC38 MU1 ltac:(lia) ltac:(lia) ltac:(unpark LSH; exact LSH) ltac:(unpark BSH; exact BSH) ltac:(unpark CSH; exact CSH)) as ACC38c;
        pose proof (acc_transport3 _ mm _ _ _ _ _ _ t14 1024 ACC14 MU1 ltac:(lia) ltac:(lia) ltac:(unpark LSH; exact LSH) ltac:(unpark BSH; exact BSH) ltac:(unpark CSH; exact CSH)) as ACC14c end.
      apply evt_done. unfold d2l0_exit, SHB. do 13 eexists. exists mm, bs1', bs2', wl'. split; [reflexivity|].
      repeat (split; [assumption|]). assumption.
    - brT.
      (* [comment removed for export] *)
      lazymatch type of MU1 with munch _ _ ?mm =>
        pose proof (u32arr_transport asegs _ _ mm ta tw UT MU1 WM1 ltac:(rewrite UTL; cbn [disjoint_from]; unpark SEPT1; unpark SEPT2; unpark SEPT3; clear - SEPT1 SEPT2 SEPT3; lia)) as UTc;
        pose proof (u32arr_transport asegs _ _ mm t38 t38w U38 MU1 WM1 ltac:(rewrite U38L; cbn [disjoint_from]; unpark SEP81; unpark SEP82; unpark SEP83; clear - SEP81 SEP82 SEP83; lia)) as U38c;
        pose proof (u32arr_transport asegs _ _ mm t14 t14w U14 MU1 WM1 ltac:(rewrite U14L; cbn [disjoint_from]; unpark SEP41; unpark SEP42; unpark SEP43; clear - SEP41 SEP42 SEP43; lia)) as U14c;
        pose proof (acc_transport3 _ mm _ _ _ _ _ _ ta 1024 ACCT MU1 ltac:(lia) ltac:(lia) ltac:(unpark LSH; exact LSH) ltac:(unpark BSH; exact BSH) ltac:(unpark CSH; exact CSH)) as ACCTc;
        pose proof (acc_transport3 _ mm _ _ _ _ _ _ t38 1024 ACC38 MU1 ltac:(lia) ltac:(lia) ltac:(unpark LSH; exact LSH) ltac:(unpark BSH; exact BSH) ltac:(unpark CSH; exact CSH)) as ACC38c;
        pose proof (acc_transport3 _ mm _ _ _ _ _ _ t14 1024 ACC14 MU1 ltac:(lia) ltac:(lia) ltac:(unpark LSH; exact LSH) ltac:(unpark BSH; exact BSH) ltac:(unpark CSH; exact CSH)) as ACC14c end.
      eapply evt_cut.
      + eapply (IH (j + 1)) with (bs1 := bs1') (bs2 := bs2') (wl := wl') (w := w) (n1 := n1) (nl := nl); try eassumption; try lia.
      + intros ms' PO. apply evt_done. unfold d2l0_exit in PO |- *.
        destruct PO as (ra'' & t0'' & t1'' & t2'' & a1'' & a7'' & s3'' & s6'' & s7'' & s8'' & s9'' & s10'' & s11'' & m' & bs1'' & bs2'' & wl'' & E & MU' & WM' & R).
        exists ra'', t0'', t1'', t2'', a1'', a7'', s3'', s6'', s7'', s8'', s9'', s10'', s11'', m', bs1'', bs2'', wl''.
        split; [exact E|]. split; [exact (munch_trans _ _ _ _ MU1 MU')|]. split; [exact (wmono_trans asegs _ _ _ WM1 WM')| exact R]. }
  (* [comment removed for export] *)
  assert (ST3 : forall (z9 : Z) (ra' t1' t2' a1' s3' s6' s7' s10' s11' : word) (mm : mem) (bs1' bs2' : list byte) (wl' : list word),
    munch (D2L0_W lined nl bufs1 bufs2 n1) m mm -> wmono asegs m mm -> mem_inv asegs mm ->
    u8arr asegs mm bufs1 bs1' -> Z.of_nat (length bs1') = n1 -> acc asegs mm bufs1 n1 ->
    u8arr asegs mm bufs2 bs2' -> Z.of_nat (length bs2') = n1 -> acc asegs mm bufs2 n1 ->
    u32arr asegs mm lined wl' -> 4 * Z.of_nat (length wl') = nl -> acc asegs mm lined nl ->
    evt asegs (d2l0_exit sp gp tp F fc m lined nl bufs1 bufs2 n1 ta t38 t14 w tw t38w t14w)
      (MS (mkR ra' sp gp tp (Z_to_bv 64 (Z.lxor (bufs2 + j + 1) 3)) t1' t2' (Z_to_bv 64 3) ONE (Z_to_bv 64 lined) a1' (Z_to_bv 64 bufs1) (Z_to_bv 64 bufs2) (Z_to_bv 64 ta) (Z_to_bv 64 t38) (Z_to_bv 64 t14) (Z_to_bv 64 (Z.lxor (bufs2 + j) 3))
             ONE s3' (Z_to_bv 64 268435455) (Z_to_bv 64 30) s6' s7' (Z_to_bv 64 (Z.lxor (bufs2 + j + 1) 3 / 8 + 2147450880)) (Z_to_bv 64 z9) s10' s11' (Z_to_bv 64 2147450880) (Z_to_bv 64 (w - 1)) (Z_to_bv 64 (2 * j)) (Z_to_bv 64 j))
          F (Z_to_bv 64 0xa3c28) fc None mm (seg_rom asegs))).
  { intros z9 ra' t1' t2' a1' s3' s6' s7' s10' s11' mm bs1' bs2' wl' MU1 WM1 MI1 UB1 UBL1 ACCB1 UC1 UCL1 ACCC1 UL1 ULL1 ACCL1.
    clear MI UB UBL ACCB UC UCL ACCC UL ULL ACCL MU WM.
    lwalk [0xa3c34; 0xa3eac].
    remember (Z.lxor (bufs2 + j + 1) 3 - bufs2) as ix eqn:EIX.
    unpark SEP2. unpark SEP12. unpark CSH.
    arr_sb bufs2 ix (Z.lxor (bufs2 + j + 1) 3).
    park SEP2. park SEP12. park CSH.
    eapply CONT; eassumption. }
  (* [comment removed for export] *)
  assert (ST2 : forall (z2 z9 : Z) (ra' t1' a1' s3' s6' s10' s11' : word) (mm : mem) (bs1' bs2' : list byte) (wl' : list word),
    munch (D2L0_W lined nl bufs1 bufs2 n1) m mm -> wmono asegs m mm -> mem_inv asegs mm ->
    u8arr asegs mm bufs1 bs1' -> Z.of_nat (length bs1') = n1 -> acc asegs mm bufs1 n1 ->
    u8arr asegs mm bufs2 bs2' -> Z.of_nat (length bs2') = n1 -> acc asegs mm bufs2 n1 ->
    u32arr asegs mm lined wl' -> 4 * Z.of_nat (length wl') = nl -> acc asegs mm lined nl ->
    evt asegs (d2l0_exit sp gp tp F fc m lined nl bufs1 bufs2 n1 ta t38 t14 w tw t38w t14w)
      (MS (mkR ra' sp gp tp (Z_to_bv 64 (Z.lxor (bufs2 + j + 1) 3)) t1' (Z_to_bv 64 z2) (Z_to_bv 64 3) ONE (Z_to_bv 64 lined) a1' (Z_to_bv 64 bufs1) (Z_to_bv 64 bufs2) (Z_to_bv 64 ta) (Z_to_bv 64 t38) (Z_to_bv 64 t14) (Z_to_bv 64 (Z.lxor (bufs2 + j) 3))
             ONE s3' (Z_to_bv 64 268435455) (Z_to_bv 64 30) s6' (Z_to_bv 64 (Z.lxor (bufs2 + j) 3 / 8 + 2147450880)) (Z_to_bv 64 (Z.lxor (bufs2 + j + 1) 3 / 8 + 2147450880)) (Z_to_bv 64 z9) s10' s11' (Z_to_bv 64 2147450880) (Z_to_bv 64 (w - 1)) (Z_to_bv 64 (2 * j)) (Z_to_bv 64 j))
          F (Z_to_bv 64 0xa3c1c) fc None mm (seg_rom asegs))).
  { intros z2 z9 ra' t1' a1' s3' s6' s10' s11' mm bs1' bs2' wl' MU1 WM1 MI1 UB1 UBL1 ACCB1 UC1 UCL1 ACCC1 UL1 ULL1 ACCL1.
    clear MI UB UBL ACCB UC UCL ACCC UL ULL ACCL MU WM.
    lwalk [0xa3c24; 0xa3eac].
    remember (Z.lxor (bufs2 + j) 3 - bufs2) as ix eqn:EIX.
    unpark SEP2. unpark SEP12. unpark CSH.
    arr_sb bufs2 ix (Z.lxor (bufs2 + j) 3).
    park SEP2. park SEP12. park CSH.
    eapply ST3; eassumption. }
  (* [comment removed for export] *)
  assert (ST1 : forall (z1 z2 z9 : Z) (ra' s3' s6' s10' s11' : word) (mm : mem) (bs1' bs2' : list byte) (wl' : list word),
    munch (D2L0_W lined nl bufs1 bufs2 n1) m mm -> wmono asegs m mm -> mem_inv asegs mm ->
    u8arr asegs mm bufs1 bs1' -> Z.of_nat (length bs1') = n1 -> acc asegs mm bufs1 n1 ->
    u8arr asegs mm bufs2 bs2' -> Z.of_nat (length bs2') = n1 -> acc asegs mm bufs2 n1 ->
    u32arr asegs mm lined wl' -> 4 * Z.of_nat (length wl') = nl -> acc asegs mm lined nl ->
    evt asegs (d2l0_exit sp gp tp F fc m lined nl bufs1 bufs2 n1 ta t38 t14 w tw t38w t14w)
      (MS (mkR ra' sp gp tp (Z_to_bv 64 (Z.lxor (bufs2 + j + 1) 3)) (Z_to_bv 64 z1) (Z_to_bv 64 z2) (Z_to_bv 64 3) ONE (Z_to_bv 64 lined) (Z_to_bv 64 (Z.lxor (bufs1 + j + 1) 3)) (Z_to_bv 64 bufs1) (Z_to_bv 64 bufs2) (Z_to_bv 64 ta) (Z_to_bv 64 t38) (Z_to_bv 64 t14) (Z_to_bv 64 (Z.lxor (bufs2 + j) 3))
             ONE s3' (Z_to_bv 64 268435455) (Z_to_bv 64 30) s6' (Z_to_bv 64 (Z.lxor (bufs2 + j) 3 / 8 + 2147450880)) (Z_to_bv 64 (Z.lxor (bufs2 + j + 1) 3 / 8 + 2147450880)) (Z_to_bv 64 z9) s10' s11' (Z_to_bv 64 2147450880) (Z_to_bv 64 (w - 1)) (Z_to_bv 64 (2 * j)) (Z_to_bv 64 j))
          F (Z_to_bv 64 0xa3c18) fc None mm (seg_rom asegs))).
  { intros z1 z2 z9 ra' s3' s6' s10' s11' mm bs1' bs2' wl' MU1 WM1 MI1 UB1 UBL1 ACCB1 UC1 UCL1 ACCC1 UL1 ULL1 ACCL1.
    clear MI UB UBL ACCB UC UCL ACCC UL ULL ACCL MU WM.
    remember (Z.lxor (bufs1 + j + 1) 3 - bufs1) as ix eqn:EIX.
    unpark SEP1. unpark SEP12. unpark BSH.
    arr_sb bufs1 ix (Z.lxor (bufs1 + j + 1) 3).
    park SEP1. park SEP12. park BSH.
    eapply ST2; eassumption. }
  (* [comment removed for export] *)
  replace (Z.land (j / 16) 268435455) with (j / 16)
    by (change 268435455 with (Z.ones 28); rewrite Z.land_ones by lia; symmetry; apply Z.mod_small; clear - HJ HK HW; Z.div_mod_to_equations; lia) || idtac.
  lwalk [0xa3cec; 0xa3eac].
  replace (Z.land (j / 16) 268435455) with (j / 16)
    by (change 268435455 with (Z.ones 28); rewrite Z.land_ones by lia; symmetry; apply Z.mod_small; clear - HJ HK HW; Z.div_mod_to_equations; lia).
  replace (lined + j / 16 * 4) with (lined + 4 * (j / 16)) by (clear; lia).
  assert (ULW : Z.of_nat (length wl) = nl / 4) by (clear - ULL L4; Z.div_mod_to_equations; lia).
  assert (JL : 0 <= j / 16 < nl / 4) by (clear - HJ HK HW WL L4; Z.div_mod_to_equations; lia).
  lwalk [0xa3cec; 0xa3eac].
  destruct UB as [HB WB].
  destruct (bytes_at_read1 m bufs1 bs1 (Z.lxor (bufs1 + j) 3 - bufs1) HB ltac:(lia)) as (ov & R).
  replace (bufs1 + (Z.lxor (bufs1 + j) 3 - bufs1)) with (Z.lxor (bufs1 + j) 3) in R by lia.
  lstep. clear R.
  assert (UB : u8arr asegs m bufs1 bs1) by (split; assumption).
  clear HB WB.
  pose proof (bv_unsigned_in_range 8 ov) as OVR. unfold bv_modulus in OVR. change (2 ^ Z.of_N 8) with 256 in OVR.
  set (oz := bv_unsigned ov) in *.
  lwalk [0xa3cec; 0xa3eac].
  replace (ta + oz * 4) with (ta + 4 * oz) by (clear; lia).
  lwalk [0xa3cec; 0xa3eac].
  (* [comment removed for export] *)
  destruct (u32arr_nth wl (j / 16) ltac:(lia)) as (dvw & NTHD).
  pose proof (u32arr_read asegs m lined wl (j / 16) dvw _ UL NTHD ltac:(lia) eq_refl) as R.
  lstep. clear R.
  lwalk [0xa3cec; 0xa3eac].
  pose proof UTL as TWL. 
  destruct (u32arr_nth tw oz ltac:(lia)) as (tv & NTHT).
  pose proof UT as UTm. unfold hid in UTm.
  pose proof (u32arr_read asegs m ta tw oz tv _ UTm NTHT ltac:(lia) eq_refl) as R.
  lstep. clear R UTm.
  lwalk [0xa3cec; 0xa3eac; 0xa3a88].
  (* [comment removed for export] *)
  clear ULL. hide ACCT.
  unpark SEP1. unpark SEP2. unpark LSH.
  arr_sw lined (j / 16) (lined + 4 * (j / 16)).
  park SEP1. park SEP2. park LSH.
  lazymatch goal with H : Z.of_nat (length ?ws) = nl / 4 |- _ => assert (ULL : 4 * Z.of_nat (length ws) = nl) by (rewrite H; clear - L4; Z.div_mod_to_equations; lia) end.
  (* [comment removed for export] *)
  lazymatch type of MU with munch _ _ ?mm =>
    pose proof (u32arr_transport asegs _ _ mm ta tw UT MU WM ltac:(rewrite UTL; cbn [disjoint_from]; unpark SEPT1; unpark SEPT2; unpark SEPT3; clear - SEPT1 SEPT2 SEPT3; lia)) as UTc;
    pose proof (u32arr_transport asegs _ _ mm t38 t38w U38 MU WM ltac:(rewrite U38L; cbn [disjoint_from]; unpark SEP81; unpark SEP82; unpark SEP83; clear - SEP81 SEP82 SEP83; lia)) as U38c;
    pose proof (u32arr_transport asegs _ _ mm t14 t14w U14 MU WM ltac:(rewrite U14L; cbn [disjoint_from]; unpark SEP41; unpark SEP42; unpark SEP43; clear - SEP41 SEP42 SEP43; lia)) as U14c;
    pose proof (acc_transport3 _ mm _ _ _ _ _ _ ta 1024 ACCT MU ltac:(lia) ltac:(lia) ltac:(unpark LSH; exact LSH) ltac:(unpark BSH; exact BSH) ltac:(unpark CSH; exact CSH)) as ACCTc;
    pose proof (acc_transport3 _ mm _ _ _ _ _ _ t38 1024 ACC38 MU ltac:(lia) ltac:(lia) ltac:(unpark LSH; exact LSH) ltac:(unpark BSH; exact BSH) ltac:(unpark CSH; exact CSH)) as ACC38c;
    pose proof (acc_transport3 _ mm _ _ _ _ _ _ t14 1024 ACC14 MU ltac:(lia) ltac:(lia) ltac:(unpark LSH; exact LSH) ltac:(unpark BSH; exact BSH) ltac:(unpark CSH; exact CSH)) as ACC14c end.
  (* [comment removed for export] *)
  lwalk [0xa3cec; 0xa3eac].
  lazymatch goal with UBx : u8arr asegs ?mm bufs1 ?bsx |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    pose proof UBx as [HB WB];
    destruct (bytes_at_read1 mm bufs1 bsx (Z.lxor (bufs1 + j + 1) 3 - bufs1) HB ltac:(lia)) as (rv & R) end.
  replace (bufs1 + (Z.lxor (bufs1 + j + 1) 3 - bufs1)) with (Z.lxor (bufs1 + j + 1) 3) in R by lia.
  lstep. clear R HB WB.
  lwalk [0xa3cec; 0xa3eac].
  lazymatch goal with UCx : u8arr asegs ?mm bufs2 ?bsx |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    pose proof UCx as [HB WB];
    destruct (bytes_at_read1 mm bufs2 bsx (Z.lxor (bufs2 + j) 3 - bufs2) HB ltac:(lia)) as (bvb & R) end.
  replace (bufs2 + (Z.lxor (bufs2 + j) 3 - bufs2)) with (Z.lxor (bufs2 + j) 3) in R by lia.
  lstep. clear R HB WB.
  replace (t38 + oz * 4) with (t38 + 4 * oz) by (clear; lia).
  lwalk [0xa3cec; 0xa3eac].
  lazymatch goal with UCx : u8arr asegs ?mm bufs2 ?bsx |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    pose proof UCx as [HB WB];
    destruct (bytes_at_read1 mm bufs2 bsx (Z.lxor (bufs2 + j + 1) 3 - bufs2) HB ltac:(lia)) as (dv2 & R) end.
  replace (bufs2 + (Z.lxor (bufs2 + j + 1) 3 - bufs2)) with (Z.lxor (bufs2 + j + 1) 3) in R by lia.
  lstep. clear R HB WB.
  replace (t14 + oz * 4) with (t14 + 4 * oz) by (clear; lia).
  lwalk [0xa3cec; 0xa3eac].
  destruct (u32arr_nth t38w oz ltac:(lia)) as (pv & NTHP).
  lazymatch goal with U : u32arr asegs ?mm t38 t38w |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    pose proof (u32arr_read asegs mm t38 t38w oz pv _ U NTHP ltac:(lia) eq_refl) as R end.
  lstep. clear R.
  lwalk [0xa3cec; 0xa3eac].
  destruct (u32arr_nth t14w oz ltac:(lia)) as (qv & NTHQ).
  lazymatch goal with U : u32arr asegs ?mm t14 t14w |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    pose proof (u32arr_read asegs mm t14 t14w oz qv _ U NTHQ ltac:(lia) eq_refl) as R end.
  lstep. clear R.
  pose proof T38S as T38Sv. unfold hid in T38Sv. pose proof (proj1 (Forall_forall tsmall t38w) T38Sv pv (nth_error_In _ _ NTHP)) as PVS. unfold tsmall in PVS. clear T38Sv.
  pose proof T14S as T14Sv. unfold hid in T14Sv. pose proof (proj1 (Forall_forall tsmall t14w) T14Sv qv (nth_error_In _ _ NTHQ)) as QVS. unfold tsmall in QVS. clear T14Sv.
  pose proof (bv_unsigned_in_range 8 rv) as RVR. unfold bv_modulus in RVR. change (2 ^ Z.of_N 8) with 256 in RVR.
  pose proof (bv_unsigned_in_range 8 bvb) as BVR. unfold bv_modulus in BVR. change (2 ^ Z.of_N 8) with 256 in BVR.
  pose proof (bv_unsigned_in_range 8 dv2) as DVR. unfold bv_modulus in DVR. change (2 ^ Z.of_N 8) with 256 in DVR.
  pose proof (bv_unsigned_in_range 64 (sx32 pv)) as PVR. unfold bv_modulus in PVR. change (2 ^ Z.of_N 64) with (2^64) in PVR.
  pose proof (bv_unsigned_in_range 64 (sx32 qv)) as QVR. unfold bv_modulus in QVR. change (2 ^ Z.of_N 64) with (2^64) in QVR.
  (* [comment removed for export] *)
  clear UTc U38c U14c ACCTc ACC38c ACC14c.
  lwalk [0xa3cec; 0xa3eac; 0xa3c18].
  (* [comment removed for export] *)
  brfork SG.
  - (* [comment removed for export] *)
    lwalk [0xa3cec; 0xa3eac; 0xa3c18].
    match goal with |- context [bv_swrap 32 (bv_unsigned ?r + bv_unsigned (sx32 ?v))] => rewrite (swrap_add_small (bv_unsigned r) (bv_unsigned (sx32 v))) by (clear - RVR BVR DVR PVS QVS PVR QVR; lia) end.
    lwalk [0xa3cec; 0xa3eac; 0xa3c18].
    (* [comment removed for export] *)
    shbr_inv_j.
    lwalk [0xa3cec; 0xa3eac; 0xa3c18].
    eapply ST1; eassumption.
  - (* [comment removed for export] *)
    lwalk [0xa3cec; 0xa3eac; 0xa3c18].
    (* [comment removed for export] *)
    rewrite ?Z.add_0_r.
    mergeZ1 0xa3b80 (Z_to_bv 5 6).
    { brfork F1; [ mergeZ_done | lstep; mergeZ_done ]. }
    lwalk [0xa3cec; 0xa3eac; 0xa3c18].
    match goal with |- context [bv_swrap 32 (bv_unsigned ?r + bv_unsigned (sx32 ?v))] => rewrite (swrap_add_small (bv_unsigned r) (bv_unsigned (sx32 v))) by (clear - RVR BVR DVR PVS QVS PVR QVR; lia) end.
    lwalk [0xa3cec; 0xa3eac; 0xa3c18].
    rewrite ?Z.add_0_r.
    brfork F2.
    * (* [comment removed for export] *)
      lwalk [0xa3cec; 0xa3eac; 0xa3c18].
      brfork F3.
      -- (* [comment removed for export] *)
         lwalk [0xa3cec; 0xa3eac; 0xa3c18]. shbr_inv_j. lwalk [0xa3cec; 0xa3eac; 0xa3c18]. eapply ST1; eassumption.
      -- (* [comment removed for export] *)
         lwalk [0xa3cec; 0xa3eac; 0xa3c18]. eapply ST1; eassumption.
    * (* [comment removed for export] *)
      lwalk [0xa3cec; 0xa3eac; 0xa3c18].
      brfork F3.
      -- (* [comment removed for export] *)
         lwalk [0xa3cec; 0xa3eac; 0xa3c18]. eapply ST1; eassumption.
      -- (* [comment removed for export] *)
         lwalk [0xa3cec; 0xa3eac; 0xa3c18]. shbr_inv_j. lwalk [0xa3cec; 0xa3eac; 0xa3c18]. eapply ST1; eassumption.
Qed.
