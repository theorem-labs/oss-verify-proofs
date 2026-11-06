(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import StepA StepA2 SysStepA AImages.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.B Require Import BF_place BF_kit BF_kit2 BF_qkit BF_free6 BF_free7.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.SpecA Require Import AsanConsts AsanSizeClass.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require ZBridge Arr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import SecRanges.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= force_section_ranges.   (* [comment removed for export] *)

From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Ltac lia ::=
  first [ LiaTuning.zify_prune; LiaTuning.zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker
        | LiaTuning.zify_prune; Zify.zify; xlia zchecker
        | Zify.zify; xlia zchecker ].
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac aceil :=
  lazymatch goal with
  | H : _ <= alloc_ceiling <= _ |- _ => idtac
  | |- context [alloc_ceiling] => repeat match goal with H : True |- _ => clear H end; pose proof alloc_ceiling_range as CEILB
  | H : context [alloc_ceiling] |- _ => repeat match goal with H' : True |- _ => clear H' end; pose proof alloc_ceiling_range as CEILB
  | _ => first [ pose proof I as CEILB | idtac ]
  end.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac slia ::= first [ exact I | dlia | split; [dlia | exact I] ].
Local Ltac flia ::= first [ assumption | lia ].
Local Definition carry_skip (P : Prop) := P.
Local Ltac skipH H := lazymatch type of H with ?TS => change TS with (carry_skip TS) in H end.

Local Ltac dlia1 := dlia.   (* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac incl_leaves xq Hq :=
  repeat match type of Hq with _ /\ _ => let Q := fresh "Q" in destruct Hq as [Q Hq] end;
  repeat match goal with |- _ /\ _ => split end; try exact I;
  let C := fresh "C" in intros C;
  first [ match goal with Q : ~ (_ <= xq < _) |- _ => apply Q; LiaA.lia_probe end
        | match goal with D : _ \/ _ |- _ => destruct D as [XD|XD]; match goal with Q : ~ (_ <= xq < _) |- _ => apply Q; LiaA.lia_probe end end ].
(* [comment removed for export] *)
Local Ltac solve_covers ::=
  let lo := fresh "lo" in let hi := fresh "hi" in let Hin := fresh "Hin" in
  intros lo hi Hin; cbn [In app] in Hin;
  repeat match type of Hin with
  | _ \/ _ => destruct Hin as [Hin|Hin]; [injection Hin as <- <-; do 2 eexists; split; [cover_member| cbn [fst snd b_addr]; LiaA.lia_probe] |]
  | _ = _ => injection Hin as <- <-; do 2 eexists; split; [cover_member| cbn [fst snd b_addr]; LiaA.lia_probe]
  | False => contradiction
  end.
Local Ltac carry_rw H MU WM ::= eapply rw_cells_transport in H; [| exact MU| exact WM| cbn; repeat match goal with |- _ /\ _ => split end; first [exact I | dlia1]].
Local Ltac carry_all mc m' MUc WMc ::=
  repeat match goal with
  | H : rw_cells bsegs mc _ _ |- _ => first [ carry_rw H MUc WMc | skipH H ]
  | H : bytes_at bsegs mc _ _ |- _ => first [ eapply bytes_at_transport in H; [| exact MUc| cbn [disjoint_from length]; rewrite ?repeat_length, ?length_le8, ?length_le4; lia] | skipH H ]
  | H : stk bsegs mc _ _ |- _ => first [ eapply stk_transport in H; [| exact MUc| exact WMc| intros; left; cbn; lia] | skipH H ]
  | H : wr_at bsegs mc _ _ |- _ => first [ eapply wr_at_transport in H; [| exact WMc] | skipH H ]
  | H : u8arr bsegs mc _ _ |- _ => first [ eapply u8arr_transport in H; [| exact MUc| exact WMc| cbn [disjoint_from length]; rewrite ?repeat_length; lia] | skipH H ]
  | H : u64arr bsegs mc _ _ |- _ => first [ eapply u64arr_transport in H; [| exact MUc| exact WMc| cbn [disjoint_from length]; lia] | skipH H ]
  | H : u32arr bsegs mc _ _ |- _ => first [ eapply u32arr_transport in H; [| exact MUc| exact WMc| cbn [disjoint_from length]; lia] | skipH H ]
  | H : munch ?W ?ma mc |- _ =>
      let H2 := fresh in
      first [ assert (H2 : munch W ma m')
          by (eapply munch_trans; [exact H| eapply munch_weaken; [| exact MUc];
              first [ sub_fp_fast | let xq := fresh "xq" in let Hq := fresh "Hq" in intros xq Hq; cbn in Hq |- *; decompose [and] Hq; clear Hq; repeat match goal with |- _ /\ _ => split end; try exact I; match goal with O : ~ (_ <= xq < _)%Z |- _ => clear -O; let R := fresh in intros R; apply O; lia end ]]);
        clear H; rename H2 into H | skipH H ]
  | H : wmono bsegs ?ma mc |- _ =>
      let H2 := fresh in
      assert (H2 : wmono bsegs ma m') by (eapply wmono_trans; [exact H| exact WMc]);
      clear H; rename H2 into H
  end;
  repeat match goal with H : carry_skip _ |- _ => unfold carry_skip in H end.
Local Ltac solve_dj ::=
  cbn [disjoint_from cells_size csize length Nat.add Nat.mul app];
  rewrite ?repeat_length, ?length_le8, ?length_le4, ?upd_length;
  repeat first [ exact I
               | split; [dlia1|]
               | (eapply disjoint_from_down; [eassumption| solve_sep1])
               | dlia1 ].
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Section LDC4.  (* [comment removed for export] *)
Variable P : acc -> Prop.
Variables (gp tp s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (usp lo : Z) (CA SB c p RI : Z).
Notation INST := 0xaaf58.
Notation PCB := (BF_free6.PCB CA c).
Notation RIc := (BF_free6.RIc c RI).
Notation FA := (SB + c * 4294967296 + 3758096384).
Notation rregs := (BF_free7.rregs gp tp t3 t4 t5 t6 usp c RI).

Hypothesis LOC : alloc_ceiling <= lo.
Hypothesis LO2 : lo <= usp - 688.
Hypothesis SPH : usp <= 2^47.
Hypothesis SPA : usp mod 16 = 0.
Hypothesis HSB : 0x603000 <= SB /\ SB mod 4096 = 0 /\ SB + kSpaceSize + 4096 <= alloc_ceiling.
Hypothesis HC : 1 <= c <= kLargestClassID.
Hypothesis HCA : (0x1000 <= CA /\ (CA + 2584 <= 0x10000 \/ 0x603000 <= CA)) /\ CA + 2584 <= alloc_ceiling /\ CA mod 8 = 0.   (* [comment removed for export] *)
Hypothesis HCASB : CA + 2584 <= SB \/ SB + kSpaceSize + 4096 <= CA.
Hypothesis HP : SB + c * 2^32 <= p /\ p + 16 <= SB + c * 2^32 + 0xE0000000.
Hypothesis HRI : RI = SB + kSpaceSize.
Hypothesis PSTK : forall a k, lo <= a -> a + Z.of_nat k <= usp -> P (Z_to_bv 64 a, k).
Hypothesis PDAT : forall a k, 0xa5000 <= a -> a + Z.of_nat k <= 0x603000 -> P (Z_to_bv 64 a, k).
Hypothesis PRO : forall a k, 0x10000 <= a -> a + Z.of_nat k <= 0x31000 -> P (Z_to_bv 64 a, k).
Hypothesis PCA : forall a k, CA <= a -> a + Z.of_nat k <= CA + 2584 -> P (Z_to_bv 64 a, k).
Hypothesis PRIR : forall a k, RIc <= a -> a + Z.of_nat k <= RIc + 128 -> P (Z_to_bv 64 a, k).

(* [comment removed for export] *)
Lemma ldc_drain_nogrow : forall mx (ra s0 s1 s2 s3 s4 t0 t1 t2 a4 a5 a6 a7 : word) (h alloc nf mfa au mu na nfr : Z) (csz : word)
    (ws fws : list word) (Q : machine_state -> Prop),
  mem_inv bsegs mx -> stk bsegs mx lo usp ->
  rw_cells bsegs mx 0xaaf78 [C8 (Z_to_bv 64 SB); C4 (Z_to_bv 64 0xffffffff); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 RI)] ->
  rw_cells bsegs mx PCB [C4 (Z_to_bv 64 (2 * h)); C4 (Z_to_bv 64 (2 * h)); C8 csz] ->
  1 <= h <= 8 ->
  u32arr bsegs mx (PCB + 16) ws -> length ws = 16%nat ->
  (forall j, (Z.to_nat h <= j < Z.to_nat (2 * h))%nat -> exists x, nth_error ws j = Some (Z_to_bv 64 x) /\ 0 <= x < 2^31) ->
  rw_cells bsegs mx (CA + 2576) [C8 (Z_to_bv 64 alloc)] ->
  rw_cells bsegs mx RIc (ri_cells 0 nf mfa au mu na nfr) -> 0 <= nf < 2^40 -> 0 <= nfr < 2^64 ->
  u32arr bsegs mx FA fws -> 4 * Z.of_nat (length fws) = mfa -> 4 * (nf + h) <= mfa -> mfa <= 2^29 ->
  (forall a k, FA <= a -> a + Z.of_nat k <= FA + mfa -> P (Z_to_bv 64 a, k)) ->
  rw_cells bsegs mx 0xa5580 [C8 (Z_to_bv 64 0x13e060)] -> rw_cells bsegs mx 0x13e060 [C8 (Z_to_bv 64 4096)] ->
  (forall m' (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' : word),
     mem_inv bsegs m' -> stk bsegs m' lo usp ->
     munch [(usp - 688, usp); (RIc, RIc + 8); (RIc + 16, RIc + 24); (RIc + 80, RIc + 88); (PCB, PCB + 4);
            (PCB + 16 + 4 * h, PCB + 16 + 4 * h + 4); (CA + 2576, CA + 2584); (FA + 4 * nf, FA + 4 * (nf + h))] mx m' -> wmono bsegs mx m' ->
     rw_cells bsegs m' 0xaaf78 [C8 (Z_to_bv 64 SB); C4 (Z_to_bv 64 0xffffffff); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 RI)] ->
     rw_cells bsegs m' PCB [C4 (Z_to_bv 64 (h + 1)); C4 (Z_to_bv 64 (2 * h)); C8 csz] ->
     u32arr bsegs m' (PCB + 16) (upd ws (Z.to_nat h) (Z_to_bv 64 (BF_free6.xc SB c p))) ->
     rw_cells bsegs m' (CA + 2576) [C8 (Z_to_bv 64 (alloc - bv_unsigned csz))] ->
     rw_cells bsegs m' RIc (ri_cells 0 (nf + h) mfa au mu na (nfr + h)) ->
     u32arr bsegs m' FA (cpn (Z.to_nat h) ws fws (Z.to_nat h) (Z.to_nat nf)) ->
     rw_cells bsegs m' 0xa5580 [C8 (Z_to_bv 64 0x13e060)] -> rw_cells bsegs m' 0x13e060 [C8 (Z_to_bv 64 4096)] ->
     evtA bsegs P Q (MS (mkR ra (Z_to_bv 64 usp) gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc ra) fc None m' (seg_rom bsegs))) ->
  evtA bsegs P Q (MS (mkR ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 CA) (Z_to_bv 64 INST) (Z_to_bv 64 c) (Z_to_bv 64 p) a4 a5 a6 a7
                          s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x35068) fc None mx (seg_rom bsegs)).
Proof. aceil.
  intros until Q. intros MI SK INS PC HH ARR LEN SMALL CST RIC NF NFR FAR FLEN MFA MFR PFA G1 V1 CONT.
  pose proof LOC as LOC0. pose proof HSB as HSB0. pose proof HRI as HRI0. pose proof HCA as HCA0. pose proof HC as HC0.
  aceil. unfold kSpaceSize in HSB, HRI0. unfold kLargestClassID in HC.
  pose proof HCASB as HCASB0. unfold kSpaceSize in HCASB.
  unfold BF_free6.PCB, BF_free6.RIc in *.
  (* [comment removed for export] *)
  eapply (ldc_drain_head P gp tp s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc usp lo CA SB c p LOC0 ltac:(clear -CEILB LO2; lia) SPH HSB0 HC0 HCA0 HCASB0 PSTK PDAT PCA RI HRI PRIR LO2);
    [exact MI| exact SK| exact INS| exact PC| exact HH| exact ARR| exact LEN| exact CST| exact RIC| exact NF|].
  clear MI SK. intros m1 j1 j2 MI SK MU1 WM1 DF INS1 PC1 ARR1 CST1 RIC1. unfold BF_free6.PCB, BF_free6.RIc in *.
  unfold BF_free6.drain_frames in DF. destruct DF as (FRa & FRb & FRc). unfold BF_free6.PCB, BF_free6.RIc in FRc.
  carry_all mx m1 MU1 WM1.
  assert (MUall : munch [(usp - 688, usp); (RI + 128 * c, RI + 128 * c + 8); (RI + 128 * c + 16, RI + 128 * c + 24); (RI + 128 * c + 80, RI + 128 * c + 88);
                         (CA + 80 * c, CA + 80 * c + 4); (CA + 80 * c + 16 + 4 * h, CA + 80 * c + 16 + 4 * h + 4); (CA + 2576, CA + 2584);
                         (SB + c * 4294967296 + 3758096384 + 4 * nf, SB + c * 4294967296 + 3758096384 + 4 * (nf + h))] mx m1)
    by (eapply munch_cover; [exact MU1| solve_covers]).
  clear MU1. rename WM1 into WMall.
  (* [comment removed for export] *)
  unfold BF_free6.rta_regs.
  eapply (efa_nogrow P gp tp t3 t4 t5 t6 F fc usp lo CA SB c RI LOC0 LO2 SPH HSB0 HC0 HCA0 HRI PSTK PRIR);
    [exact MI| exact SK| exact RIC1| exact HH| exact NF| exact MFA| clear -CEILB MFA MFR HH NF; lia|].
  clear MI SK. intros m2 MI SK MU2 WM2. unfold BF_free6.PCB, BF_free6.RIc in *.
  carry_all m1 m2 MU2 WM2.
  unfold BF_free7.rregs. unfold BF_free6.PCB, BF_free6.RIc in *.
  (* [comment removed for export] *)
  cstep.                          (* [comment removed for export] *)
  zstepA. if_cases K0; zify_cond K0; [exfalso; revert K0; rewrite ?unsigned_lit by lia; clear -CEILB HH; intros K0; lia|].   (* [comment removed for export] *)
  do 4 zstepA.                    (* [comment removed for export] *)
  replace (nf ≪ 2) with (4 * nf) by (rewrite Z.shiftl_mul_pow2 by lia; change (2^2) with 4; clear; lia).
  replace (h ≪ 2) with (4 * h) by (rewrite Z.shiftl_mul_pow2 by lia; change (2^2) with 4; clear; lia).
  rewrite ?(Z.mod_small (4 * nf)) by (clear -CEILB NF; lia). rewrite ?(Z.mod_small (4 * h)) by (clear -CEILB HH; lia).
  replace (CA + 80 * c + 4 * h + 16 + 4 * h) with (CA + 80 * c + 16 + 4 * (2 * h)) by (clear; lia).
  replace (CA + 80 * c + 4 * h + 16) with (CA + 80 * c + 16 + 4 * (h + 0)) by (clear; lia).
  replace (SB + c * 4294967296 + 3758096384 + 4 * nf) with (SB + c * 4294967296 + 3758096384 + 4 * (nf + 0)) by (clear; lia).
  eapply (fa_copy_loop P gp tp t3 t4 t5 t6 F fc usp lo CA SB c RI LOC0 LO2 HSB0 HC0 HCA0 HCASB0 HRI PCA (Z.to_nat h) 0);
    [clear -CEILB HH; lia| clear -CEILB HH; lia| exact HH| clear -CEILB NF; lia| exact MFA| exact MFR| exact MI| exact ARR1| exact LEN| exact SMALL| exact FAR| exact FLEN| exact PFA|].
  clear MI. intros m3 a1' MI MU3 WM3 ARR3 FAR3. unfold BF_free6.PCB, BF_free6.RIc in *.
  carry_all m2 m3 MU3 WM3.
  (* [comment removed for export] *)
  eapply (rta_tail P gp tp s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc usp lo CA SB c p RI LOC0 LO2 SPH SPA HSB0 HC0 HCA0 HCASB0 HP HRI PSTK PDAT PRO PCA PRIR);
    [exact MI| exact SK| unfold BF_free6.drain_frames; split; [exact FRa| split; [exact FRb| exact FRc]]| exact INS1| exact PC1| exact HH| exact ARR3| exact LEN| exact CST1| exact RIC1| exact NF| exact NFR
    | exact FAR3| rewrite cpn_length; exact FLEN| exact MFR| exact G1| exact V1|].
  clear MI SK. intros m4 t0' t1' t2' a0x a1x a2x a3x a4x a5x a6x a7x MI SK MU4 WM4 INS4 PC4 ARR4 CST4 RIC4 FAR4 G14 V14. unfold BF_free6.PCB, BF_free6.RIc in *.
  replace (Z.to_nat (h + 0)) with (Z.to_nat h) in FAR4 by (clear; lia). replace (Z.to_nat (nf + 0)) with (Z.to_nat nf) in FAR4 by (clear; lia).
  carry_all m3 m4 MU4 WM4.
  eapply CONT; [exact MI| exact SK| exact MUall| exact WMall| exact INS4| exact PC4| exact ARR4| exact CST4| exact RIC4| exact FAR4| exact G14| exact V14].
Qed.
End LDC4.
End RC__1.
(* [comment removed for export] *)
