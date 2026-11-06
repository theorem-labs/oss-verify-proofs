(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import StepA StepA2 SysStepA AImages.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.A Require Import AF_place AF_kit AF_kit2 AF_poison AF_qkit AF_free6 AF_free7.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA.examples Require Import X_mmap_fixed.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.SpecA Require Import AsanConsts AsanSizeClass.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require ZBridge Arr.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import StrFun.
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
  | H : rw_cells asegs mc _ _ |- _ => first [ carry_rw H MUc WMc | skipH H ]
  | H : bytes_at asegs mc _ _ |- _ => first [ eapply bytes_at_transport in H; [| exact MUc| cbn [disjoint_from length]; rewrite ?repeat_length, ?length_le8, ?length_le4; lia] | skipH H ]
  | H : stk asegs mc _ _ |- _ => first [ eapply stk_transport in H; [| exact MUc| exact WMc| intros; left; cbn; lia] | skipH H ]
  | H : wr_at asegs mc _ _ |- _ => first [ eapply wr_at_transport in H; [| exact WMc] | skipH H ]
  | H : u8arr asegs mc _ _ |- _ => first [ eapply u8arr_transport in H; [| exact MUc| exact WMc| cbn [disjoint_from length]; rewrite ?repeat_length; lia] | skipH H ]
  | H : u64arr asegs mc _ _ |- _ => first [ eapply u64arr_transport in H; [| exact MUc| exact WMc| cbn [disjoint_from length]; lia] | skipH H ]
  | H : u32arr asegs mc _ _ |- _ => first [ eapply u32arr_transport in H; [| exact MUc| exact WMc| cbn [disjoint_from length]; lia] | skipH H ]
  | H : munch ?W ?ma mc |- _ =>
      let H2 := fresh in
      first [ assert (H2 : munch W ma m')
          by (eapply munch_trans; [exact H| eapply munch_weaken; [| exact MUc];
              first [ sub_fp_fast | let xq := fresh "xq" in let Hq := fresh "Hq" in intros xq Hq; cbn in Hq |- *; decompose [and] Hq; clear Hq; repeat match goal with |- _ /\ _ => split end; try exact I; match goal with O : ~ (_ <= xq < _)%Z |- _ => clear -O; let R := fresh in intros R; apply O; lia end ]]);
        clear H; rename H2 into H | skipH H ]
  | H : wmono asegs ?ma mc |- _ =>
      let H2 := fresh in
      assert (H2 : wmono asegs ma m') by (eapply wmono_trans; [exact H| exact WMc]);
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
Lemma land_roundup18 : forall x, 0 <= x < 2^62 -> Z.land (x + 262143) 18446744073709289472 = 262144 * ((x + 262143) / 262144).
Proof. aceil.
  intros x Hx. change 18446744073709289472 with (2^64 - 2^18). rewrite land_align_down by lia. change (2^18) with 262144.
  Z.div_mod_to_equations. lia.
Qed.
(* [comment removed for export] *)
Lemma roundup18_next : forall mfa x, 0 <= mfa -> mfa mod 262144 = 0 -> mfa < x <= mfa + 262144 -> 262144 * ((x + 262143) / 262144) = mfa + 262144.
Proof. aceil. intros mfa x H0 HM HX. Z.div_mod_to_equations. nia. Qed.

Section EFAG.
Variable P : acc -> Prop.
Variables (gp tp s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (usp lo : Z) (CA SB c p RI : Z).
Notation INST := 0xaa518.
Notation PCB := (AF_free6.PCB CA c).
Notation RIc := (AF_free6.RIc c RI).
Notation FA := (SB + c * 4294967296 + 3758096384).
Notation rregs := (AF_free7.rregs gp tp t3 t4 t5 t6 usp c RI).
Notation rta_regs := (AF_free6.rta_regs gp tp t3 t4 t5 t6 usp CA SB c RI).

Hypothesis LOC : alloc_ceiling <= lo.
Hypothesis LO2 : lo <= usp - 688.
Hypothesis SPH : usp <= 2^47.
Hypothesis SPA : usp mod 16 = 0.
Hypothesis HSB : 0x603000 <= SB /\ SB mod 4096 = 0 /\ SB + kSpaceSize + 4096 <= alloc_ceiling.
Hypothesis HSBH : kHighMemBeg <= SB.
Hypothesis HC : 1 <= c <= kLargestClassID.
Hypothesis HCA : (0x1000 <= CA /\ (CA + 2584 <= 0x10000 \/ 0x603000 <= CA)) /\ CA + 2584 <= alloc_ceiling /\ CA mod 8 = 0.   (* [comment removed for export] *)
Hypothesis HCASB : CA + 2584 <= SB \/ SB + kSpaceSize + 4096 <= CA.
Hypothesis HRI : RI = SB + kSpaceSize.
Hypothesis PSTK : forall a k, lo <= a -> a + Z.of_nat k <= usp -> P (Z_to_bv 64 a, k).
Hypothesis PDAT : forall a k, 0xa4000 <= a -> a + Z.of_nat k <= 0x603000 -> P (Z_to_bv 64 a, k).
Hypothesis PRO : forall a k, 0x10000 <= a -> a + Z.of_nat k <= 0x31000 -> P (Z_to_bv 64 a, k).
Hypothesis PRIR : forall a k, RIc <= a -> a + Z.of_nat k <= RIc + 128 -> P (Z_to_bv 64 a, k).

(* [comment removed for export] *)
Definition gregs (ra : word) (sp : Z) (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 : word) (h nf mfa : Z) : _ :=
  mkR ra (Z_to_bv 64 sp) gp tp t0 t1 t2 (Z_to_bv 64 (mfa + 262144)) (Z_to_bv 64 (FA + mfa)) a0 a1 a2 a3 a4 a5 a6 a7
      (Z_to_bv 64 262144) (Z_to_bv 64 RIc) (Z_to_bv 64 INST) (Z_to_bv 64 h) (Z_to_bv 64 (PCB + 4 * h + 16)) (Z_to_bv 64 (nf + h))
      (Z_to_bv 64 2305843009213693952) (Z_to_bv 64 FA) (Z_to_bv 64 1152921504607895551) (Z_to_bv 64 1152921504606846976) t3 t4 t5 t6.
Definition efa_frame (m : mem) (j : list byte) (nf : Z) : Prop :=
  rw_cells asegs m (usp + -288) [CB 8 j; C8 (Z_to_bv 64 (usp + -104)); C8 (Z_to_bv 64 c); C8 (Z_to_bv 64 nf); C8 (Z_to_bv 64 RIc); C8 (Z_to_bv 64 0x358f8)].

(* [comment removed for export] *)
Lemma efa_grow_pre : forall mx (t0 t1 t2 : word) (h nf mfa au mu na nfr mtx : Z) (Q : machine_state -> Prop),
  mem_inv asegs mx -> stk asegs mx lo (usp + -240) ->
  rw_cells asegs mx 0xaa538 [C8 (Z_to_bv 64 SB); C4 (Z_to_bv 64 0xffffffff); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 RI); C1 (Z_to_bv 8 0)] ->
  rw_cells asegs mx RIc (ri_cells mtx nf mfa au mu na nfr) ->
  1 <= h <= 8 -> 0 <= nf -> 4 * nf <= mfa -> mfa < 4 * (nf + h) -> 0 <= mfa -> mfa mod 262144 = 0 -> mfa + 262144 <= 2^29 ->
  (forall m' j,
     mem_inv asegs m' -> stk asegs m' lo (usp + -288) ->
     munch [(usp + -288, usp + -240)] mx m' -> wmono asegs mx m' -> efa_frame m' j nf ->
     evtA asegs P Q (MS (gregs (Z_to_bv 64 0x35b5c) (usp + -288) t0 t1 t2 (Z_to_bv 64 INST) (Z_to_bv 64 (FA + mfa)) (Z_to_bv 64 262144) (Z_to_bv 64 0x189ef)
                               (Z_to_bv 64 mfa) (Z_to_bv 64 3758096384) (Z_to_bv 64 0) (Z_to_bv 64 1500) h nf mfa)
                        F (Z_to_bv 64 0x6fb6c) fc None m' (seg_rom asegs))) ->
  evtA asegs P Q (MS (rta_regs (Z_to_bv 64 0x358f8) t0 t1 t2 (Z_to_bv 64 nf) (Z_to_bv 64 INST) (Z_to_bv 64 RIc) (Z_to_bv 64 (nf + h))
                            (Z_to_bv 64 0) (Z_to_bv 64 1152921504606846976) (Z_to_bv 64 0) (Z_to_bv 64 1500) h nf)
                     F (Z_to_bv 64 0x35abc) fc None mx (seg_rom asegs)).
Proof. aceil.
  intros until Q. intros MI SK INS RIC HH NF NF4 MFA MF0 MFM MFR CONT. unfold ri_cells in RIC. unfold AF_free6.rta_regs, gregs, efa_frame in *.
  pose proof LOC as LOC0. pose proof HSB as HSB0. pose proof HRI as HRI0. aceil.
  unfold kSpaceSize in HSB, HCASB, HRI0. pose proof HC as HC0. unfold kLargestClassID in HC.
  assert (MU : munch [(usp + -288, usp + -240)] mx mx) by apply munch_refl.
  assert (WM : wmono asegs mx mx) by apply wmono_refl.
  unfold AF_free6.PCB in *. set (PCBv := CA + 80 * c) in *. assert (HPCB : PCBv = CA + 80 * c) by reflexivity. clearbody PCBv.
  unfold AF_free6.RIc in *. set (RIv := RI + 128 * c) in *. assert (HRIv : RIv = RI + 128 * c) by reflexivity. clearbody RIv.
  carve_frame 48%nat SK.
  do 6 cstep.                     (* [comment removed for export] *)
  zstepA.                         (* [comment removed for export] *)
  do 2 zstepA.                    (* [comment removed for export] *)
  replace ((nf + h) ≪ 2) with (4 * (nf + h)) by (rewrite Z.shiftl_mul_pow2 by lia; change (2^2) with 4; clear; lia).
  rewrite ?(Z.mod_small (4 * (nf + h))) by (clear -CEILB HH NF; lia).
  zstepA. if_cases K0; zify_cond K0; [exfalso; revert K0; rewrite ?unsigned_lit by lia; clear -CEILB HH NF MFA MFR MF0; intros K0; lia|].  (* [comment removed for export] *)
  do 3 zstepA.                    (* [comment removed for export] *)
  do 2 zstepA.                    (* [comment removed for export] *)
  rewrite land_roundup18 by (clear -CEILB HH NF NF4 MFR; lia).
  rewrite (roundup18_next mfa (4 * (nf + h))) by (clear -CEILB HH NF MF0 MFM MFA NF4; lia).
  do 2 zstepA.                    (* [comment removed for export] *)
  zstepA. if_cases K1; zify_cond K1; [exfalso; revert K1; rewrite ?unsigned_lit by lia; clear -CEILB MFR MF0; intros K1; lia|].  (* [comment removed for export] *)
  zstepA.                         (* [comment removed for export] *)
  do 4 zstepA.                    (* [comment removed for export] *)
  cstep.                          (* [comment removed for export] *)
  do 2 zstepA.                    (* [comment removed for export] *)
  replace (mfa + 262144 - mfa) with 262144 by (clear; lia).
  do 4 zstepA.                    (* [comment removed for export] *)
  cstep.                          (* [comment removed for export] *)
  (* [comment removed for export] *)
  replace (mfa + (SB + c * 4294967296 + 3758096384)) with (SB + c * 4294967296 + 3758096384 + mfa) by (clear; lia).
  eapply CONT; [exact MI| exact SK| exact MU| exact WM| eexact FR].
Qed.

(* [comment removed for export] *)
Lemma efa_grow_ok : forall mx (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 : word) (h nf mfa au mu na nfr mtx : Z) (j : list byte) (shj : list byte)
    (TSD CTX T nmaps nmapped : Z) (Q : machine_state -> Prop),
  mem_inv asegs mx -> stk asegs mx lo (usp + -288) -> efa_frame mx j nf ->
  rw_cells asegs mx RIc (ri_cells mtx nf mfa au mu na nfr) ->
  1 <= h <= 8 -> 0 <= nf -> 4 * nf <= mfa -> 0 <= mfa -> mfa mod 262144 = 0 -> mfa + 262144 <= 2^29 ->
  poison_globals mx ->
  rw_cells asegs mx (kShadowBase + (FA + mfa) / 8) [CB (Z.to_nat 32768) shj] ->
  (forall a k, kShadowBase + (FA + mfa) / 8 <= a -> a + Z.of_nat k <= kShadowBase + (FA + mfa) / 8 + 32768 -> P (Z_to_bv 64 a, k)) ->
  thread_cells mx tp TSD CTX T -> 0x5cfdd0 <= TSD -> TSD + 8 <= 0x603000 -> placed_s CTX 4096 -> placed_s T 4096 ->   (* [comment removed for export] *)
  0x5cfdd0 + 88 <= bv_unsigned tp < 0x603000 -> (CTX + 160 <= T \/ T + 4096 <= CTX) ->
  (T + 4096 <= SB \/ SB + kSpaceSize + 4096 <= T) -> (CTX + 4096 <= SB \/ SB + kSpaceSize + 4096 <= CTX) ->
  P (Z_to_bv 64 (CTX + 152), 8%nat) -> (forall a k, T <= a -> a + Z.of_nat k <= T + 4096 -> P (Z_to_bv 64 a, k)) ->
  rw_cells asegs mx (T + 2872) [C8 (Z_to_bv 64 nmaps); C8 (Z_to_bv 64 nmapped)] -> 0 <= nmaps -> 0 <= nmapped ->
  (forall m' (t0' t1' t2' a4' a5' a6' a7' t3' t4' t5' t6' : word),
     mem_inv asegs m' -> stk asegs m' lo (usp + -240) ->
     munch [(usp - 688, usp + -240); (kShadowBase + (FA + mfa) / 8, kShadowBase + (FA + mfa) / 8 + 32768); (T + 2872, T + 2888); (RIc + 24, RIc + 32)] mx m' ->
     wmono asegs mx m' ->
     rw_cells asegs m' RIc (ri_cells mtx nf (mfa + 262144) au mu na nfr) ->
     poison_globals m' ->
     rw_cells asegs m' (kShadowBase + (FA + mfa) / 8) [CB (Z.to_nat 32768) (repeat (Z_to_bv 8 250) (Z.to_nat 32768))] ->
     thread_cells m' tp TSD CTX T ->
     rw_cells asegs m' (T + 2872) [C8 (Z_to_bv 64 (nmaps + 1)); C8 (Z_to_bv 64 (nmapped + 262144))] ->
     evtA asegs P Q (MS (AF_free7.rregs gp tp t3' t4' t5' t6' usp c RI (Z_to_bv 64 0x358f8) t0' t1' t2' (Z_to_bv 64 nf) (Z_to_bv 64 1) (Z_to_bv 64 RIc) (Z_to_bv 64 (nmaps + 1)) (Z_to_bv 64 1)
                               a4' a5' a6' a7' (Z_to_bv 64 (PCB + 4 * h + 16)) (Z_to_bv 64 FA) h nf)
                        F (Z_to_bv 64 0x358f8) fc None m' (seg_rom asegs))) ->
  evtA asegs P Q (MS (gregs (Z_to_bv 64 0x35b5c) (usp + -288) t0 t1 t2 (Z_to_bv 64 (FA + mfa)) a1 a2 a3 a4 a5 a6 a7 h nf mfa)
                     F (Z_to_bv 64 0x35b5c) fc None mx (seg_rom asegs)).
Proof. aceil.
  intros until Q. intros MI SK FR RIC HH NF NF4 MF0 MFM MFR PG SHJ PSH TC HT1 HT2 HCp HTp HTP HTC HTSB HCSB PCTX PT TST HNM HNMD CONT.
  pose proof SPA as SPA_dep.   (* [comment removed for export] *)
  pose proof HCp as (HC1 & HC2 & HCg & HCs). pose proof HTp as (HT3 & HT4 & HTg & HTs). unfold A_IMG_END in HCg, HTg. unfold A_LOWAPP_END, A_HIGH_BEG in HCs, HTs.
  unfold ri_cells in RIC, CONT. unfold gregs, efa_frame, AF_free7.rregs in *.
  pose proof LOC as LOC0. pose proof HSB as HSB0. pose proof HRI as HRI0. pose proof HCA as HCApin. pose proof HCASB as HCASBpin. aceil.
  unfold kSpaceSize in HSB, HCASB, HRI0, HTSB, HCSB. pose proof HC as HC0. unfold kLargestClassID in HC. pose proof HSBH as HSBH0. rewrite kHighMemBeg_val in HSBH0.
  assert (MU : munch [(usp - 688, usp + -240); (kShadowBase + (FA + mfa) / 8, kShadowBase + (FA + mfa) / 8 + 32768); (T + 2872, T + 2888); (RIc + 24, RIc + 32)] mx mx) by apply munch_refl.
  assert (WM : wmono asegs mx mx) by apply wmono_refl.
  unfold kShadowBase in *.
  unfold AF_free6.PCB in *. set (PCBv := CA + 80 * c) in *. assert (HPCB : PCBv = CA + 80 * c) by reflexivity. clearbody PCBv.
  unfold AF_free6.RIc in *. set (RIv := RI + 128 * c) in *. assert (HRIv : RIv = RI + 128 * c) by reflexivity. clearbody RIv.
  set (A := SB + c * 4294967296 + 3758096384 + mfa) in *. assert (HA : A = SB + c * 4294967296 + 3758096384 + mfa) by reflexivity. clearbody A.
  assert (A8 : A mod 8 = 0) by (rewrite HA; clear -CEILB HSB MFM; Z.div_mod_to_equations; lia).
  destruct TC as (TC1 & TC2 & TC3 & TC4 & TC5).
  zstepA. if_cases K0; zify_cond K0; [exfalso; revert K0; rewrite ?unsigned_lit by lia; clear -CEILB HA HSB HC MF0; intros K0; lia|].   (* [comment removed for export] *)
  zstepA.                         (* [comment removed for export] *)
  zstepA. if_cases K1; zify_cond K1; [exfalso; clear -CEILB K1; lia|].     (* [comment removed for export] *)
  do 3 zstepA.                    (* [comment removed for export] *)
  cstep.                          (* [comment removed for export] *)
  pose proof PG as (G1 & G2 & G3 & G4 & G5 & G6 & G7).
  assert (HA8 : A / 8 * 8 = A) by (clear -CEILB A8; Z.div_mod_to_equations; lia).
  eapply evtA_cut;
    [ eapply (poison_walk P _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo A 262144 250 shj);
      [ rewrite unsigned_lit by lia; exact SK| exact LOC0| rewrite unsigned_lit by lia; clear -CEILB LO2; lia| rewrite unsigned_lit by lia; clear -CEILB SPH; lia| exact MI
      | exact (conj G1 (conj G2 (conj G3 (conj G4 (conj G5 (conj G6 G7))))))
      | exact A8| reflexivity| clear; lia| clear -CEILB HA HSB HSBH0 HC MF0 MFR; lia| clear -CEILB HA HSB HC MF0 MFR; lia
      | right; rewrite kHighMemBeg_val; split; [clear -CEILB HA HSB HSBH0 HC MF0 MFR; lia| right; clear; lia]| clear; lia| left; clear; lia
      | change (262144 / 8) with 32768; exact SHJ
      | rewrite unsigned_lit by lia; intros; apply PSTK; lia| exact PDAT
      | change (262144 / 8) with 32768; unfold kShadowBase; exact PSH ]
    |].
  clear G1 G2 G3 G4 G5 G6 G7 SHJ.
  cbv beta. intros ms' POST. unfold poison_post in POST. destruct POST as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> & MUc & WMc & MI' & SK' & SH' & PG').
  unfold kShadowBase in MUc, SH'. rewrite !unsigned_lit in MUc, SK' by lia. change (262144 / 8) with 32768 in MUc, SH'.
  clear MI SK. lazymatch type of MUc with munch _ ?mc _ => after_call mc m' MUc WMc end. ret_pc_lit.
  rename MI' into MI. rename SK' into SK.
  destruct PG' as (G1 & G2 & G3 & G4 & G5 & G6 & G7).
  (* [comment removed for export] *)
  cstep.                          (* [comment removed for export] *)
  eapply evtA_cut;
    [ eapply (gcts_walk P _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo TSD CTX T);
      [ rewrite unsigned_lit by lia; exact SK| exact LOC0| rewrite unsigned_lit by lia; clear -CEILB LO2; lia| rewrite unsigned_lit by lia; clear -CEILB SPH; lia| exact MI
      | exact (conj TC1 (conj TC2 (conj TC3 (conj TC4 TC5))))| clear -CEILB HT1; lia| exact HT2| clear -CEILB HC1; lia| exact HC2| clear -CEILB HT3 HT4; lia| clear -CEILB HTP; lia
      | rewrite unsigned_lit by lia; intros; apply PSTK; lia| exact PDAT| exact PCTX ]
    |].
  cbv beta. intros ms2 POST. unfold gcts_post in POST. destruct POST as (a1x & m2 & -> & MU2 & WM2 & MI2 & SK2).
  rewrite !unsigned_lit in MU2, SK2 by lia.
  clear MI SK. lazymatch type of MU2 with munch _ ?mc _ => after_call mc m2 MU2 WM2 end. ret_pc_lit.
  rename MI2 into MI. rename SK2 into SK.
  zstepA. zstepA.                 (* [comment removed for export] *)
  zstepA. zstepA.                 (* [comment removed for export] *)
  cstep. cstep.                   (* [comment removed for export] *)
  zstepA.                         (* [comment removed for export] *)
  cstep.                          (* [comment removed for export] *)
  zstepA.                         (* [comment removed for export] *)
  cstep.                          (* [comment removed for export] *)
  do 6 cstep.                     (* [comment removed for export] *)
  release_frame FR SK (usp + -240).
  cstep. ret_pc_lit.              (* [comment removed for export] *)
  subst PCBv RIv A.
  eapply CONT; [exact MI| exact SK| exact MU| exact WM| exact RIC| exact (conj G1 (conj G2 (conj G3 (conj G4 (conj G5 (conj G6 G7))))))
               | exact SH'| exact (conj TC1 (conj TC2 (conj TC3 (conj TC4 TC5))))| exact TST].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
End EFAG.

End RC__1.
(* [comment removed for export] *)
