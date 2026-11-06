(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import StepA StepA2 SysStepA AImages AImageFacts NodesA ImplRzA NodesA_mm.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA.examples Require Import X_mmap_fixed.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.A Require Import AF_place AF_kit AF_kit2 AF_poison AF_qkit AF_mmfix1 AF_free6 AF_free7 AF_free9.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.SpecA Require Import AsanConsts AsanSizeClass.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require ZBridge Arr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
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
  | H : u8arr asegs mc _ _ |- _ => first [ eapply u8arr_transport in H; [| exact MUc| exact WMc| cbn [disjoint_from length]; rewrite ?repeat_length; repeat match goal with |- _ /\ _ => split end; first [exact I | dlia1]] | skipH H ]
  | H : u64arr asegs mc _ _ |- _ => first [ eapply u64arr_transport in H; [| exact MUc| exact WMc| cbn [disjoint_from length]; repeat match goal with |- _ /\ _ => split end; first [exact I | dlia1]] | skipH H ]
  | H : u32arr asegs mc _ _ |- _ => first [ eapply u32arr_transport in H; [| exact MUc| exact WMc| cbn [disjoint_from length]; repeat match goal with |- _ /\ _ => split end; first [exact I | dlia1]] | skipH H ]
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
Section RAG.
Variable P : acc -> Prop.
Variables (gp tp s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (usp lo : Z) (CA SB c p RI : Z).
Notation INST := 0xaa518.
Notation PCB := (AF_free6.PCB CA c).
Notation RIc := (AF_free6.RIc c RI).
Notation FA := (SB + c * 4294967296 + 3758096384).
Notation rregs := (AF_free7.rregs gp tp t3 t4 t5 t6 usp c RI).
Notation gregs := (AF_free9.gregs gp tp t3 t4 t5 t6 CA SB c RI).

Hypothesis LOC : alloc_ceiling <= lo.
Hypothesis LO2 : lo <= usp - 688.
Hypothesis SPH : usp <= 2^47.
Hypothesis SPA : usp mod 16 = 0.
Hypothesis HSB : 0x603000 <= SB /\ SB mod 4096 = 0 /\ SB + kSpaceSize + 4096 <= alloc_ceiling.
Hypothesis HSBH : kHighMemBeg <= SB.
Hypothesis HC : 1 <= c <= kLargestClassID.
Hypothesis HCA : (0x1000 <= CA /\ (CA + 2584 <= 0x10000 \/ 0x603000 <= CA)) /\ CA + 2584 <= alloc_ceiling /\ CA mod 8 = 0.   (* [comment removed for export] *)
Hypothesis HCASB : CA + 2584 <= SB \/ SB + kSpaceSize + 4096 <= CA.
Hypothesis HP : SB + c * 2^32 <= p /\ p + 16 <= SB + c * 2^32 + 0xE0000000.
Hypothesis HRI : RI = SB + kSpaceSize.
Hypothesis PSTK : forall a k, lo <= a -> a + Z.of_nat k <= usp -> P (Z_to_bv 64 a, k).
Hypothesis PDAT : forall a k, 0xa4000 <= a -> a + Z.of_nat k <= 0x603000 -> P (Z_to_bv 64 a, k).
Hypothesis PRO : forall a k, 0x10000 <= a -> a + Z.of_nat k <= 0x31000 -> P (Z_to_bv 64 a, k).
Hypothesis PCA : forall a k, CA <= a -> a + Z.of_nat k <= CA + 2584 -> P (Z_to_bv 64 a, k).
Hypothesis PRIR : forall a k, RIc <= a -> a + Z.of_nat k <= RIc + 128 -> P (Z_to_bv 64 a, k).


(* [comment removed for export] *)
Lemma rta_after_grow : forall m3 (ra s0 s1 s2 s3 s4 t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
    (h alloc nf mfa au mu na nfr : Z) (csz : word) (ws fws : list word) (shj j1 j2 j : list byte) (TSD CTX T nmaps nmapped : Z)
    (Q : machine_state -> Prop),
  mem_inv asegs m3 -> stk asegs m3 lo (usp + -288) ->
  AF_free6.drain_frames s5 s6 s7 s8 s9 s10 s11 usp CA c p RI m3 ra s0 s1 s2 s3 s4 j1 j2 ->
  AF_free9.efa_frame usp c RI m3 j nf ->
  rw_cells asegs m3 0xaa538 [C8 (Z_to_bv 64 SB); C4 (Z_to_bv 64 0xffffffff); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 RI); C1 (Z_to_bv 8 0)] ->
  rw_cells asegs m3 PCB [C4 (Z_to_bv 64 h); C4 (Z_to_bv 64 (2 * h)); C8 csz] ->
  1 <= h <= 8 ->
  Arr.u32arr asegs m3 (PCB + 16) ws -> length ws = 16%nat ->
  (forall j, (Z.to_nat h <= j < Z.to_nat (2 * h))%nat -> exists x, nth_error ws j = Some (Z_to_bv 64 x) /\ 0 <= x < 2^31) ->
  rw_cells asegs m3 (CA + 2576) [C8 (Z_to_bv 64 alloc)] ->
  rw_cells asegs m3 RIc (ri_cells 1152921504606846976 nf mfa au mu na nfr) -> 0 <= nf -> 0 <= nfr < 2^64 ->
  Arr.u32arr asegs m3 FA (fws ++ repeat (Z_to_bv 64 0) (Z.to_nat 65536)) -> 4 * Z.of_nat (length fws) = mfa ->
  4 * nf <= mfa -> mfa < 4 * (nf + h) -> mfa mod 262144 = 0 -> mfa + 262144 <= 2^29 ->
  (forall a k, FA <= a -> a + Z.of_nat k <= FA + mfa + 262144 -> P (Z_to_bv 64 a, k)) ->
  statics m3 -> poison_globals m3 ->
  rw_cells asegs m3 (kShadowBase + (FA + mfa) / 8) [CB (Z.to_nat 32768) shj] ->
  (forall a k, kShadowBase + (FA + mfa) / 8 <= a -> a + Z.of_nat k <= kShadowBase + (FA + mfa) / 8 + 32768 -> P (Z_to_bv 64 a, k)) ->
  thread_cells m3 tp TSD CTX T -> 0x5cfdd0 <= TSD -> TSD + 8 <= 0x603000 -> placed_s CTX 4096 -> placed_s T 4096 ->   (* [comment removed for export] *)
  0x5cfdd0 + 88 <= bv_unsigned tp < 0x603000 -> (CTX + 160 <= T \/ T + 4096 <= CTX) ->
  (T + 4096 <= SB \/ SB + kSpaceSize + 4096 <= T) -> (CTX + 4096 <= SB \/ SB + kSpaceSize + 4096 <= CTX) ->
  P (Z_to_bv 64 (CTX + 152), 8%nat) -> (forall a k, T <= a -> a + Z.of_nat k <= T + 4096 -> P (Z_to_bv 64 a, k)) ->
  rw_cells asegs m3 (T + 2872) [C8 (Z_to_bv 64 nmaps); C8 (Z_to_bv 64 nmapped)] -> 0 <= nmaps -> 0 <= nmapped -> CA = T + 208 ->
  (forall m' (t0x t1x t2x a0x a1x a2x a3x a4x a5x a6x a7x t3x t4x t5x t6x : word),
     mem_inv asegs m' -> stk asegs m' lo usp -> statics m' ->
     munch [(usp - 688, usp); (RIc, RIc + 8); (RIc + 16, RIc + 32); (RIc + 80, RIc + 88); (PCB, PCB + 4);
            (PCB + 16 + 4 * h, PCB + 16 + 4 * h + 4); (CA + 2576, CA + 2584); (FA + 4 * nf, FA + 4 * (nf + h));
            (kShadowBase + (FA + mfa) / 8, kShadowBase + (FA + mfa) / 8 + 32768); (T + 2872, T + 2888)] m3 m' ->
     wmono asegs m3 m' ->
     rw_cells asegs m' 0xaa538 [C8 (Z_to_bv 64 SB); C4 (Z_to_bv 64 0xffffffff); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 RI); C1 (Z_to_bv 8 0)] ->
     rw_cells asegs m' PCB [C4 (Z_to_bv 64 (h + 1)); C4 (Z_to_bv 64 (2 * h)); C8 csz] ->
     Arr.u32arr asegs m' (PCB + 16) (upd ws (Z.to_nat h) (Z_to_bv 64 (AF_free6.xc SB c p))) ->
     rw_cells asegs m' (CA + 2576) [C8 (Z_to_bv 64 (alloc - bv_unsigned csz))] ->
     rw_cells asegs m' RIc (ri_cells 0 (nf + h) (mfa + 262144) au mu na (nfr + h)) ->
     Arr.u32arr asegs m' FA (cpn (Z.to_nat h) ws (fws ++ repeat (Z_to_bv 64 0) (Z.to_nat 65536)) (Z.to_nat h) (Z.to_nat nf)) ->
     rw_cells asegs m' (kShadowBase + (FA + mfa) / 8) [CB (Z.to_nat 32768) (repeat (Z_to_bv 8 250) (Z.to_nat 32768))] ->
     poison_globals m' -> thread_cells m' tp TSD CTX T ->
     rw_cells asegs m' (T + 2872) [C8 (Z_to_bv 64 (nmaps + 1)); C8 (Z_to_bv 64 (nmapped + 262144))] ->
     evtA asegs P Q (MS (mkR ra (Z_to_bv 64 usp) gp tp t0x t1x t2x s0 s1 a0x a1x a2x a3x a4x a5x a6x a7x
                             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3x t4x t5x t6x) F (ret_pc ra) fc None m' (seg_rom asegs))) ->
  evtA asegs P Q (MS (AF_free9.gregs gp tp t3' t4' t5' t6' CA SB c RI (Z_to_bv 64 0x35b5c) (usp + -288) t0' t1' t2' (Z_to_bv 64 (FA + mfa)) a1' a2' a3' a4' a5' a6' a7' h nf mfa)
                     F (Z_to_bv 64 0x35b5c) fc None m3 (seg_rom asegs)).
Proof. aceil.
  intros until Q. intros MI3 SK3 DF FRd INS PC HH ARR LEN SMALL CST RIC NF NFR FAR3 FLEN NF4 MFA MFM MFR PFA STA3 PG SHJ PSH
         TC HT1 HT2 HCp HTp HTP HTC HTSB HCSB PCTX PT TST HNM HNMD HCAT CONT.
  pose proof LOC as LOC0. pose proof HSB as HSB0. pose proof HRI as HRI0. pose proof HCA as HCA0. pose proof HC as HC0. pose proof HCASB as HCASB0.
  aceil.
  pose proof HCp as (HC1 & HC2 & HCg & HCs). pose proof HTp as (HT3 & HT4 & HTg & HTs). unfold A_IMG_END in HCg, HTg. unfold A_LOWAPP_END, A_HIGH_BEG in HCs, HTs.
  unfold kSpaceSize in HTSB, HCSB. unfold kSpaceSize in HSB, HRI0, HCASB. unfold kLargestClassID in HC.
  pose proof HSBH as HSBH0. rewrite kHighMemBeg_val in HSBH0.
  assert (MF0 : 0 <= mfa) by (clear -CEILB FLEN; lia).
  unfold kShadowBase in *. unfold ri_cells in RIC, CONT.
  unfold AF_free6.drain_frames in DF. destruct DF as (FRa & FRb & FRc). unfold AF_free6.PCB, AF_free6.RIc in *.
  lazymatch type of INS with rw_cells _ _ _ (?c1 :: ?c2 :: ?c3 :: ?c4 :: ?c5 :: nil) =>
    destruct (rwc_split asegs m3 0xaa538 [c1; c2; c3; c4] [c5] INS) as [INS4 _] end.
  assert (FLEN3 : 4 * Z.of_nat (length (fws ++ repeat (Z_to_bv 64 0) (Z.to_nat 65536))) = mfa + 262144) by (rewrite length_app, repeat_length; clear -CEILB FLEN; lia).
  open_statics STA3. destruct PG as (P1 & P2 & P3 & P4 & P5 & P6 & P7). destruct TC as (TC1 & TC2 & TC3 & TC4 & TC5).
  eapply (efa_grow_ok P gp tp t3' t4' t5' t6' F fc usp lo CA SB c RI LOC0 LO2 SPH SPA HSB0 HSBH HC0 HCA0 HCASB0 HRI PSTK PDAT PRIR);
    [ exact MI3| exact SK3| unfold AF_free9.efa_frame, AF_free6.RIc; exact FRd| unfold ri_cells; exact RIC| exact HH| exact NF| exact NF4| exact MF0| exact MFM| exact MFR
    | exact (conj P1 (conj P2 (conj P3 (conj P4 (conj P5 (conj P6 P7))))))
    | unfold kShadowBase; exact SHJ| unfold kShadowBase; exact PSH
    | exact (conj TC1 (conj TC2 (conj TC3 (conj TC4 TC5))))| exact HT1| exact HT2| exact HCp| exact HTp| exact HTP| exact HTC
    | unfold kSpaceSize; exact HTSB| unfold kSpaceSize; exact HCSB| exact PCTX| exact PT| exact TST| exact HNM| exact HNMD|].
  assert (MUall : munch [(usp - 688, usp); (RI + 128 * c, RI + 128 * c + 8); (RI + 128 * c + 16, RI + 128 * c + 32); (RI + 128 * c + 80, RI + 128 * c + 88);
                         (CA + 80 * c, CA + 80 * c + 4); (CA + 80 * c + 16 + 4 * h, CA + 80 * c + 16 + 4 * h + 4); (CA + 2576, CA + 2584);
                         (FA + 4 * nf, FA + 4 * (nf + h));
                         (2147450880 + (FA + mfa) / 8, 2147450880 + (FA + mfa) / 8 + 32768); (T + 2872, T + 2888)] m3 m3) by apply munch_refl.
  assert (WMall : wmono asegs m3 m3) by apply wmono_refl.
  clear MI3 SK3 RIC SHJ TST P1 P2 P3 P4 P5 P6 P7 TC1 TC2 TC3 TC4 TC5.
  intros m4 t0x t1x t2x a4x a5x a6x a7x t3x t4x t5x t6x MI SK MU4 WM4 RIC PG SH4 TC TST. unfold kShadowBase, ri_cells in *. unfold AF_free6.RIc, AF_free6.PCB in *.
  destruct PG as (P1 & P2 & P3 & P4 & P5 & P6 & P7). destruct TC as (TC1 & TC2 & TC3 & TC4 & TC5).
  carry_all m3 m4 MU4 WM4.
  unfold AF_free7.rregs.
  (* [comment removed for export] *)
  cstep.                          (* [comment removed for export] *)
  zstepA. if_cases K0; zify_cond K0; [exfalso; revert K0; rewrite ?unsigned_lit by lia; clear -CEILB HH; intros K0; lia|].   (* [comment removed for export] *)
  do 4 zstepA.                    (* [comment removed for export] *)
  replace (nf ≪ 2) with (4 * nf) by (rewrite Z.shiftl_mul_pow2 by lia; change (2^2) with 4; clear; lia).
  replace (h ≪ 2) with (4 * h) by (rewrite Z.shiftl_mul_pow2 by lia; change (2^2) with 4; clear; lia).
  rewrite ?(Z.mod_small (4 * nf)) by (clear -CEILB NF NF4 MFR; lia). rewrite ?(Z.mod_small (4 * h)) by (clear -CEILB HH; lia).
  replace (CA + 80 * c + 4 * h + 16 + 4 * h) with (CA + 80 * c + 16 + 4 * (2 * h)) by (clear; lia).
  replace (CA + 80 * c + 4 * h + 16) with (CA + 80 * c + 16 + 4 * (h + 0)) by (clear; lia).
  replace (SB + c * 4294967296 + 3758096384 + 4 * nf) with (SB + c * 4294967296 + 3758096384 + 4 * (nf + 0)) by (clear; lia).
  eapply (fa_copy_loop P gp tp t3x t4x t5x t6x F fc usp lo CA SB c RI LOC0 LO2 HSB0 HC0 HCA0 HCASB0 HRI PCA (Z.to_nat h) 0) with (mfa := mfa + 262144);
    [clear -CEILB HH; lia| clear -CEILB HH; lia| exact HH| clear -CEILB NF; lia| clear -CEILB NF4 HH; lia| clear -CEILB MFR; lia| exact MI| exact ARR| exact LEN| exact SMALL| exact FAR3| exact FLEN3| |].
  { intros a k Ha Hk. apply PFA; clear -CEILB Ha Hk; lia. }
  clear MI. intros m5 a1y MI MU5 WM5 ARR5 FAR5. unfold AF_free6.PCB, AF_free6.RIc in *.
  carry_all m4 m5 MU5 WM5.
  (* [comment removed for export] *)
  eapply (rta_tail P gp tp s5 s6 s7 s8 s9 s10 s11 t3x t4x t5x t6x F fc usp lo CA SB c p RI LOC0 LO2 SPH SPA HSB0 HC0 HCA0 HCASB0 HP HRI PSTK PDAT PRO PCA PRIR);
    [exact MI| exact SK| unfold AF_free6.drain_frames; split; [exact FRa| split; [exact FRb| exact FRc]]| exact INS4| exact PC| exact HH| exact ARR5| exact LEN| exact CST| exact RIC| clear -CEILB NF NF4 MFR; lia| exact NFR
    | exact FAR5| rewrite cpn_length; exact FLEN3| clear -CEILB MFR; lia| exact G1| exact V1|].
  clear MI SK. intros m6 t0y t1y t2y a0y a1z a2y a3y a4y a5y a6y a7y MI SK MU6 WM6 INS6 PC6 ARR6 CST6 RIC6 FAR6 G16 V16. unfold AF_free6.PCB, AF_free6.RIc in *.
  clear G1 V1. carry_all m5 m6 MU6 WM6.
  replace (Z.to_nat (h + 0)) with (Z.to_nat h) in FAR6 by (clear; lia). replace (Z.to_nat (nf + 0)) with (Z.to_nat nf) in FAR6 by (clear; lia).
  eapply CONT; [exact MI| exact SK| close_statics| exact MUall| exact WMall| exact INS| exact PC6| exact ARR6| exact CST6| exact RIC6| exact FAR6| exact SH4
    | exact (conj P1 (conj P2 (conj P3 (conj P4 (conj P5 (conj P6 P7))))))| exact (conj TC1 (conj TC2 (conj TC3 (conj TC4 TC5))))| exact TST].
Qed.
End RAG.
End RC__1.
(* [comment removed for export] *)
