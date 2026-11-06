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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import RU_ssdc V_Ma6xg.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import ImgU.
From Stdlib Require Import FunctionalExtensionality.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require JunkName.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.split_for_access H segs m A cs kn n ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.JunkName.split_for_access_jn H segs m A cs kn n.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.transport_chunks segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_chunks segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.footprint_after_store segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_footprint_after_store segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_mem_after_store.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.transport_after_call segs m m' MU WM ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_after_call segs m m' MU WM.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.addr_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_addr_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.mlia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_zmlia.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.RL.sec := Ltac2.Init.true.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require StepFast.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sfx_on := Ltac2.Init.true.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.step_core segs R F pc fc rv m ro ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_step_core segs R F pc fc rv m ro.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.zstep ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_zstep.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require LiaSec.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaSec.lia_sec.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Destzna.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_exs PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_exs PO.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_ands PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_ands PO.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require WeqG3qt TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= first [ exact eq_refl | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.WeqG3qt.weq_guard; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac ].
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Stor0fe.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stor0fe.sb_mem_after_store.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Diet8ul.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Diet8ul.dlia_sec.
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition vep_match_entry := 0x1bb80%Z.
Definition VM_FRAME := 80%Z.

(* [comment removed for export] *)
Notation mtab_strings := (mtab_strings rsegs).

Definition vep_match_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (T : Z) (es : list mentry) (inp : list byte) (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (vm_result T es inp) a1 a2 a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ munch [(bv_unsigned sp - VM_FRAME, bv_unsigned sp)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
    /\ stk rsegs m' lo (bv_unsigned sp).


(* [comment removed for export] *)
Lemma land7_of_mod8 : forall x, (0 <= x)%Z -> (x mod 8 = 0)%Z -> (Z.land x 7 = 0)%Z.
Proof. intros x Hx Hm. change 7%Z with (Z.ones 3). rewrite Z.land_ones by lia. change (2^3)%Z with 8%Z. exact Hm. Qed.

Ltac klia' K := first [rewrite Z.mod_small in K by lia | idtac]; lia.

Section Proof.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
            (VEP T : Z) (es : list mentry) (inp : list byte) (lo : Z).

  (* [comment removed for export] *)
  Hypothesis MI : mem_inv rsegs m.
  Hypothesis ST : stk rsegs m lo (bv_unsigned sp).
  Hypothesis LO : (lo + VM_FRAME <= bv_unsigned sp)%Z.
  Hypothesis A0 : a0 = Z_to_bv 64 VEP.
  Hypothesis MATCH : ro_cells rsegs m (VEP + 240) [C8 (Z_to_bv 64 T)].
  Hypothesis T0 : (0 < T)%Z.
  Hypothesis TAB : ro_cells rsegs m T (mtab_cells es).
  Hypothesis WF : mtab_wf es.
  Hypothesis STRS : mtab_strings m es.
  Hypothesis INP : bytes_at rsegs m (bv_unsigned a1) inp.
  Hypothesis A2 : a2 = Z_to_bv 64 (bv_unsigned a1 + Z.of_nat (length inp)).
  Hypothesis SEP_VEP : (VEP + 248 <= bv_unsigned sp - VM_FRAME \/ bv_unsigned sp <= VEP + 240)%Z.
  Hypothesis SEP_TAB : (T + Z.of_nat (cells_size (mtab_cells es)) <= bv_unsigned sp - VM_FRAME \/ bv_unsigned sp <= T)%Z.
  Hypothesis SEP_INP : (bv_unsigned a1 + Z.of_nat (length inp) <= bv_unsigned sp - VM_FRAME \/ bv_unsigned sp <= bv_unsigned a1)%Z.
  Hypothesis SEP_STR : forall i e, nth_error es i = Some e -> me_ptr e <> 0%Z ->
      (me_ptr e + 16 <= bv_unsigned sp - VM_FRAME \/ bv_unsigned sp <= me_ptr e)%Z.
  (* [comment removed for export] *)
  Hypothesis VAL : (0 <= VEP /\ VEP + 312 < 2^47 /\ VEP mod 8 = 0)%Z.
  Hypothesis TAL : (T mod 8 = 0 /\ T + Z.of_nat (cells_size (mtab_cells es)) < 2^47)%Z.
  Hypothesis B0 : (0 < bv_unsigned a1 /\ bv_unsigned a1 + Z.of_nat (length inp) < 2^47)%Z.

  Notation POST := (vep_match_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc T es inp lo m).
  Notation B := (bv_unsigned a1).
  Notation E := (bv_unsigned a1 + Z.of_nat (length inp))%Z.

  Section AfterPrologue.
    Variable m1 : word -> option byte.
    Variable junk8 : list byte.
    Hypothesis MU1 : munch [(bv_unsigned sp - VM_FRAME, bv_unsigned sp)]%Z m m1.
    Hypothesis WM1 : wmono rsegs m m1.
    Hypothesis MI1 : mem_inv rsegs m1.
    Hypothesis ST1 : stk rsegs m1 lo (bv_unsigned sp - VM_FRAME).
    Hypothesis FR1 : rw_cells rsegs m1 (bv_unsigned sp - VM_FRAME)
                       [CB 8 junk8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
    Hypothesis TAB1 : ro_cells rsegs m1 T (mtab_cells es).
    Hypothesis INP1 : bytes_at rsegs m1 B inp.
    Hypothesis TB : (0 <= T /\ T + 16 * Z.of_nat (length es) < 2^47)%Z.
    Hypothesis IB : (0 < B /\ E < 2^47)%Z.

    (* [comment removed for export] *)
    Notation AT pc xra x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x28 x29 x30 x31 :=
      (MS (mkR xra (Z_to_bv 64 (bv_unsigned sp - 80)) gp tp x5 x6 x7
              (Z_to_bv 64 69360) (Z_to_bv 64 E) x10 x11 x12 x13 x14 x15 x16 x17
              a1 x19 x20 (Z_to_bv 64 8) (Z_to_bv 64 (-1)) (Z_to_bv 64 (-17)) s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 pc) fc None m1 (seg_rom rsegs)).

    Ltac klia K := first [rewrite Z.mod_small in K by lia | idtac]; lia.

    (* [comment removed for export] *)
    #[using="FR1 ST1 MI1 WM1 MU1 junk8 LO VEP"] Lemma epilogue : forall xra x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x19 x20 x28 x29 x30 x31,
      evt rsegs POST (AT 0x1bc58 xra x5 x6 x7 (vm_result T es inp) x11 x12 x13 x14 x15 x16 x17 x19 x20 x28 x29 x30 x31).
    Proof.
      intros. unfold VM_FRAME in *.
      pose proof MU1 as MU. pose proof WM1 as WM. pose proof FR1 as FR. pose proof ST1 as STK. clear MI. pose proof MI1 as MI.
      do 10 zstep. zstep.
      replace (bv_unsigned sp - 80 + 80)%Z with (bv_unsigned sp) by lia. rewrite (Z_to_bv_bv_unsigned sp).
      release_frame FR STK (bv_unsigned sp). finish.
    Qed.

    (* [comment removed for export] *)
    #[using="FR1 ST1 MI1 WM1 MU1 junk8 LO VEP"] Lemma ret_vm : forall i xra x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x28 x29 x30 x31,
      vm_find es inp = Some i ->
      evt rsegs POST (AT 0x1bc4c xra x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 (Z_to_bv 64 (T + 16 * Z.of_nat i)) x28 x29 x30 x31).
    Proof.
      intros. unfold VM_FRAME in *.
      pose proof MU1 as MU. pose proof WM1 as WM. pose proof FR1 as FR. pose proof ST1 as STK. clear MI. pose proof MI1 as MI.
      zstep. zstep.
      replace (Z_to_bv 64 (T + 16 * Z.of_nat i)) with (vm_result T es inp) by (unfold vm_result; rewrite H; reflexivity).
      apply epilogue.
    Qed.

    (* [comment removed for export] *)
    #[using="FR1 ST1 MI1 WM1 MU1 junk8 LO VEP"] Lemma ret_null : forall xra x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x28 x29 x30 x31,
      vm_find es inp = None ->
      evt rsegs POST (AT 0x1bc54 xra x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x28 x29 x30 x31).
    Proof.
      intros. unfold VM_FRAME in *.
      pose proof MU1 as MU. pose proof WM1 as WM. pose proof FR1 as FR. pose proof ST1 as STK. clear MI. pose proof MI1 as MI.
      zstep.
      replace (Z_to_bv 64 0) with (vm_result T es inp) by (unfold vm_result; rewrite H; reflexivity).
      apply epilogue.
    Qed.

    (* [comment removed for export] *)
    #[using="MU1 VAL SEP_STR STRS T0 inp T VEP m sp"] Lemma str1 : forall i e, nth_error es i = Some e -> me_ptr e <> 0%Z ->
      exists slack, bytes_at rsegs m1 (me_ptr e) (me_str e ++ Z_to_bv 8 0 :: slack)
        /\ ((- (me_ptr e + Z.of_nat (length (me_str e)) + 1)) mod 8 <= Z.of_nat (length slack))%Z.
    Proof.
      intros i e Hn Hp. destruct (STRS i e Hn Hp) as (slack & Hb & Hpad & Hlen).
      exists slack. split; [|exact Hpad].
      eapply bytes_at_transport; [exact Hb | exact MU1 |].
      cbn [disjoint_from]. split; [|exact I].
      pose proof (SEP_STR i e Hn Hp) as HS. rewrite app_length. cbn [length]. unfold VM_FRAME in *. lia.
    Qed.

    (* [comment removed for export] *)
    Definition OUTER (i : nat) : Prop :=
      forall (e : mentry) xra x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31,
      nth_error es i = Some e -> me_ptr e <> 0%Z -> searched inp es i ->
      evt rsegs POST (AT 0x1bbe4 xra x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17
                         (Z_to_bv 64 (me_ptr e)) (Z_to_bv 64 (T + 16 * Z.of_nat i)) x28 x29 x30 x31).

    (* [comment removed for export] *)
    #[using="IB TB TAB1 FR1 ST1 MI1 WM1 MU1 junk8 VAL WF T0 LO VEP"] Lemma next_entry : forall i e xra x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x28 x29 x30 x31,
      nth_error es i = Some e -> me_ptr e <> 0%Z -> searched inp es i ->
      is_prefixb (me_str e) inp = false -> runs_outb (me_str e) inp = false ->
      OUTER (S i) ->
      evt rsegs POST (AT 0x1bc34 xra x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 (Z_to_bv 64 (T + 16 * Z.of_nat i)) x28 x29 x30 x31).
    Proof.
      intros i e xra x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x28 x29 x30 x31 Hn Hp Hs H1 H2 IH.
      unfold VM_FRAME in *.
      pose proof MU1 as MU. pose proof WM1 as WM. pose proof FR1 as FR. pose proof ST1 as STK. clear MI. pose proof MI1 as MI.
      pose proof TB as TB'.
      destruct (wf_entry es i e WF Hn Hp) as (_ & _ & Hlen).
      destruct (nth_error es (S i)) as [e2|] eqn:He2. 2:{ apply nth_error_None in He2. lia. }
      pose proof (wf_ptr_nonneg es (S i) e2 WF He2) as Hp2.
      pose proof (nth_error_lt _ _ _ He2) as Hi2.
      pose proof (mtab_read_ptr rsegs m1 T es (S i) e2 _ TAB1 He2 eq_refl) as RD2.
      pose proof (searched_next inp es i e Hs Hn Hp H1 H2) as Hs2.
      (* [comment removed for export] *)
      zstep. if_cases KT; zify_cond KT. { exfalso. klia KT. }
      zstep. zstep. zstep.
      (* [comment removed for export] *)
      zstep. if_cases K; zify_cond K.
      - replace (T + 16 * Z.of_nat i + 16)%Z with (T + 16 * Z.of_nat (S i))%Z by lia.
        apply (IH e2); auto; klia K.
      - zstep.
        replace (Z_to_bv 64 (T + 16 * Z.of_nat i + 16)) with (vm_result T es inp).
        2:{ unfold vm_result. rewrite (vm_sentinel inp es (S i) e2 Hs2 He2) by klia K. f_equal. lia. }
        apply epilogue.
    Qed.

    (* [comment removed for export] *)
    #[using="IB TB INP1 TAB1 FR1 ST1 MI1 WM1 MU1 junk8 B0 TAL VAL SEP_STR SEP_INP SEP_TAB SEP_VEP STRS WF T0 LO VEP"] Lemma inner : forall (k : nat) (i j : nat) (e : mentry) (c : byte)
                         xra x5 x6 x7 x10 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31,
      (k = length inp - j)%nat ->
      nth_error es i = Some e -> me_ptr e <> 0%Z -> searched inp es i -> OUTER (S i) ->
      nth_error (me_str e) j = Some c -> (j < length inp)%nat ->
      agree_upto inp (me_str e) j ->
      x10 = Z_to_bv 64 (B + Z.of_nat j) ->
      evt rsegs POST (AT 0x1bc00 xra x5 x6 x7 x10 (Z_to_bv 64 (bv_unsigned c)) x12 x13 x14 x15 x16 x17
                         (Z_to_bv 64 (me_ptr e + Z.of_nat j)) (Z_to_bv 64 (T + 16 * Z.of_nat i)) x28 x29 x30 x31).
    Proof.
      induction k as [|k IH]; intros i j e c xra x5 x6 x7 x10 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 Hk Hn Hp Hs HO Hc Hj Hag ->.
      { exfalso. lia. }
      unfold VM_FRAME in *.
      pose proof MU1 as MU. pose proof WM1 as WM. pose proof FR1 as FR. pose proof ST1 as STK. clear MI. pose proof MI1 as MI.
      pose proof (nth_error_lt _ _ _ Hc) as Hjs.
      pose proof (bv_unsigned_in_range _ c) as Hcr. pose proof TB as TB'. pose proof IB as IB'.
      destruct (wf_entry es i e WF Hn Hp) as (Hslen & Hnonul & Hlen).
      pose proof (wf_ptr_nonneg es i e WF Hn) as Hpr.
      destruct (nth_error inp j) as [d|] eqn:Hd. 2:{ apply nth_error_None in Hd. lia. }
      pose proof (bv_unsigned_in_range _ d) as Hdr.
      pose proof (u8ro_read rsegs m1 B inp (Z.of_nat j) d _ INP1 ltac:(rewrite Nat2Z.id; exact Hd) ltac:(lia) eq_refl) as RD.
      destruct (str1 i e Hn Hp) as (slack & SB & _).
      pose proof (bytes_at_bound _ _ _ _ SB) as SBB. rewrite app_length in SBB. cbn [length] in SBB.
      (* [comment removed for export] *)
      zstep. if_cases KT; zify_cond KT. { exfalso. klia KT. }
      (* [comment removed for export] *)
      zstep. cbv beta.
      zstep. if_cases K; zify_cond K.
      - (* [comment removed for export] *)
        assert (Hcd : c <> d) by (intros ->; apply K; reflexivity).
        destruct (mismatch_at inp (me_str e) j c d Hag Hc Hd Hcd) as [M1 M2].
        zstep. if_cases K2; zify_cond K2. { exfalso. klia K2. }
        eapply next_entry; eauto.
      - assert (Ecd : c = d) by (apply bv_eq; klia K).
        subst d.
        pose proof (agree_step inp (me_str e) j c Hag Hc Hd) as Hag'.
        (* [comment removed for export] *)
        zstep. if_cases KT2; zify_cond KT2. { exfalso. klia KT2. }
        destruct (Nat.eq_dec (S j) (length (me_str e))) as [Hend|Hmore].
        + (* [comment removed for export] *)
          pose proof (u8ro_read rsegs m1 (me_ptr e) (me_str e ++ Z_to_bv 8 0 :: slack) (Z.of_nat (S j)) (Z_to_bv 8 0) _ SB
                        ltac:(rewrite Nat2Z.id, nth_error_app2, Hend, Nat.sub_diag by lia; reflexivity) ltac:(lia) eq_refl) as RD2.
          zstep. cbv beta. zstep. zstep. if_cases K2; zify_cond K2. 2:{ exfalso. apply K2. reflexivity. }
          (* [comment removed for export] *)
          zstep. if_cases K3; zify_cond K3. 2:{ exfalso. apply K3. reflexivity. }
          apply ret_vm. eapply (vm_found inp es); try eassumption. eapply prefix_at_end; eauto.   (* [comment removed for export] *)
        + destruct (nth_error (me_str e) (S j)) as [c2|] eqn:Hc2. 2:{ apply nth_error_None in Hc2. lia. }
          pose proof (bv_unsigned_in_range _ c2) as Hc2r.
          assert (Hc20 : bv_unsigned c2 <> 0%Z).
          { intros Z0. apply Hnonul. replace (Z_to_bv 8 0) with c2 by (apply bv_eq; rewrite Z0; reflexivity). eapply nth_error_In; eauto. }
          pose proof (u8ro_read rsegs m1 (me_ptr e) (me_str e ++ Z_to_bv 8 0 :: slack) (Z.of_nat (S j)) c2 _ SB
                        ltac:(rewrite Nat2Z.id, nth_error_app1 by lia; exact Hc2) ltac:(lia) eq_refl) as RD2.
          zstep. cbv beta. zstep. zstep. if_cases K2; zify_cond K2. { exfalso. klia K2. }
          (* [comment removed for export] *)
          zstep. zstep. if_cases K3; zify_cond K3.
          * replace (me_ptr e + Z.of_nat j + 1)%Z with (me_ptr e + Z.of_nat (S j))%Z by lia.
            apply (IH i (S j) e c2 xra); auto; try lia; try klia K3. f_equal. lia.
          * assert (Hje : (S j = length inp)%nat) by klia K3.
            destruct (runs_out_at inp (me_str e) (S j) Hag' ltac:(lia) Hje) as [M1 M2].
            zstep. zstep. if_cases K4; zify_cond K4. { exfalso. klia K4. }
            zstep. if_cases K5; zify_cond K5. 2:{ exfalso. klia K5. }
            apply ret_null. eapply (vm_ranout inp es); eauto.
    Qed.
  End AfterPrologue.

  #[using="B0 TAL VAL SEP_STR SEP_INP SEP_TAB SEP_VEP A2 INP STRS WF T0 LO VEP a2"] Lemma outer : forall k i (m1 : word -> option byte) junk8,
    munch [(bv_unsigned sp - VM_FRAME, bv_unsigned sp)]%Z m m1 ->
    wmono rsegs m m1 -> mem_inv rsegs m1 ->
    stk rsegs m1 lo (bv_unsigned sp - VM_FRAME) ->
    rw_cells rsegs m1 (bv_unsigned sp - VM_FRAME) [CB 8 junk8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    ro_cells rsegs m1 T (mtab_cells es) ->
    bytes_at rsegs m1 B inp ->
    (0 <= T /\ T + 16 * Z.of_nat (length es) < 2^47)%Z ->
    (0 < B /\ E < 2^47)%Z ->
    (k = length es - i)%nat -> OUTER m1 i.
  Proof.
    induction k as [|k IH]; intros i m1 junk8 MU WM MI1 STK FR TAB1 INP1 TB IB Hk e xra x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 Hn Hp Hs.
    { exfalso. pose proof (nth_error_lt _ _ _ Hn). lia. }
    unfold VM_FRAME in *. clear MI. pose proof MI1 as MI. clear MI1.
    pose proof TB as TB'. pose proof IB as IB'.
    destruct (wf_entry es i e WF Hn Hp) as (Hslen & Hnonul & Hlen).
    pose proof (wf_ptr_nonneg es i e WF Hn) as Hpr.
    destruct (STRS i e Hn Hp) as (slack & SB0 & PAD & SLK).
    assert (SB : bytes_at rsegs m1 (me_ptr e) (me_str e ++ Z_to_bv 8 0 :: slack)).
    { eapply bytes_at_transport; [exact SB0 | exact MU |]. cbn [disjoint_from]. split; [|exact I].
      pose proof (SEP_STR i e Hn Hp) as HS. rewrite app_length. cbn [length]. unfold VM_FRAME in *. lia. }
    clear SB0.
    pose proof (bytes_at_bound _ _ _ _ SB) as SBB. rewrite app_length in SBB. cbn [length] in SBB.
    (* [comment removed for export] *)
    zstep. zstep.
    call (strlen_spec).
    1:{ rewrite unsigned_lit by lia. exact SB. }
    1:{ exact Hnonul. }
    1:{ rewrite unsigned_lit by lia. exact PAD. }
    1:{ exact MI. }
    lazymatch goal with FRx : rw_cells rsegs ?mx _ [CB 8 ?j8; _; _; _; _; _; _; _; _; _] |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      assert (HO : OUTER mx (S i)) by (apply (IH (S i) mx j8); try assumption; lia) end.
    (* [comment removed for export] *)
    zstep. if_cases K; zify_cond K. { exfalso. klia' K. }
    destruct (me_str e) as [|c str'] eqn:Estr. { cbn in Hslen. lia. }
    assert (Hc0 : nth_error (me_str e) 0 = Some c) by (rewrite Estr; reflexivity).
    rewrite <- Estr in *.
    pose proof (bv_unsigned_in_range _ c) as Hcr.
    assert (Hcnz : bv_unsigned c <> 0%Z).
    { intros Z0. apply Hnonul. replace (Z_to_bv 8 0) with c by (apply bv_eq; rewrite Z0; reflexivity). eapply nth_error_In; eauto. }
    lazymatch goal with SBx : bytes_at rsegs ?mx (me_ptr e) _ |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      pose proof (u8ro_read rsegs mx (me_ptr e) (me_str e ++ Z_to_bv 8 0 :: slack) 0 c _ SBx
                    ltac:(cbn [Z.to_nat]; rewrite nth_error_app1 by lia; exact Hc0) ltac:(lia) ltac:(rewrite Z.add_0_r; reflexivity)) as RD0 end.
    (* [comment removed for export] *)
    zstep. cbv beta.
    zstep. if_cases K2; zify_cond K2. { exfalso. klia' K2. }
    (* [comment removed for export] *)
    zstep. if_cases K3; zify_cond K3.
    - assert (Hinp : inp = []) by (destruct inp; [reflexivity| cbn [length] in K3; exfalso; klia' K3]).
      destruct (runs_out_at inp (me_str e) 0 (agree_upto_0 inp (me_str e)) ltac:(lia) ltac:(rewrite Hinp; reflexivity)) as [M1 M2].
      (* [comment removed for export] *)
      zstep. zstep. if_cases K4; zify_cond K4. { exfalso. klia' K4. }
      zstep. if_cases K5; zify_cond K5. 2:{ exfalso. rewrite Hinp in K5. cbn [length] in K5. klia' K5. }
      unshelve (eapply ret_null; eauto); try (unfold VM_FRAME in *; assumption). eapply (vm_ranout inp es); eauto.
    - (* [comment removed for export] *)
      zstep.
      replace (Z_to_bv 64 (me_ptr e)) with (Z_to_bv 64 (me_ptr e + Z.of_nat 0)) by (f_equal; lia).
      lazymatch goal with FRx : rw_cells rsegs ?mx _ [CB 8 ?j8; _; _; _; _; _; _; _; _; _] |- _ =>
        unshelve (eapply (inner mx j8 _ _ _ _ FRx _ _ _ _ (length inp - 0) i 0 e c); eauto; try lia);
          try (unfold VM_FRAME in *; assumption); try (unfold VM_FRAME in *; lia) end.
      + apply (agree_upto_0 inp).
      + rewrite Z.add_0_r. symmetry. apply Z_to_bv_bv_unsigned.
  Qed.
End Proof.

Theorem vep_match_spec :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (VEP T : Z) (es : list mentry) (inp : list byte) (lo : Z),
  mem_inv rsegs m ->
  stk rsegs m lo (bv_unsigned sp) ->
  (lo + VM_FRAME <= bv_unsigned sp)%Z ->
  a0 = Z_to_bv 64 VEP ->
  ro_cells rsegs m (VEP + 240) [C8 (Z_to_bv 64 T)] ->
  (0 < T)%Z ->
  ro_cells rsegs m T (mtab_cells es) ->
  mtab_wf es ->
  mtab_strings m es ->
  bytes_at rsegs m (bv_unsigned a1) inp ->
  a2 = Z_to_bv 64 (bv_unsigned a1 + Z.of_nat (length inp)) ->
  (VEP + 248 <= bv_unsigned sp - VM_FRAME \/ bv_unsigned sp <= VEP + 240)%Z ->
  (T + Z.of_nat (cells_size (mtab_cells es)) <= bv_unsigned sp - VM_FRAME \/ bv_unsigned sp <= T)%Z ->
  (bv_unsigned a1 + Z.of_nat (length inp) <= bv_unsigned sp - VM_FRAME \/ bv_unsigned sp <= bv_unsigned a1)%Z ->
  (forall i e, nth_error es i = Some e -> me_ptr e <> 0%Z ->
      (me_ptr e + 16 <= bv_unsigned sp - VM_FRAME \/ bv_unsigned sp <= me_ptr e)%Z) ->
  (0 <= VEP /\ VEP + 312 < 2^47 /\ VEP mod 8 = 0)%Z ->
  (T mod 8 = 0 /\ T + Z.of_nat (cells_size (mtab_cells es)) < 2^47)%Z ->
  (0 < bv_unsigned a1 /\ bv_unsigned a1 + Z.of_nat (length inp) < 2^47)%Z ->
  evt rsegs (vep_match_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc T es inp lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 vep_match_entry) fc None m (seg_rom rsegs)).
Proof.
  intros until lo. intros MI ST LO A0 MATCH T0 TAB WF STRS INP A2 SEP_VEP SEP_TAB SEP_INP SEP_STR VAL TAL B0.
  rewrite A0, A2.
  pose proof (munch_refl [(bv_unsigned sp - VM_FRAME, bv_unsigned sp)]%Z m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (bytes_at_bound _ _ _ _ INP) as IB.
  pose proof (mtab_cells_size es) as TSZ.
  destruct es as [|e0 es'] eqn:Ees. { cbn in WF. contradiction. }
  rewrite <- Ees in *.
  assert (LEN : length es = S (length es')) by (rewrite Ees; reflexivity).
  assert (He0 : nth_error es 0 = Some e0) by (rewrite Ees; reflexivity).
  pose proof (wf_ptr_nonneg es 0 e0 WF He0) as Hp0.
  pose proof (land7_of_mod8 VEP ltac:(lia) (proj2 (proj2 VAL))) as VAL7.
  pose proof (land7_of_mod8 T ltac:(lia) (proj1 TAL)) as TAL7.
  pose proof (conj INP I) as INP0. pose proof (conj TAB I) as TAB0. pose proof (conj ST I) as ST0.
  unfold VM_FRAME in *. unfold vep_match_entry.
  carve_frame 80%nat ST.
  do 11 zstep.
  (* [comment removed for export] *)
  zstep. zstep. if_cases K; zify_cond K. { exfalso. first [rewrite Z.mod_small in K by lia|idtac]; lia. } clear K.
  (* [comment removed for export] *)
  zstep. zstep. if_cases K; zify_cond K. { exfalso. klia' K. } clear K.
  (* [comment removed for export] *)
  zstep. zstep. if_cases K; zify_cond K. { exfalso. first [rewrite Z.mod_small in K by lia|idtac]; lia. } clear K.
  (* [comment removed for export] *)
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
    pose proof (mtab_read_ptr rsegs mx T es 0 e0 _ TAB He0 eq_refl) as RD0 end.
  replace (T + 16 * Z.of_nat 0)%Z with T in RD0 by lia.
  zstep.
  zstep. if_cases K; zify_cond K.
  - (* [comment removed for export] *)
    assert (Hvm : vm_find es inp = Some 0%nat).
    { apply (vm_sentinel inp es 0 e0); [unfold searched; intros i' e' Hi'; lia | exact He0 | klia' K]. }
    do 13 zstep.
    replace (Z_to_bv 64 T) with (vm_result T es inp) by (unfold vm_result; rewrite Hvm; f_equal; lia).
    release_frame FR ST (bv_unsigned sp). finish.
  - (* [comment removed for export] *)
    do 6 zstep.
    replace (Z_to_bv 64 T) with (Z_to_bv 64 (T + 16 * Z.of_nat 0)) by (f_equal; lia).
    replace (bv_unsigned sp + -80)%Z with (bv_unsigned sp - 80)%Z in * by lia.
    unshelve (eapply (outer _ _ _ _ _ _ a1 a2); eauto); try (unfold VM_FRAME in *; assumption); try (unfold VM_FRAME in *; lia);
      try exact (proj1 INP0); try exact (proj1 TAB0); try exact (proj1 ST0).
    all: try (unfold searched; intros i' e' Hi'; lia).
Qed.
