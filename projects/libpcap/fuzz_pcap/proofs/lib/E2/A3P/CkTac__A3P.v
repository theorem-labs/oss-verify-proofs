(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Lia.
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Arr Bytes ZBridge.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg ABase.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require AsanEmbed.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require ExecF Shadow StepF RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Tac Frame StoreFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Module CkTac.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Arr Bytes ZBridge.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import AImg ABase.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require AsanEmbed.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import ExecF Shadow StepF RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section CANSEC1. Context {rc : runConstT}.

(* [comment removed for export] *)
#[using="Type"] Lemma ck_full_rd : forall (m : word -> option byte) lo hi P,
  unpoisoned m lo hi -> lo <= P -> 8 * (P / 8) + 8 <= hi ->
  ov_read_bytes asegs m (wa (Z.shiftr P 3 + 2147450880)) 1 = Some [Z_to_bv 8 0].
Proof.
  intros m lo hi P U H1 H2. pose proof U as (A & B & _).
  apply (unpoisoned_full_rd asegs m lo hi); [exact U| |].
  - rewrite shad_div. unfold ASHOFF. rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8. Z.div_mod_to_equations. lia.
  - unfold ASHOFF. rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8. lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma ck_part_rd : forall (m : word -> option byte) lo hi P N,
  unpoisoned m lo hi -> lo <= P -> P + N <= hi -> 1 <= N -> P mod 8 + N <= 8 ->
  exists b, ov_read_bytes asegs m (wa (Z.shiftr P 3 + 2147450880)) 1 = Some [b]
            /\ (sval b = 0 \/ (0 < sval b <= 7 /\ P mod 8 + N - 1 < sval b)).
Proof.
  intros m lo hi P N U H1 H2 H3 H4.
  destruct (unpoisoned_check_rd asegs m lo hi P N U H1 H2 H3 H4) as (b & RD & CK).
  exists b. split; [|exact CK]. unfold shad, ASHOFF in RD.
  replace (Z.shiftr P 3 + 2147450880) with (2147450880 + Z.shiftr P 3) by lia. exact RD.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma unpoisoned_write_band : forall (m : word -> option byte) lo hi a bs n,
  unpoisoned m lo hi -> hi <= KEND -> Z.of_nat (length bs) = n -> 0 <= a -> a + n <= 2^64 ->
  (a + n <= 0x7fff7000 \/ 0x10007fff8000 <= a) ->
  unpoisoned (write_to_mem m (wa a) bs) lo hi.
Proof.
  intros m lo hi a bs n U HK Hn Ha Hl HB. pose proof U as (A & B & _).
  destruct (Z_lt_le_dec lo hi) as [LT|GE].
  - apply unpoisoned_write_other; [exact U| exact Ha| lia|].
    rewrite !shad_div. unfold ASHOFF, KEND in *. destruct HB as [HB|HB]; [right | left]; Z.div_mod_to_equations; lia.
  - split; [exact A|]. split; [exact B|]. intros G H0. exfalso. lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma unpoisoned_munch_band : forall W (m m' : word -> option byte) lo hi,
  unpoisoned m lo hi -> hi <= KEND -> munch W m m' ->
  Forall (fun iv => snd iv <= 0x7fff7000 \/ 0x10007fff8000 <= fst iv) W ->
  unpoisoned m' lo hi.
Proof.
  intros W m m' lo hi U HK MU FW. pose proof U as (A & B & _).
  destruct (Z_lt_le_dec lo hi) as [LT|GE].
  - eapply unpoisoned_munch; [exact U| exact MU|].
    assert (S1 : 0x7fff8000 <= shad lo) by (rewrite shad_div; unfold ASHOFF; Z.div_mod_to_equations; lia).
    assert (S2 : shad (hi - 1) + 1 <= 0x10007fff8000) by (rewrite shad_div; unfold ASHOFF, KEND in *; Z.div_mod_to_equations; lia).
    assert (S3 : shad lo <= shad (hi - 1)) by (apply shad_mono; lia).
    clear -FW S1 S2 S3. induction W as [|[wl wh] W IH]; cbn [disjoint_from]; [exact I|].
    apply Forall_cons_iff in FW as [F1 F2]. cbn [fst snd] in F1. split; [lia| apply IH; exact F2].
  - split; [exact A|]. split; [exact B|]. intros G H0. exfalso. lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma ablk_ind : forall lo hi, ablk lo hi ->
  exists b : Z, 0 <= b <= 1 /\ hi <= 0x7fff7000 + b * 0x7FFFFF800000 /\ 0x10007fff8000 * b <= lo /\ 0x603000 <= lo.
Proof.
  intros lo hi H. atop_facts. unfold ablk, AIMG_HI, KLS in *. destruct H as [(A & B)|(A & B)].
  - exists 0. lia.
  - exists 1. lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma ck_acc : forall RNG slo slen P,
  rng RNG slo slen -> slo <= Z.shiftr P 3 + 2147450880 -> Z.shiftr P 3 + 2147450880 + 1 <= slo + slen ->
  acc_in RNG (Z_to_bv 64 (Z.shiftr P 3 + 2147450880), 1%nat).
Proof.
  intros RNG slo slen P H H1 H2.
  apply (rng_acc_litZ' RNG slo slen _ 1%nat 1 H (@eq_refl Z 1) (@eq_refl bool true)). lia.
Qed.

End CANSEC1.

(* [comment removed for export] *)
Fixpoint ck_post (rs : list Z) (k : bvmap 5 word -> Prop) (R : bvmap 5 word) : Prop :=
  match rs with
  | [] => k R
  | r :: rs' => exists y : word, ck_post rs' k (bvmap_set (Z_to_bv 5 r) y R)
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Ltac band_ind H b :=
  let b0 := fresh b "r" in let b1 := fresh b "hi" in let b2 := fresh b "lo" in let b3 := fresh b "img" in
  destruct (ablk_ind _ _ H) as (b & b0 & b1 & b2 & b3); clear H.

(* [comment removed for export] *)
Ltac ck_lia := first [ lia | Z.div_mod_to_equations; lia ].

(* [comment removed for export] *)
Ltac ck_P k :=
  lazymatch goal with
  | |- evtF ?segs _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) =>
    let fw := eval vm_compute in (fetch_word segs (Z_to_bv 64 pc)) in
    lazymatch fw with
    | Some ?w =>
      let d := eval vm_compute in (decode_any w) in
      lazymatch d with
      | Some (ShiftImm ALU_SRL _ ?rs1 _, _) =>
          let n := eval vm_compute in (bv_unsigned rs1) in
          let v := getreg n in
          lazymatch v with
          | Z_to_bv 64 ?P => k P
          | _ => fail "ck: register" n "holds" v
          end
      | _ => fail "ck: no srli at pc" pc
      end
    | None => fail "ck: no instruction at" pc
    end
  end.

(* [comment removed for export] *)
Ltac sh_lia :=
  rewrite ?shad_div, ?nshad_div; unfold AsanEmbed.shlen, ASHOFF; rewrite ?Z.shiftr_div_pow2 by lia; change (2^3) with 8;
  first [ lia | Z.div_mod_to_equations; lia ].

(* [comment removed for export] *)
Ltac ck_fp_at lo P :=
  lazymatch goal with
  | |- evtF _ ?RNG _ _ =>
    let ACC := fresh "ACCsh" in
    first [ match goal with
            | H : rng RNG (shad lo) ?len |- _ => pose proof (ck_acc RNG (shad lo) len P H ltac:(sh_lia) ltac:(sh_lia)) as ACC
            end
          | match goal with
            | H : rng RNG ?slo ?len |- _ => pose proof (ck_acc RNG slo len P H ltac:(sh_lia) ltac:(sh_lia)) as ACC
            end
          | fail 1 "ck: no [rng] hypothesis covers the shadow byte of" P ]
  end.

(* [comment removed for export] *)
Ltac ck_clear :=
  repeat match goal with
  | H : ov_read_bytes _ _ (wa (Z.shiftr _ 3 + 2147450880)) 1 = Some _ |- _ => clear H
  | H : acc_in _ (Z_to_bv 64 (Z.shiftr _ 3 + 2147450880), 1%nat) |- _ => clear H
  end.

(* [comment removed for export] *)
Ltac ck0_at UNP P :=
  ck_clear;
  lazymatch goal with
  | |- evtF _ _ _ (MS _ _ _ _ _ ?m _) =>
    lazymatch type of UNP with
    | unpoisoned m ?lo ?hi =>
        let RD := fresh "RDsh" in
        pose proof (ck_full_rd m lo hi P UNP ltac:(ck_lia) ltac:(ck_lia)) as RD;
        ck_fp_at lo P
    | unpoisoned ?m' _ _ => fail "ck0: the shadow fact" UNP "is about memory" m' "but the state's memory is" m
    end
  end.
Ltac ck0 UNP := ck_P ltac:(fun P => ck0_at UNP P).

(* [comment removed for export] *)
Ltac ck_steps n :=
  lazymatch n with
  | O => idtac
  | S ?n' => lazymatch goal with
             | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 _) _ _ _ _) => zstep; ck_steps n'
             | _ => idtac
             end
  end.
(* [comment removed for export] *)
Ltac ck_go := ck_steps 8%nat; first [ if_false | if_true ].

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Ltac ck_zify K :=
  lazymatch type of K with
  | context [bv_lts] =>
      unfold bv_lts in K; rewrite ?land7_mod in K;
      rewrite ?signed_lit_small64 in K by (first [ lia | Z.div_mod_to_equations; lia ]);
      zify_bool K
  | _ => zify_cond K
  end.

(* [comment removed for export] *)
Ltac ck_arm OK n :=
  lazymatch n with
  | O => fail "ck_join: step budget exhausted before reaching the join point" OK
  | S ?n' =>
    lazymatch goal with
    | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 OK) _ _ _ _) =>
        apply evtF_done; cbn [ck_post]; repeat eexists; simp_regs;
        first [ reflexivity | fail 1 "ck_join: a register outside the clobber list changed before" OK ]
    | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 _) _ _ _ _) => zstep; rewrite ?sxb_sval; ck_arm OK n'
    | |- evtF _ _ _ (MS _ _ (if _ then _ else _) _ _ _ _) =>
        let K := fresh "Kck" in
        if_cases K; ck_zify K; first [ exfalso; ck_lia | ck_arm OK n' ]
    end
  end.

(* [comment removed for export] *)
Ltac ck_join_at UNP P N OK RS :=
  ck_clear; cbv beta delta [mkR];
  lazymatch goal with
  | |- evtF ?segs ?RNG ?Q (MS ?R ?F ?pc ?fc ?rv ?m ?ro) =>
    lazymatch type of UNP with
    | unpoisoned m ?lo ?hi =>
      let b := fresh "shb" in let RD := fresh "RDsh" in let CK := fresh "CKsh" in let SR := fresh "SRsh" in
      destruct (ck_part_rd m lo hi P N UNP ltac:(ck_lia) ltac:(ck_lia) ltac:(lia) ltac:(ck_lia)) as (b & RD & CK);
      ck_fp_at lo P;
      pose proof (sval_range b) as SR;
      eapply (evtF_cut segs RNG (fun ms' => ck_post RS (fun R' => ms' = MS R' F (Z_to_bv 64 OK) fc rv m ro) R));
      [ ck_arm OK 16%nat
      | let ms' := fresh "ms'" in let H := fresh "Hck" in
        intros ms' H; cbn [ck_post] in H; destruct_exs H; subst ms'; simp_regs; clear RD CK SR; ck_clear; try clear b ]
    | unpoisoned ?m' _ _ => fail "ck_join: the shadow fact" UNP "is about memory" m' "but the state's memory is" m
    end
  end.
Ltac ck_join UNP N OK RS := ck_P ltac:(fun P => ck_join_at UNP P N OK RS).

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac unp_store_d0 m a bs n Hn Ha Hl :=
  repeat match goal with
  | H : unpoisoned m ?lo ?hi |- _ =>
      first [ apply (unpoisoned_write_band m lo hi a bs n) in H;
              [ | unfold KEND; lia | exact Hn | exact Ha | exact Hl | lia ]
            | idtac "note: dropping shadow fact (store not provably outside the shadow band):" H; clear H ]
  end.
(* [comment removed for export] *)
Ltac unp_store m a bs n Hn Ha Hl :=
  repeat match goal with
  | H : unpoisoned m ?lo ?hi |- _ =>
      first [ d_target asegs (write_to_mem m (wa a) bs) a ltac:(fun A SZ kz =>
                d_true constr:(dchk kz n SZ);
                d_fact (hi <= KEND)%Z ltac:(unfold KEND; lia)
                  ltac:(fun HK => d_fact (A + SZ <= 0x7fff7000 \/ 0x10007fff8000 <= A)%Z ltac:(lia)
                     ltac:(fun HBD => apply (unpoisoned_write_band m lo hi a bs n) in H;
                                      [ | exact (dfact_out _ HK) | exact Hn | exact Ha | exact Hl
                                        | exact (d_band_sub A SZ kz n 0x7fff7000%Z 0x10007fff8000%Z HBD (@eq_refl bool true)) ])
                     ltac:(fun _ => fail))
                  ltac:(fun _ => fail))
            | apply (unpoisoned_write_band m lo hi a bs n) in H;
              [ | unfold KEND; lia | exact Hn | exact Ha | exact Hl | lia ]
            | idtac "note: dropping shadow fact (store not provably outside the shadow band):" H; clear H ]
  end.
Ltac unp_call W m m' MU :=
  repeat match goal with
  | H : unpoisoned m ?lo ?hi |- _ =>
      first [ apply (unpoisoned_munch_band W m m' lo hi) in H;
              [ | unfold KEND; lia | exact MU
                | repeat (apply Forall_cons; [cbn [fst snd]; lia|]); apply Forall_nil ]
            | idtac "note: dropping shadow fact (callee footprint not provably outside the shadow band):" H; clear H ]
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac ck UNP N OK RS := first [ ck0 UNP; ck_go | ck_join UNP N OK RS ].

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Bytes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ZBridge.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.
(* [comment removed for export] *)
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ExecF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.Shadow OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.StepF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw. Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section CANSEC1. Context {rc : runConstT}.

(* [comment removed for export] *)
#[using="Type"] Lemma ck_full_rd : forall (m : word -> option byte) lo hi P,
  unpoisoned m lo hi -> lo <= P -> 8 * (P / 8) + 8 <= hi ->
  ov_read_bytes asegs m (wa (Z.shiftr P 3 + 2147450880)) 1 = Some [Z_to_bv 8 0].
Proof.
  intros m lo hi P U H1 H2. pose proof U as (A & B & _).
  apply (unpoisoned_full_rd asegs m lo hi); [exact U| |].
  - rewrite shad_div. unfold ASHOFF. rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8. Z.div_mod_to_equations. lia.
  - unfold ASHOFF. rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8. lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma ck_part_rd : forall (m : word -> option byte) lo hi P N,
  unpoisoned m lo hi -> lo <= P -> P + N <= hi -> 1 <= N -> P mod 8 + N <= 8 ->
  exists b, ov_read_bytes asegs m (wa (Z.shiftr P 3 + 2147450880)) 1 = Some [b]
            /\ (sval b = 0 \/ (0 < sval b <= 7 /\ P mod 8 + N - 1 < sval b)).
Proof.
  intros m lo hi P N U H1 H2 H3 H4.
  destruct (unpoisoned_check_rd asegs m lo hi P N U H1 H2 H3 H4) as (b & RD & CK).
  exists b. split; [|exact CK]. unfold shad, ASHOFF in RD.
  replace (Z.shiftr P 3 + 2147450880) with (2147450880 + Z.shiftr P 3) by lia. exact RD.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma unpoisoned_write_band : forall (m : word -> option byte) lo hi a bs n,
  unpoisoned m lo hi -> hi <= KEND -> Z.of_nat (length bs) = n -> 0 <= a -> a + n <= 2^64 ->
  (a + n <= 0x7fff7000 \/ 0x10007fff8000 <= a) ->
  unpoisoned (write_to_mem m (wa a) bs) lo hi.
Proof.
  intros m lo hi a bs n U HK Hn Ha Hl HB. pose proof U as (A & B & _).
  destruct (Z_lt_le_dec lo hi) as [LT|GE].
  - apply unpoisoned_write_other; [exact U| exact Ha| lia|].
    rewrite !shad_div. unfold ASHOFF, KEND in *. destruct HB as [HB|HB]; [right | left]; Z.div_mod_to_equations; lia.
  - split; [exact A|]. split; [exact B|]. intros G H0. exfalso. lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma unpoisoned_munch_band : forall W (m m' : word -> option byte) lo hi,
  unpoisoned m lo hi -> hi <= KEND -> munch W m m' ->
  Forall (fun iv => snd iv <= 0x7fff7000 \/ 0x10007fff8000 <= fst iv) W ->
  unpoisoned m' lo hi.
Proof.
  intros W m m' lo hi U HK MU FW. pose proof U as (A & B & _).
  destruct (Z_lt_le_dec lo hi) as [LT|GE].
  - eapply unpoisoned_munch; [exact U| exact MU|].
    assert (S1 : 0x7fff8000 <= shad lo) by (rewrite shad_div; unfold ASHOFF; Z.div_mod_to_equations; lia).
    assert (S2 : shad (hi - 1) + 1 <= 0x10007fff8000) by (rewrite shad_div; unfold ASHOFF, KEND in *; Z.div_mod_to_equations; lia).
    assert (S3 : shad lo <= shad (hi - 1)) by (apply shad_mono; lia).
    clear -FW S1 S2 S3. induction W as [|[wl wh] W IH]; cbn [disjoint_from]; [exact I|].
    apply Forall_cons_iff in FW as [F1 F2]. cbn [fst snd] in F1. split; [lia| apply IH; exact F2].
  - split; [exact A|]. split; [exact B|]. intros G H0. exfalso. lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma ablk_ind : forall lo hi, ablk lo hi ->
  exists b : Z, 0 <= b <= 1 /\ hi <= 0x7fff7000 + b * 0x7FFFFF800000 /\ 0x10007fff8000 * b <= lo /\ 0x604000 <= lo.
Proof.
  intros lo hi H. atop_facts. unfold ablk, AIMG_HI, KLS in *. destruct H as [(A & B)|(A & B)].
  - exists 0. lia.
  - exists 1. lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma ck_acc : forall RNG slo slen P,
  rng RNG slo slen -> slo <= Z.shiftr P 3 + 2147450880 -> Z.shiftr P 3 + 2147450880 + 1 <= slo + slen ->
  acc_in RNG (Z_to_bv 64 (Z.shiftr P 3 + 2147450880), 1%nat).
Proof.
  intros RNG slo slen P H H1 H2.
  apply (rng_acc_litZ' RNG slo slen _ 1%nat 1 H (@eq_refl Z 1) (@eq_refl bool true)). lia.
Qed.

End CANSEC1.

(* [comment removed for export] *)
Fixpoint ck_post (rs : list Z) (k : bvmap 5 word -> Prop) (R : bvmap 5 word) : Prop :=
  match rs with
  | [] => k R
  | r :: rs' => exists y : word, ck_post rs' k (bvmap_set (Z_to_bv 5 r) y R)
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Ltac band_ind H b :=
  let b0 := fresh b "r" in let b1 := fresh b "hi" in let b2 := fresh b "lo" in let b3 := fresh b "img" in
  destruct (ablk_ind _ _ H) as (b & b0 & b1 & b2 & b3); clear H.

(* [comment removed for export] *)
Ltac ck_lia := first [ lia | Z.div_mod_to_equations; lia ].

(* [comment removed for export] *)
Ltac ck_P k :=
  lazymatch goal with
  | |- evtF ?segs _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) =>
    let fw := eval vm_compute in (fetch_word segs (Z_to_bv 64 pc)) in
    lazymatch fw with
    | Some ?w =>
      let d := eval vm_compute in (decode_any w) in
      lazymatch d with
      | Some (ShiftImm ALU_SRL _ ?rs1 _, _) =>
          let n := eval vm_compute in (bv_unsigned rs1) in
          let v := getreg n in
          lazymatch v with
          | Z_to_bv 64 ?P => k P
          | _ => fail "ck: register" n "holds" v
          end
      | _ => fail "ck: no srli at pc" pc
      end
    | None => fail "ck: no instruction at" pc
    end
  end.

(* [comment removed for export] *)
Ltac sh_lia :=
  rewrite ?shad_div, ?nshad_div; unfold AsanEmbed.shlen, ASHOFF; rewrite ?Z.shiftr_div_pow2 by lia; change (2^3) with 8;
  first [ lia | Z.div_mod_to_equations; lia ].

(* [comment removed for export] *)
Ltac ck_fp_at lo P :=
  lazymatch goal with
  | |- evtF _ ?RNG _ _ =>
    let ACC := fresh "ACCsh" in
    first [ match goal with
            | H : rng RNG (shad lo) ?len |- _ => pose proof (ck_acc RNG (shad lo) len P H ltac:(sh_lia) ltac:(sh_lia)) as ACC
            end
          | match goal with
            | H : rng RNG ?slo ?len |- _ => pose proof (ck_acc RNG slo len P H ltac:(sh_lia) ltac:(sh_lia)) as ACC
            end
          | fail 1 "ck: no [rng] hypothesis covers the shadow byte of" P ]
  end.

(* [comment removed for export] *)
Ltac ck_clear :=
  repeat match goal with
  | H : ov_read_bytes _ _ (wa (Z.shiftr _ 3 + 2147450880)) 1 = Some _ |- _ => clear H
  | H : acc_in _ (Z_to_bv 64 (Z.shiftr _ 3 + 2147450880), 1%nat) |- _ => clear H
  end.

(* [comment removed for export] *)
Ltac ck0_at UNP P :=
  ck_clear;
  lazymatch goal with
  | |- evtF _ _ _ (MS _ _ _ _ _ ?m _) =>
    lazymatch type of UNP with
    | unpoisoned m ?lo ?hi =>
        let RD := fresh "RDsh" in
        pose proof (ck_full_rd m lo hi P UNP ltac:(ck_lia) ltac:(ck_lia)) as RD;
        ck_fp_at lo P
    | unpoisoned ?m' _ _ => fail "ck0: the shadow fact" UNP "is about memory" m' "but the state's memory is" m
    end
  end.
Ltac ck0 UNP := ck_P ltac:(fun P => ck0_at UNP P).

(* [comment removed for export] *)
Ltac ck_steps n :=
  lazymatch n with
  | O => idtac
  | S ?n' => lazymatch goal with
             | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 _) _ _ _ _) => zstep; ck_steps n'
             | _ => idtac
             end
  end.
(* [comment removed for export] *)
Ltac ck_go := ck_steps 8%nat; first [ if_false | if_true ].

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Ltac ck_zify K :=
  lazymatch type of K with
  | context [bv_lts] =>
      unfold bv_lts in K; rewrite ?land7_mod in K;
      rewrite ?signed_lit_small64 in K by (first [ lia | Z.div_mod_to_equations; lia ]);
      zify_bool K
  | _ => zify_cond K
  end.

(* [comment removed for export] *)
Ltac ck_arm OK n :=
  lazymatch n with
  | O => fail "ck_join: step budget exhausted before reaching the join point" OK
  | S ?n' =>
    lazymatch goal with
    | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 OK) _ _ _ _) =>
        apply evtF_done; cbn [ck_post]; repeat eexists; simp_regs;
        first [ reflexivity | fail 1 "ck_join: a register outside the clobber list changed before" OK ]
    | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 _) _ _ _ _) => zstep; rewrite ?sxb_sval; ck_arm OK n'
    | |- evtF _ _ _ (MS _ _ (if _ then _ else _) _ _ _ _) =>
        let K := fresh "Kck" in
        if_cases K; ck_zify K; first [ exfalso; ck_lia | ck_arm OK n' ]
    end
  end.

(* [comment removed for export] *)
Ltac ck_join_at UNP P N OK RS :=
  ck_clear; cbv beta delta [mkR];
  lazymatch goal with
  | |- evtF ?segs ?RNG ?Q (MS ?R ?F ?pc ?fc ?rv ?m ?ro) =>
    lazymatch type of UNP with
    | unpoisoned m ?lo ?hi =>
      let b := fresh "shb" in let RD := fresh "RDsh" in let CK := fresh "CKsh" in let SR := fresh "SRsh" in
      destruct (ck_part_rd m lo hi P N UNP ltac:(ck_lia) ltac:(ck_lia) ltac:(lia) ltac:(ck_lia)) as (b & RD & CK);
      ck_fp_at lo P;
      pose proof (sval_range b) as SR;
      eapply (evtF_cut segs RNG (fun ms' => ck_post RS (fun R' => ms' = MS R' F (Z_to_bv 64 OK) fc rv m ro) R));
      [ ck_arm OK 16%nat
      | let ms' := fresh "ms'" in let H := fresh "Hck" in
        intros ms' H; cbn [ck_post] in H; destruct_exs H; subst ms'; simp_regs; clear RD CK SR; ck_clear; try clear b ]
    | unpoisoned ?m' _ _ => fail "ck_join: the shadow fact" UNP "is about memory" m' "but the state's memory is" m
    end
  end.
Ltac ck_join UNP N OK RS := ck_P ltac:(fun P => ck_join_at UNP P N OK RS).

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac unp_store_d0 m a bs n Hn Ha Hl :=
  repeat match goal with
  | H : unpoisoned m ?lo ?hi |- _ =>
      first [ apply (unpoisoned_write_band m lo hi a bs n) in H;
              [ | unfold KEND; lia | exact Hn | exact Ha | exact Hl | lia ]
            | idtac "note: dropping shadow fact (store not provably outside the shadow band):" H; clear H ]
  end.
(* [comment removed for export] *)
Ltac unp_store m a bs n Hn Ha Hl :=
  repeat match goal with
  | H : unpoisoned m ?lo ?hi |- _ =>
      first [ d_target asegs (write_to_mem m (wa a) bs) a ltac:(fun A SZ kz =>
                d_true constr:(dchk kz n SZ);
                d_fact (hi <= KEND)%Z ltac:(unfold KEND; lia)
                  ltac:(fun HK => d_fact (A + SZ <= 0x7fff7000 \/ 0x10007fff8000 <= A)%Z ltac:(lia)
                     ltac:(fun HBD => apply (unpoisoned_write_band m lo hi a bs n) in H;
                                      [ | exact (dfact_out _ HK) | exact Hn | exact Ha | exact Hl
                                        | exact (d_band_sub A SZ kz n 0x7fff7000%Z 0x10007fff8000%Z HBD (@eq_refl bool true)) ])
                     ltac:(fun _ => fail))
                  ltac:(fun _ => fail))
            | apply (unpoisoned_write_band m lo hi a bs n) in H;
              [ | unfold KEND; lia | exact Hn | exact Ha | exact Hl | lia ]
            | idtac "note: dropping shadow fact (store not provably outside the shadow band):" H; clear H ]
  end.
Ltac unp_call W m m' MU :=
  repeat match goal with
  | H : unpoisoned m ?lo ?hi |- _ =>
      first [ apply (unpoisoned_munch_band W m m' lo hi) in H;
              [ | unfold KEND; lia | exact MU
                | repeat (apply Forall_cons; [cbn [fst snd]; lia|]); apply Forall_nil ]
            | idtac "note: dropping shadow fact (callee footprint not provably outside the shadow band):" H; clear H ]
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac ck UNP N OK RS := first [ ck0 UNP; ck_go | ck_join UNP N OK RS ].
End TwB.
End CkTac.

(* [comment removed for export] *)
Module PerfKit.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr Bytes ZBridge Frame StoreFast.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import ExecF Shadow StepF RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import AImg ABase.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.CkTac.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition hidc (P : Prop) : Prop := P.

Ltac in_zlist A l :=
  lazymatch l with
  | @nil _ => fail
  | @cons _ ?x ?l' => first [ constr_eq A x | in_zlist A l' ]
  end.

(* [comment removed for export] *)
Ltac hide_chunks_of m keep :=
  repeat match goal with
  | H : rw_cells asegs m ?A ?cs |- _ => tryif in_zlist A keep then fail else change (hidc (rw_cells asegs m A cs)) in H
  | H : ro_cells asegs m ?A ?cs |- _ => tryif in_zlist A keep then fail else change (hidc (ro_cells asegs m A cs)) in H
  | H : bytes_at asegs m ?A ?bs |- _ => tryif in_zlist A keep then fail else change (hidc (bytes_at asegs m A bs)) in H
  | H : unpoisoned m ?lo ?hi |- _ => change (hidc (unpoisoned m lo hi)) in H
  end.

Tactic Notation "burst_begin" constr(W) constr(keep) ident(MUb) ident(WMb) :=
  lazymatch goal with
  | |- evtF _ _ _ (MS _ _ _ _ _ ?m _) =>
      pose proof (munch_refl W m) as MUb; pose proof (wmono_refl asegs m) as WMb;
      hide_chunks_of m keep
  end.

(* [comment removed for export] *)
Ltac burst_end MUb WMb :=
  lazymatch type of MUb with
  | munch ?W ?m0 ?m1 =>
    repeat match goal with
    | H : hidc (rw_cells asegs m0 ?A ?cs) |- _ =>
        unfold hidc in H;
        first [ apply (rw_cells_transport asegs W m0 m1 A cs) in H; [ | exact MUb | exact WMb | disjoint_goal ]
              | idtac "note: burst_end DROPS (not provably apart from the burst windows):" H; clear H ]
    | H : hidc (ro_cells asegs m0 ?A ?cs) |- _ =>
        unfold hidc in H;
        first [ apply (ro_cells_transport asegs W m0 m1 A cs) in H; [ | exact MUb | disjoint_goal ]
              | idtac "note: burst_end DROPS (not provably apart from the burst windows):" H; clear H ]
    | H : hidc (bytes_at asegs m0 ?A ?bs) |- _ =>
        unfold hidc in H;
        first [ apply (bytes_at_transport asegs W m0 m1 A bs) in H; [ | exact MUb | disjoint_goal ]
              | idtac "note: burst_end DROPS (not provably apart from the burst windows):" H; clear H ]
    | H : hidc (unpoisoned m0 ?lo ?hi) |- _ =>
        unfold hidc in H;
        first [ apply (unpoisoned_munch_band W m0 m1 lo hi) in H;
                [ | unfold KEND; lia | exact MUb | repeat (apply Forall_cons; [cbn [fst snd]; lia|]); apply Forall_nil ]
              | idtac "note: burst_end DROPS a shadow fact (burst windows not provably outside the shadow band):" H; clear H ]
    end;
    clear MUb WMb
  end.

(* [comment removed for export] *)
Ltac rng_sp_window RSTK sp NAME :=
  lazymatch type of RSTK with
  | rng ?RNG ?lo _ => assert (NAME : rng RNG lo (bv_unsigned sp - lo)) by (eapply rng_sub'; [exact RSTK | lia])
  end.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Bytes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ZBridge OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Frame OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.StoreFast.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ExecF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.Shadow OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.StepF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.CkTac.TwB. Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition hidc (P : Prop) : Prop := P.

Ltac in_zlist A l :=
  lazymatch l with
  | @nil _ => fail
  | @cons _ ?x ?l' => first [ constr_eq A x | in_zlist A l' ]
  end.

(* [comment removed for export] *)
Ltac hide_chunks_of m keep :=
  repeat match goal with
  | H : rw_cells asegs m ?A ?cs |- _ => tryif in_zlist A keep then fail else change (hidc (rw_cells asegs m A cs)) in H
  | H : ro_cells asegs m ?A ?cs |- _ => tryif in_zlist A keep then fail else change (hidc (ro_cells asegs m A cs)) in H
  | H : bytes_at asegs m ?A ?bs |- _ => tryif in_zlist A keep then fail else change (hidc (bytes_at asegs m A bs)) in H
  | H : unpoisoned m ?lo ?hi |- _ => change (hidc (unpoisoned m lo hi)) in H
  end.

Tactic Notation "burst_begin" constr(W) constr(keep) ident(MUb) ident(WMb) :=
  lazymatch goal with
  | |- evtF _ _ _ (MS _ _ _ _ _ ?m _) =>
      pose proof (munch_refl W m) as MUb; pose proof (wmono_refl asegs m) as WMb;
      hide_chunks_of m keep
  end.

(* [comment removed for export] *)
Ltac burst_end MUb WMb :=
  lazymatch type of MUb with
  | munch ?W ?m0 ?m1 =>
    repeat match goal with
    | H : hidc (rw_cells asegs m0 ?A ?cs) |- _ =>
        unfold hidc in H;
        first [ apply (rw_cells_transport asegs W m0 m1 A cs) in H; [ | exact MUb | exact WMb | disjoint_goal ]
              | idtac "note: burst_end DROPS (not provably apart from the burst windows):" H; clear H ]
    | H : hidc (ro_cells asegs m0 ?A ?cs) |- _ =>
        unfold hidc in H;
        first [ apply (ro_cells_transport asegs W m0 m1 A cs) in H; [ | exact MUb | disjoint_goal ]
              | idtac "note: burst_end DROPS (not provably apart from the burst windows):" H; clear H ]
    | H : hidc (bytes_at asegs m0 ?A ?bs) |- _ =>
        unfold hidc in H;
        first [ apply (bytes_at_transport asegs W m0 m1 A bs) in H; [ | exact MUb | disjoint_goal ]
              | idtac "note: burst_end DROPS (not provably apart from the burst windows):" H; clear H ]
    | H : hidc (unpoisoned m0 ?lo ?hi) |- _ =>
        unfold hidc in H;
        first [ apply (unpoisoned_munch_band W m0 m1 lo hi) in H;
                [ | unfold KEND; lia | exact MUb | repeat (apply Forall_cons; [cbn [fst snd]; lia|]); apply Forall_nil ]
              | idtac "note: burst_end DROPS a shadow fact (burst windows not provably outside the shadow band):" H; clear H ]
    end;
    clear MUb WMb
  end.

(* [comment removed for export] *)
Ltac rng_sp_window RSTK sp NAME :=
  lazymatch type of RSTK with
  | rng ?RNG ?lo _ => assert (NAME : rng RNG lo (bv_unsigned sp - lo)) by (eapply rng_sub'; [exact RSTK | lia])
  end.
End TwB.
End PerfKit.
