(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import MState.
From LinuxProcessSemantics.LinuxProcessSem Require Import RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import PropExec Shape.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.BB Require Import Amb SymExec2 SymExec2Sound SymRun SymDrive SymDriveX.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import ALazy SRz AEvtS AEvtA Restrict RestrictLib SymDriveA SymDriveAX.
Import ListNotations.
Import SX2. Import SX2S.
Open Scope Z_scope.

Section KnDS.
  Variable D : word -> bool.
  Variable E : env.
  Variable sp0 : word.
  Variables FLO FHI : Z.            (* [comment removed for export] *)
  Variable LITS : list (Z * Z).     (* [comment removed for export] *)
  Hypothesis Hev0 : ev E 0 = sp0.
  Hypothesis Hframe : forall lo hi, bv_unsigned sp0 + FLO <= lo -> hi <= bv_unsigned sp0 + FHI -> DcovZ D lo hi.
  Hypothesis Hlits : Forall (fun iv => DcovZ D (fst iv) (snd iv)) LITS.

  Definition inb_litsS (lo hi : Z) : bool := List.existsb (fun iv => (fst iv <=? lo) && (hi <=? snd iv)) LITS.

  Definition chk_rangeS (a : saddr) (len : Z) : bool :=
    match a_base a with
    | ELit z => (z =? 0) && inb_litsS (a_off a) (a_off a + len)
    | EVar O => (FLO <=? a_off a) && (a_off a + len <=? FHI)
    | _ => false
    end.

  Definition chk_entryS (K : kentry) : bool :=
    match K with
    | KWord a w _ => chk_rangeS a (Z.of_nat w)
    | KZero a (ELit n) => (0 <=? n) && (n <? 2 ^ 64) && chk_rangeS a n
    | KBlob a (ELit n) _ => (0 <=? n) && (n <? 2 ^ 64) && chk_rangeS a n
    | KImg lo hi => inb_litsS lo hi
    | KWr a n => chk_rangeS a n
    | KAlign _ _ | KRange _ _ _ | KDisj _ _ _ _ => true
    | _ => false
    end.

  Definition knd_residualS (kn : list kentry) : list kentry := List.filter (fun K => negb (chk_entryS K)) kn.

  Lemma inb_litsS_soundS : forall lo hi, inb_litsS lo hi = true -> DcovZ D lo hi.
  Proof.
    intros lo hi H. unfold inb_litsS in H. apply List.existsb_exists in H. destruct H as ([a b] & Hin & Hab). cbn [fst snd] in Hab.
    apply andb_prop in Hab. destruct Hab as [Ha Hb]. apply Z.leb_le in Ha. apply Z.leb_le in Hb.
    rewrite Forall_forall in Hlits. specialize (Hlits (a, b) Hin). cbn [fst snd] in Hlits.
    intros z Hz. apply Hlits. lia.
  Qed.

  Lemma chk_rangeS_soundS : forall a len, chk_rangeS a len = true -> DcovZ D (estart E a) (estart E a + len).
  Proof.
    intros [b off] len H. unfold chk_rangeS in H. cbn [a_base a_off] in H. unfold estart. cbn [a_base a_off].
    destruct b; try discriminate.
    - apply andb_prop in H. destruct H as [Hz Hin]. apply Z.eqb_eq in Hz. subst.
      cbn [edenot]. rewrite (unsigned_lit 0) by lia. rewrite Z.add_0_l. apply inb_litsS_soundS. exact Hin.
    - destruct n; try discriminate. apply andb_prop in H. destruct H as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
      cbn [edenot]. rewrite Hev0. apply Hframe; lia.
  Qed.

  Lemma chk_entryS_soundS : forall K, chk_entryS K = true -> kentry_inD D E K.
  Proof.
    intros K H. destruct K; cbn [chk_entryS kentry_inD] in *; try exact I; try discriminate.
    - apply chk_rangeS_soundS. exact H.
    - destruct n; try discriminate. apply andb_prop in H. destruct H as [H12 H3]. apply andb_prop in H12. destruct H12 as [H1 H2].
      apply Z.leb_le in H1. apply Z.ltb_lt in H2. unfold elenZ. cbn [edenot]. rewrite unsigned_lit by lia. apply chk_rangeS_soundS. exact H3.
    - destruct n; try discriminate. apply andb_prop in H. destruct H as [H12 H3]. apply andb_prop in H12. destruct H12 as [H1 H2].
      apply Z.leb_le in H1. apply Z.ltb_lt in H2. unfold elenZ. cbn [edenot]. rewrite unsigned_lit by lia. apply chk_rangeS_soundS. exact H3.
    - apply inb_litsS_soundS. exact H.
    - apply chk_rangeS_soundS. exact H.
  Qed.

  Lemma kn_inD_residualS : forall kn, Forall (kentry_inD D E) (knd_residualS kn) -> kn_inD D E kn.
  Proof.
    intros kn HR. unfold kn_inD. apply Forall_forall. intros K HK.
    destruct (chk_entryS K) eqn:C.
    - apply chk_entryS_soundS. exact C.
    - rewrite Forall_forall in HR. apply HR. unfold knd_residualS. apply (proj2 (filter_In _ _ _)). split; [exact HK|]. rewrite C. reflexivity.
  Qed.
End KnDS.

(* [comment removed for export] *)
Ltac solve_kn_inD_fastS KND covtac :=
  lazymatch goal with
  | |- kn_inD ?D ?E ?kn =>
      apply (KND kn);
      lazymatch goal with
      | |- Forall _ (knd_residualS ?FLO ?FHI ?LITS _) =>
          let r := eval vm_compute in (knd_residualS FLO FHI LITS kn) in
          change (Forall (kentry_inD D E) r)
      end;
      repeat (apply Forall_cons; [ cbn [kentry_inD]; covtac | ]); apply Forall_nil
  end.

Ltac run_blockA3_withS RRUN KND HR HK fuel stops scr NX keep covtac :=
  lazymatch type of HR with
  | regs_ok ?E ?sr ?R =>
    lazymatch type of HK with
    | know_ok ?segs _ ?M ?kn =>
      lazymatch goal with
      | |- srealizesJ _ (mkCfg (mkst R (Z_to_bv 64 ?pc) M ?rom) ?model) ?T =>
        let r := eval vm_compute in (sym_exec segs fuel true stops scr (SS pc sr [] kn NX) []) in
        lazymatch r with
        | (?ss', ?scs, ?scr') =>
          let c := eval vm_compute in (carry (s_log ss') kn []) in
          lazymatch c with
          | (?kn', ?scs2, ?hs2) =>
            eapply (RRUN fuel stops scr pc sr kn NX ss' scs scr' kn' scs2 hs2 E M R model T);
            [ vm_cast_no_check (@eq_refl _ (ss', scs, scr'))
            | vm_cast_no_check (@eq_refl _ (kn', scs2, hs2))
            | exact HR | exact HK
            | first [ solve_kn_inD_fastS KND covtac | try (solve_kn_inD covtac) ]
            | first [ solve_kn_inD_fastS KND covtac | try (solve_kn_inD covtac) ]
            | split_foralls
            | split_foralls
            | try assumption
            | clear HR HK;
              let R' := fresh "R" in let M' := fresh "M" in let EQM := fresh "EQM" in let OUT := fresh "OUT" in
              let mo' := fresh "mo" in let HKM := fresh "HKmo" in let MM := fresh "MM" in
              intros R' M' mo' HR HK EQM OUT HKM MM; cbn [s_pc s_regs s_log] in HR, EQM |- *;
              lazymatch keep with
              | true => idtac
              | false => clear EQM; try clear R; try clear M;
                         try rename R' into R; try rename M' into M
              end ]
          end
        end
      end
    end
  end.

Tactic Notation "run_blockA3S" constr(RRUN) constr(KND) constr(fuel) constr(stops) constr(scr) constr(NX) constr(keep) tactic3(covtac) :=
  match goal with
  | HR : regs_ok _ _ _, HK : know_ok _ _ _ _ |- _ => run_blockA3_withS RRUN KND HR HK fuel stops scr NX keep covtac
  end.
