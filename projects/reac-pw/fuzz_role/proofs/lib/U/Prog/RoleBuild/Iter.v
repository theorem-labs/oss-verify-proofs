(** One property of the UBSan builder, 0x13160 -> the property loop's latch 0x13e00 ([Cut.S_iter], the premise
    of PropLoop.prop_loop): the shape-7 object's Int pod, or the key and flags ([Key.key_entry]) and then the
    Int-7 value or the params Struct ([Struct.struct_open], the pod loop [CntLoop.cnt_loop] and the close
    [Cut.S_close]). It refines [Model.prop_step]. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Lib Require Import Tac.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.U Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.U.Prog Require Import SlotInv LLVMFuzzerTestOneInput_c.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.U.Prog.RoleBuild Require Import
  Facts Cut CntLoop PropLoop UTac Key Struct EntCut.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Pod Require Import Cursor Model Layout.
Import ListNotations.
Open Scope Z_scope.

Section Iter.
Variables (sp gp tp : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte).
Variables (rest : list byte) (fl src pp lo : Z).
Hypothesis HOK : BOK sp rest src pp lo.
Hypothesis HPPA : pp mod 16 = 0.
Hypothesis HSPA : bv_unsigned sp mod 16 = 0.

(** The shape-7 object's property: one Int pod, no key (pod.h:401-405). *)
Definition S_shape7 : Prop :=
  forall (np : Z) (ps : list (Z * pval)) (r : list byte) (ms : machine_state),
    PROPH sp gp tp F fc m rest fl src pp lo 7 np ps r ms ->
    evt rsegs (PROPL sp gp tp F fc m rest fl src pp lo 7 np (length ps) (ps ++ [fst (prop_step 7 r)])
                 (snd (prop_step 7 r))) ms.

(** The Int-7 value of a property whose selector is not a Struct's (pod.h:412-419). *)
Definition S_int7 : Prop :=
  forall (sh np : Z) (ps : list (Z * pval)) (r : list byte) (sel : Z) (ms : machine_state),
    PKEY sp gp tp F fc m rest fl src pp lo sh np ps r sel ms ->
    (sel mod 4 = 0 \/ Z.testbit sel 4 = true) ->
    evt rsegs (PROPL sp gp tp F fc m rest fl src pp lo sh np (length ps) (ps ++ [(key_of sel, PInt 7)]) r) ms.

Hypothesis ENT : rb_ent_contract.
Hypothesis WR : S_write sp gp tp F fc m rest fl src pp lo.
Hypothesis CL : S_close sp gp tp F fc m rest fl src pp lo.
Hypothesis SH7 : S_shape7.
Hypothesis INT7 : S_int7.

Lemma iter_ok : S_iter sp gp tp F fc m rest fl src pp lo.
Proof.
  intros sh np ps r ms HP.
  destruct (Z.eq_dec sh 7) as [->|Hsh]; [exact (SH7 np ps r ms HP)|].
  eapply evt_cut; [exact (key_entry sp gp tp F fc m rest fl src pp lo HOK sh np ps r ms HP Hsh)|].
  intros ms1 HK.
  unfold prop_step. destruct (fuzz_u8 r) as [sel r1] eqn:Ef. cbn [fst snd] in HK |- *.
  replace (sh =? 7) with false by (symmetry; apply Z.eqb_neq; exact Hsh).
  destruct (sel mod 4 =? 0) eqn:E0.
  - assert (Ek : key_of sel = POD_PROP_VOLUME) by (unfold key_of; rewrite E0; reflexivity).
    rewrite <- Ek. apply (INT7 sh np ps r1 sel ms1 HK). left. apply Z.eqb_eq. exact E0.
  - assert (Ek : key_of sel = POD_PROP_PARAMS) by (unfold key_of; rewrite E0; reflexivity).
    destruct (Z.testbit sel 4) eqn:Eb.
    + rewrite <- Ek. apply (INT7 sh np ps r1 sel ms1 HK). right. exact Eb.
    + eapply evt_cut;
        [exact (struct_open sp gp tp F fc m rest fl src pp lo HOK sh np ps r1 sel ms1 HK
                  ltac:(apply Z.eqb_neq; exact E0) Eb)|].
      intros ms2 HS. unfold SOPEN in HS.
      destruct (fuzz_u8 r1) as [c r2] eqn:Ec.
      destruct (ents_loop (Z.to_nat (c mod 33)) r2) as [es r3] eqn:El.
      cbn [fst snd] in HS |- *.
      destruct HS as [[Hpos HC] | [Hz HPC]].
      * eapply evt_cut.
        { eapply (cnt_loop sp gp tp F fc m rest fl src pp lo HOK HPPA HSPA ENT WR
                    (Z.to_nat (c mod 33)) sh np ps (length ps) (c mod 33) [] 0%nat r2 ms2);
            [cbn [Nat.add]; reflexivity | exact HC]. }
        rewrite El. cbn [fst snd app]. intros ms3 HPC. exact (CL HOK sh np ps (length ps) es r3 ms3 HPC).
      * assert (Hn : (Z.to_nat (c mod 33) = 0)%nat) by lia.
        rewrite Hn in El. cbn [ents_loop] in El. injection El as <- <-.
        exact (CL HOK sh np ps (length ps) [] r2 ms2 HPC).
Qed.

End Iter.
