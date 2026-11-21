(* SPDX-License-Identifier: MIT *)
(* Theorem Labs, 2026-11: the vDSO window stays clean along every run of the model, with no
   premise on the system calls the run makes beyond the two pins being well formed
   ([PinsOk.pins_ok], which every run keeps).
     - [pc_spec_ok_all]: [PairClean.pc_spec_ok] holds at every input from a model whose pins are
       well formed.  A number with no arm has no outcome ([PairClean.pc_spec_ok_unarmed]); a
       number with an arm ([Dispatch.lookup_arm], Sys/Dispatch.v:41-45) is one of the 93 numbers
       of Sys/SyscallTable.v:41-135 ([pca_lookup_no], [pca_table_nos]), and each is closed by its
       [pc_spec_ok_<N>]: 17 in PairClean.v ([pc_proved_nos]), the 46 write-free arms in
       PairCleanQ.v, and the 30 writing arms with mremap (216) in PairCleanW.v; uname (160) and
       prlimit64 (261) read the pins.
     - [sreach_keep]: an invariant every step keeps holds, beside the target, where an
       [SReach.sreach] reach ends ([SReach.sr_step], SReach.v:30-35, covers every successor).
     - [vcm_cfg]: [MmVdso.vc_cfg], "every map misses the window" ([MapsOff.maps_off]) and the
       pins ([PinsOk.pins_ok]).  [pc_step_clean] keeps it over every step of [Run.sstep_cfg]
       under any spurious-failure configuration: [PairClean.pc_step] with [pc_spec_ok_all] as its
       step premise, [MapsOff.mo_step] with the pair invariant [MmVdso.mm_vinv] that [vc_cfg]
       carries, and [PinsOk.pins_step].  [pc_star_clean] is the same over [Run.star_cfg],
       [sreach_keep_vcm] over a reach. *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics State Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Dispatch SyscallTable.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Import Scfg SReach.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import MmVdso.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Common.Cfg Require Import
  PairClean PairCleanQ PairCleanW MapsOff PinsOk.
Import ListNotations.
Open Scope Z_scope.

(** * The numbers the table carries *)

(** [Dispatch.lookup_arm] (Sys/Dispatch.v:41-45) answers only with an arm carrying the number it
    was asked. *)
Lemma pca_lookup_no : forall t n (a : LinuxProcessSemantics.LinuxProcessSem.Sys.Dispatch.SpecArm),
  LinuxProcessSemantics.LinuxProcessSem.Sys.Dispatch.lookup_arm t n = Some a ->
  List.In n (List.map LinuxProcessSemantics.LinuxProcessSem.Sys.Dispatch.sa_no t).
Proof.
  induction t as [|b r IH]; intros n a H;
    cbn [LinuxProcessSemantics.LinuxProcessSem.Sys.Dispatch.lookup_arm] in H; [discriminate H|].
  cbn [List.map List.In].
  destruct (Z.eqb (LinuxProcessSemantics.LinuxProcessSem.Sys.Dispatch.sa_no b) n) eqn:Eb.
  - left. exact (proj1 (Z.eqb_eq _ _) Eb).
  - right. apply (IH n a). try rewrite Eb in H. exact H.
Qed.

(** The 93 numbers of Sys/SyscallTable.v:41-135, in the table's order. *)
Lemma pca_table_nos :
  List.map LinuxProcessSemantics.LinuxProcessSem.Sys.Dispatch.sa_no
    LinuxProcessSemantics.LinuxProcessSem.Sys.SyscallTable.spec_table =
  [17; 19; 20; 21; 22; 23; 24; 25; 29; 32; 35; 46; 48; 56; 57; 59; 61; 62; 63; 64; 65; 66; 67;
     68; 72; 73; 78; 79; 80; 82; 83; 85; 93; 94; 96; 98; 99; 101; 113; 114; 119; 123; 124; 130;
     131; 132; 134; 135; 144; 146; 147; 149; 157; 158; 159; 160; 167; 169; 172; 174; 175; 176; 177;
     178; 198; 199; 200; 201; 202; 203; 204; 205; 206; 207; 208; 209; 210; 211; 212; 214; 215; 216;
     220; 222; 226; 233; 242; 260; 261; 278; 287; 435; 439].
Proof. reflexivity. Qed.

(** * An invariant along a reach *)

(** [SReach.sr_step] asks the reach of every [SNext] successor, so an invariant every step keeps
    still holds where the reach ends. *)
Lemma sreach_keep {SC : StepCfg} : forall segs (I Q : config -> Prop) c,
  (forall d evs d', I d -> sstep_cfg segs the_scfg d evs (SNext d') -> I d') ->
  sreach segs Q c -> I c -> sreach segs (fun c' => Q c' /\ I c') c.
Proof.
  intros segs I Q c HI H. induction H as [c Hc | c Hrob Hprog Hall Hk IH]; intros Ic.
  - apply sr_done. exact (conj Hc Ic).
  - apply sr_step; [exact Hrob | exact Hprog | exact Hall |].
    intros evs c' Hss. exact (IH evs c' Hss (HI c evs c' Ic Hss)).
Qed.

(** * Every number, and the step, run and reach lemmas *)

Section PairCleanAll.
  Variable segs : list Segment.
  Variables vlo vhi : Z.
  (* no writable segment of [segs] holds a byte of the window, as in [PairClean] *)
  Hypothesis Hnw : forall (x : word) s, vlo <= bv_unsigned x < vhi ->
    find_segment segs (bv_unsigned x) 1 = Some s -> seg_writable s = false.

  (** Every input: the arm the dispatcher picks, closed by the lemma of its number (given the
      pins when that lemma asks them). *)
  Theorem pc_spec_ok_all : forall i mo, PinsOk.pins_ok mo -> pc_spec_ok vlo vhi i mo.
  Proof.
    intros i mo P.
    destruct (LinuxProcessSemantics.LinuxProcessSem.Sys.Dispatch.lookup_arm
                LinuxProcessSemantics.LinuxProcessSem.Sys.SyscallTable.spec_table
                (bv_unsigned (in_sysno i))) as [a|] eqn:E.
    - pose proof (pca_lookup_no _ _ _ E) as Hin.
      rewrite pca_table_nos in Hin. cbn [List.In] in Hin.
      repeat match type of Hin with _ \/ _ => destruct Hin as [Hin | Hin] end.
      all: first
        [ contradiction
        | (apply pc_spec_ok_17; first [exact (eq_sym Hin) | exact P])
        | (apply pc_spec_ok_19; first [exact (eq_sym Hin) | exact P])
        | (apply pc_spec_ok_20; first [exact (eq_sym Hin) | exact P])
        | (apply pc_spec_ok_21; first [exact (eq_sym Hin) | exact P])
        | (apply pc_spec_ok_22; first [exact (eq_sym Hin) | exact P])
        | (apply pc_spec_ok_23; first [exact (eq_sym Hin) | exact P])
        | (apply pc_spec_ok_24; first [exact (eq_sym Hin) | exact P])
        | (apply pc_spec_ok_25; first [exact (eq_sym Hin) | exact P])
        | (apply pc_spec_ok_29; first [exact (eq_sym Hin) | exact P])
        | (apply pc_spec_ok_32; first [exact (eq_sym Hin) | exact P])
        | (apply pc_spec_ok_35; first [exact (eq_sym Hin) | exact P])
        | (apply pc_spec_ok_46; first [exact (eq_sym Hin) | exact P])
        | (apply pc_spec_ok_48; first [exact (eq_sym Hin) | exact P])
        | (apply pc_spec_ok_56; first [exact (eq_sym Hin) | exact P])
        | (apply pc_spec_ok_57; first [exact (eq_sym Hin) | exact P])
        | (apply pc_spec_ok_59; first [exact (eq_sym Hin) | exact P])
        | (apply pc_spec_ok_61; first [exact (eq_sym Hin) | exact P])
        | (apply pc_spec_ok_62; first [exact (eq_sym Hin) | exact P])
        | (apply pc_spec_ok_63; first [exact (eq_sym Hin) | exact P])
        | (apply pc_spec_ok_64; first [exact (eq_sym Hin) | exact P])
        | (apply pc_spec_ok_65; first [exact (eq_sym Hin) | exact P])
        | (apply pc_spec_ok_66; first [exact (eq_sym Hin) | exact P])
        | (apply pc_spec_ok_67; first [exact (eq_sym Hin) | exact P])
        | (apply pc_spec_ok_68; first [exact (eq_sym Hin) | exact P])
        | (apply pc_spec_ok_72; first [exact (eq_sym Hin) | exact P])
        | (apply pc_spec_ok_73; first [exact (eq_sym Hin) | exact P])
        | (apply pc_spec_ok_78; first [exact (eq_sym Hin) | exact P])
        | (apply pc_spec_ok_79; first [exact (eq_sym Hin) | exact P])
        | (apply pc_spec_ok_80; first [exact (eq_sym Hin) | exact P])
        | (apply pc_spec_ok_82; first [exact (eq_sym Hin) | exact P])
        | (apply pc_spec_ok_83; first [exact (eq_sym Hin) | exact P])
        | (apply pc_spec_ok_85; first [exact (eq_sym Hin) | exact P])
        | (apply pc_spec_ok_93; first [exact (eq_sym Hin) | exact P])
        | (apply pc_spec_ok_94; first [exact (eq_sym Hin) | exact P])
        | (apply pc_spec_ok_96; first [exact (eq_sym Hin) | exact P])
        | (apply pc_spec_ok_98; first [exact (eq_sym Hin) | exact P])
        | (apply pc_spec_ok_99; first [exact (eq_sym Hin) | exact P])
        | (apply pc_spec_ok_101; first [exact (eq_sym Hin) | exact P])
        | (apply pc_spec_ok_113; first [exact (eq_sym Hin) | exact P])
        | (apply pc_spec_ok_114; first [exact (eq_sym Hin) | exact P])
        | (apply pc_spec_ok_119; first [exact (eq_sym Hin) | exact P])
        | (apply pc_spec_ok_123; first [exact (eq_sym Hin) | exact P])
        | (apply pc_spec_ok_124; first [exact (eq_sym Hin) | exact P])
        | (apply pc_spec_ok_130; first [exact (eq_sym Hin) | exact P])
        | (apply pc_spec_ok_131; first [exact (eq_sym Hin) | exact P])
        | (apply pc_spec_ok_132; first [exact (eq_sym Hin) | exact P])
        | (apply pc_spec_ok_134; first [exact (eq_sym Hin) | exact P])
        | (apply pc_spec_ok_135; first [exact (eq_sym Hin) | exact P])
        | (apply pc_spec_ok_144; first [exact (eq_sym Hin) | exact P])
        | (apply pc_spec_ok_146; first [exact (eq_sym Hin) | exact P])
        | (apply pc_spec_ok_147; first [exact (eq_sym Hin) | exact P])
        | (apply pc_spec_ok_149; first [exact (eq_sym Hin) | exact P])
        | (apply pc_spec_ok_157; first [exact (eq_sym Hin) | exact P])
        | (apply pc_spec_ok_158; first [exact (eq_sym Hin) | exact P])
        | (apply pc_spec_ok_159; first [exact (eq_sym Hin) | exact P])
        | (apply pc_spec_ok_160; first [exact (eq_sym Hin) | exact P])
        | (apply pc_spec_ok_167; first [exact (eq_sym Hin) | exact P])
        | (apply pc_spec_ok_169; first [exact (eq_sym Hin) | exact P])
        | (apply pc_spec_ok_172; first [exact (eq_sym Hin) | exact P])
        | (apply pc_spec_ok_174; first [exact (eq_sym Hin) | exact P])
        | (apply pc_spec_ok_175; first [exact (eq_sym Hin) | exact P])
        | (apply pc_spec_ok_176; first [exact (eq_sym Hin) | exact P])
        | (apply pc_spec_ok_177; first [exact (eq_sym Hin) | exact P])
        | (apply pc_spec_ok_178; first [exact (eq_sym Hin) | exact P])
        | (apply pc_spec_ok_198; first [exact (eq_sym Hin) | exact P])
        | (apply pc_spec_ok_199; first [exact (eq_sym Hin) | exact P])
        | (apply pc_spec_ok_200; first [exact (eq_sym Hin) | exact P])
        | (apply pc_spec_ok_201; first [exact (eq_sym Hin) | exact P])
        | (apply pc_spec_ok_202; first [exact (eq_sym Hin) | exact P])
        | (apply pc_spec_ok_203; first [exact (eq_sym Hin) | exact P])
        | (apply pc_spec_ok_204; first [exact (eq_sym Hin) | exact P])
        | (apply pc_spec_ok_205; first [exact (eq_sym Hin) | exact P])
        | (apply pc_spec_ok_206; first [exact (eq_sym Hin) | exact P])
        | (apply pc_spec_ok_207; first [exact (eq_sym Hin) | exact P])
        | (apply pc_spec_ok_208; first [exact (eq_sym Hin) | exact P])
        | (apply pc_spec_ok_209; first [exact (eq_sym Hin) | exact P])
        | (apply pc_spec_ok_210; first [exact (eq_sym Hin) | exact P])
        | (apply pc_spec_ok_211; first [exact (eq_sym Hin) | exact P])
        | (apply pc_spec_ok_212; first [exact (eq_sym Hin) | exact P])
        | (apply pc_spec_ok_214; first [exact (eq_sym Hin) | exact P])
        | (apply pc_spec_ok_215; first [exact (eq_sym Hin) | exact P])
        | (apply pc_spec_ok_216; first [exact (eq_sym Hin) | exact P])
        | (apply pc_spec_ok_220; first [exact (eq_sym Hin) | exact P])
        | (apply pc_spec_ok_222; first [exact (eq_sym Hin) | exact P])
        | (apply pc_spec_ok_226; first [exact (eq_sym Hin) | exact P])
        | (apply pc_spec_ok_233; first [exact (eq_sym Hin) | exact P])
        | (apply pc_spec_ok_242; first [exact (eq_sym Hin) | exact P])
        | (apply pc_spec_ok_260; first [exact (eq_sym Hin) | exact P])
        | (apply pc_spec_ok_261; first [exact (eq_sym Hin) | exact P])
        | (apply pc_spec_ok_278; first [exact (eq_sym Hin) | exact P])
        | (apply pc_spec_ok_287; first [exact (eq_sym Hin) | exact P])
        | (apply pc_spec_ok_435; first [exact (eq_sym Hin) | exact P])
        | (apply pc_spec_ok_439; first [exact (eq_sym Hin) | exact P]) ].
    - apply pc_spec_ok_unarmed. exact E.
  Qed.

  (** The window clean, the pair reserved, every map off the window, and the pins well
      formed. *)
  Definition vcm_cfg (c : config) : Prop :=
    MmVdso.vc_cfg vlo vhi c /\ maps_off vlo vhi (cfg_model c) /\ PinsOk.pins_ok (cfg_model c).

  Theorem pc_step_clean : forall cfg c evs c',
    sstep_cfg segs cfg c evs (SNext c') -> vcm_cfg c -> vcm_cfg c'.
  Proof.
    intros cfg c evs c' H [VC [MO PO]].
    pose proof VC as [_ VI].
    split; [| split].
    - apply (pc_step segs vlo vhi Hnw cfg c evs c' H); [| exact VC].
      intros x8 _. exact (pc_spec_ok_all _ _ PO).
    - eapply mo_step; eassumption.
    - exact (PinsOk.pins_step _ _ _ _ _ H PO).
  Qed.

  Theorem pc_star_clean : forall cfg c tr c',
    star_cfg segs cfg c tr c' -> vcm_cfg c -> vcm_cfg c'.
  Proof.
    intros cfg c tr c' Hs. induction Hs as [d | d1 evs1 d2 tr1 d3 Hst Hs1 IH]; intros V.
    - exact V.
    - exact (IH (pc_step_clean cfg d1 evs1 d2 Hst V)).
  Qed.

  Corollary sreach_keep_vcm {SC : StepCfg} : forall Q c,
    sreach segs Q c -> vcm_cfg c -> sreach segs (fun c' => Q c' /\ vcm_cfg c') c.
  Proof.
    intros Q c H V. apply (@sreach_keep SC segs vcm_cfg Q c); [| exact H | exact V].
    intros d evs d' Vd Hs. exact (pc_step_clean _ d evs d' Hs Vd).
  Qed.
End PairCleanAll.
