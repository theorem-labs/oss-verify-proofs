From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PropExec CatSim SymExec3 SymExec3Sound SymRun3.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HLib.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BTac BArr BSysStep BExec BellsX BacX BMem BMState BLFrame.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BPrelim.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsIface BsCXXHeap BXXRep BsStack0 RtB_Iface.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LibIface FPSteps.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HRep HRepFacts HStmts.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require Import CRep.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs Require Import PrsInv PmBase.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_Kit LbB_Bridge LbB_Call LbB_Conv LbB_SR LbB_FKit LbB_MILB LbB_PrsStmt LbB_Own LbB_PmBase LbB_FSlots LbB_PmOwn LbB_PmCut LbB_PmTac LbB_PmCall LbB_PmXp LbB_PmXv LbB_PmVec LbB_PmVup LbB_PmGlue LbB_PmVops.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

Definition VCL_KEEP : list (bv 5) :=
  [1;2;3;4;5;6;7;8;9;10;11;12;14;15;16;17;18;19;20;21;22;23;24;25;26;27;28;29;30;31]%bv.

Lemma vcl_in : forall (r : bv 5) (l : list (bv 5)), existsb (bv_eqb r) l = true -> In r l.
Proof.
  intros r l. induction l as [|y l IH]; cbn [existsb In]; [discriminate|].
  intros Hx. apply orb_true_iff in Hx. destruct Hx as [Hx|Hx]; [left | right; exact (IH Hx)].
  unfold bv_eqb in Hx. apply Z.eqb_eq in Hx. symmetry. apply bv_eq. exact Hx.
Qed.

Lemma vcl_frame : forall (R R' : bvmap 5 word),
  (forall r, In r VCL_KEEP -> PropExec.getr R' r = PropExec.getr R r) ->
  forall r : bv 5, r <> 13%bv -> PropExec.getr R' r = PropExec.getr R r.
Proof.
  intros R R' K r H13. destruct (bv_eqb r 0%bv) eqn:E0.
  { assert (Z0 : r = 0%bv) by (apply bv_eq; unfold bv_eqb in E0; apply Z.eqb_eq in E0; exact E0).
    subst r. reflexivity. }
  apply K, vcl_in.
  assert (N0 : bv_unsigned r <> 0) by (intro Hu; unfold bv_eqb in E0; rewrite Hu in E0; vm_compute in E0; discriminate E0).
  assert (N13 : bv_unsigned r <> 13) by (intro Hu; apply H13; apply bv_eq; rewrite Hu; reflexivity).
  pose proof (u5_range r) as U.
  change (existsb (fun y => bv_unsigned r =? bv_unsigned y) VCL_KEEP = true).
  revert N0 N13 U. generalize (bv_unsigned r) as u. intros u N0 N13 U.
  assert (Hn : exists n, u = Z.of_nat n) by (exists (Z.to_nat u); lia).
  destruct Hn as [n ->].
  do 32 (destruct n as [|n]; [first [exfalso; lia | vm_compute; reflexivity] |]).
  exfalso. lia.
Qed.

Ltac fixr := try replace (Z_to_bv 5 (Z.of_N 10)) with (10%bv : reg) by (apply bv_eq; reflexivity);
             try replace (Z_to_bv 5 (Z.of_N 11)) with (11%bv : reg) by (apply bv_eq; reflexivity).
Ltac vsc H10 H11 := cbn [sc_denot]; evs; fixr; rewrite ?H10, ?H11, ?w_addm by lia;
                    rewrite ?br_geu, ?br_ne, ?br_ltu, ?br_eq by lia; bool_lia.

Lemma vcl_loop2 : forall (F : bvmap 5 word) (fc : bv 32) (M : word -> option byte) (b : Z) (k : nat) (R : bvmap 5 word),
  PropExec.getr R 10%bv = Z_to_bv 64 b ->
  PropExec.getr R 13%bv = Z_to_bv 64 (b + 4 * Z.of_nat (S k)) ->
  PropExec.getr R 11%bv = Z_to_bv 64 4 ->
  8 <= b -> b + 4 * Z.of_nat (S k) <= 2 ^ 63 ->
  exists R', CatSim.msteps asegs (MS R F (Z_to_bv 64 0xf0810) fc None M (seg_rom asegs))
                                 (MS R' F (Z_to_bv 64 0xf081c) fc None M (seg_rom asegs))
    /\ (forall r : bv 5, r <> 13%bv -> PropExec.getr R' r = PropExec.getr R r)
    /\ PropExec.getr R' 13%bv = Z_to_bv 64 b.
Proof.
  intros F fc M b k. induction k as [|k IH]; intros R H10 H13 H11 Hb8 Hhi.
  - pose (E := Eseed R [Z_to_bv 64 (b + 4 * Z.of_nat 1)]).
    assert (HR : regs_ok E (srs sr_id [(13%bv, EVar 32)]) R).
    { apply regs_ok_srs; [apply regs_ok_seed|].
      repeat constructor; cbn [fst snd]; try (intros X; discriminate X); evs. exact H13. }
    assert (HK : know_ok asegs E M []) by constructor.
    change (MS R F (Z_to_bv 64 0xf0810) fc None M (seg_rom asegs))
      with (@PropExec.mkst (PropExec.mkFP F fc) R (Z_to_bv 64 0xf0810) M (seg_rom asegs)).
    xrun HR HK 20%nat [0xf0810; 0xf081c] (SCR [false; false] [] []) 33%N.
    { split_scs. all: vsc H10 H11. }
    exists R'. split; [exact Hms|]. split.
    + apply vcl_frame. exact (syms_id_sound _ _ _ R' VCL_KEEP HR' eq_refl).
    + rreg HR' 13%bv G. rewrite G. evs. rewrite ?w_addm by lia. f_equal. lia.
  - pose (E := Eseed R [Z_to_bv 64 (b + 4 * Z.of_nat (S (S k)))]).
    assert (HR : regs_ok E (srs sr_id [(13%bv, EVar 32)]) R).
    { apply regs_ok_srs; [apply regs_ok_seed|].
      repeat constructor; cbn [fst snd]; try (intros X; discriminate X); evs. exact H13. }
    assert (HK : know_ok asegs E M []) by constructor.
    change (MS R F (Z_to_bv 64 0xf0810) fc None M (seg_rom asegs))
      with (@PropExec.mkst (PropExec.mkFP F fc) R (Z_to_bv 64 0xf0810) M (seg_rom asegs)).
    xrun HR HK 20%nat [0xf0810; 0xf081c] (SCR [false; true] [] []) 33%N.
    { split_scs. all: vsc H10 H11. }
    pose proof (vcl_frame R R' (syms_id_sound _ _ _ R' VCL_KEEP HR' eq_refl)) as KF.
    rreg HR' 13%bv G. rewrite ?w_addm in G by lia.
    destruct (IH R' ltac:(rewrite (KF 10%bv) by discriminate; exact H10) ltac:(rewrite G; f_equal; lia)
                 ltac:(rewrite (KF 11%bv) by discriminate; exact H11) Hb8 ltac:(lia)) as (R2 & RUN2 & K2 & G2).
    exists R2. split; [eapply CatSim.msteps_trans; [exact Hms | exact RUN2]|]. split; [|exact G2].
    intros r Hr. rewrite (K2 r Hr). exact (KF r Hr).
Qed.

Lemma vcl_loop1 : forall (F : bvmap 5 word) (fc : bv 32) (M : word -> option byte) (b : Z) (k : nat) (R : bvmap 5 word),
  PropExec.getr R 10%bv = Z_to_bv 64 b ->
  PropExec.getr R 13%bv = Z_to_bv 64 (b + 20 * Z.of_nat (S k)) ->
  PropExec.getr R 11%bv = Z_to_bv 64 20 ->
  8 <= b -> b + 20 * Z.of_nat (S k) <= 2 ^ 63 ->
  exists R', CatSim.msteps asegs (MS R F (Z_to_bv 64 0xf0998) fc None M (seg_rom asegs))
                                 (MS R' F (Z_to_bv 64 0xf09a8) fc None M (seg_rom asegs))
    /\ (forall r : bv 5, r <> 13%bv -> PropExec.getr R' r = PropExec.getr R r)
    /\ PropExec.getr R' 13%bv = Z_to_bv 64 b.
Proof.
  intros F fc M b k. induction k as [|k IH]; intros R H10 H13 H11 Hb8 Hhi.
  - pose (E := Eseed R [Z_to_bv 64 (b + 20 * Z.of_nat 1)]).
    assert (HR : regs_ok E (srs sr_id [(13%bv, EVar 32)]) R).
    { apply regs_ok_srs; [apply regs_ok_seed|].
      repeat constructor; cbn [fst snd]; try (intros X; discriminate X); evs. exact H13. }
    assert (HK : know_ok asegs E M []) by constructor.
    change (MS R F (Z_to_bv 64 0xf0998) fc None M (seg_rom asegs))
      with (@PropExec.mkst (PropExec.mkFP F fc) R (Z_to_bv 64 0xf0998) M (seg_rom asegs)).
    xrun HR HK 20%nat [0xf0998; 0xf09a8] (SCR [false; false; false] [] []) 33%N.
    { split_scs. all: vsc H10 H11. }
    exists R'. split; [exact Hms|]. split.
    + apply vcl_frame. exact (syms_id_sound _ _ _ R' VCL_KEEP HR' eq_refl).
    + rreg HR' 13%bv G. rewrite G. evs. rewrite ?w_addm by lia. f_equal. lia.
  - pose (E := Eseed R [Z_to_bv 64 (b + 20 * Z.of_nat (S (S k)))]).
    assert (HR : regs_ok E (srs sr_id [(13%bv, EVar 32)]) R).
    { apply regs_ok_srs; [apply regs_ok_seed|].
      repeat constructor; cbn [fst snd]; try (intros X; discriminate X); evs. exact H13. }
    assert (HK : know_ok asegs E M []) by constructor.
    change (MS R F (Z_to_bv 64 0xf0998) fc None M (seg_rom asegs))
      with (@PropExec.mkst (PropExec.mkFP F fc) R (Z_to_bv 64 0xf0998) M (seg_rom asegs)).
    xrun HR HK 20%nat [0xf0998; 0xf09a8] (SCR [false; false; true] [] []) 33%N.
    { split_scs. all: vsc H10 H11. }
    pose proof (vcl_frame R R' (syms_id_sound _ _ _ R' VCL_KEEP HR' eq_refl)) as KF.
    rreg HR' 13%bv G. rewrite ?w_addm in G by lia.
    destruct (IH R' ltac:(rewrite (KF 10%bv) by discriminate; exact H10) ltac:(rewrite G; f_equal; lia)
                 ltac:(rewrite (KF 11%bv) by discriminate; exact H11) Hb8 ltac:(lia)) as (R2 & RUN2 & K2 & G2).
    exists R2. split; [eapply CatSim.msteps_trans; [exact Hms | exact RUN2]|]. split; [|exact G2].
    intros r Hr. rewrite (K2 r Hr). exact (KF r Hr).
Qed.

Lemma vcl_loop3 : forall (F : bvmap 5 word) (fc : bv 32) (M : word -> option byte) (b : Z) (k : nat) (R : bvmap 5 word),
  PropExec.getr R 10%bv = Z_to_bv 64 b ->
  PropExec.getr R 13%bv = Z_to_bv 64 (b + 4 * Z.of_nat (S k)) ->
  PropExec.getr R 11%bv = Z_to_bv 64 4 ->
  8 <= b -> b + 4 * Z.of_nat (S k) <= 2 ^ 63 ->
  exists R', CatSim.msteps asegs (MS R F (Z_to_bv 64 0xf1010) fc None M (seg_rom asegs))
                                 (MS R' F (Z_to_bv 64 0xf1020) fc None M (seg_rom asegs))
    /\ (forall r : bv 5, r <> 13%bv -> PropExec.getr R' r = PropExec.getr R r)
    /\ PropExec.getr R' 13%bv = Z_to_bv 64 b.
Proof.
  intros F fc M b k. induction k as [|k IH]; intros R H10 H13 H11 Hb8 Hhi.
  - pose (E := Eseed R [Z_to_bv 64 (b + 4 * Z.of_nat 1)]).
    assert (HR : regs_ok E (srs sr_id [(13%bv, EVar 32)]) R).
    { apply regs_ok_srs; [apply regs_ok_seed|].
      repeat constructor; cbn [fst snd]; try (intros X; discriminate X); evs. exact H13. }
    assert (HK : know_ok asegs E M []) by constructor.
    change (MS R F (Z_to_bv 64 0xf1010) fc None M (seg_rom asegs))
      with (@PropExec.mkst (PropExec.mkFP F fc) R (Z_to_bv 64 0xf1010) M (seg_rom asegs)).
    xrun HR HK 20%nat [0xf1010; 0xf1020] (SCR [true] [] []) 33%N.
    { split_scs. all: vsc H10 H11. }
    exists R'. split; [exact Hms|]. split.
    + apply vcl_frame. exact (syms_id_sound _ _ _ R' VCL_KEEP HR' eq_refl).
    + rreg HR' 13%bv G. rewrite G. evs. rewrite ?w_addm by lia. f_equal. lia.
  - pose (E := Eseed R [Z_to_bv 64 (b + 4 * Z.of_nat (S (S k)))]).
    assert (HR : regs_ok E (srs sr_id [(13%bv, EVar 32)]) R).
    { apply regs_ok_srs; [apply regs_ok_seed|].
      repeat constructor; cbn [fst snd]; try (intros X; discriminate X); evs. exact H13. }
    assert (HK : know_ok asegs E M []) by constructor.
    change (MS R F (Z_to_bv 64 0xf1010) fc None M (seg_rom asegs))
      with (@PropExec.mkst (PropExec.mkFP F fc) R (Z_to_bv 64 0xf1010) M (seg_rom asegs)).
    xrun HR HK 20%nat [0xf1010; 0xf1020] (SCR [false; true] [] []) 33%N.
    { split_scs. all: vsc H10 H11. }
    pose proof (vcl_frame R R' (syms_id_sound _ _ _ R' VCL_KEEP HR' eq_refl)) as KF.
    rreg HR' 13%bv G. rewrite ?w_addm in G by lia.
    destruct (IH R' ltac:(rewrite (KF 10%bv) by discriminate; exact H10) ltac:(rewrite G; f_equal; lia)
                 ltac:(rewrite (KF 11%bv) by discriminate; exact H11) Hb8 ltac:(lia)) as (R2 & RUN2 & K2 & G2).
    exists R2. split; [eapply CatSim.msteps_trans; [exact Hms | exact RUN2]|]. split; [|exact G2].
    intros r Hr. rewrite (K2 r Hr). exact (KF r Hr).
Qed.
