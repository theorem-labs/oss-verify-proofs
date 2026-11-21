(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Specs Run.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.Lib Require Import PropExec MState ITree Nodes Decode.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.LibA Require Import AcctCore ExecF ITreeA ModelX MmXfer NodesA.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.AS Require Import BackingAlgebra. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.UnpW.AS Require Import MainExport MainFactsAsan MainEntry.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.Spec Require Import Prelim Monad STree Stdio Harness Adapter Driver ProgA AsanCtrl AsanCtrlProps SizeHist AsanEmbed AsanProgDeps AsanInv AsanTotal. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.UnpW.Spec Require Import AsanOK. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.Spec Require Import RSimProg. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.UnpW.Spec Require Import AsanHandoff. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.Spec Require Import Prog.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.UnpW.AsanW Require Import AImg AProto ATsafeCore. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.AsanW Require Import ATsafeEv. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.UnpW.AsanW Require Import ATsafeAlloc ATsafeOps ATsafeProg ATsafeMainGen.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.Common Require Import RunDraw.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.Spec Require ProgAC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section CANSEC1. Context {rc : runConstT}.
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition K0 : Z := 601040 + 31 * ((2^15 + 3) + (2^14 + 2)) + (2^8 + 2).          (* [comment removed for export] *)
Definition NMAXZ : Z := K0 + VMAX / 1024.
Definition NMAX : nat := Z.to_nat NMAXZ.

Lemma NMAX_Z : Z.of_nat NMAX = NMAXZ.
Proof. unfold NMAX. apply Z2Nat.id. vm_compute. discriminate. Qed.

(* [comment removed for export] *)
Definition win_pages (SB c : Z) : list word :=
  range_pages (shad (SB + c * K_REGION) - 4096) (shlen UWIN + 4096) ++ range_pages (shad (SB + c * K_REGION + K_FREEARR_OFF)) (shlen K_FREEARR_MAX).
Definition ash_pages (V : nat -> Z) : list word :=
  concat (map (win_pages (a_space_beg0 V)) CLASSES) ++ range_pages (shad (a_ptr_array0 V)) (shlen K_PTRARR_RESERVE).

(* [comment removed for export] *)
Definition Ahand (V : nat -> Z) : alw := fun p => bv_unsigned p mod 4096 = 0 /\ aallowed (allow_of ASHOFF V asan_vis) p.

Definition A0 (V : nat -> Z) : alw := aunion (Ahand V) (ash_pages V).

Theorem A0_init : forall V (p : word), bv_unsigned p mod 4096 = 0 -> aallowed (allow_of ASHOFF V asan_vis) p -> A0 V p.
Proof. intros V p Hal Ha. left. split; assumption. Qed.

(* [comment removed for export] *)
Lemma shad_div8_loc : forall a, shad a = 2147450880 + a / 8.          (* [comment removed for export] *)
Proof. intros. unfold shad, ASHOFF. rewrite Z.shiftr_div_pow2 by lia. reflexivity. Qed.
Lemma shad_region_lo : forall SB c, 0 <= shad SB -> 1 <= c -> 4096 <= shad (SB + c * K_REGION) - shad SB.
Proof.
  intros SB c Hs Hc. rewrite !shad_div8_loc.
  assert (SB / 8 + 4096 <= (SB + c * K_REGION) / 8); [| lia].
  replace (SB / 8 + 4096) with ((SB + 4096 * 8) / 8) by (rewrite Z.div_add by lia; reflexivity). apply Z.div_le_mono; [lia| unfold K_REGION; lia].
Qed.
Theorem A0_ashc : forall V c (p : word), bv_unsigned p mod 4096 = 0 -> 1 <= c < K_NUM_CLASSES ->
  shad (a_space_beg0 V + c * K_REGION) - 4096 <= bv_unsigned p < shad (a_space_beg0 V + c * K_REGION) + shlen UWIN ->
  0 <= shad (a_space_beg0 V) -> A0 V p.
Proof.
  intros V c p Hal Hc Hp Hs. right. unfold ash_pages. apply in_app_iff. left.
  apply in_concat. exists (win_pages (a_space_beg0 V) c). split; [apply in_map; apply In_CLASSES; unfold K_NUM_CLASSES in Hc; lia|].
  unfold win_pages. apply in_app_iff. left.
  pose proof (shad_region_lo (a_space_beg0 V) c Hs ltac:(lia)) as LO.
  rewrite <- (ATsafeAlloc.page_base_of_self 0%nat p Hal). apply range_pages_spec; lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma HLIM : NLK0 + Z.of_nat NMAX * 4096 <= HLIMIT.          (* [comment removed for export] *)
Proof. rewrite NMAX_Z. vm_compute. discriminate. Qed.

Lemma shlen_vals : shlen UWIN + 4096 = 2^27 + 4096 /\ shlen K_FREEARR_MAX = 2^26 /\ shlen K_PTRARR_RESERVE = 2^20.
Proof. repeat split; reflexivity. Qed.

Lemma win_pages_length : forall SB c, 0 <= shad SB -> 1 <= c -> 0 <= SB -> Z.of_nat (length (win_pages SB c)) <= (2^15 + 3) + (2^14 + 2).
Proof.
  intros SB c Hs Hc HSB0. unfold win_pages. rewrite length_app, Nat2Z.inj_add. pose proof shlen_vals as (E1 & E2 & _).
  pose proof (shad_region_lo SB c Hs Hc) as LO.
  pose proof (range_pages_length (shad (SB + c * K_REGION) - 4096) (shlen UWIN + 4096) ltac:(lia) ltac:(rewrite E1; lia)) as L1.
  assert (0 <= shad (SB + c * K_REGION + K_FREEARR_OFF)) as Hf.
  { rewrite shad_div8_loc. pose proof (Z.div_pos (SB + c * K_REGION + K_FREEARR_OFF) 8 ltac:(unfold K_REGION, K_FREEARR_OFF; lia) ltac:(lia)). lia. }
  pose proof (range_pages_length (shad (SB + c * K_REGION + K_FREEARR_OFF)) (shlen K_FREEARR_MAX) Hf ltac:(rewrite E2; lia)) as L2.
  rewrite E1, E2 in *. change ((2^27 + 4096) / 4096) with (2^15 + 1) in L1. change (2^26 / 4096) with (2^14) in L2. lia.
Qed.
Lemma concat_map_length_le : forall (f : Z -> list word) (B : Z) l, (forall c, In c l -> Z.of_nat (length (f c)) <= B) ->
  Z.of_nat (length (concat (map f l))) <= Z.of_nat (length l) * B.
Proof.
  intros f B. induction l as [|c l IH]; intros H; [cbn; lia|]. cbn [map concat length]. rewrite length_app, Nat2Z.inj_add, Nat2Z.inj_succ.
  pose proof (H c (or_introl eq_refl)). specialize (IH ltac:(intros c' Hc'; apply H; right; exact Hc')). lia.
Qed.

Section V.
  Variable V : nat -> Z.
  Hypothesis HP : Forall (pfact_ok V) asan_pure_facts.
  (* [comment removed for export] *)
  Hypothesis HAT : a_usp0 V - 8388608 = ATOP.
  Local Notation SB := (a_space_beg0 V).
  Local Notation PA := (a_ptr_array0 V).

  Lemma HSB : 0 <= SB /\ SB + K_SPACE_SIZE <= ATOP.
  Proof. pose proof (placement_facts V HP) as (H1 & H2 & H3 & H4 & H5 & H6 & H7). unfold a_space_beg0, K_SPACE_SIZE, PRIM_SZ, a_usp0 in *. lia. Qed.

  Lemma HPA : 0 <= PA /\ PA + K_PTRARR_RESERVE <= ATOP.
  Proof. pose proof (placement_facts V HP) as (H1 & H2 & H3 & H4 & H5 & H6 & H7). unfold a_ptr_array0, K_PTRARR_RESERVE, PTR_SZ, a_usp0 in *. lia. Qed.

  Lemma SB_al : SB mod 4096 = 0.
  Proof. pose proof (space_beg0_facts V HP) as (H1 & _). apply (Z.mod_divide _ 65536) in H1; [|lia]. destruct H1 as [q Hq]. rewrite Hq.
         replace (q * 65536) with ((q * 16) * 4096) by lia. apply Z.mod_mul. lia. Qed.

  Lemma PA_al : PA mod 4096 = 0.
  Proof. pose proof (space_beg0_facts V HP) as (_ & _ & H & _). exact H. Qed.

  Lemma region_al : forall c, (SB + c * K_REGION) mod 4096 = 0 /\ (SB + c * K_REGION + K_FREEARR_OFF) mod 4096 = 0.
  Proof.
    intros c. pose proof SB_al as A. split.
    - replace (c * K_REGION) with (c * 1048576 * 4096) by (unfold K_REGION; lia). rewrite Z_mod_plus_full. exact A.
    - replace (SB + c * K_REGION + K_FREEARR_OFF) with (SB + (c * 1048576 + 917504) * 4096) by (unfold K_REGION, K_FREEARR_OFF; lia). rewrite Z_mod_plus_full. exact A.
  Qed.

  Lemma ABASE_SH : forall z',
    ((exists c, 1 <= c <= 31 /\ shad (SB + c * K_REGION) <= z' < shad (SB + c * K_REGION + UWIN))
     \/ (exists c, 1 <= c <= 31 /\ shad (SB + c * K_REGION + K_FREEARR_OFF) <= z' < shad (SB + c * K_REGION + K_FREEARR_OFF + K_FREEARR_MAX))
     \/ shad PA <= z' < shad (PA + K_PTRARR_RESERVE)) -> A0 V (page_base_of z').
  Proof.
    intros z' Hz. right. unfold ash_pages. apply in_or_app.
    pose proof HSB as [S1 S2]. pose proof HPA as [P1 P2].
    pose proof (shad_bounds 0%nat SB ltac:(unfold K_SPACE_SIZE in *; lia)) as SH1.
    pose proof (shad_bounds 0%nat PA ltac:(unfold K_PTRARR_RESERVE in *; lia)) as SH2.
    destruct Hz as [(c & Hc & Hz)|[(c & Hc & Hz)|Hz]].
    - left. apply in_concat. exists (win_pages SB c). split; [apply in_map; apply In_CLASSES; exact Hc|]. unfold win_pages. apply in_or_app. left.
      pose proof (shad_region_lo SB c ltac:(lia) ltac:(lia)) as LO. rewrite (shad8 0%nat _ UWIN (proj1 (region_al c))) in Hz.
      apply range_pages_spec; lia.
    - left. apply in_concat. exists (win_pages SB c). split; [apply in_map; apply In_CLASSES; exact Hc|]. unfold win_pages. apply in_or_app. right.
      rewrite (shad8 0%nat _ K_FREEARR_MAX (proj2 (region_al c))) in Hz.
      apply range_pages_spec; [| lia]. rewrite shad_div8_loc.
      pose proof (Z.div_pos (SB + c * K_REGION + K_FREEARR_OFF) 8 ltac:(unfold K_REGION, K_FREEARR_OFF; lia) ltac:(lia)). lia.
    - right. apply range_pages_spec; try lia. rewrite (shad8 0%nat PA K_PTRARR_RESERVE PA_al) in Hz. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma A0_abud : forall sp fs mo, amodel V sp fs mo -> abud (A0 V) K0.
  Proof.
    intros sp fs mo HM. unfold A0, K0.
    pose proof HSB as [S1 S2]. pose proof HPA as [P1 P2]. pose proof shlen_vals as (_ & _ & E2).
    pose proof (shad_bounds 0%nat SB ltac:(unfold K_SPACE_SIZE in *; lia)) as SH1.
    pose proof (shad_bounds 0%nat PA ltac:(unfold K_PTRARR_RESERVE in *; lia)) as SH2.
    assert (HL : Z.of_nat (length (ash_pages V)) <= 31 * ((2^15 + 3) + (2^14 + 2)) + (2^8 + 2)).
    { unfold ash_pages. rewrite length_app, Nat2Z.inj_add.
      pose proof (concat_map_length_le (win_pages SB) ((2^15 + 3) + (2^14 + 2)) CLASSES
                    ltac:(intros c Hc; apply In_CLASSES in Hc; apply win_pages_length; lia)) as HW.
      replace (Z.of_nat (length CLASSES)) with 31 in HW by reflexivity.
      pose proof (range_pages_length (shad PA) (shlen K_PTRARR_RESERVE) ltac:(lia) ltac:(rewrite E2; lia)).
      rewrite E2 in *. change (2^20 / 4096) with (2^8) in *. lia. }
    apply (abud_mono _ (601040 + Z.of_nat (length (ash_pages V)))); [apply abud_union| lia].
    destruct (aallowed_fin (allow_of ASHOFF V asan_vis) (am_allow_wf _ _ _ _ HM)) as (L & ND & HLL & HIN).
    exists L. split; [exact ND|]. split; [| intros p [Hal Ha]; apply HIN; assumption].
    pose proof (am_abytes _ _ _ _ HM) as AB. unfold asan_abytes in AB. change MainEntry.ASHOFF with ASHOFF in AB.
    pose proof (Z.div_le_mono _ _ 4096 ltac:(lia) AB) as AB'. change (2461350400 / 4096) with 600915 in AB'. lia.   (* [comment removed for export] *)
  Qed.
End V.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Main.
  Variable V : nat -> Z.
  Hypothesis HP : Forall (pfact_ok V) asan_pure_facts.
  Hypothesis HAT : a_usp0 V - 8388608 = ATOP.
  Variable sp : word.                          (* [comment removed for export] *)
  Hypothesis HSP : atop_of sp = ATOP.
  Local Notation SB := (a_space_beg0 V).
  Local Notation PA := (a_ptr_array0 V).

  (* [comment removed for export] *)
  Theorem progA_tsafe : forall rs inp mo, amodel V sp (in_fs inp) mo ->
    tsafeA nstepA (nsafeA NMAX) fstepS NMAX (fp_ok (m_vm_lazy (MX mo [])) (A0 V)) (A0 V)
           (progA_tree AAllocAsan (aps_init SB PA (resv_of V) (atop_of sp)) rs (argv_Z (in_argv inp))) (MX mo []).
  Proof.
    intros rs inp mo HM. destruct (AI_init V sp (in_fs inp) mo HM HP) as (HAI & _).
    apply (progA_tsafe_gen NMAX SB PA (A0 V) K0 HLIM (ABASE_SH V HP HAT) (HSB V HP HAT) (HPA V HP HAT)).
    - split; [unfold K0; lia|]. rewrite NMAX_Z. unfold NMAXZ. lia.
    - eapply A0_abud; [exact HP| exact HAT| exact HM].
    - exact HAI.
    - exact HSP.
    - reflexivity.
    - reflexivity.
    - unfold QOK. cbn [aps_m aps_init]. rewrite all_chunks_ainit. constructor.
    - cbn [aps_m aps_init]. rewrite acost_ainit. lia.
  Qed.

  (* [comment removed for export] *)
  Theorem progA_tsafeD : forall D rs inp mo, amodel V sp (in_fs inp) mo ->
    tsafeA nstepA (nsafeA NMAX) fstepS NMAX (fp_ok (m_vm_lazy (MX mo [])) (A0 V)) (A0 V)
           (ProgAC.progA_treeD AAllocAsan D (aps_init SB PA (resv_of V) (atop_of sp)) rs (argv_Z (in_argv inp))) (MX mo []).
  Proof.
    intros D rs inp mo HM. destruct (AI_init V sp (in_fs inp) mo HM HP) as (HAI & _).
    apply (progA_tsafe_genD NMAX SB PA (A0 V) K0 HLIM (ABASE_SH V HP HAT) (HSB V HP HAT) (HPA V HP HAT)).
    - split; [unfold K0; lia|]. rewrite NMAX_Z. unfold NMAXZ. lia.
    - eapply A0_abud; [exact HP| exact HAT| exact HM].
    - exact HAI.
    - exact HSP.
    - reflexivity.
    - reflexivity.
    - unfold QOK. cbn [aps_m aps_init]. rewrite all_chunks_ainit. constructor.
    - cbn [aps_m aps_init]. rewrite acost_ainit. lia.
  Qed.
End Main.

(* [comment removed for export] *)
Corollary progA_tsafe_open : forall rs V sp inp mo,
  Forall (pfact_ok V) asan_pure_facts -> a_usp0 V - 8388608 = ATOP -> atop_of sp = ATOP -> amodel V sp (in_fs inp) mo ->
  tsafeA nstepA (nsafeA NMAX) fstepS NMAX (fp_ok (m_vm_lazy (MX mo [])) (A0 V)) (A0 V)
         (progA_tree AAllocAsan (aps_init (a_space_beg0 V) (a_ptr_array0 V) (resv_of V) (atop_of sp)) rs (argv_Z (in_argv inp))) (MX mo []).
Proof. intros rs V sp inp mo HP HAT HSP HM. exact (progA_tsafe V HP HAT sp HSP rs inp mo HM). Qed.
End CANSEC1.
