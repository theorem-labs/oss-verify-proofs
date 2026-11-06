(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Lia.
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Sem.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Tac Arr Bytes ZBridge ITree Nodes Decode SysStep.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Prelim Monad PcapPrelim PcapTypes Pcap Prog.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require ExecF ITreeA Shadow StepF RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg ABase RtCells AMalloc_iface.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require GIA PcapRepA UnwKit.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadGX__A3P.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require Pcap_ifaceA LibcKit.
From LinuxProcessSemantics.Riscv Require Instr Decode DecodeC Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Frame StoreFast.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Fmt StdioCore Stdio PcapPure.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_kit__Musl.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require SysStepF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require CkTac__A3P.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadG.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
From Stdlib Require String.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require Pcap_iface_ngA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Module FrameKit.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr Bytes ZBridge ITree Nodes Decode SysStep.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import Prelim Monad PcapPrelim PcapTypes Pcap Prog.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import ExecF ITreeA Shadow StepF RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import AImg ABase RtCells AMalloc_iface.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require GIA PcapRepA UnwKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadGX__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require Pcap_ifaceA LibcKit. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LibcKit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Lemma shad_shiftr : forall a, Z.shiftr a 3 + 2147450880 = shad a.
Proof. intros a. unfold shad, ASHOFF. lia. Qed.

(* [comment removed for export] *)
Ltac neg_lits :=
  repeat match goal with
  | |- context [Z_to_bv 64 (Zneg ?p)] =>
      let v := eval vm_compute in (18446744073709551616 + Zneg p) in
      replace (Z_to_bv 64 (Zneg p)) with (Z_to_bv 64 v) by (apply Z_to_bv_eqm; reflexivity)
  end.

(* [comment removed for export] *)
Ltac shr_consts :=
  repeat match goal with
  | |- context [Z.shiftr (Zpos ?p) 3] => let v := eval vm_compute in (Z.shiftr (Zpos p) 3) in change (Z.shiftr (Zpos p) 3) with v
  end.

Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="Type"] Lemma cells_wf_repeat_C1 : forall b n, cells_wf (repeat (C1 b) n).
Proof. intros b n. induction n; cbn; [exact I| split; [exact I| exact IHn]]. Qed.
#[using="Type"] Lemma cells_bytes_repeat_C1 : forall b n, cells_bytes (repeat (C1 b) n) = repeat b n.
Proof. intros b n. induction n; cbn; [reflexivity| rewrite IHn; reflexivity]. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma sh_zero_cells : forall m S n,
  rw_cells asegs m S [CB n (repeat (Z_to_bv 8 0) n)] -> rw_cells asegs m S (repeat (C1 (Z_to_bv 8 0)) n).
Proof.
  intros m S n HC. eapply rw_cells_recell; [exact HC| apply cells_wf_repeat_C1|].
  rewrite cells_bytes_repeat_C1. cbn [cells_bytes cbytes]. rewrite app_nil_r. reflexivity.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma unp_of_zero_cells : forall m p (k : nat) cs,
  rw_cells asegs m (Z.shiftr p 3 + 2147450880) cs -> cells_bytes cs = repeat (Z_to_bv 8 0) k ->
  p mod 8 = 0 -> 0 <= p -> p + 8 * Z.of_nat k <= 2^64 ->
  unpoisoned m p (p + 8 * Z.of_nat k).
Proof.
  intros m p k cs HC HB P8 P0 PT. apply shadow_block_unpoisoned.
  assert (EM : (8 * Z.of_nat k) mod 8 = 0) by (rewrite Z.mul_comm, Z_mod_mult; reflexivity).
  apply (shadow_block_of_memset0 asegs); try lia.
  - apply no_image_asan. rewrite shad_div. unfold ASHOFF. Z.div_mod_to_equations. lia.
  - replace (8 * Z.of_nat k / 8) with (Z.of_nat k) by (rewrite Z.mul_comm, Z_div_mult by lia; reflexivity).
    rewrite Nat2Z.id. rewrite <- shad_shiftr.
    eapply rw_cells_recell; [exact HC| cbn; split; [apply repeat_length| exact I]|].
    cbn [cells_bytes cbytes]. rewrite app_nil_r. symmetry. exact HB.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma unp_of_part_cells : forall m p (k : nat) r cs,
  rw_cells asegs m (Z.shiftr p 3 + 2147450880) cs -> cells_bytes cs = repeat (Z_to_bv 8 0) k ++ [Z_to_bv 8 r] ->
  1 <= r <= 7 -> p mod 8 = 0 -> 0 <= p -> p + 8 * Z.of_nat k + 8 <= 2^64 ->
  unpoisoned m p (p + (8 * Z.of_nat k + r)).
Proof.
  intros m p k r cs HC HB HR P8 P0 PT. apply shadow_block_unpoisoned.
  assert (E8 : (8 * Z.of_nat k + r) / 8 = Z.of_nat k) by (Z.div_mod_to_equations; lia).
  assert (EM : (8 * Z.of_nat k + r) mod 8 = r) by (Z.div_mod_to_equations; lia).
  apply (shadow_block_of_memset0_partial asegs m p (8 * Z.of_nat k + r) r); try lia.
  - rewrite E8. apply no_image_asan. rewrite shad_div. unfold ASHOFF. Z.div_mod_to_equations. lia.
  - rewrite E8, Nat2Z.id, <- shad_shiftr.
    eapply rw_cells_recell; [exact HC| cbn; split; [apply repeat_length| split; exact I]|].
    cbn [cells_bytes cbytes]. rewrite HB. reflexivity.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma shiftr3_add : forall F i, F mod 8 = 0 -> Z.shiftr (F + 8 * i) 3 = Z.shiftr F 3 + i.
Proof. intros F i H8. rewrite !Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8. Z.div_mod_to_equations. lia. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma unp_of_sh_bytes : forall m F cs (i k : nat),
  rw_cells asegs m (Z.shiftr F 3 + 2147450880) cs -> F mod 8 = 0 -> 0 <= F -> F + 8 * Z.of_nat (cells_size cs) <= 2^64 ->
  firstn k (skipn i (cells_bytes cs)) = repeat (Z_to_bv 8 0) k -> (i + k <= cells_size cs)%nat ->
  unpoisoned m (F + 8 * Z.of_nat i) (F + 8 * Z.of_nat i + 8 * Z.of_nat k).
Proof.
  intros m F cs i k HC F8 F0 FT HB HL.
  pose proof HC as [[WF _] _]. pose proof (cells_bytes_length cs WF) as LB.
  pose proof (rw_cells_merge asegs m _ [] cs [] ltac:(rewrite app_nil_r; exact HC)) as M. cbn [app] in M.
  apply (rw_cells_split_CB asegs _ _ [] _ _ [] [i; k; (cells_size cs - i - k)%nat]) in M; [|cbn; lia].
  cbn [app mk_CB_cells] in M. rewrite ?app_nil_r in M.
  destruct (rw_cells_cut _ _ _ 1 M) as [_ M1]. cbn [firstn skipn cells_size csize Nat.add] in M1.
  destruct (rw_cells_cut _ _ _ 1 M1) as [M2 _]. cbn [firstn skipn cells_size csize Nat.add] in M2.
  rewrite HB in M2. rewrite Nat.add_0_r in M2.
  eapply unp_of_zero_cells; [| | | |].
  - rewrite shiftr3_add by exact F8. replace (Z.shiftr F 3 + Z.of_nat i + 2147450880) with (Z.shiftr F 3 + 2147450880 + Z.of_nat i) by lia. exact M2.
  - cbn [cells_bytes cbytes]. rewrite app_nil_r. reflexivity.
  - rewrite Z.add_mod, F8 by lia. rewrite Z.mul_comm, Z_mod_mult. reflexivity.
  - lia.
  - lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma unp_of_sh_part : forall m F cs (i k : nat) r,
  rw_cells asegs m (Z.shiftr F 3 + 2147450880) cs -> F mod 8 = 0 -> 0 <= F -> F + 8 * Z.of_nat (cells_size cs) <= 2^64 ->
  firstn (k + 1) (skipn i (cells_bytes cs)) = repeat (Z_to_bv 8 0) k ++ [Z_to_bv 8 r] -> (i + k + 1 <= cells_size cs)%nat -> 1 <= r <= 7 ->
  unpoisoned m (F + 8 * Z.of_nat i) (F + 8 * Z.of_nat i + (8 * Z.of_nat k + r)).
Proof.
  intros m F cs i k r HC F8 F0 FT HB HL HR.
  pose proof HC as [[WF _] _]. pose proof (cells_bytes_length cs WF) as LB.
  pose proof (rw_cells_merge asegs m _ [] cs [] ltac:(rewrite app_nil_r; exact HC)) as M. cbn [app] in M.
  apply (rw_cells_split_CB asegs _ _ [] _ _ [] [i; (k + 1)%nat; (cells_size cs - i - (k + 1))%nat]) in M; [|cbn; lia].
  cbn [app mk_CB_cells] in M. rewrite ?app_nil_r in M.
  destruct (rw_cells_cut _ _ _ 1 M) as [_ M1]. cbn [firstn skipn cells_size csize Nat.add] in M1.
  destruct (rw_cells_cut _ _ _ 1 M1) as [M2 _]. cbn [firstn skipn cells_size csize Nat.add] in M2.
  rewrite HB in M2. rewrite Nat.add_0_r in M2.
  eapply unp_of_part_cells; [| | exact HR | | |].
  - rewrite shiftr3_add by exact F8. replace (Z.shiftr F 3 + Z.of_nat i + 2147450880) with (Z.shiftr F 3 + 2147450880 + Z.of_nat i) by lia. exact M2.
  - cbn [cells_bytes cbytes]. rewrite app_nil_r. reflexivity.
  - rewrite Z.add_mod, F8 by lia. rewrite Z.mul_comm, Z_mod_mult. reflexivity.
  - lia.
  - lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma rw_cells_nth_C8 : forall m A cs (k : nat) v,
  rw_cells asegs m A cs -> nth_error cs k = Some (C8 v) -> bytes_at asegs m (A + Z.of_nat (cells_size (firstn k cs))) (le8 v).
Proof.
  intros m A cs k v HC HN. destruct (rw_cells_cut _ _ _ k HC) as [_ H2].
  assert (E : skipn k cs = C8 v :: skipn (S k) cs).
  { clear - HN. revert k HN. induction cs as [|c cs IH]; intros [|k] HN; cbn in *; try discriminate; [injection HN as ->; reflexivity| apply IH; exact HN]. }
  rewrite E in H2. destruct (rw_cells_cut _ _ _ 1 H2) as [H3 _]. cbn [firstn] in H3.
  apply rw_cells_bytes_at in H3. cbn [cells_bytes cbytes] in H3. rewrite app_nil_r in H3. exact H3.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Objs.
  Context {hptr : Type}.
  Notation cblk := (@cblock hptr).

  #[using="Type"] Lemma clocA_incl : forall FL FL' (CL CL' : list cblk) A n,
    clocA FL CL A n -> incl CL CL' -> incl FL FL' -> clocA FL' CL' A n.
  Proof.
    intros FL FL' CL CL' A n [(b & Hb & H1)|(fr & Hf & H1)] IC IF; [left; exists b | right; exists fr]; (split; [auto| exact H1]).
  Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma clocA_iv : forall FL (CL : list cblk) A n, clocA FL CL A n -> client_ivA FL CL (A, A + n).
  Proof.
    intros FL CL A n [(b & Hb & H1 & H2)|(fr & Hf & H1 & H2)]; unfold client_ivA.
    - right; left. unfold iv_in_block. apply Exists_exists. exists b. split; [exact Hb| cbn [fst snd]; lia].
    - right; right; left. unfold iv_in_frames. apply Exists_exists. exists fr. split; [exact Hf| cbn [fst snd]; lia].
  Qed.

  #[using="Type"] Lemma blockA_aobj : forall RNG m (b : cblk) A n,
    blockA RNG m b -> cb_addr b <= A -> A + n <= cb_addr b + cb_size b -> 0 <= n -> aobjA RNG m A n.
  Proof.
    intros RNG m b A n ((BAND & N0 & TOP & AL) & P0 & UNP & RB & RSH & AR) H1 H2 Hn. atop_facts.
    split; [lia|]. split; [lia|]. split; [eapply unpoisoned_sub; [exact UNP| lia| lia]|].
    split; [eapply rng_sub; [exact RB| lia| lia]|].
    split; [| split; [eapply arenaA_sub; [exact AR| lia| lia]| eapply ablk_sub; [exact BAND| lia| lia]]].
    eapply rng_sub'; [exact RSH|]. rewrite !shad_div, !nshad_div. Z.div_mod_to_equations. lia.
  Qed.

  #[using="Type"] Lemma frameA_aobj : forall RNG m fr A n,
    frameA RNG m fr -> fb_addr fr <= A -> A + n <= fb_addr fr + fb_size fr -> 0 <= n -> unpoisoned m A (A + n) -> aobjA RNG m A n.
  Proof.
    intros RNG m fr A n (BAND & TOP & A64 & N64 & RF & RSF & S64 & WSF) H1 H2 Hn UNP. atop_facts.
    pose proof (ablk_lin _ _ BAND) as (IMG & F0 & _ & T47). unfold AIMG_HI in IMG.
    rewrite !Z.shiftr_div_pow2 in RSF, WSF by lia. change (2 ^ 3) with 8 in RSF, WSF.
    split; [lia|]. split; [lia|]. split; [exact UNP|].
    split; [eapply rng_sub; [exact RF| lia| lia]|]. split.
    - eapply rng_sub'; [exact RSF|]. rewrite !shad_div, !nshad_div. unfold ASHOFF. Z.div_mod_to_equations. lia.
    - split; [| eapply ablk_sub; [exact BAND| lia| lia]].
      exists (fb_addr fr), (fb_addr fr + fb_size fr). split; [lia|]. split; [lia|]. split; [exact A64|].
      split; [rewrite Z.add_mod, A64, S64 by lia; reflexivity|]. split; [lia|]. split; [unfold KEND; lia|].
      assert (E : shad (fb_addr fr + fb_size fr) - shad (fb_addr fr) = fb_size fr / 8)
        by (rewrite !shad_div; Z.div_mod_to_equations; lia).
      rewrite E, shad_div. unfold ASHOFF. rewrite Z.add_comm. split; [exact WSF| exact RSF].
  Qed.
End Objs.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Cobj.
  Context {H hptr : Type} (FO : @FrameOps H hptr).
  Variable GIOA : alayout -> footprint -> PState H hptr -> list (@cblock hptr) -> list (@cblock hptr) -> list fblock -> mem -> Prop.
  Variable fflagA : alayout -> fframe -> Z -> Z.
  Hypothesis GL : gia_laws FO GIOA fflagA.

  #[using="tlsI FO fflagA GL"] Lemma clocA_below : forall L RNG s CL FB FL m A n,
    GIOA L RNG s CL FB FL m -> clocA FL CL A n -> 0x603000 <= A /\ A + n <= ATOP.
  Proof.
    intros L RNG s CL FB FL m A n G [(b & Hb & H1 & H2)|(fr & Hf & H1 & H2)].
    - destruct (gl_block _ _ _ GL _ _ _ _ _ _ _ b G ltac:(apply in_or_app; left; exact Hb)) as ((BAND & _ & TOP & _) & _).
      pose proof (ablk_lin _ _ BAND) as (IMG & _). unfold AIMG_HI in IMG. lia.
    - destruct (gl_frames _ _ _ GL _ _ _ _ _ _ _ G) as [FA _]. pose proof (proj1 (Forall_forall _ _) FA fr Hf) as (BAND & TOP & _).
      pose proof (ablk_lin _ _ BAND) as (IMG & _). unfold AIMG_HI in IMG. lia.
  Qed.

  (* [comment removed for export] *)
  #[using="tlsI FO fflagA GL"] Lemma clocA_ablk : forall L RNG s CL FB FL m A n,
    GIOA L RNG s CL FB FL m -> clocA FL CL A n -> 0 <= n -> ablk A (A + n).
  Proof.
    intros L RNG s CL FB FL m A n G [(b & Hb & H1 & H2)|(fr & Hf & H1 & H2)] Hn.
    - destruct (gl_block _ _ _ GL _ _ _ _ _ _ _ b G ltac:(apply in_or_app; left; exact Hb)) as ((BAND & _) & _).
      eapply ablk_sub; [exact BAND| lia| lia].
    - destruct (gl_frames _ _ _ GL _ _ _ _ _ _ _ G) as [FA _]. pose proof (proj1 (Forall_forall _ _) FA fr Hf) as (BAND & _).
      eapply ablk_sub; [exact BAND| lia| lia].
  Qed.

  (* [comment removed for export] *)
  #[using="rc tlsI FO fflagA GL"] Lemma clocA_apart_frame : forall L RNG s CL FB FL m fr A n,
    GIOA L RNG s CL FB (fr :: FL) m -> clocA FL CL A n -> 0 < n ->
    exists k, 0 <= k <= 1 /\ A + n <= fb_addr fr + k * 18446744073709551616 /\ fb_addr fr + fb_size fr <= A + (1 - k) * 18446744073709551616.
  Proof.
    intros L RNG s CL FB FL m fr A n G LOC Hn.
    destruct (gl_frames _ _ _ GL _ _ _ _ _ _ _ G) as [FA ND].
    pose proof (Forall_inv FA) as (BAND & TOP & _ & N64 & _). pose proof (ablk_lin _ _ BAND) as (_ & F0 & _ & T47).
    assert (D : A + n <= fb_addr fr \/ fb_addr fr + fb_size fr <= A).
    { destruct LOC as [(b & Hb & H1 & H2)|(fr' & Hf & H1 & H2)].
      - destruct (Z_le_gt_dec (A + n) (fb_addr fr)) as [?|G1]; [left; assumption|].
        destruct (Z_le_gt_dec (fb_addr fr + fb_size fr) A) as [?|G2]; [right; assumption|]. exfalso.
        apply (gl_fr_apart _ _ _ GL _ _ _ _ _ _ _ (Z.max A (fb_addr fr)) G).
        + apply in_frames_In. exists fr. split; [left; reflexivity| lia].
        + apply in_block_app. left. apply in_block_In. exists b. split; [exact Hb| lia].
      - assert (NE : fb_fn fr' <> fb_fn fr).
        { cbn [map] in ND. apply List.NoDup_cons_iff in ND as [NI _]. intros E. apply NI. rewrite <- E. apply in_map. exact Hf. }
        pose proof (proj1 (Forall_forall _ _) FA fr' (or_intror Hf)) as (BAND' & _ & _ & N64' & _).
        destruct (gl_fr_disj _ _ _ GL _ _ _ _ _ _ _ fr' fr G (or_intror Hf) (or_introl eq_refl) NE) as [D|D]; [left; lia| right; lia]. }
    pose proof (clocA_below _ _ _ _ _ _ _ _ _ G (clocA_incl _ _ _ _ _ _ LOC (incl_refl _) (incl_tl _ (incl_refl _)))) as (ALO & AHI).
    atop_facts. destruct D; [exists 0 | exists 1]; lia.
  Qed.

  (* [comment removed for export] *)
  #[using="rc tlsI FO fflagA GL"] Lemma clocA_apart_block : forall L RNG s CLc PB FB FL m (b : @cblock hptr) A n,
    GIOA L RNG s (CLc ++ PB) FB FL m -> clocA FL CLc A n -> In b PB -> 0 < n -> 0 < cb_size b ->
    exists k, 0 <= k <= 1 /\ A + n <= cb_addr b + k * 18446744073709551616 /\ cb_addr b + cb_size b <= A + (1 - k) * 18446744073709551616.
  Proof.
    intros L RNG s CLc PB FB FL m b A n G LOC Hb Hn Hs.
    assert (HbA : In b ((CLc ++ PB) ++ FB)) by (apply in_or_app; left; apply in_or_app; right; exact Hb).
    destruct (gl_block _ _ _ GL _ _ _ _ _ _ _ b G HbA) as ((BAND & _ & TOP & _) & B0 & _).
    assert (D : A + n <= cb_addr b \/ cb_addr b + cb_size b <= A).
    { destruct LOC as [(b0 & Hb0 & H1 & H2)|(fr & Hf & H1 & H2)].
      - pose proof (gl_apart _ _ _ GL _ _ _ _ _ _ _ G) as BA. apply blocks_apart_app_inv in BA as (BA & _ & _).
        apply blocks_apart_app_inv in BA as (_ & _ & BX). specialize (BX b0 b Hb0 Hb). unfold apart in BX. lia.
      - destruct (Z_le_gt_dec (A + n) (cb_addr b)) as [?|G1]; [left; assumption|].
        destruct (Z_le_gt_dec (cb_addr b + cb_size b) A) as [?|G2]; [right; assumption|]. exfalso.
        apply (gl_fr_apart _ _ _ GL _ _ _ _ _ _ _ (Z.max A (cb_addr b)) G).
        + apply in_frames_In. exists fr. split; [exact Hf| lia].
        + apply in_block_In. exists b. split; [exact HbA| lia]. }
    pose proof (clocA_below _ _ _ _ _ _ _ _ _ G (clocA_incl _ _ _ _ _ _ LOC (incl_appl _ (incl_refl _)) (incl_refl _))) as (ALO & AHI).
    atop_facts. destruct D; [exists 0 | exists 1]; lia.
  Qed.

  (* [comment removed for export] *)
  #[using="rc tlsI FO fflagA GL"] Lemma PB_apartA : forall L RNG s CLc PB FB FL m (p : PcapTypes.pcap hptr hptr) P B I,
    GIOA L RNG s (CLc ++ PB) FB FL m -> PB = pcap_blocks p P B I ->
    (P + psize p <= B \/ B + pc_bufalloc p <= P)
    /\ (forall sg q, pc_priv p = PrivNg sg (Some q) ->
          (P + psize p <= I \/ I + 40 * ng_ifaces_size sg <= P) /\ (B + pc_bufalloc p <= I \/ I + 40 * ng_ifaces_size sg <= B)).
  Proof.
    intros L RNG s CLc PB FB FL m p P B I G EPB.
    pose proof (gl_apart _ _ _ GL _ _ _ _ _ _ _ G) as BA.
    apply blocks_apart_app_inv in BA as (BA & _ & _). apply blocks_apart_app_inv in BA as (_ & BA & _).
    rewrite EPB in BA. unfold pcap_blocks in BA. cbn [blocks_apart] in BA.
    destruct BA as (F1 & F2 & _). pose proof (Forall_inv F1) as A12. apply Forall_inv_tail in F1.
    unfold apart, cb_addr, cb_size in A12; cbn [fst snd] in A12. split; [lia|].
    intros sg q Hq. rewrite Hq in F1, F2. pose proof (Forall_inv F1) as A13. pose proof (Forall_inv F2) as A23.
    unfold apart, cb_addr, cb_size in A13, A23; cbn [fst snd] in A13, A23. lia.
  Qed.

  (* [comment removed for export] *)
  #[using="rc tlsI FO fflagA GL"] Lemma block_apart_frame : forall L RNG s CL FB FL m (b : @cblock hptr) fr,
    GIOA L RNG s CL FB FL m -> In b (CL ++ FB) -> In fr FL -> 0 < cb_size b ->
    exists k, 0 <= k <= 1 /\ cb_addr b + cb_size b <= fb_addr fr + k * 18446744073709551616
              /\ fb_addr fr + fb_size fr <= cb_addr b + (1 - k) * 18446744073709551616.
  Proof.
    intros L RNG s CL FB FL m b fr G Hb Hf Hs.
    destruct (gl_block _ _ _ GL _ _ _ _ _ _ _ b G Hb) as ((BAND & _ & TOP & _) & B0 & _).
    destruct (gl_frames _ _ _ GL _ _ _ _ _ _ _ G) as [FA _]. pose proof (proj1 (Forall_forall _ _) FA fr Hf) as (FBAND & FTOP & _ & N64 & _).
    pose proof (ablk_lin _ _ FBAND) as (_ & F0 & _ & T47). atop_facts.
    assert (D : cb_addr b + cb_size b <= fb_addr fr \/ fb_addr fr + fb_size fr <= cb_addr b).
    { destruct (Z_le_gt_dec (cb_addr b + cb_size b) (fb_addr fr)) as [?|G1]; [left; assumption|].
      destruct (Z_le_gt_dec (fb_addr fr + fb_size fr) (cb_addr b)) as [?|G2]; [right; assumption|]. exfalso.
      apply (gl_fr_apart _ _ _ GL _ _ _ _ _ _ _ (Z.max (cb_addr b) (fb_addr fr)) G).
      - apply in_frames_In. exists fr. split; [exact Hf| lia].
      - apply in_block_In. exists b. split; [exact Hb| lia]. }
    destruct D; [exists 0 | exists 1]; lia.
  Qed.

  (* [comment removed for export] *)
  #[using="tlsI FO fflagA GL"] Lemma keeps_not_own_frame : forall L RNG s CL FB FL m fr (CLc : list (@cblock hptr)) SP a,
    GIOA L RNG s CL FB (fr :: FL) m -> incl CLc CL -> ATOP <= SP -> client_keeps FL CLc SP a ->
    ~ (fb_addr fr <= a < fb_addr fr + fb_size fr)
    /\ ~ (Z.shiftr (fb_addr fr) 3 + 2147450880 <= a < Z.shiftr (fb_addr fr) 3 + 2147450880 + Z.shiftr (fb_size fr) 3).
  Proof.
    intros L RNG s CL FB FL m fr CLc SP a G IC HSP K.
    destruct (gl_frames _ _ _ GL _ _ _ _ _ _ _ G) as [FA ND]. pose proof (Forall_inv FA) as (BAND & TOP & A64 & N64 & _ & _ & S64 & _).
    assert (INF : forall x, fb_addr fr <= x < fb_addr fr + fb_size fr -> in_frames (fr :: FL) x)
      by (intros x Hx; apply in_frames_In; exists fr; split; [left; reflexivity| exact Hx]).
    assert (INS : forall x, Z.shiftr (fb_addr fr) 3 + 2147450880 <= x < Z.shiftr (fb_addr fr) 3 + 2147450880 + Z.shiftr (fb_size fr) 3 -> in_frame_sh (fr :: FL) x)
      by (intros x Hx; apply in_frame_sh_In; exists fr; split; [left; reflexivity| exact Hx]).
    destruct K as [K|[K|[K|K]]].
    - split; intros Hin.
      + pose proof (gia_in_frames_below _ _ _ GL _ _ _ _ _ _ _ a G (INF a Hin)). lia.
      + pose proof (gia_in_frame_sh_band _ _ _ GL _ _ _ _ _ _ _ a G (INS a Hin)). atop_facts. lia.
    - assert (KB : in_block (CL ++ FB) a).
      { apply in_block_app. left. apply in_block_In in K as (b & Hb & Hr). apply in_block_In. exists b. split; [apply IC; exact Hb| exact Hr]. }
      split; intros Hin.
      + exact (gl_fr_apart _ _ _ GL _ _ _ _ _ _ _ a G (INF a Hin) KB).
      + pose proof (gia_in_frame_sh_band _ _ _ GL _ _ _ _ _ _ _ a G (INS a Hin)) as BD.
        apply in_block_In in KB as (b & Hb & Hr). destruct (gl_block _ _ _ GL _ _ _ _ _ _ _ b G Hb) as ((BB & _) & _).
        exact (ablk_clear_band _ _ a BB ltac:(unfold KLS; lia) Hr).
    - apply in_frames_In in K as (fr' & Hf' & Hr').
      assert (NE : fb_fn fr' <> fb_fn fr).
      { cbn [map] in ND. apply List.NoDup_cons_iff in ND as [NI _]. intros E. apply NI. rewrite <- E. apply in_map. exact Hf'. }
      pose proof (proj1 (Forall_forall _ _) FA fr' (or_intror Hf')) as (BAND' & _).
      split; intros Hin.
      + destruct (gl_fr_disj _ _ _ GL _ _ _ _ _ _ _ fr' fr G (or_intror Hf') (or_introl eq_refl) NE) as [D|D]; lia.
      + pose proof (gia_in_frame_sh_band _ _ _ GL _ _ _ _ _ _ _ a G (INS a Hin)) as BD.
        exact (ablk_clear_band _ _ a BAND' ltac:(unfold KLS; lia) Hr').
    - pose proof (gia_in_frame_sh_band _ _ _ GL _ _ _ _ _ _ _ a G (in_frame_sh_cons _ _ _ K)) as BD.
      split; intros Hin.
      + exact (ablk_clear_band _ _ a BAND ltac:(unfold KLS; lia) Hin).
      + (* [comment removed for export] *)
        apply in_frame_sh_In in K as (fr' & Hf' & Hr').
        assert (NE : fb_fn fr' <> fb_fn fr).
        { cbn [map] in ND. apply List.NoDup_cons_iff in ND as [NI _]. intros E. apply NI. rewrite <- E. apply in_map. exact Hf'. }
        pose proof (proj1 (Forall_forall _ _) FA fr' (or_intror Hf')) as (BAND' & _ & A64' & N64' & _ & _ & S64' & _).
        pose proof (ablk_lin _ _ BAND) as (_ & F0 & _). pose proof (ablk_lin _ _ BAND') as (_ & F0' & _).
        rewrite !Z.shiftr_div_pow2 in Hin, Hr' by lia. change (2 ^ 3) with 8 in Hin, Hr'.
        destruct (gl_fr_disj _ _ _ GL _ _ _ _ _ _ _ fr' fr G (or_intror Hf') (or_introl eq_refl) NE) as [D|D]; Z.div_mod_to_equations; lia.
  Qed.

  (* [comment removed for export] *)
  #[using="tlsI FO GL"] Lemma flag_facts : forall L RNG s CL FB FL m f Fb n,
    GIOA L RNG s CL FB ((f, Fb, n) :: FL) m ->
    rw_cells asegs m (fflagA L f Fb) [C1 (Z_to_bv 8 1)] /\ rng RNG (fflagA L f Fb) 1 /\ ablk (fflagA L f Fb) (fflagA L f Fb + 1)
    /\ fflagA L f Fb + 1 <= ATOP /\ ~ in_block (CL ++ FB) (fflagA L f Fb)
    /\ exists k, 0 <= k <= 1 /\ fflagA L f Fb + 1 <= Fb + k * 18446744073709551616 /\ Fb + n <= fflagA L f Fb + (1 - k) * 18446744073709551616.
  Proof.
    intros L RNG s CL FB FL m f Fb n G.
    destruct (gl_flag _ _ _ GL _ _ _ _ _ _ _ f Fb n G (or_introl eq_refl)) as (C & R & B & T & NB & NF).
    split; [exact C|]. split; [exact R|]. split; [exact B|]. split; [exact T|]. split; [exact NB|].
    destruct (gl_frames _ _ _ GL _ _ _ _ _ _ _ G) as [FA _]. pose proof (Forall_inv FA) as (BAND & TOP & _). cbn [fb_addr fb_size fst snd] in BAND, TOP.
    pose proof (ablk_lin _ _ BAND) as (_ & F0 & _ & T47). pose proof (ablk_lin _ _ B) as (_ & G0 & _ & G47). atop_facts.
    assert (D : fflagA L f Fb + 1 <= Fb \/ Fb + n <= fflagA L f Fb).
    { destruct (Z_le_gt_dec (fflagA L f Fb + 1) Fb) as [?|G1]; [left; assumption|].
      destruct (Z_le_gt_dec (Fb + n) (fflagA L f Fb)) as [?|G2]; [right; assumption|]. exfalso. apply NF.
      apply in_frames_In. exists (f, Fb, n). split; [left; reflexivity| cbn [fb_addr fb_size fst snd]; lia]. }
    destruct D; [exists 0 | exists 1]; lia.
  Qed.
  #[using="rc tlsI FO GL"] Lemma flag_apart_cloc : forall L RNG s CL FB FL m f Fb n FLc CLc A k,
    GIOA L RNG s CL FB ((f, Fb, n) :: FL) m -> clocA FLc CLc A k -> incl CLc CL -> incl FLc ((f, Fb, n) :: FL) -> 0 < k ->
    exists i, 0 <= i <= 1 /\ fflagA L f Fb + 1 <= A + i * 18446744073709551616 /\ A + k <= fflagA L f Fb + (1 - i) * 18446744073709551616.
  Proof.
    intros L RNG s CL FB FL m f Fb n FLc CLc A k G LOC IC IF Hk.
    destruct (gl_flag _ _ _ GL _ _ _ _ _ _ _ f Fb n G (or_introl eq_refl)) as (C & R & B & T & NB & NF).
    pose proof (clocA_below _ _ _ _ _ _ _ _ _ G (clocA_incl _ _ _ _ _ _ LOC IC IF)) as (ALO & AHI).
    pose proof (ablk_lin _ _ B) as (_ & G0 & _ & G47). atop_facts.
    assert (D : fflagA L f Fb + 1 <= A \/ A + k <= fflagA L f Fb).
    { destruct (Z_le_gt_dec (fflagA L f Fb + 1) A) as [?|G1]; [left; assumption|].
      destruct (Z_le_gt_dec (A + k) (fflagA L f Fb)) as [?|G2]; [right; assumption|]. exfalso.
      destruct LOC as [(b & Hb & H1 & H2)|(fr & Hf & H1 & H2)].
      - apply NB. apply in_block_app. left. apply in_block_In. exists b. split; [apply IC; exact Hb| lia].
      - apply NF. apply in_frames_In. exists fr. split; [apply IF; exact Hf| lia]. }
    destruct D; [exists 0 | exists 1]; lia.
  Qed.

  (* [comment removed for export] *)
  #[using="tlsI FO GL"] Lemma flag_keeps : forall L RNG s CL FB FL m m' f Fb n (CLc : list (@cblock hptr)) SP,
    GIOA L RNG s CL FB ((f, Fb, n) :: FL) m -> munch [(fflagA L f Fb, fflagA L f Fb + 1)] m m' -> wmono asegs m m' ->
    incl CLc CL -> ATOP <= SP ->
    agrees_on (client_keeps FL CLc SP) m m' /\ agrees_on (fun a => in_block CL a) m m'.
  Proof.
    intros L RNG s CL FB FL m m' f Fb n CLc SP G MU WM IC HSP.
    destruct (gl_flag _ _ _ GL _ _ _ _ _ _ _ f Fb n G (or_introl eq_refl)) as (C & R & B & T & NB & NF).
    split; (eapply agrees_on_of_munch; [exact MU| exact WM|]); intros a _ K; cbn [outside]; (split; [|exact I]); intros Hin;
      assert (E : a = fflagA L f Fb) by (clear - Hin; lia); subst a.
    - destruct K as [K|[K|[K|K]]].
      + lia.
      + apply NB. apply in_block_app. left. apply in_block_In in K as (b & Hb & Hr). apply in_block_In. exists b. split; [apply IC; exact Hb| exact Hr].
      + apply NF. apply in_frames_cons. exact K.
      + pose proof (gia_in_frame_sh_band _ _ _ GL _ _ _ _ _ _ _ _ G (in_frame_sh_cons _ _ _ K)) as BD.
        exact (ablk_clear_band _ _ (fflagA L f Fb) B ltac:(unfold KLS; lia) ltac:(lia)).
    - apply NB. apply in_block_app. left. exact K.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition own_ivA (FLo : list fblock) (PB : list (@cblock hptr)) (SP : Z) (iv : Z * Z) : Prop :=
    (ATOP + 4096 <= fst iv /\ snd iv <= SP) \/ iv_in_block PB iv \/ iv_in_frames FLo iv \/ iv_in_frame_shadow FLo iv.
  Definition cobj_iv (FLc : list fblock) (CLc : list (@cblock hptr)) (iv : Z * Z) : Prop :=
    clocA FLc CLc (fst iv) (snd iv - fst iv) /\ fst iv < snd iv.

  #[using="Type"] Lemma own_ivA_PB : forall FLo PB SP iv, own_ivA FLo [] SP iv -> own_ivA FLo PB SP iv.
  Proof. intros FLo PB SP iv [Hs|[Hb|Hf]]; [left; exact Hs| apply Exists_nil in Hb; destruct Hb| right; right; exact Hf]. Qed.

  (* [comment removed for export] *)
  #[using="tlsI FO fflagA GL"] Lemma own_writes : forall L RNG s CLc PB FB FLc FLo m m' W WX SP,
    Forall (own_ivA FLo PB SP) W -> Forall (cobj_iv FLc CLc) WX ->
    GIOA L RNG s (CLc ++ PB) FB (FLo ++ FLc) m -> munch (W ++ WX) m m' -> wmono asegs m m' -> ATOP + 4096 <= SP ->
    GIOA L RNG s (CLc ++ PB) FB (FLo ++ FLc) m' /\ agrees_on (fun a => client_keeps FLc CLc SP a /\ outside WX a) m m'.
  Proof.
    intros L RNG s CLc PB FB FLc FLo m m' W WX SP FW FX G MU WM HSP. split.
    - eapply (gl_client_frame _ _ _ GL); [exact G| exact MU| exact WM|]. apply Forall_app. split.
      + eapply Forall_impl; [|exact FW]. intros iv [Hs|[Hb|[Hf|Hf]]]; unfold client_ivA.
        * left. lia.
        * right; left. unfold iv_in_block in *. apply Exists_app. right. exact Hb.
        * right; right; left. unfold iv_in_frames in *. apply Exists_app. left. exact Hf.
        * right; right; right. unfold iv_in_frame_shadow in *. apply Exists_app. left. exact Hf.
      + eapply Forall_impl; [|exact FX]. intros [lo hi] [LOC LT]. cbn [fst snd] in *.
        replace hi with (lo + (hi - lo)) at 1 by lia. eapply clocA_iv. eapply clocA_incl; [exact LOC| apply incl_appl; apply incl_refl| apply incl_appr; apply incl_refl].
    - eapply (gl_keepsx _ _ _ GL); [exact G| exact MU| exact WM| exact FW| exact HSP].
  Qed.

  (* [comment removed for export] *)
  #[using="tlsI FO fflagA GL"] Lemma pb_outside : forall L RNG s CLc PB FB FLc FLo m W WX SP,
    Forall (own_ivA FLo [] SP) W -> Forall (cobj_iv FLc CLc) WX ->
    GIOA L RNG s (CLc ++ PB) FB (FLo ++ FLc) m ->
    forall a, in_block PB a -> outside (W ++ WX) a.
  Proof.
    intros L RNG s CLc PB FB FLc FLo m W WX SP FW FX G a Ha.
    assert (HaB : in_block ((CLc ++ PB) ++ FB) a) by (apply in_block_app; left; apply in_block_app; right; exact Ha).
    pose proof (gia_in_block_below _ _ _ GL _ _ _ _ _ _ _ a G HaB) as AB.
    assert (OW : outside W a).
    { clear FX. induction W as [|[lo hi] W IH]; [exact I|]. apply Forall_cons_iff in FW as [Hiv FW]. split; [| apply IH; exact FW].
      cbn [fst snd] in *. destruct Hiv as [Hs|[Hb|[Hf|Hf]]].
      - cbn [fst snd] in Hs. lia.
      - apply Exists_nil in Hb. destruct Hb.
      - intros Hin. apply (gl_fr_apart _ _ _ GL _ _ _ _ _ _ _ a G); [|exact HaB].
        unfold iv_in_frames in Hf. apply Exists_exists in Hf as (fr & Hfr & H1 & H2). cbn [fst snd] in H1, H2.
        apply in_frames_In. exists fr. split; [apply in_or_app; left; exact Hfr| lia].
      - intros Hin. unfold iv_in_frame_shadow in Hf. apply Exists_exists in Hf as (fr & Hfr & H1 & H2). cbn [fst snd] in H1, H2.
        assert (SH : in_frame_sh (FLo ++ FLc) a) by (apply in_frame_sh_In; exists fr; split; [apply in_or_app; left; exact Hfr| lia]).
        pose proof (gia_in_frame_sh_band _ _ _ GL _ _ _ _ _ _ _ a G SH) as BD.
        apply in_block_In in HaB as (b & Hb & Hr).
        destruct (gl_block _ _ _ GL _ _ _ _ _ _ _ b G Hb) as ((BAND & _) & _).
        exact (ablk_clear_band _ _ a BAND ltac:(unfold KLS; lia) Hr). }
    assert (OX : outside WX a).
    { clear FW OW. induction WX as [|[lo hi] WX IH]; [exact I|]. apply Forall_cons_iff in FX as [[LOC LT] FX]. split; [| apply IH; exact FX].
      cbn [fst snd] in *. intros Hin. destruct LOC as [(b & Hb & H1 & H2)|(fr & Hf & H1 & H2)].
      - apply in_block_In in Ha as (b' & Hb' & Hr').
        pose proof (gl_apart _ _ _ GL _ _ _ _ _ _ _ G) as BA. apply blocks_apart_app_inv in BA as (BA & _ & _).
        apply blocks_apart_app_inv in BA as (_ & _ & BX). specialize (BX b b' Hb Hb'). unfold apart in BX. lia.
      - apply (gl_fr_apart _ _ _ GL _ _ _ _ _ _ _ a G); [|exact HaB].
        apply in_frames_In. exists fr. split; [apply in_or_app; right; exact Hf| lia]. }
    clear - OW OX. induction W as [|[lo hi] W IH]; [exact OX|]. destruct OW as [O1 O2]. split; [exact O1| apply IH; exact O2].
  Qed.

  (* [comment removed for export] *)
  #[using="tlsI FO fflagA GL"] Lemma cobjA_keep : forall L RNG RNG' s' CL CL' FB' FL FL' m m' A n,
    cobjA RNG m FL CL A n -> GIOA L RNG' s' CL' FB' FL' m' -> incl CL CL' -> incl FL FL' ->
    agrees_on (in_frame_sh FL) m m' -> 0 < n ->
    cobjA RNG' m' FL CL A n.
  Proof.
    intros L RNG RNG' s' CL CL' FB' FL FL' m m' A n [LOC (A0 & A47 & UNP & _)] G' ICL IFL AG Hn. split; [exact LOC|].
    destruct LOC as [(b & Hb & H1 & H2)|(fr & Hf & H1 & H2)].
    - eapply blockA_aobj; [eapply (gl_block _ _ _ GL); [exact G'| apply in_or_app; left; apply ICL; exact Hb] | exact H1 | exact H2 | lia].
    - destruct (gl_frames _ _ _ GL _ _ _ _ _ _ _ G') as [FA _]. pose proof (proj1 (Forall_forall _ _) FA fr (IFL _ Hf)) as FRA.
      eapply frameA_aobj; [exact FRA| exact H1| exact H2| lia|].
      destruct FRA as (BAND & TOP & A64 & N64 & _ & _ & S64 & _).
      eapply unpoisoned_agree; [exact UNP|]. intros sa Hsa.
      assert (R : 0 <= sa < 2^64 /\ Z.shiftr (fb_addr fr) 3 + 2147450880 <= sa < Z.shiftr (fb_addr fr) 3 + 2147450880 + Z.shiftr (fb_size fr) 3).
      { rewrite !Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8. rewrite !shad_div in Hsa. unfold ASHOFF in Hsa.
        pose proof (ablk_lin _ _ BAND) as (IMG & F0 & _ & T47). atop_facts. Z.div_mod_to_equations. lia. }
      destruct R as [R0 R1].
      apply (AG sa R0). apply in_frame_sh_In. exists fr. split; [exact Hf| exact R1].
  Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma keeps_frame_sh : forall FL (CL : list (@cblock hptr)) SP m m', agrees_on (client_keeps FL CL SP) m m' -> agrees_on (in_frame_sh FL) m m'.
  Proof. intros FL CL SP m m' AG. eapply agrees_on_weaken; [exact AG|]. intros a Ha. right; right; right. exact Ha. Qed.
  (* [comment removed for export] *)
  #[using="tlsI FO fflagA GL"] Lemma keepsx_frame_sh : forall L RNG s CL FB FL FLc (CLc : list (@cblock hptr)) SP WX m0 m m',
    GIOA L RNG s CL FB FL m0 -> incl FLc FL ->
    agrees_on (fun a => client_keeps FLc CLc SP a /\ outside WX a) m m' ->
    Forall (fun iv => ablk (fst iv) (snd iv)) WX -> agrees_on (in_frame_sh FLc) m m'.
  Proof.
    intros L RNG s CL FB FL FLc CLc SP WX m0 m m' G IFL AG FX. eapply agrees_on_weaken; [exact AG|]. intros a Ha.
    split; [right; right; right; exact Ha|].
    pose proof (gia_in_frame_sh_band _ _ _ GL _ _ _ _ _ _ _ a G (in_frame_sh_incl _ _ _ IFL Ha)) as BD.
    clear AG. induction WX as [|[lo hi] WX IH]; [exact I|]. apply Forall_cons_iff in FX as [BAND FX]. split; [| apply IH; exact FX].
    cbn [fst snd] in BAND. apply (ablk_clear_band _ _ a BAND). unfold KLS. lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="Type"] Lemma client_globals_lo : forall g, In g client_globals -> 0x10040 <= fst g /\ 0 <= snd g /\ fst g + snd g <= 0x602fc0.
  Proof.
    intros g Hin. unfold client_globals in Hin. cbn [In] in Hin.
    repeat (destruct Hin as [Hin|Hin]; [subst g; cbn [fst snd]; lia|]). destruct Hin.
  Qed.

  #[using="FO fflagA GL"] Lemma slocA_mobjA_keep : forall L RNG RNG' s' CL CL' FB' FL FL' (m m' : mem) tls P n k,
    slocA tls FL CL P n k -> mobjA RNG m P n -> GIOA L RNG' s' CL' FB' FL' m' -> incl CL CL' -> incl FL FL' ->
    agrees_on (in_frame_sh FL) m m' -> rng_aimg RNG' -> rng_aimg_sh RNG' -> rng_atls RNG' -> 0 < n -> 0 <= k ->
    mobjA RNG' m' P n.
  Proof.
    intros L RNG RNG' s' CL CL' FB' FL FL' m m' tls P n k LOC (A0 & A47 & UNP & _) G' ICL IFL AG RI RS RT Hn Hk.
    destruct LOC as [[(b & Hb & H1 & H2)|(fr & Hf & H1 & H2)]|[(g & Hg & G1 & G2 & G3 & G4)|(_ & T1 & T2)]].
    - apply aobjA_mobjA; [|lia]. eapply blockA_aobj; [eapply (gl_block _ _ _ GL); [exact G'| apply in_or_app; left; apply ICL; exact Hb] | exact H1 | lia | lia].
    - apply aobjA_mobjA; [|lia].
      destruct (gl_frames _ _ _ GL _ _ _ _ _ _ _ G') as [FA _]. pose proof (proj1 (Forall_forall _ _) FA fr (IFL _ Hf)) as FRA.
      eapply frameA_aobj; [exact FRA| exact H1| lia| lia|].
      destruct FRA as (BAND & TOP & A64 & N64 & _ & _ & S64 & _).
      eapply unpoisoned_agree; [exact UNP|]. intros sa Hsa.
      assert (R : 0 <= sa < 2^64 /\ Z.shiftr (fb_addr fr) 3 + 2147450880 <= sa < Z.shiftr (fb_addr fr) 3 + 2147450880 + Z.shiftr (fb_size fr) 3).
      { rewrite !Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8. rewrite !shad_div in Hsa. unfold ASHOFF in Hsa.
        pose proof (ablk_lin _ _ BAND) as (IMG & F0 & _ & T47). atop_facts. Z.div_mod_to_equations. lia. }
      destruct R as [R0 R1].
      apply (AG sa R0). apply in_frame_sh_In. exists fr. split; [exact Hf| exact R1].
    - pose proof (client_globals_lo g Hg) as (GLO & GN & _).
      eapply mobjA_sub; [eapply (gia_global_mobjA _ _ _ GL _ _ _ _ _ _ _ (fst g) (snd g)); [exact G' | destruct g; exact Hg | exact RI | exact RS] | lia | lia | lia].
    - eapply mobjA_sub; [eapply (gl_tls _ _ _ GL); [exact G' | exact RT] | lia | lia | lia].
  Qed.

  #[using="FO fflagA GL"] Lemma farg_word_keep : forall L RNG RNG' s' CL CL' FB' FL FL' SPk SP SP' D dn (m m' : mem) a w,
    farg_word false L RNG FL CL SP D dn m a w ->
    GIOA L RNG' s' CL' FB' FL' m' -> incl CL CL' -> incl FL FL' -> fp_le RNG RNG' ->
    agrees_on (client_keeps FL CL SPk) m m' -> mem_inv asegs m -> mem_inv asegs m' ->
    rng_aimg RNG' -> rng_aimg_sh RNG' -> rng_atls RNG' ->
    farg_word false L RNG' FL' CL' SP' D dn m' a w.
  Proof.
    intros L RNG RNG' s' CL CL' FB' FL FL' SPk SP SP' D dn m m' a w FW G' ICL IFL FP AG MI MI' RI RS RT.
    destruct a as [z|cs]; cbn [farg_word] in *; [exact FW|].
    destruct FW as (P & bs & slack & -> & HB & NN & -> & LEN & SLK & DIS & LOC & OBJ & RNGS).
    exists P, bs, slack. split; [reflexivity|].
    pose proof (bytes_at_bound _ _ _ _ HB) as BB. rewrite length_app in BB. cbn [length] in BB.
    split.
    { destruct LOC as [LC|[(g & Hg & G1 & G2 & G3 & G4)|(T0 & _)]]; [| | discriminate T0].
      - eapply agrees_bytes_at; [exact AG | exact HB |]. intros x Hx. rewrite length_app in Hx. cbn [length] in Hx.
        eapply clocA_keeps; [exact LC| lia].
      - pose proof (client_globals_lo g Hg) as (GLO & _). eapply ro_bytes_at_any; [exact MI | exact MI' | exact HB | lia |].
        rewrite length_app. cbn [length]. lia. }
    split; [exact NN|]. split; [reflexivity|]. split; [exact LEN|]. split; [exact SLK|]. split; [exact DIS|].
    split.
    { destruct LOC as [LC|[GC|(T0 & _)]]; [left; eapply clocA_incl; eassumption | right; left; exact GC | discriminate T0]. }
    split; [| eapply rng_fp_le; eassumption].
    eapply slocA_mobjA_keep; [exact LOC | exact OBJ | exact G' | exact ICL | exact IFL | | exact RI | exact RS | exact RT | lia | lia].
    eapply agrees_on_weaken; [exact AG|]. intros x Hx. right; right; right. exact Hx.
  Qed.

  (* [comment removed for export] *)
  #[using="FO fflagA GL"] Lemma clocA_apart_tls : forall L RNG s CL FB FL m A n, GIOA L RNG s CL FB FL m -> clocA FL CL A n -> 0 < n ->
    A + n <= ATP + -200 \/ ATP + -200 + 504 <= A.
  Proof.
    intros L RNG s CL FB FL m A n G LOC Hn.
    assert (PW : forall a, A <= a < A + n -> ~ (ATP + -200 <= a < ATP + -200 + 504)).
    { intros a Ha. apply (gl_tls_apart _ _ _ GL _ _ _ _ _ _ _ a G).
      destruct LOC as [(b & Hb & H1 & H2)|(fr & Hf & H1 & H2)].
      - left. apply in_block_app. left. apply in_block_In. exists b. split; [exact Hb| lia].
      - right. apply in_frames_In. exists fr. split; [exact Hf| lia]. }
    destruct (Z_le_gt_dec (A + n) (ATP + -200)) as [?|X]; [left; assumption|].
    destruct (Z_le_gt_dec (ATP + -200 + 504) A) as [?|Y]; [right; assumption|]. exfalso.
    destruct (Z_le_gt_dec A (ATP + -200)) as [Z1|Z1]; [apply (PW (ATP + -200)); lia | apply (PW A); lia].
  Qed.

  #[using="Type"] Lemma fmt_at_keep : forall (m m' : mem) FMTA fs, fmt_at m FMTA fs -> mem_inv asegs m -> mem_inv asegs m' -> fmt_at m' FMTA fs.
  Proof.
    intros m m' FMTA fs (HB & H1 & H2 & H3) MI MI'. split; [|split; [exact H1| split; [exact H2| exact H3]]].
    eapply ro_bytes_at_any; [exact MI | exact MI' | exact HB | lia |].
    pose proof (bytes_at_bound _ _ _ _ HB) as BB. rewrite length_app, length_map in *. cbn [length] in *.
    assert (E : length (String.list_ascii_of_string fs) = String.length fs) by (clear; induction fs as [|c fs IH]; cbn; [reflexivity| now rewrite IH]).
    rewrite E. lia.
  Qed.
End Cobj.
End CANSEC1.

(* [comment removed for export] *)
Ltac own_iv1 :=
  unfold own_ivA, iv_in_block, iv_in_frames, iv_in_frame_shadow;
  first [ left; cbn [fst snd]; lia
        | right; right; left; apply Exists_cons_hd; cbn [fb_addr fb_size fst snd]; lia
        | right; right; right; apply Exists_cons_hd; cbn [fb_addr fb_size fst snd]; shr_consts; lia
        | right; left; first [ apply Exists_cons_hd | apply Exists_cons_tl; apply Exists_cons_hd | apply Exists_cons_tl; apply Exists_cons_tl; apply Exists_cons_hd ];
          cbn [cb_addr cb_size fst snd]; lia ].
Ltac own_ivs := repeat (apply Forall_cons; [own_iv1|]); apply Forall_nil.
Ltac cobj_iv1 :=
  split; [ cbn [fst snd];
           lazymatch goal with |- clocA _ _ ?A ?d =>
             match goal with O : cobjA _ _ _ _ A ?n |- _ => replace d with n by lia; exact (proj1 O) end end
         | cbn [fst snd]; lia ].
Ltac cobj_ivs := repeat (apply Forall_cons; [cobj_iv1|]); apply Forall_nil.

(* [comment removed for export] *)
Ltac zstep_sh0 :=
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) =>
    lazymatch goal with SH : rw_cells asegs mx (Z.shiftr _ 3 + 2147450880)%Z _ |- _ =>
      let SOK := fresh "SOK" in
      pose proof (rw_cells_store_ok asegs mx _ _ 0%nat _ 1%nat SH ltac:(cells_cbv; reflexivity) ltac:(reflexivity)) as SOK; zstep; clear SOK
    end
  end.

(* [comment removed for export] *)
Ltac join_a0 OK V :=
  cbv beta delta [mkR];
  lazymatch goal with
  | |- evtF ?segs ?RNG ?Q (MS ?R ?F ?pc ?fc ?rv ?m ?ro) =>
      eapply (evtF_cut segs RNG (fun ms' => ms' = MS (bvmap_set (Z_to_bv 5 10) V R) F (Z_to_bv 64 OK) fc rv m ro));
      [ | let ms' := fresh "ms'" in let H := fresh "Hj" in intros ms' H; subst ms'; simp_regs ]
  end.
Ltac join_done := apply evtF_done; simp_regs; reflexivity.

(* [comment removed for export] *)
Ltac disj_ind H k :=
  let k0 := fresh k "r" in let k1 := fresh k "a" in let k2 := fresh k "b" in
  lazymatch type of H with
  | (?x <= ?b \/ ?y <= ?a)%Z =>
      assert (exists k : Z, (0 <= k <= 1 /\ x <= b + k * 18446744073709551616 /\ y <= a + (1 - k) * 18446744073709551616)%Z)
        as (k & k0 & k1 & k2) by (destruct H; [exists 0%Z | exists 1%Z]; lia)
  end.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Bytes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ZBridge OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPrelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapTypes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Pcap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prog.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ExecF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ITreeA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.Shadow OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.StepF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.RtCells.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AMalloc_iface.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LibcKit.TwB. Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Lemma shad_shiftr : forall a, Z.shiftr a 3 + 2147450880 = shad a.
Proof. intros a. unfold shad, ASHOFF. lia. Qed.

(* [comment removed for export] *)
Ltac neg_lits :=
  repeat match goal with
  | |- context [Z_to_bv 64 (Zneg ?p)] =>
      let v := eval vm_compute in (18446744073709551616 + Zneg p) in
      replace (Z_to_bv 64 (Zneg p)) with (Z_to_bv 64 v) by (apply Z_to_bv_eqm; reflexivity)
  end.

(* [comment removed for export] *)
Ltac shr_consts :=
  repeat match goal with
  | |- context [Z.shiftr (Zpos ?p) 3] => let v := eval vm_compute in (Z.shiftr (Zpos p) 3) in change (Z.shiftr (Zpos p) 3) with v
  end.

Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="Type"] Lemma cells_wf_repeat_C1 : forall b n, cells_wf (repeat (C1 b) n).
Proof. intros b n. induction n; cbn; [exact I| split; [exact I| exact IHn]]. Qed.
#[using="Type"] Lemma cells_bytes_repeat_C1 : forall b n, cells_bytes (repeat (C1 b) n) = repeat b n.
Proof. intros b n. induction n; cbn; [reflexivity| rewrite IHn; reflexivity]. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma sh_zero_cells : forall m S n,
  rw_cells asegs m S [CB n (repeat (Z_to_bv 8 0) n)] -> rw_cells asegs m S (repeat (C1 (Z_to_bv 8 0)) n).
Proof.
  intros m S n HC. eapply rw_cells_recell; [exact HC| apply cells_wf_repeat_C1|].
  rewrite cells_bytes_repeat_C1. cbn [cells_bytes cbytes]. rewrite app_nil_r. reflexivity.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma unp_of_zero_cells : forall m p (k : nat) cs,
  rw_cells asegs m (Z.shiftr p 3 + 2147450880) cs -> cells_bytes cs = repeat (Z_to_bv 8 0) k ->
  p mod 8 = 0 -> 0 <= p -> p + 8 * Z.of_nat k <= 2^64 ->
  unpoisoned m p (p + 8 * Z.of_nat k).
Proof.
  intros m p k cs HC HB P8 P0 PT. apply shadow_block_unpoisoned.
  assert (EM : (8 * Z.of_nat k) mod 8 = 0) by (rewrite Z.mul_comm, Z_mod_mult; reflexivity).
  apply (shadow_block_of_memset0 asegs); try lia.
  - apply no_image_asan. rewrite shad_div. unfold ASHOFF. Z.div_mod_to_equations. lia.
  - replace (8 * Z.of_nat k / 8) with (Z.of_nat k) by (rewrite Z.mul_comm, Z_div_mult by lia; reflexivity).
    rewrite Nat2Z.id. rewrite <- shad_shiftr.
    eapply rw_cells_recell; [exact HC| cbn; split; [apply repeat_length| exact I]|].
    cbn [cells_bytes cbytes]. rewrite app_nil_r. symmetry. exact HB.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma unp_of_part_cells : forall m p (k : nat) r cs,
  rw_cells asegs m (Z.shiftr p 3 + 2147450880) cs -> cells_bytes cs = repeat (Z_to_bv 8 0) k ++ [Z_to_bv 8 r] ->
  1 <= r <= 7 -> p mod 8 = 0 -> 0 <= p -> p + 8 * Z.of_nat k + 8 <= 2^64 ->
  unpoisoned m p (p + (8 * Z.of_nat k + r)).
Proof.
  intros m p k r cs HC HB HR P8 P0 PT. apply shadow_block_unpoisoned.
  assert (E8 : (8 * Z.of_nat k + r) / 8 = Z.of_nat k) by (Z.div_mod_to_equations; lia).
  assert (EM : (8 * Z.of_nat k + r) mod 8 = r) by (Z.div_mod_to_equations; lia).
  apply (shadow_block_of_memset0_partial asegs m p (8 * Z.of_nat k + r) r); try lia.
  - rewrite E8. apply no_image_asan. rewrite shad_div. unfold ASHOFF. Z.div_mod_to_equations. lia.
  - rewrite E8, Nat2Z.id, <- shad_shiftr.
    eapply rw_cells_recell; [exact HC| cbn; split; [apply repeat_length| split; exact I]|].
    cbn [cells_bytes cbytes]. rewrite HB. reflexivity.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma shiftr3_add : forall F i, F mod 8 = 0 -> Z.shiftr (F + 8 * i) 3 = Z.shiftr F 3 + i.
Proof. intros F i H8. rewrite !Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8. Z.div_mod_to_equations. lia. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma unp_of_sh_bytes : forall m F cs (i k : nat),
  rw_cells asegs m (Z.shiftr F 3 + 2147450880) cs -> F mod 8 = 0 -> 0 <= F -> F + 8 * Z.of_nat (cells_size cs) <= 2^64 ->
  firstn k (skipn i (cells_bytes cs)) = repeat (Z_to_bv 8 0) k -> (i + k <= cells_size cs)%nat ->
  unpoisoned m (F + 8 * Z.of_nat i) (F + 8 * Z.of_nat i + 8 * Z.of_nat k).
Proof.
  intros m F cs i k HC F8 F0 FT HB HL.
  pose proof HC as [[WF _] _]. pose proof (cells_bytes_length cs WF) as LB.
  pose proof (rw_cells_merge asegs m _ [] cs [] ltac:(rewrite app_nil_r; exact HC)) as M. cbn [app] in M.
  apply (rw_cells_split_CB asegs _ _ [] _ _ [] [i; k; (cells_size cs - i - k)%nat]) in M; [|cbn; lia].
  cbn [app mk_CB_cells] in M. rewrite ?app_nil_r in M.
  destruct (rw_cells_cut _ _ _ 1 M) as [_ M1]. cbn [firstn skipn cells_size csize Nat.add] in M1.
  destruct (rw_cells_cut _ _ _ 1 M1) as [M2 _]. cbn [firstn skipn cells_size csize Nat.add] in M2.
  rewrite HB in M2. rewrite Nat.add_0_r in M2.
  eapply unp_of_zero_cells; [| | | |].
  - rewrite shiftr3_add by exact F8. replace (Z.shiftr F 3 + Z.of_nat i + 2147450880) with (Z.shiftr F 3 + 2147450880 + Z.of_nat i) by lia. exact M2.
  - cbn [cells_bytes cbytes]. rewrite app_nil_r. reflexivity.
  - rewrite Z.add_mod, F8 by lia. rewrite Z.mul_comm, Z_mod_mult. reflexivity.
  - lia.
  - lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma unp_of_sh_part : forall m F cs (i k : nat) r,
  rw_cells asegs m (Z.shiftr F 3 + 2147450880) cs -> F mod 8 = 0 -> 0 <= F -> F + 8 * Z.of_nat (cells_size cs) <= 2^64 ->
  firstn (k + 1) (skipn i (cells_bytes cs)) = repeat (Z_to_bv 8 0) k ++ [Z_to_bv 8 r] -> (i + k + 1 <= cells_size cs)%nat -> 1 <= r <= 7 ->
  unpoisoned m (F + 8 * Z.of_nat i) (F + 8 * Z.of_nat i + (8 * Z.of_nat k + r)).
Proof.
  intros m F cs i k r HC F8 F0 FT HB HL HR.
  pose proof HC as [[WF _] _]. pose proof (cells_bytes_length cs WF) as LB.
  pose proof (rw_cells_merge asegs m _ [] cs [] ltac:(rewrite app_nil_r; exact HC)) as M. cbn [app] in M.
  apply (rw_cells_split_CB asegs _ _ [] _ _ [] [i; (k + 1)%nat; (cells_size cs - i - (k + 1))%nat]) in M; [|cbn; lia].
  cbn [app mk_CB_cells] in M. rewrite ?app_nil_r in M.
  destruct (rw_cells_cut _ _ _ 1 M) as [_ M1]. cbn [firstn skipn cells_size csize Nat.add] in M1.
  destruct (rw_cells_cut _ _ _ 1 M1) as [M2 _]. cbn [firstn skipn cells_size csize Nat.add] in M2.
  rewrite HB in M2. rewrite Nat.add_0_r in M2.
  eapply unp_of_part_cells; [| | exact HR | | |].
  - rewrite shiftr3_add by exact F8. replace (Z.shiftr F 3 + Z.of_nat i + 2147450880) with (Z.shiftr F 3 + 2147450880 + Z.of_nat i) by lia. exact M2.
  - cbn [cells_bytes cbytes]. rewrite app_nil_r. reflexivity.
  - rewrite Z.add_mod, F8 by lia. rewrite Z.mul_comm, Z_mod_mult. reflexivity.
  - lia.
  - lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma rw_cells_nth_C8 : forall m A cs (k : nat) v,
  rw_cells asegs m A cs -> nth_error cs k = Some (C8 v) -> bytes_at asegs m (A + Z.of_nat (cells_size (firstn k cs))) (le8 v).
Proof.
  intros m A cs k v HC HN. destruct (rw_cells_cut _ _ _ k HC) as [_ H2].
  assert (E : skipn k cs = C8 v :: skipn (S k) cs).
  { clear - HN. revert k HN. induction cs as [|c cs IH]; intros [|k] HN; cbn in *; try discriminate; [injection HN as ->; reflexivity| apply IH; exact HN]. }
  rewrite E in H2. destruct (rw_cells_cut _ _ _ 1 H2) as [H3 _]. cbn [firstn] in H3.
  apply rw_cells_bytes_at in H3. cbn [cells_bytes cbytes] in H3. rewrite app_nil_r in H3. exact H3.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Objs.
  Context {hptr : Type}.
  Notation cblk := (@cblock hptr).

  #[using="Type"] Lemma clocA_incl : forall FL FL' (CL CL' : list cblk) A n,
    clocA FL CL A n -> incl CL CL' -> incl FL FL' -> clocA FL' CL' A n.
  Proof.
    intros FL FL' CL CL' A n [(b & Hb & H1)|(fr & Hf & H1)] IC IF; [left; exists b | right; exists fr]; (split; [auto| exact H1]).
  Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma clocA_iv : forall FL (CL : list cblk) A n, clocA FL CL A n -> client_ivA FL CL (A, A + n).
  Proof.
    intros FL CL A n [(b & Hb & H1 & H2)|(fr & Hf & H1 & H2)]; unfold client_ivA.
    - right; left. unfold iv_in_block. apply Exists_exists. exists b. split; [exact Hb| cbn [fst snd]; lia].
    - right; right; left. unfold iv_in_frames. apply Exists_exists. exists fr. split; [exact Hf| cbn [fst snd]; lia].
  Qed.

  #[using="Type"] Lemma blockA_aobj : forall RNG m (b : cblk) A n,
    blockA RNG m b -> cb_addr b <= A -> A + n <= cb_addr b + cb_size b -> 0 <= n -> aobjA RNG m A n.
  Proof.
    intros RNG m b A n ((BAND & N0 & TOP & AL) & P0 & UNP & RB & RSH & AR) H1 H2 Hn. atop_facts.
    split; [lia|]. split; [lia|]. split; [eapply unpoisoned_sub; [exact UNP| lia| lia]|].
    split; [eapply rng_sub; [exact RB| lia| lia]|].
    split; [| split; [eapply arenaA_sub; [exact AR| lia| lia]| eapply ablk_sub; [exact BAND| lia| lia]]].
    eapply rng_sub'; [exact RSH|]. rewrite !shad_div, !nshad_div. Z.div_mod_to_equations. lia.
  Qed.

  #[using="Type"] Lemma frameA_aobj : forall RNG m fr A n,
    frameA RNG m fr -> fb_addr fr <= A -> A + n <= fb_addr fr + fb_size fr -> 0 <= n -> unpoisoned m A (A + n) -> aobjA RNG m A n.
  Proof.
    intros RNG m fr A n (BAND & TOP & A64 & N64 & RF & RSF & S64 & WSF) H1 H2 Hn UNP. atop_facts.
    pose proof (ablk_lin _ _ BAND) as (IMG & F0 & _ & T47). unfold AIMG_HI in IMG.
    rewrite !Z.shiftr_div_pow2 in RSF, WSF by lia. change (2 ^ 3) with 8 in RSF, WSF.
    split; [lia|]. split; [lia|]. split; [exact UNP|].
    split; [eapply rng_sub; [exact RF| lia| lia]|]. split.
    - eapply rng_sub'; [exact RSF|]. rewrite !shad_div, !nshad_div. unfold ASHOFF. Z.div_mod_to_equations. lia.
    - split; [| eapply ablk_sub; [exact BAND| lia| lia]].
      exists (fb_addr fr), (fb_addr fr + fb_size fr). split; [lia|]. split; [lia|]. split; [exact A64|].
      split; [rewrite Z.add_mod, A64, S64 by lia; reflexivity|]. split; [lia|]. split; [unfold KEND; lia|].
      assert (E : shad (fb_addr fr + fb_size fr) - shad (fb_addr fr) = fb_size fr / 8)
        by (rewrite !shad_div; Z.div_mod_to_equations; lia).
      rewrite E, shad_div. unfold ASHOFF. rewrite Z.add_comm. split; [exact WSF| exact RSF].
  Qed.
End Objs.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Cobj.
  Context {H hptr : Type} (FO : @FrameOps H hptr).
  Variable GIOA : alayout -> footprint -> PState H hptr -> list (@cblock hptr) -> list (@cblock hptr) -> list fblock -> mem -> Prop.
  Variable fflagA : alayout -> fframe -> Z -> Z.
  Hypothesis GL : gia_laws FO GIOA fflagA.

  #[using="tlsI FO fflagA GL"] Lemma clocA_below : forall L RNG s CL FB FL m A n,
    GIOA L RNG s CL FB FL m -> clocA FL CL A n -> 0x604000 <= A /\ A + n <= ATOP.
  Proof.
    intros L RNG s CL FB FL m A n G [(b & Hb & H1 & H2)|(fr & Hf & H1 & H2)].
    - destruct (gl_block _ _ _ GL _ _ _ _ _ _ _ b G ltac:(apply in_or_app; left; exact Hb)) as ((BAND & _ & TOP & _) & _).
      pose proof (ablk_lin _ _ BAND) as (IMG & _). unfold AIMG_HI in IMG. lia.
    - destruct (gl_frames _ _ _ GL _ _ _ _ _ _ _ G) as [FA _]. pose proof (proj1 (Forall_forall _ _) FA fr Hf) as (BAND & TOP & _).
      pose proof (ablk_lin _ _ BAND) as (IMG & _). unfold AIMG_HI in IMG. lia.
  Qed.

  (* [comment removed for export] *)
  #[using="tlsI FO fflagA GL"] Lemma clocA_ablk : forall L RNG s CL FB FL m A n,
    GIOA L RNG s CL FB FL m -> clocA FL CL A n -> 0 <= n -> ablk A (A + n).
  Proof.
    intros L RNG s CL FB FL m A n G [(b & Hb & H1 & H2)|(fr & Hf & H1 & H2)] Hn.
    - destruct (gl_block _ _ _ GL _ _ _ _ _ _ _ b G ltac:(apply in_or_app; left; exact Hb)) as ((BAND & _) & _).
      eapply ablk_sub; [exact BAND| lia| lia].
    - destruct (gl_frames _ _ _ GL _ _ _ _ _ _ _ G) as [FA _]. pose proof (proj1 (Forall_forall _ _) FA fr Hf) as (BAND & _).
      eapply ablk_sub; [exact BAND| lia| lia].
  Qed.

  (* [comment removed for export] *)
  #[using="rc tlsI FO fflagA GL"] Lemma clocA_apart_frame : forall L RNG s CL FB FL m fr A n,
    GIOA L RNG s CL FB (fr :: FL) m -> clocA FL CL A n -> 0 < n ->
    exists k, 0 <= k <= 1 /\ A + n <= fb_addr fr + k * 18446744073709551616 /\ fb_addr fr + fb_size fr <= A + (1 - k) * 18446744073709551616.
  Proof.
    intros L RNG s CL FB FL m fr A n G LOC Hn.
    destruct (gl_frames _ _ _ GL _ _ _ _ _ _ _ G) as [FA ND].
    pose proof (Forall_inv FA) as (BAND & TOP & _ & N64 & _). pose proof (ablk_lin _ _ BAND) as (_ & F0 & _ & T47).
    assert (D : A + n <= fb_addr fr \/ fb_addr fr + fb_size fr <= A).
    { destruct LOC as [(b & Hb & H1 & H2)|(fr' & Hf & H1 & H2)].
      - destruct (Z_le_gt_dec (A + n) (fb_addr fr)) as [?|G1]; [left; assumption|].
        destruct (Z_le_gt_dec (fb_addr fr + fb_size fr) A) as [?|G2]; [right; assumption|]. exfalso.
        apply (gl_fr_apart _ _ _ GL _ _ _ _ _ _ _ (Z.max A (fb_addr fr)) G).
        + apply in_frames_In. exists fr. split; [left; reflexivity| lia].
        + apply in_block_app. left. apply in_block_In. exists b. split; [exact Hb| lia].
      - assert (NE : fb_fn fr' <> fb_fn fr).
        { cbn [map] in ND. apply List.NoDup_cons_iff in ND as [NI _]. intros E. apply NI. rewrite <- E. apply in_map. exact Hf. }
        pose proof (proj1 (Forall_forall _ _) FA fr' (or_intror Hf)) as (BAND' & _ & _ & N64' & _).
        destruct (gl_fr_disj _ _ _ GL _ _ _ _ _ _ _ fr' fr G (or_intror Hf) (or_introl eq_refl) NE) as [D|D]; [left; lia| right; lia]. }
    pose proof (clocA_below _ _ _ _ _ _ _ _ _ G (clocA_incl _ _ _ _ _ _ LOC (incl_refl _) (incl_tl _ (incl_refl _)))) as (ALO & AHI).
    atop_facts. destruct D; [exists 0 | exists 1]; lia.
  Qed.

  (* [comment removed for export] *)
  #[using="rc tlsI FO fflagA GL"] Lemma clocA_apart_block : forall L RNG s CLc PB FB FL m (b : @cblock hptr) A n,
    GIOA L RNG s (CLc ++ PB) FB FL m -> clocA FL CLc A n -> In b PB -> 0 < n -> 0 < cb_size b ->
    exists k, 0 <= k <= 1 /\ A + n <= cb_addr b + k * 18446744073709551616 /\ cb_addr b + cb_size b <= A + (1 - k) * 18446744073709551616.
  Proof.
    intros L RNG s CLc PB FB FL m b A n G LOC Hb Hn Hs.
    assert (HbA : In b ((CLc ++ PB) ++ FB)) by (apply in_or_app; left; apply in_or_app; right; exact Hb).
    destruct (gl_block _ _ _ GL _ _ _ _ _ _ _ b G HbA) as ((BAND & _ & TOP & _) & B0 & _).
    assert (D : A + n <= cb_addr b \/ cb_addr b + cb_size b <= A).
    { destruct LOC as [(b0 & Hb0 & H1 & H2)|(fr & Hf & H1 & H2)].
      - pose proof (gl_apart _ _ _ GL _ _ _ _ _ _ _ G) as BA. apply blocks_apart_app_inv in BA as (BA & _ & _).
        apply blocks_apart_app_inv in BA as (_ & _ & BX). specialize (BX b0 b Hb0 Hb). unfold apart in BX. lia.
      - destruct (Z_le_gt_dec (A + n) (cb_addr b)) as [?|G1]; [left; assumption|].
        destruct (Z_le_gt_dec (cb_addr b + cb_size b) A) as [?|G2]; [right; assumption|]. exfalso.
        apply (gl_fr_apart _ _ _ GL _ _ _ _ _ _ _ (Z.max A (cb_addr b)) G).
        + apply in_frames_In. exists fr. split; [exact Hf| lia].
        + apply in_block_In. exists b. split; [exact HbA| lia]. }
    pose proof (clocA_below _ _ _ _ _ _ _ _ _ G (clocA_incl _ _ _ _ _ _ LOC (incl_appl _ (incl_refl _)) (incl_refl _))) as (ALO & AHI).
    atop_facts. destruct D; [exists 0 | exists 1]; lia.
  Qed.

  (* [comment removed for export] *)
  #[using="rc tlsI FO fflagA GL"] Lemma PB_apartA : forall L RNG s CLc PB FB FL m (p : PcapTypes.pcap hptr hptr) P B I,
    GIOA L RNG s (CLc ++ PB) FB FL m -> PB = pcap_blocks p P B I ->
    (P + psize p <= B \/ B + pc_bufalloc p <= P)
    /\ (forall sg q, pc_priv p = PrivNg sg (Some q) ->
          (P + psize p <= I \/ I + 40 * ng_ifaces_size sg <= P) /\ (B + pc_bufalloc p <= I \/ I + 40 * ng_ifaces_size sg <= B)).
  Proof.
    intros L RNG s CLc PB FB FL m p P B I G EPB.
    pose proof (gl_apart _ _ _ GL _ _ _ _ _ _ _ G) as BA.
    apply blocks_apart_app_inv in BA as (BA & _ & _). apply blocks_apart_app_inv in BA as (_ & BA & _).
    rewrite EPB in BA. unfold pcap_blocks in BA. cbn [blocks_apart] in BA.
    destruct BA as (F1 & F2 & _). pose proof (Forall_inv F1) as A12. apply Forall_inv_tail in F1.
    unfold apart, cb_addr, cb_size in A12; cbn [fst snd] in A12. split; [lia|].
    intros sg q Hq. rewrite Hq in F1, F2. pose proof (Forall_inv F1) as A13. pose proof (Forall_inv F2) as A23.
    unfold apart, cb_addr, cb_size in A13, A23; cbn [fst snd] in A13, A23. lia.
  Qed.

  (* [comment removed for export] *)
  #[using="rc tlsI FO fflagA GL"] Lemma block_apart_frame : forall L RNG s CL FB FL m (b : @cblock hptr) fr,
    GIOA L RNG s CL FB FL m -> In b (CL ++ FB) -> In fr FL -> 0 < cb_size b ->
    exists k, 0 <= k <= 1 /\ cb_addr b + cb_size b <= fb_addr fr + k * 18446744073709551616
              /\ fb_addr fr + fb_size fr <= cb_addr b + (1 - k) * 18446744073709551616.
  Proof.
    intros L RNG s CL FB FL m b fr G Hb Hf Hs.
    destruct (gl_block _ _ _ GL _ _ _ _ _ _ _ b G Hb) as ((BAND & _ & TOP & _) & B0 & _).
    destruct (gl_frames _ _ _ GL _ _ _ _ _ _ _ G) as [FA _]. pose proof (proj1 (Forall_forall _ _) FA fr Hf) as (FBAND & FTOP & _ & N64 & _).
    pose proof (ablk_lin _ _ FBAND) as (_ & F0 & _ & T47). atop_facts.
    assert (D : cb_addr b + cb_size b <= fb_addr fr \/ fb_addr fr + fb_size fr <= cb_addr b).
    { destruct (Z_le_gt_dec (cb_addr b + cb_size b) (fb_addr fr)) as [?|G1]; [left; assumption|].
      destruct (Z_le_gt_dec (fb_addr fr + fb_size fr) (cb_addr b)) as [?|G2]; [right; assumption|]. exfalso.
      apply (gl_fr_apart _ _ _ GL _ _ _ _ _ _ _ (Z.max (cb_addr b) (fb_addr fr)) G).
      - apply in_frames_In. exists fr. split; [exact Hf| lia].
      - apply in_block_In. exists b. split; [exact Hb| lia]. }
    destruct D; [exists 0 | exists 1]; lia.
  Qed.

  (* [comment removed for export] *)
  #[using="tlsI FO fflagA GL"] Lemma keeps_not_own_frame : forall L RNG s CL FB FL m fr (CLc : list (@cblock hptr)) SP a,
    GIOA L RNG s CL FB (fr :: FL) m -> incl CLc CL -> ATOP <= SP -> client_keeps FL CLc SP a ->
    ~ (fb_addr fr <= a < fb_addr fr + fb_size fr)
    /\ ~ (Z.shiftr (fb_addr fr) 3 + 2147450880 <= a < Z.shiftr (fb_addr fr) 3 + 2147450880 + Z.shiftr (fb_size fr) 3).
  Proof.
    intros L RNG s CL FB FL m fr CLc SP a G IC HSP K.
    destruct (gl_frames _ _ _ GL _ _ _ _ _ _ _ G) as [FA ND]. pose proof (Forall_inv FA) as (BAND & TOP & A64 & N64 & _ & _ & S64 & _).
    assert (INF : forall x, fb_addr fr <= x < fb_addr fr + fb_size fr -> in_frames (fr :: FL) x)
      by (intros x Hx; apply in_frames_In; exists fr; split; [left; reflexivity| exact Hx]).
    assert (INS : forall x, Z.shiftr (fb_addr fr) 3 + 2147450880 <= x < Z.shiftr (fb_addr fr) 3 + 2147450880 + Z.shiftr (fb_size fr) 3 -> in_frame_sh (fr :: FL) x)
      by (intros x Hx; apply in_frame_sh_In; exists fr; split; [left; reflexivity| exact Hx]).
    destruct K as [K|[K|[K|K]]].
    - split; intros Hin.
      + pose proof (gia_in_frames_below _ _ _ GL _ _ _ _ _ _ _ a G (INF a Hin)). lia.
      + pose proof (gia_in_frame_sh_band _ _ _ GL _ _ _ _ _ _ _ a G (INS a Hin)). atop_facts. lia.
    - assert (KB : in_block (CL ++ FB) a).
      { apply in_block_app. left. apply in_block_In in K as (b & Hb & Hr). apply in_block_In. exists b. split; [apply IC; exact Hb| exact Hr]. }
      split; intros Hin.
      + exact (gl_fr_apart _ _ _ GL _ _ _ _ _ _ _ a G (INF a Hin) KB).
      + pose proof (gia_in_frame_sh_band _ _ _ GL _ _ _ _ _ _ _ a G (INS a Hin)) as BD.
        apply in_block_In in KB as (b & Hb & Hr). destruct (gl_block _ _ _ GL _ _ _ _ _ _ _ b G Hb) as ((BB & _) & _).
        exact (ablk_clear_band _ _ a BB ltac:(unfold KLS; lia) Hr).
    - apply in_frames_In in K as (fr' & Hf' & Hr').
      assert (NE : fb_fn fr' <> fb_fn fr).
      { cbn [map] in ND. apply List.NoDup_cons_iff in ND as [NI _]. intros E. apply NI. rewrite <- E. apply in_map. exact Hf'. }
      pose proof (proj1 (Forall_forall _ _) FA fr' (or_intror Hf')) as (BAND' & _).
      split; intros Hin.
      + destruct (gl_fr_disj _ _ _ GL _ _ _ _ _ _ _ fr' fr G (or_intror Hf') (or_introl eq_refl) NE) as [D|D]; lia.
      + pose proof (gia_in_frame_sh_band _ _ _ GL _ _ _ _ _ _ _ a G (INS a Hin)) as BD.
        exact (ablk_clear_band _ _ a BAND' ltac:(unfold KLS; lia) Hr').
    - pose proof (gia_in_frame_sh_band _ _ _ GL _ _ _ _ _ _ _ a G (in_frame_sh_cons _ _ _ K)) as BD.
      split; intros Hin.
      + exact (ablk_clear_band _ _ a BAND ltac:(unfold KLS; lia) Hin).
      + (* [comment removed for export] *)
        apply in_frame_sh_In in K as (fr' & Hf' & Hr').
        assert (NE : fb_fn fr' <> fb_fn fr).
        { cbn [map] in ND. apply List.NoDup_cons_iff in ND as [NI _]. intros E. apply NI. rewrite <- E. apply in_map. exact Hf'. }
        pose proof (proj1 (Forall_forall _ _) FA fr' (or_intror Hf')) as (BAND' & _ & A64' & N64' & _ & _ & S64' & _).
        pose proof (ablk_lin _ _ BAND) as (_ & F0 & _). pose proof (ablk_lin _ _ BAND') as (_ & F0' & _).
        rewrite !Z.shiftr_div_pow2 in Hin, Hr' by lia. change (2 ^ 3) with 8 in Hin, Hr'.
        destruct (gl_fr_disj _ _ _ GL _ _ _ _ _ _ _ fr' fr G (or_intror Hf') (or_introl eq_refl) NE) as [D|D]; Z.div_mod_to_equations; lia.
  Qed.

  (* [comment removed for export] *)
  #[using="tlsI FO GL"] Lemma flag_facts : forall L RNG s CL FB FL m f Fb n,
    GIOA L RNG s CL FB ((f, Fb, n) :: FL) m ->
    rw_cells asegs m (fflagA L f Fb) [C1 (Z_to_bv 8 1)] /\ rng RNG (fflagA L f Fb) 1 /\ ablk (fflagA L f Fb) (fflagA L f Fb + 1)
    /\ fflagA L f Fb + 1 <= ATOP /\ ~ in_block (CL ++ FB) (fflagA L f Fb)
    /\ exists k, 0 <= k <= 1 /\ fflagA L f Fb + 1 <= Fb + k * 18446744073709551616 /\ Fb + n <= fflagA L f Fb + (1 - k) * 18446744073709551616.
  Proof.
    intros L RNG s CL FB FL m f Fb n G.
    destruct (gl_flag _ _ _ GL _ _ _ _ _ _ _ f Fb n G (or_introl eq_refl)) as (C & R & B & T & NB & NF).
    split; [exact C|]. split; [exact R|]. split; [exact B|]. split; [exact T|]. split; [exact NB|].
    destruct (gl_frames _ _ _ GL _ _ _ _ _ _ _ G) as [FA _]. pose proof (Forall_inv FA) as (BAND & TOP & _). cbn [fb_addr fb_size fst snd] in BAND, TOP.
    pose proof (ablk_lin _ _ BAND) as (_ & F0 & _ & T47). pose proof (ablk_lin _ _ B) as (_ & G0 & _ & G47). atop_facts.
    assert (D : fflagA L f Fb + 1 <= Fb \/ Fb + n <= fflagA L f Fb).
    { destruct (Z_le_gt_dec (fflagA L f Fb + 1) Fb) as [?|G1]; [left; assumption|].
      destruct (Z_le_gt_dec (Fb + n) (fflagA L f Fb)) as [?|G2]; [right; assumption|]. exfalso. apply NF.
      apply in_frames_In. exists (f, Fb, n). split; [left; reflexivity| cbn [fb_addr fb_size fst snd]; lia]. }
    destruct D; [exists 0 | exists 1]; lia.
  Qed.
  #[using="rc tlsI FO GL"] Lemma flag_apart_cloc : forall L RNG s CL FB FL m f Fb n FLc CLc A k,
    GIOA L RNG s CL FB ((f, Fb, n) :: FL) m -> clocA FLc CLc A k -> incl CLc CL -> incl FLc ((f, Fb, n) :: FL) -> 0 < k ->
    exists i, 0 <= i <= 1 /\ fflagA L f Fb + 1 <= A + i * 18446744073709551616 /\ A + k <= fflagA L f Fb + (1 - i) * 18446744073709551616.
  Proof.
    intros L RNG s CL FB FL m f Fb n FLc CLc A k G LOC IC IF Hk.
    destruct (gl_flag _ _ _ GL _ _ _ _ _ _ _ f Fb n G (or_introl eq_refl)) as (C & R & B & T & NB & NF).
    pose proof (clocA_below _ _ _ _ _ _ _ _ _ G (clocA_incl _ _ _ _ _ _ LOC IC IF)) as (ALO & AHI).
    pose proof (ablk_lin _ _ B) as (_ & G0 & _ & G47). atop_facts.
    assert (D : fflagA L f Fb + 1 <= A \/ A + k <= fflagA L f Fb).
    { destruct (Z_le_gt_dec (fflagA L f Fb + 1) A) as [?|G1]; [left; assumption|].
      destruct (Z_le_gt_dec (A + k) (fflagA L f Fb)) as [?|G2]; [right; assumption|]. exfalso.
      destruct LOC as [(b & Hb & H1 & H2)|(fr & Hf & H1 & H2)].
      - apply NB. apply in_block_app. left. apply in_block_In. exists b. split; [apply IC; exact Hb| lia].
      - apply NF. apply in_frames_In. exists fr. split; [apply IF; exact Hf| lia]. }
    destruct D; [exists 0 | exists 1]; lia.
  Qed.

  (* [comment removed for export] *)
  #[using="tlsI FO GL"] Lemma flag_keeps : forall L RNG s CL FB FL m m' f Fb n (CLc : list (@cblock hptr)) SP,
    GIOA L RNG s CL FB ((f, Fb, n) :: FL) m -> munch [(fflagA L f Fb, fflagA L f Fb + 1)] m m' -> wmono asegs m m' ->
    incl CLc CL -> ATOP <= SP ->
    agrees_on (client_keeps FL CLc SP) m m' /\ agrees_on (fun a => in_block CL a) m m'.
  Proof.
    intros L RNG s CL FB FL m m' f Fb n CLc SP G MU WM IC HSP.
    destruct (gl_flag _ _ _ GL _ _ _ _ _ _ _ f Fb n G (or_introl eq_refl)) as (C & R & B & T & NB & NF).
    split; (eapply agrees_on_of_munch; [exact MU| exact WM|]); intros a _ K; cbn [outside]; (split; [|exact I]); intros Hin;
      assert (E : a = fflagA L f Fb) by (clear - Hin; lia); subst a.
    - destruct K as [K|[K|[K|K]]].
      + lia.
      + apply NB. apply in_block_app. left. apply in_block_In in K as (b & Hb & Hr). apply in_block_In. exists b. split; [apply IC; exact Hb| exact Hr].
      + apply NF. apply in_frames_cons. exact K.
      + pose proof (gia_in_frame_sh_band _ _ _ GL _ _ _ _ _ _ _ _ G (in_frame_sh_cons _ _ _ K)) as BD.
        exact (ablk_clear_band _ _ (fflagA L f Fb) B ltac:(unfold KLS; lia) ltac:(lia)).
    - apply NB. apply in_block_app. left. exact K.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition own_ivA (FLo : list fblock) (PB : list (@cblock hptr)) (SP : Z) (iv : Z * Z) : Prop :=
    (ATOP + 4096 <= fst iv /\ snd iv <= SP) \/ iv_in_block PB iv \/ iv_in_frames FLo iv \/ iv_in_frame_shadow FLo iv.
  Definition cobj_iv (FLc : list fblock) (CLc : list (@cblock hptr)) (iv : Z * Z) : Prop :=
    clocA FLc CLc (fst iv) (snd iv - fst iv) /\ fst iv < snd iv.

  #[using="Type"] Lemma own_ivA_PB : forall FLo PB SP iv, own_ivA FLo [] SP iv -> own_ivA FLo PB SP iv.
  Proof. intros FLo PB SP iv [Hs|[Hb|Hf]]; [left; exact Hs| apply Exists_nil in Hb; destruct Hb| right; right; exact Hf]. Qed.

  (* [comment removed for export] *)
  #[using="tlsI FO fflagA GL"] Lemma own_writes : forall L RNG s CLc PB FB FLc FLo m m' W WX SP,
    Forall (own_ivA FLo PB SP) W -> Forall (cobj_iv FLc CLc) WX ->
    GIOA L RNG s (CLc ++ PB) FB (FLo ++ FLc) m -> munch (W ++ WX) m m' -> wmono asegs m m' -> ATOP + 4096 <= SP ->
    GIOA L RNG s (CLc ++ PB) FB (FLo ++ FLc) m' /\ agrees_on (fun a => client_keeps FLc CLc SP a /\ outside WX a) m m'.
  Proof.
    intros L RNG s CLc PB FB FLc FLo m m' W WX SP FW FX G MU WM HSP. split.
    - eapply (gl_client_frame _ _ _ GL); [exact G| exact MU| exact WM|]. apply Forall_app. split.
      + eapply Forall_impl; [|exact FW]. intros iv [Hs|[Hb|[Hf|Hf]]]; unfold client_ivA.
        * left. lia.
        * right; left. unfold iv_in_block in *. apply Exists_app. right. exact Hb.
        * right; right; left. unfold iv_in_frames in *. apply Exists_app. left. exact Hf.
        * right; right; right. unfold iv_in_frame_shadow in *. apply Exists_app. left. exact Hf.
      + eapply Forall_impl; [|exact FX]. intros [lo hi] [LOC LT]. cbn [fst snd] in *.
        replace hi with (lo + (hi - lo)) at 1 by lia. eapply clocA_iv. eapply clocA_incl; [exact LOC| apply incl_appl; apply incl_refl| apply incl_appr; apply incl_refl].
    - eapply (gl_keepsx _ _ _ GL); [exact G| exact MU| exact WM| exact FW| exact HSP].
  Qed.

  (* [comment removed for export] *)
  #[using="tlsI FO fflagA GL"] Lemma pb_outside : forall L RNG s CLc PB FB FLc FLo m W WX SP,
    Forall (own_ivA FLo [] SP) W -> Forall (cobj_iv FLc CLc) WX ->
    GIOA L RNG s (CLc ++ PB) FB (FLo ++ FLc) m ->
    forall a, in_block PB a -> outside (W ++ WX) a.
  Proof.
    intros L RNG s CLc PB FB FLc FLo m W WX SP FW FX G a Ha.
    assert (HaB : in_block ((CLc ++ PB) ++ FB) a) by (apply in_block_app; left; apply in_block_app; right; exact Ha).
    pose proof (gia_in_block_below _ _ _ GL _ _ _ _ _ _ _ a G HaB) as AB.
    assert (OW : outside W a).
    { clear FX. induction W as [|[lo hi] W IH]; [exact I|]. apply Forall_cons_iff in FW as [Hiv FW]. split; [| apply IH; exact FW].
      cbn [fst snd] in *. destruct Hiv as [Hs|[Hb|[Hf|Hf]]].
      - cbn [fst snd] in Hs. lia.
      - apply Exists_nil in Hb. destruct Hb.
      - intros Hin. apply (gl_fr_apart _ _ _ GL _ _ _ _ _ _ _ a G); [|exact HaB].
        unfold iv_in_frames in Hf. apply Exists_exists in Hf as (fr & Hfr & H1 & H2). cbn [fst snd] in H1, H2.
        apply in_frames_In. exists fr. split; [apply in_or_app; left; exact Hfr| lia].
      - intros Hin. unfold iv_in_frame_shadow in Hf. apply Exists_exists in Hf as (fr & Hfr & H1 & H2). cbn [fst snd] in H1, H2.
        assert (SH : in_frame_sh (FLo ++ FLc) a) by (apply in_frame_sh_In; exists fr; split; [apply in_or_app; left; exact Hfr| lia]).
        pose proof (gia_in_frame_sh_band _ _ _ GL _ _ _ _ _ _ _ a G SH) as BD.
        apply in_block_In in HaB as (b & Hb & Hr).
        destruct (gl_block _ _ _ GL _ _ _ _ _ _ _ b G Hb) as ((BAND & _) & _).
        exact (ablk_clear_band _ _ a BAND ltac:(unfold KLS; lia) Hr). }
    assert (OX : outside WX a).
    { clear FW OW. induction WX as [|[lo hi] WX IH]; [exact I|]. apply Forall_cons_iff in FX as [[LOC LT] FX]. split; [| apply IH; exact FX].
      cbn [fst snd] in *. intros Hin. destruct LOC as [(b & Hb & H1 & H2)|(fr & Hf & H1 & H2)].
      - apply in_block_In in Ha as (b' & Hb' & Hr').
        pose proof (gl_apart _ _ _ GL _ _ _ _ _ _ _ G) as BA. apply blocks_apart_app_inv in BA as (BA & _ & _).
        apply blocks_apart_app_inv in BA as (_ & _ & BX). specialize (BX b b' Hb Hb'). unfold apart in BX. lia.
      - apply (gl_fr_apart _ _ _ GL _ _ _ _ _ _ _ a G); [|exact HaB].
        apply in_frames_In. exists fr. split; [apply in_or_app; right; exact Hf| lia]. }
    clear - OW OX. induction W as [|[lo hi] W IH]; [exact OX|]. destruct OW as [O1 O2]. split; [exact O1| apply IH; exact O2].
  Qed.

  (* [comment removed for export] *)
  #[using="tlsI FO fflagA GL"] Lemma cobjA_keep : forall L RNG RNG' s' CL CL' FB' FL FL' m m' A n,
    cobjA RNG m FL CL A n -> GIOA L RNG' s' CL' FB' FL' m' -> incl CL CL' -> incl FL FL' ->
    agrees_on (in_frame_sh FL) m m' -> 0 < n ->
    cobjA RNG' m' FL CL A n.
  Proof.
    intros L RNG RNG' s' CL CL' FB' FL FL' m m' A n [LOC (A0 & A47 & UNP & _)] G' ICL IFL AG Hn. split; [exact LOC|].
    destruct LOC as [(b & Hb & H1 & H2)|(fr & Hf & H1 & H2)].
    - eapply blockA_aobj; [eapply (gl_block _ _ _ GL); [exact G'| apply in_or_app; left; apply ICL; exact Hb] | exact H1 | exact H2 | lia].
    - destruct (gl_frames _ _ _ GL _ _ _ _ _ _ _ G') as [FA _]. pose proof (proj1 (Forall_forall _ _) FA fr (IFL _ Hf)) as FRA.
      eapply frameA_aobj; [exact FRA| exact H1| exact H2| lia|].
      destruct FRA as (BAND & TOP & A64 & N64 & _ & _ & S64 & _).
      eapply unpoisoned_agree; [exact UNP|]. intros sa Hsa.
      assert (R : 0 <= sa < 2^64 /\ Z.shiftr (fb_addr fr) 3 + 2147450880 <= sa < Z.shiftr (fb_addr fr) 3 + 2147450880 + Z.shiftr (fb_size fr) 3).
      { rewrite !Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8. rewrite !shad_div in Hsa. unfold ASHOFF in Hsa.
        pose proof (ablk_lin _ _ BAND) as (IMG & F0 & _ & T47). atop_facts. Z.div_mod_to_equations. lia. }
      destruct R as [R0 R1].
      apply (AG sa R0). apply in_frame_sh_In. exists fr. split; [exact Hf| exact R1].
  Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma keeps_frame_sh : forall FL (CL : list (@cblock hptr)) SP m m', agrees_on (client_keeps FL CL SP) m m' -> agrees_on (in_frame_sh FL) m m'.
  Proof. intros FL CL SP m m' AG. eapply agrees_on_weaken; [exact AG|]. intros a Ha. right; right; right. exact Ha. Qed.
  (* [comment removed for export] *)
  #[using="tlsI FO fflagA GL"] Lemma keepsx_frame_sh : forall L RNG s CL FB FL FLc (CLc : list (@cblock hptr)) SP WX m0 m m',
    GIOA L RNG s CL FB FL m0 -> incl FLc FL ->
    agrees_on (fun a => client_keeps FLc CLc SP a /\ outside WX a) m m' ->
    Forall (fun iv => ablk (fst iv) (snd iv)) WX -> agrees_on (in_frame_sh FLc) m m'.
  Proof.
    intros L RNG s CL FB FL FLc CLc SP WX m0 m m' G IFL AG FX. eapply agrees_on_weaken; [exact AG|]. intros a Ha.
    split; [right; right; right; exact Ha|].
    pose proof (gia_in_frame_sh_band _ _ _ GL _ _ _ _ _ _ _ a G (in_frame_sh_incl _ _ _ IFL Ha)) as BD.
    clear AG. induction WX as [|[lo hi] WX IH]; [exact I|]. apply Forall_cons_iff in FX as [BAND FX]. split; [| apply IH; exact FX].
    cbn [fst snd] in BAND. apply (ablk_clear_band _ _ a BAND). unfold KLS. lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="Type"] Lemma client_globals_lo : forall g, In g client_globals -> 0x10040 <= fst g /\ 0 <= snd g /\ fst g + snd g <= 0x603fc0.
  Proof.
    intros g Hin. unfold client_globals in Hin. cbn [In] in Hin.
    repeat (destruct Hin as [Hin|Hin]; [subst g; cbn [fst snd]; lia|]). destruct Hin.
  Qed.

  #[using="FO fflagA GL"] Lemma slocA_mobjA_keep : forall L RNG RNG' s' CL CL' FB' FL FL' (m m' : mem) tls P n k,
    slocA tls FL CL P n k -> mobjA RNG m P n -> GIOA L RNG' s' CL' FB' FL' m' -> incl CL CL' -> incl FL FL' ->
    agrees_on (in_frame_sh FL) m m' -> rng_aimg RNG' -> rng_aimg_sh RNG' -> rng_atls RNG' -> 0 < n -> 0 <= k ->
    mobjA RNG' m' P n.
  Proof.
    intros L RNG RNG' s' CL CL' FB' FL FL' m m' tls P n k LOC (A0 & A47 & UNP & _) G' ICL IFL AG RI RS RT Hn Hk.
    destruct LOC as [[(b & Hb & H1 & H2)|(fr & Hf & H1 & H2)]|[(g & Hg & G1 & G2 & G3 & G4)|(_ & T1 & T2)]].
    - apply aobjA_mobjA; [|lia]. eapply blockA_aobj; [eapply (gl_block _ _ _ GL); [exact G'| apply in_or_app; left; apply ICL; exact Hb] | exact H1 | lia | lia].
    - apply aobjA_mobjA; [|lia].
      destruct (gl_frames _ _ _ GL _ _ _ _ _ _ _ G') as [FA _]. pose proof (proj1 (Forall_forall _ _) FA fr (IFL _ Hf)) as FRA.
      eapply frameA_aobj; [exact FRA| exact H1| lia| lia|].
      destruct FRA as (BAND & TOP & A64 & N64 & _ & _ & S64 & _).
      eapply unpoisoned_agree; [exact UNP|]. intros sa Hsa.
      assert (R : 0 <= sa < 2^64 /\ Z.shiftr (fb_addr fr) 3 + 2147450880 <= sa < Z.shiftr (fb_addr fr) 3 + 2147450880 + Z.shiftr (fb_size fr) 3).
      { rewrite !Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8. rewrite !shad_div in Hsa. unfold ASHOFF in Hsa.
        pose proof (ablk_lin _ _ BAND) as (IMG & F0 & _ & T47). atop_facts. Z.div_mod_to_equations. lia. }
      destruct R as [R0 R1].
      apply (AG sa R0). apply in_frame_sh_In. exists fr. split; [exact Hf| exact R1].
    - pose proof (client_globals_lo g Hg) as (GLO & GN & _).
      eapply mobjA_sub; [eapply (gia_global_mobjA _ _ _ GL _ _ _ _ _ _ _ (fst g) (snd g)); [exact G' | destruct g; exact Hg | exact RI | exact RS] | lia | lia | lia].
    - eapply mobjA_sub; [eapply (gl_tls _ _ _ GL); [exact G' | exact RT] | lia | lia | lia].
  Qed.

  #[using="FO fflagA GL"] Lemma farg_word_keep : forall L RNG RNG' s' CL CL' FB' FL FL' SPk SP SP' D dn (m m' : mem) a w,
    farg_word false L RNG FL CL SP D dn m a w ->
    GIOA L RNG' s' CL' FB' FL' m' -> incl CL CL' -> incl FL FL' -> fp_le RNG RNG' ->
    agrees_on (client_keeps FL CL SPk) m m' -> mem_inv asegs m -> mem_inv asegs m' ->
    rng_aimg RNG' -> rng_aimg_sh RNG' -> rng_atls RNG' ->
    farg_word false L RNG' FL' CL' SP' D dn m' a w.
  Proof.
    intros L RNG RNG' s' CL CL' FB' FL FL' SPk SP SP' D dn m m' a w FW G' ICL IFL FP AG MI MI' RI RS RT.
    destruct a as [z|cs]; cbn [farg_word] in *; [exact FW|].
    destruct FW as (P & bs & slack & -> & HB & NN & -> & LEN & SLK & DIS & LOC & OBJ & RNGS).
    exists P, bs, slack. split; [reflexivity|].
    pose proof (bytes_at_bound _ _ _ _ HB) as BB. rewrite length_app in BB. cbn [length] in BB.
    split.
    { destruct LOC as [LC|[(g & Hg & G1 & G2 & G3 & G4)|(T0 & _)]]; [| | discriminate T0].
      - eapply agrees_bytes_at; [exact AG | exact HB |]. intros x Hx. rewrite length_app in Hx. cbn [length] in Hx.
        eapply clocA_keeps; [exact LC| lia].
      - pose proof (client_globals_lo g Hg) as (GLO & _). eapply ro_bytes_at_any; [exact MI | exact MI' | exact HB | lia |].
        rewrite length_app. cbn [length]. lia. }
    split; [exact NN|]. split; [reflexivity|]. split; [exact LEN|]. split; [exact SLK|]. split; [exact DIS|].
    split.
    { destruct LOC as [LC|[GC|(T0 & _)]]; [left; eapply clocA_incl; eassumption | right; left; exact GC | discriminate T0]. }
    split; [| eapply rng_fp_le; eassumption].
    eapply slocA_mobjA_keep; [exact LOC | exact OBJ | exact G' | exact ICL | exact IFL | | exact RI | exact RS | exact RT | lia | lia].
    eapply agrees_on_weaken; [exact AG|]. intros x Hx. right; right; right. exact Hx.
  Qed.

  (* [comment removed for export] *)
  #[using="FO fflagA GL"] Lemma clocA_apart_tls : forall L RNG s CL FB FL m A n, GIOA L RNG s CL FB FL m -> clocA FL CL A n -> 0 < n ->
    A + n <= ATP + -200 \/ ATP + -200 + 504 <= A.
  Proof.
    intros L RNG s CL FB FL m A n G LOC Hn.
    assert (PW : forall a, A <= a < A + n -> ~ (ATP + -200 <= a < ATP + -200 + 504)).
    { intros a Ha. apply (gl_tls_apart _ _ _ GL _ _ _ _ _ _ _ a G).
      destruct LOC as [(b & Hb & H1 & H2)|(fr & Hf & H1 & H2)].
      - left. apply in_block_app. left. apply in_block_In. exists b. split; [exact Hb| lia].
      - right. apply in_frames_In. exists fr. split; [exact Hf| lia]. }
    destruct (Z_le_gt_dec (A + n) (ATP + -200)) as [?|X]; [left; assumption|].
    destruct (Z_le_gt_dec (ATP + -200 + 504) A) as [?|Y]; [right; assumption|]. exfalso.
    destruct (Z_le_gt_dec A (ATP + -200)) as [Z1|Z1]; [apply (PW (ATP + -200)); lia | apply (PW A); lia].
  Qed.

  #[using="Type"] Lemma fmt_at_keep : forall (m m' : mem) FMTA fs, fmt_at m FMTA fs -> mem_inv asegs m -> mem_inv asegs m' -> fmt_at m' FMTA fs.
  Proof.
    intros m m' FMTA fs (HB & H1 & H2 & H3) MI MI'. split; [|split; [exact H1| split; [exact H2| exact H3]]].
    eapply ro_bytes_at_any; [exact MI | exact MI' | exact HB | lia |].
    pose proof (bytes_at_bound _ _ _ _ HB) as BB. rewrite length_app, length_map in *. cbn [length] in *.
    assert (E : length (String.list_ascii_of_string fs) = String.length fs) by (clear; induction fs as [|c fs IH]; cbn; [reflexivity| now rewrite IH]).
    rewrite E. lia.
  Qed.
End Cobj.
End CANSEC1.

(* [comment removed for export] *)
Ltac own_iv1 :=
  unfold own_ivA, iv_in_block, iv_in_frames, iv_in_frame_shadow;
  first [ left; cbn [fst snd]; lia
        | right; right; left; apply Exists_cons_hd; cbn [fb_addr fb_size fst snd]; lia
        | right; right; right; apply Exists_cons_hd; cbn [fb_addr fb_size fst snd]; shr_consts; lia
        | right; left; first [ apply Exists_cons_hd | apply Exists_cons_tl; apply Exists_cons_hd | apply Exists_cons_tl; apply Exists_cons_tl; apply Exists_cons_hd ];
          cbn [cb_addr cb_size fst snd]; lia ].
Ltac own_ivs := repeat (apply Forall_cons; [own_iv1|]); apply Forall_nil.
Ltac cobj_iv1 :=
  split; [ cbn [fst snd];
           lazymatch goal with |- clocA _ _ ?A ?d =>
             match goal with O : cobjA _ _ _ _ A ?n |- _ => replace d with n by lia; exact (proj1 O) end end
         | cbn [fst snd]; lia ].
Ltac cobj_ivs := repeat (apply Forall_cons; [cobj_iv1|]); apply Forall_nil.

(* [comment removed for export] *)
Ltac zstep_sh0 :=
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) =>
    lazymatch goal with SH : rw_cells asegs mx (Z.shiftr _ 3 + 2147450880)%Z _ |- _ =>
      let SOK := fresh "SOK" in
      pose proof (rw_cells_store_ok asegs mx _ _ 0%nat _ 1%nat SH ltac:(cells_cbv; reflexivity) ltac:(reflexivity)) as SOK; zstep; clear SOK
    end
  end.

(* [comment removed for export] *)
Ltac join_a0 OK V :=
  cbv beta delta [mkR];
  lazymatch goal with
  | |- evtF ?segs ?RNG ?Q (MS ?R ?F ?pc ?fc ?rv ?m ?ro) =>
      eapply (evtF_cut segs RNG (fun ms' => ms' = MS (bvmap_set (Z_to_bv 5 10) V R) F (Z_to_bv 64 OK) fc rv m ro));
      [ | let ms' := fresh "ms'" in let H := fresh "Hj" in intros ms' H; subst ms'; simp_regs ]
  end.
Ltac join_done := apply evtF_done; simp_regs; reflexivity.

(* [comment removed for export] *)
Ltac disj_ind H k :=
  let k0 := fresh k "r" in let k1 := fresh k "a" in let k2 := fresh k "b" in
  lazymatch type of H with
  | (?x <= ?b \/ ?y <= ?a)%Z =>
      assert (exists k : Z, (0 <= k <= 1 /\ x <= b + k * 18446744073709551616 /\ y <= a + (1 - k) * 18446744073709551616)%Z)
        as (k & k0 & k1 & k2) by (destruct H; [exists 0%Z | exists 1%Z]; lia)
  end.
End TwB.
End FrameKit.

(* [comment removed for export] *)
Module F_ngblk_epiA.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr Bytes ZBridge ITree Nodes Decode SysStep Frame StoreFast.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import Prelim Monad Fmt StdioCore Stdio PcapPrelim PcapTypes PcapPure Pcap Prog.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_kit__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import ExecF ITreeA Shadow StepF SysStepF RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import AImg ABase AMalloc_iface.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require CkTac__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadG GIA PcapRepA UnwKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadGX__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require Pcap_ifaceA. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.CkTac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FrameKit__A3P.FrameKit.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_chunks_extra m a bs n Hn Ha Hl ::= unp_store m a bs n Hn Ha Hl.
Local Ltac transport_call_extra segs W m m' MU WM ::= unp_call W m m' MU.
Ltac hide H := lazymatch type of H with ?T => let X := fresh "AUX" in set (X := T) in H end.
Ltac unhide H := lazymatch type of H with ?X => subst X end.
Ltac ienterG := lazymatch goal with |- implMG _ _ _ ?Q _ => let QQ := fresh "POSTQ" in set (QQ := Q) end; apply implMG_from_evtF.

Lemma land_m32B : forall x, (0 <= x < 2^64)%Z -> Z.land x 18446744073709551584 = (x - x mod 32)%Z.
Proof. intros x Hx. exact (land_align_down x 5 Hx ltac:(lia)). Qed.

Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
Section RbEpi.
  Context {H hptr : Type} (HO : HeapOps H hptr) (FO : @FrameOps H hptr) (sites : stack_site -> Z).
  Variable GIOA : alayout -> footprint -> PState H hptr -> list (@cblock hptr) -> list (@cblock hptr) -> list fblock -> mem -> Prop.
  Variable TP : tparams.
  Variable fflagA : alayout -> fframe -> Z -> Z.
  Hypothesis GL : gia_laws FO GIOA fflagA.
  Hypothesis FRET : fret_inline_law FO GIOA fflagA.

  Definition rb_epi__stmt : Prop := forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (L : alayout) (RNG : footprint) (s : PState H hptr) (CLc PB FB : list (@cblock hptr)) (FL : list fblock) (lo SPA Fb : Z) (m : mem)
      (ra0 sp0 t0 t1 t2 r9 av a1 a2 a3 a4 a5 a6 a7 r19 r21 r22 r23 r24 r25 r26 t3 t4 t5 t6 : word)
      (jS : list byte) (k0 k1 k2 : word) (pre post : list byte) (b0 b1 b2 b3 b4 b5 b6 b7 : byte)
      (A : Type) (x : A),
    (bv_unsigned sp - 208 <= SPA <= bv_unsigned sp - 192)%Z -> (SPA mod 32 = 0)%Z -> (ATOP + 4096 <= lo)%Z -> (lo <= SPA)%Z ->
    (bv_unsigned sp + 16 < al_top L)%Z -> (al_top L <= 2^47)%Z ->
    GIOA L RNG s (CLc ++ PB) FB ((FF_READ_BLOCK, Fb, 64%Z) :: FL) m -> mem_inv asegs m ->
    stk asegs m lo SPA -> stk asegs m (SPA + 88) (bv_unsigned sp + -104) ->
    rw_cells asegs m SPA [CB 88 jS] ->
    rw_cells asegs m (bv_unsigned sp + -104) [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    rw_cells asegs m Fb [C8 k0; C8 k1; C8 k2; CB 8 pre] ->
    rw_cells asegs m (Fb + 40) [CB 16 post; C8 (Z_to_bv 64 (fflagA L FF_READ_BLOCK Fb))] ->
    rw_cells asegs m (Z.shiftr Fb 3 + 2147450880) [C1 b0; C1 b1; C1 b2; C1 b3; C1 b4; C1 b5; C1 b6; C1 b7] ->
    rng RNG lo (al_top L - lo) ->
    implMG RNG (fo_ret FO _ FF_READ_BLOCK x) s
      (fun r s' RNG' ms' => r = x /\ RNG' = RNG /\ exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m',
           ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 av a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                    F (ret_pc ra) fc None m' (seg_rom asegs)
           /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
           /\ agrees_on (client_keeps FL CLc (bv_unsigned sp)) m m' /\ agrees_on (fun a => in_block (CLc ++ PB) a) m m'
           /\ GIOA L RNG s' (CLc ++ PB) FB FL m' /\ ps_outfile s' = ps_outfile s)
      (MS (mkR ra0 sp0 gp tp t0 t1 t2 sp r9 av a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 Fb) r19 (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450880)) r21 r22 r23 r24 r25 r26 (Z_to_bv 64 Fb) t3 t4 t5 t6)
          F (Z_to_bv 64 0x8bdb0) fc None m (seg_rom asegs)).
  Section Sz2.
  Variables ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG s CLc PB FB FL lo SPA Fb m ra0 sp0 t0 t1 t2 r9 av a1 a2 a3 a4 a5 a6 a7 r19 r21 r22 r23 r24 r25 r26 t3 t4 t5 t6 jS k0 k1 k2 pre post b0 b1 b2 b3 b4 b5 b6 b7 A x : ltac2:(SecDiet.SzSec.tyM 'rb_epi__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  #[using="tlsI GL FRET"] Lemma rb_epi__body : ltac2:(SecDiet.SzSec.bodyP 'rb_epi__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof.
 intros SPAB SPA32 LO LOS SPT TOP47 G MI ST STG FRA FR FRC1 FRC3 SHC RSTK.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    destruct (gl_frames _ _ _ GL _ _ _ _ _ _ _ G) as [FAll _]. pose proof (Forall_inv FAll) as (FBAND & FTOP & F64 & _ & FRNG & FSRNG & _ & _).
    cbn [fb_addr fb_size fst snd] in FBAND, FTOP, F64, FRNG, FSRNG. clear FAll. change (Z.shiftr 64 3) with 8%Z in FSRNG.
    pose proof (ablk_lin _ _ FBAND) as (_ & Fb0 & _ & _). band_ind FBAND bF.
    destruct (flag_facts _ _ _ GL _ _ _ _ _ _ _ _ _ _ G) as (_ & FLR & FLB & FLT & _ & (kF & kFr & kF1 & kF2)). band_ind FLB bG.
    assert (SHLO : (0x7fff8000 <= Z.shiftr Fb 3 + 2147450880 /\ Z.shiftr Fb 3 + 2147450880 + 8 <= 0x10007fff8000)%Z)
      by (rewrite Z.shiftr_div_pow2 by lia; change (2^3)%Z with 8%Z; Z.div_mod_to_equations; lia).
    destruct SHLO as (SLO & SHI).
    assert (FW : Forall (own_ivA [(FF_READ_BLOCK, Fb, 64%Z)] ([] : list (@cblock hptr)) (bv_unsigned sp))
                   [(Fb, Fb + 64); (Z.shiftr Fb 3 + 2147450880, Z.shiftr Fb 3 + 2147450880 + 8)]%Z) by own_ivs.
    pose proof (munch_refl [(Fb, Fb + 64); (Z.shiftr Fb 3 + 2147450880, Z.shiftr Fb 3 + 2147450880 + 8)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
    ienterG.
    zstep. neg_lits.
    zstep.
    do 3 zstep.
    zstep. if_false_by (eqz_false Fb ltac:(lia)).
    zstep. neg_lits.
    do 4 zstep. zstep_sh0. do 3 zstep.
    zstep.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      destruct (own_writes _ _ _ GL _ _ _ _ _ _ _ _ _ mm _ [] _ (Forall_impl _ (own_ivA_PB _ PB _) FW) (Forall_nil _) G MU WM ltac:(lia)) as [G5 AG5];
      assert (AGP5 : agrees_on (fun a => in_block (CLc ++ PB) a) m mm)
        by (eapply agrees_on_of_munch; [exact MU| exact WM|]; intros a _ Ha;
            exact (pb_outside _ _ _ GL _ _ _ [] (CLc ++ PB) _ _ _ _ _ [] (bv_unsigned sp) FW (Forall_nil _) G a Ha));
      pose proof (munch_refl [(fflagA L FF_READ_BLOCK Fb, fflagA L FF_READ_BLOCK Fb + 1)]%Z mm) as MU2; pose proof (wmono_refl asegs mm) as WM2
    end.
    destruct (flag_facts _ _ _ GL _ _ _ _ _ _ _ _ _ _ G5) as (FLC & _).
    clear MU WM.
    zstep.
    apply evtF_done. eapply FRET; [exact G5 | unfold ff_class; lia | exact MU2 | exact WM2 | exact FLC |].
    intros s3' G6 OF3 LC3 TL3.
    clear FRNG FSRNG FLR kF kFr kF1 kF2 bF bFr bFhi bFlo bFimg bG bGr bGhi bGlo bGimg SLO SHI.
    zstep.
    do 16 zstep.
    release_frame FRA ST (SPA + 88)%Z.
    pose proof (stk_merge asegs _ _ _ _ ST STG ltac:(lia)) as ST3. clear ST STG.
    release_frame FR ST3 (bv_unsigned sp).
    destruct (flag_keeps _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ CLc (bv_unsigned sp) G5 MU2 WM2 (incl_appl _ (incl_refl _)) ltac:(lia)) as [AG6 AGP6].
    apply evtF_done. subst POSTQ. cbv beta iota.
    split; [reflexivity|]. split; [reflexivity|].
    do 14 eexists. lazymatch goal with |- context [MS _ _ _ _ _ ?mm _] => exists mm end.
    split; [reflexivity|]. split; [assumption|]. split; [exact ST3|].
    split. { eapply agrees_on_trans; [eapply agrees_on_weaken; [exact AG5|]; intros a K; split; [exact K| exact I] | exact AG6]. }
    split. { eapply agrees_on_trans; [exact AGP5| exact AGP6]. }
    split; [exact G6| exact OF3].
  Qed.
  End Sz2.
  #[using="tlsI GL FRET"] Lemma rb_epi : ltac:(let t := eval cbv delta [rb_epi__stmt] in rb_epi__stmt in exact t).
  Proof. intros ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG s CLc PB FB FL lo SPA Fb m ra0 sp0 t0 t1 t2 r9 av a1 a2 a3 a4 a5 a6 a7 r19 r21 r22 r23 r24 r25 r26 t3 t4 t5 t6 jS k0 k1 k2 pre post b0 b1 b2 b3 b4 b5 b6 b7 A x. ltac2:(SecDiet.SzSec.closeP 'rb_epi__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End RbEpi.
End CANSEC1.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Bytes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ZBridge OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Frame OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.StoreFast.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Fmt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Stdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPrelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapTypes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPure OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Pcap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prog.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ExecF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ITreeA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.Shadow OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.StepF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.SysStepF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AMalloc_iface.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.CkTac.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FrameKit__A3P.FrameKit.TwB.
(* [comment removed for export] *) Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_chunks_extra m a bs n Hn Ha Hl ::= unp_store m a bs n Hn Ha Hl.
Local Ltac transport_call_extra segs W m m' MU WM ::= unp_call W m m' MU.
Ltac hide H := lazymatch type of H with ?T => let X := fresh "AUX" in set (X := T) in H end.
Ltac unhide H := lazymatch type of H with ?X => subst X end.
Ltac ienterG := lazymatch goal with |- implMG _ _ _ ?Q _ => let QQ := fresh "POSTQ" in set (QQ := Q) end; apply implMG_from_evtF.

Lemma land_m32B : forall x, (0 <= x < 2^64)%Z -> Z.land x 18446744073709551584 = (x - x mod 32)%Z.
Proof. intros x Hx. exact (land_align_down x 5 Hx ltac:(lia)). Qed.

Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
Section RbEpi.
  Context {H hptr : Type} (HO : HeapOps H hptr) (FO : @FrameOps H hptr) (sites : stack_site -> Z).
  Variable GIOA : alayout -> footprint -> PState H hptr -> list (@cblock hptr) -> list (@cblock hptr) -> list fblock -> mem -> Prop.
  Variable TP : tparams.
  Variable fflagA : alayout -> fframe -> Z -> Z.
  Hypothesis GL : gia_laws FO GIOA fflagA.
  Hypothesis FRET : fret_inline_law FO GIOA fflagA.

  Definition rb_epi__stmt : Prop := forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (L : alayout) (RNG : footprint) (s : PState H hptr) (CLc PB FB : list (@cblock hptr)) (FL : list fblock) (lo SPA Fb : Z) (m : mem)
      (ra0 sp0 t0 t1 t2 r9 av a1 a2 a3 a4 a5 a6 a7 r19 r21 r22 r23 r24 r25 r26 t3 t4 t5 t6 : word)
      (jS : list byte) (k0 k1 k2 : word) (pre post : list byte) (b0 b1 b2 b3 b4 b5 b6 b7 : byte)
      (A : Type) (x : A),
    (bv_unsigned sp - 208 <= SPA <= bv_unsigned sp - 192)%Z -> (SPA mod 32 = 0)%Z -> (ATOP + 4096 <= lo)%Z -> (lo <= SPA)%Z ->
    (bv_unsigned sp + 16 < al_top L)%Z -> (al_top L <= 2^47)%Z ->
    GIOA L RNG s (CLc ++ PB) FB ((FF_READ_BLOCK, Fb, 64%Z) :: FL) m -> mem_inv asegs m ->
    stk asegs m lo SPA -> stk asegs m (SPA + 88) (bv_unsigned sp + -104) ->
    rw_cells asegs m SPA [CB 88 jS] ->
    rw_cells asegs m (bv_unsigned sp + -104) [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    rw_cells asegs m Fb [C8 k0; C8 k1; C8 k2; CB 8 pre] ->
    rw_cells asegs m (Fb + 40) [CB 16 post; C8 (Z_to_bv 64 (fflagA L FF_READ_BLOCK Fb))] ->
    rw_cells asegs m (Z.shiftr Fb 3 + 2147450880) [C1 b0; C1 b1; C1 b2; C1 b3; C1 b4; C1 b5; C1 b6; C1 b7] ->
    rng RNG lo (al_top L - lo) ->
    implMG RNG (fo_ret FO _ FF_READ_BLOCK x) s
      (fun r s' RNG' ms' => r = x /\ RNG' = RNG /\ exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m',
           ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 av a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                    F (ret_pc ra) fc None m' (seg_rom asegs)
           /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
           /\ agrees_on (client_keeps FL CLc (bv_unsigned sp)) m m' /\ agrees_on (fun a => in_block (CLc ++ PB) a) m m'
           /\ GIOA L RNG s' (CLc ++ PB) FB FL m' /\ ps_outfile s' = ps_outfile s)
      (MS (mkR ra0 sp0 gp tp t0 t1 t2 sp r9 av a1 a2 a3 a4 a5 a7 a6
               (Z_to_bv 64 Fb) r26 (Z_to_bv 64 Fb) r21 r22 r24 r23 r25 r19 (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450880)) t3 t4 t5 t6)
          F (Z_to_bv 64 0x8bd70) fc None m (seg_rom asegs)).
  Section Sz2.
  Variables ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG s CLc PB FB FL lo SPA Fb m ra0 sp0 t0 t1 t2 r9 av a1 a2 a3 a4 a5 a6 a7 r19 r21 r22 r23 r24 r25 r26 t3 t4 t5 t6 jS k0 k1 k2 pre post b0 b1 b2 b3 b4 b5 b6 b7 A x : ltac2:(SecDiet.SzSec.tyM 'rb_epi__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  #[using="tlsI GL FRET"] Lemma rb_epi__body : ltac2:(SecDiet.SzSec.bodyP 'rb_epi__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof.
 intros SPAB SPA32 LO LOS SPT TOP47 G MI ST STG FRA FR FRC1 FRC3 SHC RSTK.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    destruct (gl_frames _ _ _ GL _ _ _ _ _ _ _ G) as [FAll _]. pose proof (Forall_inv FAll) as (FBAND & FTOP & F64 & _ & FRNG & FSRNG & _ & _).
    cbn [fb_addr fb_size fst snd] in FBAND, FTOP, F64, FRNG, FSRNG. clear FAll. change (Z.shiftr 64 3) with 8%Z in FSRNG.
    pose proof (ablk_lin _ _ FBAND) as (_ & Fb0 & _ & _). band_ind FBAND bF.
    destruct (flag_facts _ _ _ GL _ _ _ _ _ _ _ _ _ _ G) as (_ & FLR & FLB & FLT & _ & (kF & kFr & kF1 & kF2)). band_ind FLB bG.
    assert (SHLO : (0x7fff8000 <= Z.shiftr Fb 3 + 2147450880 /\ Z.shiftr Fb 3 + 2147450880 + 8 <= 0x10007fff8000)%Z)
      by (rewrite Z.shiftr_div_pow2 by lia; change (2^3)%Z with 8%Z; Z.div_mod_to_equations; lia).
    destruct SHLO as (SLO & SHI).
    assert (FW : Forall (own_ivA [(FF_READ_BLOCK, Fb, 64%Z)] ([] : list (@cblock hptr)) (bv_unsigned sp))
                   [(Fb, Fb + 64); (Z.shiftr Fb 3 + 2147450880, Z.shiftr Fb 3 + 2147450880 + 8)]%Z) by own_ivs.
    pose proof (munch_refl [(Fb, Fb + 64); (Z.shiftr Fb 3 + 2147450880, Z.shiftr Fb 3 + 2147450880 + 8)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
    ienterG.
    zstep. neg_lits.
    zstep.
    do 3 zstep.
    zstep. if_false_by (eqz_false Fb ltac:(lia)).
    zstep. neg_lits.
    do 4 zstep. zstep_sh0. do 3 zstep.
    zstep.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      destruct (own_writes _ _ _ GL _ _ _ _ _ _ _ _ _ mm _ [] _ (Forall_impl _ (own_ivA_PB _ PB _) FW) (Forall_nil _) G MU WM ltac:(lia)) as [G5 AG5];
      assert (AGP5 : agrees_on (fun a => in_block (CLc ++ PB) a) m mm)
        by (eapply agrees_on_of_munch; [exact MU| exact WM|]; intros a _ Ha;
            exact (pb_outside _ _ _ GL _ _ _ [] (CLc ++ PB) _ _ _ _ _ [] (bv_unsigned sp) FW (Forall_nil _) G a Ha));
      pose proof (munch_refl [(fflagA L FF_READ_BLOCK Fb, fflagA L FF_READ_BLOCK Fb + 1)]%Z mm) as MU2; pose proof (wmono_refl asegs mm) as WM2
    end.
    destruct (flag_facts _ _ _ GL _ _ _ _ _ _ _ _ _ _ G5) as (FLC & _).
    clear MU WM.
    zstep.
    apply evtF_done. eapply FRET; [exact G5 | unfold ff_class; lia | exact MU2 | exact WM2 | exact FLC |].
    intros s3' G6 OF3 LC3 TL3.
    clear FRNG FSRNG FLR kF kFr kF1 kF2 bF bFr bFhi bFlo bFimg bG bGr bGhi bGlo bGimg SLO SHI.
    zstep.
    do 16 zstep.
    release_frame FRA ST (SPA + 88)%Z.
    pose proof (stk_merge asegs _ _ _ _ ST STG ltac:(lia)) as ST3. clear ST STG.
    release_frame FR ST3 (bv_unsigned sp).
    destruct (flag_keeps _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ CLc (bv_unsigned sp) G5 MU2 WM2 (incl_appl _ (incl_refl _)) ltac:(lia)) as [AG6 AGP6].
    apply evtF_done. subst POSTQ. cbv beta iota.
    split; [reflexivity|]. split; [reflexivity|].
    do 14 eexists. lazymatch goal with |- context [MS _ _ _ _ _ ?mm _] => exists mm end.
    split; [reflexivity|]. split; [assumption|]. split; [exact ST3|].
    split. { eapply agrees_on_trans; [eapply agrees_on_weaken; [exact AG5|]; intros a K; split; [exact K| exact I] | exact AG6]. }
    split. { eapply agrees_on_trans; [exact AGP5| exact AGP6]. }
    split; [exact G6| exact OF3].
  Qed.
  End Sz2.
  #[using="tlsI GL FRET"] Lemma rb_epi : ltac:(let t := eval cbv delta [rb_epi__stmt] in rb_epi__stmt in exact t).
  Proof. intros ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG s CLc PB FB FL lo SPA Fb m ra0 sp0 t0 t1 t2 r9 av a1 a2 a3 a4 a5 a6 a7 r19 r21 r22 r23 r24 r25 r26 t3 t4 t5 t6 jS k0 k1 k2 pre post b0 b1 b2 b3 b4 b5 b6 b7 A x. ltac2:(SecDiet.SzSec.closeP 'rb_epi__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End RbEpi.
End CANSEC1.
End TwB.
End F_ngblk_epiA.

(* [comment removed for export] *)
Module F_ngblk_defsA.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr Bytes ZBridge ITree Nodes Decode SysStep Frame StoreFast.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import Prelim Monad Fmt StdioCore Stdio PcapPrelim PcapTypes PcapPure Pcap Prog.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_kit__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import ExecF ITreeA Shadow StepF SysStepF RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import AImg ABase AMalloc_iface.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require CkTac__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadG GIA PcapRepA UnwKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadGX__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require Pcap_ifaceA Pcap_iface_ngA. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.CkTac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_iface_ngA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FrameKit__A3P.FrameKit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition rb_shadow : list cell :=
  [C1 (Z_to_bv 8 18446744073709551601); C1 (Z_to_bv 8 18446744073709551601); C1 (Z_to_bv 8 18446744073709551601); C1 (Z_to_bv 8 18446744073709551601);
   C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 18446744073709551603); C1 (Z_to_bv 8 18446744073709551603); C1 (Z_to_bv 8 18446744073709551603)].

Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
Section RbModel.
  Context {H hptr : Type} (HO : HeapOps H hptr) (FO : @FrameOps H hptr) (sites : stack_site -> Z).
  #[local] Abbreviation PS := (PState H hptr).
  #[local] Abbreviation pcapT := (PcapTypes.pcap hptr hptr).
  #[local] Abbreviation PR := (prims HO FO sites).

  (* [comment removed for export] *)
  Definition rb_bodyA (f : hptr) (bt tl : Z) (p0 : pcapT) : Monad.M PS block_result :=
    let p1 := set_bufdata (le_bytes 4 bt ++ le_bytes 4 tl) p0 in
    mo_bind MOps (read_bytes MOps PR f (DHeap (pc_buffer p1) 8) (tl - 8) true) (fun x => let '(st, data) := x in
    let p2 := set_bufdata (pc_bufdata p1 ++ data) p1 in
    match st with
    | RBS_Err m => e_fret PR FF_READ_BLOCK (RB_Err m p2)
    | RBS_Eof => e_fret PR FF_READ_BLOCK (RB_Err [] p2)
    | RBS_Ok =>
      let toff := tl - 4 in
      let p3 := if pc_swapped p2 then set_bufdata (swap_field 4 toff (pc_bufdata p2)) p2 else p2 in
      let trailer_length := get_le32 (pc_bufdata p3) toff in
      if negb (tl =? trailer_length)
      then e_fret PR FF_READ_BLOCK (RB_Err (Msg.header_trailer_mismatch tl trailer_length) p3)
      else e_fret PR FF_READ_BLOCK (RB_Ok (mkCursor 8 (tl - 12) bt) p3)
    end).

  Definition rb_tailA (f : hptr) (bt tl : Z) (p : pcapT) : Monad.M PS block_result :=
    if tl <? 12 then e_fret PR FF_READ_BLOCK (RB_Err (Msg.block_length_lt tl) p)
    else if negb (tl mod 4 =? 0) then e_fret PR FF_READ_BLOCK (RB_Err (Msg.block_length_not_mult4 tl) p)
    else
    mo_bind MOps
      (if pc_bufsize p <? tl then
         if ng_max_blocksize (ng_of p) <? tl
         then mo_ret MOps (Some (Msg.block_size_gt_max tl (ng_max_blocksize (ng_of p))), p)
         else
           mo_bind MOps (e_realloc PR (pc_buffer p) tl) (fun r =>
           match r with
           | None => mo_ret MOps (Some Msg.out_of_memory, p)
           | Some b => mo_ret MOps (@None (list Z), set_buffer b (pc_bufsize p) tl (zfirstn tl (pc_bufdata p)) p)
           end)
       else mo_ret MOps (@None (list Z), p))
      (fun x => let '(gerr, p0) := x in
       match gerr with
       | Some m => e_fret PR FF_READ_BLOCK (RB_Err m p0)
       | None => rb_bodyA f bt tl p0
       end).

  #[using="Type"] Lemma read_block_eqA : forall a_bhdr (p : pcapT),
    read_block MOps PR a_bhdr p =
    e_fenter PR FF_READ_BLOCK
      (mo_bind MOps (read_bytes MOps PR (pc_rfile p) a_bhdr 8 false) (fun x => let '(st, bh) := x in
        match st with
        | RBS_Eof => e_fret PR FF_READ_BLOCK (RB_Eof p)
        | RBS_Err m => e_fret PR FF_READ_BLOCK (RB_Err m p)
        | RBS_Ok => rb_tailA (pc_rfile p)
                      (if pc_swapped p then bswap32 (get_le32 bh 0) else get_le32 bh 0)
                      (if pc_swapped p then bswap32 (get_le32 bh 4) else get_le32 bh 4) p
        end)).
  Proof. intros. reflexivity. Qed.
End RbModel.
Section RbDefs.
  Context {H hptr : Type} (HO : HeapOps H hptr) (FO : @FrameOps H hptr) (sites : stack_site -> Z).
  Variable GIOA : alayout -> footprint -> PState H hptr -> list (@cblock hptr) -> list (@cblock hptr) -> list fblock -> mem -> Prop.
  Variable TP : tparams.
  Variable fflagA : alayout -> fframe -> Z -> Z.
  #[local] Abbreviation pcapT := (PcapTypes.pcap hptr hptr).

  (* [comment removed for export] *)
  Definition rb_ctx (ra sp tp s0 : word) (L : alayout) (RNG : footprint) (C1 C2 FB : list (@cblock hptr)) (FL : list fblock) (trC : list Z)
      (lo P CUR EB Af SPA : Z) (self f : hptr) (m : mem) : Prop :=
    (ATOP + 4096 <= lo)%Z /\ (lo + READ_BLOCK_STACK <= bv_unsigned sp)%Z /\ (bv_unsigned sp + 16 < al_top L /\ al_top L <= 2^47)%Z
    /\ tp = Z_to_bv 64 ATP /\ (bv_unsigned sp mod 16 = 0)%Z
    /\ (rng RNG lo (al_top L - lo) /\ rng_aimg RNG /\ rng_aimg_sh RNG /\ rng_atls RNG)
    /\ ucallerA depth_read_block L m sp s0 ra trC /\ traces_read_block TP L (bv_unsigned ra) trC
    /\ nofr frames_read_block FL /\ In (f, Af, FILE_BLOCK) FB
    /\ In (self, P, PCAP_NG_SF_TOTAL) (C1 ++ C2)
    /\ (bv_unsigned sp <= CUR /\ CUR + 24 <= al_top L)%Z /\ (CUR mod 8 = 0)%Z
    /\ ((cobjA RNG m FL (C1 ++ C2) EB 256 /\ (EB + 256 <= CUR \/ CUR + 24 <= EB)%Z /\ (EB + 256 <= P \/ P + PCAP_NG_SF_TOTAL <= EB)%Z) \/ (P + 216 = EB)%Z)
    /\ (EB mod 8 = 0)%Z
    /\ (bv_unsigned sp - 208 <= SPA <= bv_unsigned sp - 192)%Z /\ (SPA mod 32 = 0)%Z.

  (* [comment removed for export] *)
  Definition rb_inv (ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (L : alayout) (RNG : footprint) (C1 C2 FB : list (@cblock hptr)) (FL : list fblock)
      (lo P CUR EB SPA Fb : Z) (o : option hptr) (m : mem)
      (RNGx : footprint) (sx : PState H hptr) (bq : hptr) (B alloc : Z) (mm : mem) : Prop :=
    fp_le RNG RNGx /\ GIOA L RNGx sx ((C1 ++ C2) ++ [(bq, B, alloc)]) FB ((FF_READ_BLOCK, Fb, 64%Z) :: FL) mm /\ ps_outfile sx = o /\ mem_inv asegs mm
    /\ stk asegs mm lo SPA /\ stk asegs mm (SPA + 88) (bv_unsigned sp + -104)
    /\ rw_cells asegs mm (bv_unsigned sp + -104) [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
    /\ agrees_on (fun a => client_keeps FL (C1 ++ C2) (bv_unsigned sp) a /\ ~ (P + 24 <= a < P + 32) /\ ~ (CUR <= a < CUR + 24) /\ ~ (EB <= a < EB + 256))%Z m mm
    /\ (exists (k0 k1 k2 : word) (pre : list byte), rw_cells asegs mm Fb [C8 k0; C8 k1; C8 k2; CB 8 pre])
    /\ (exists post : list byte, rw_cells asegs mm (Fb + 40) [CB 16 post; C8 (Z_to_bv 64 (fflagA L FF_READ_BLOCK Fb))])
    /\ rw_cells asegs mm (Z.shiftr Fb 3 + 2147450880) rb_shadow.

  (* [comment removed for export] *)
  Definition rb_handle (p p' : pcapT) (s : pcap_ng_sf) (P B' : Z) (mm : mem) : Prop :=
    blk_handle p' s P B' mm
    /\ (exists bs', rw_cells asegs mm B' [CB (Z.to_nat (pc_bufalloc p')) bs'] /\ firstn (length (pc_bufdata p')) bs' = map b8 (pc_bufdata p'))
    /\ (Z.of_nat (length (pc_bufdata p')) <= pc_bufalloc p')%Z
    /\ pc_priv p' = pc_priv p /\ pc_rfile p' = pc_rfile p /\ pc_self p' = pc_self p /\ pc_bufsize p' = pc_bufsize p /\ pc_swapped p' = pc_swapped p
    /\ same_meta p' p.

  (* [comment removed for export] *)
  Definition rb_result (r : block_result) (av : word) (p' : pcapT) (B' CUR EB : Z) (ej : list byte) (mm : mem) : Prop :=
    match r with
    | RB_Ok c p'' => p'' = p' /\ av = Z_to_bv 64 1 /\ rw_cells asegs mm EB [CB 256 ej]
        /\ (exists cpad, rw_cells asegs mm CUR [C8 (Z_to_bv 64 (B' + 8)); C8 (Z_to_bv 64 (cur_remaining c)); C4 (Z_to_bv 64 (cur_block_type c)); CB 4 cpad])
        /\ cur_off c = 8%Z /\ (0 <= cur_remaining c)%Z /\ (cur_remaining c + 12 <= pc_bufalloc p')%Z /\ (cur_remaining c + 12 <= 2^30)%Z /\ (0 <= cur_block_type c < 2^32)%Z
        /\ Z.of_nat (length (pc_bufdata p')) = (cur_remaining c + 12)%Z /\ Forall (fun z => 0 <= z < 256)%Z (pc_bufdata p')
    | RB_Eof p'' => p'' = p' /\ av = Z_to_bv 64 0 /\ rw_cells asegs mm EB [CB 256 ej]
        /\ (exists ccs', rw_cells asegs mm CUR ccs' /\ cells_size ccs' = 24%nat)
    | RB_Err msg p'' => p'' = p' /\ av = Z_to_bv 64 (-1)
        /\ (exists junk'', rw_cells asegs mm EB [CB (length msg + 1) (map b8 msg ++ [Z_to_bv 8 0]); CB (255 - length msg) junk''])
        /\ (Z.of_nat (length msg) < 256)%Z /\ Forall (fun z => 0 < z < 256)%Z msg
        /\ (exists ccs', rw_cells asegs mm CUR ccs' /\ cells_size ccs' = 24%nat)
    end.
End RbDefs.

Section RbKit.
  Context {H hptr : Type} (FO : @FrameOps H hptr).
  Variable GIOA : alayout -> footprint -> PState H hptr -> list (@cblock hptr) -> list (@cblock hptr) -> list fblock -> mem -> Prop.
  Variable fflagA : alayout -> fframe -> Z -> Z.
  Hypothesis GL : gia_laws FO GIOA fflagA.

  (* [comment removed for export] *)
  #[using="tlsI FO fflagA GL"] Lemma own_writes_s : forall L RNG s (CLc PB FB : list (@cblock hptr)) FLc FLo m m' W WX WS SP,
    Forall (own_ivA FLo PB SP) W -> Forall (cobj_iv FLc CLc) WX -> Forall (fun iv : Z * Z => SP <= fst iv)%Z WS ->
    GIOA L RNG s (CLc ++ PB) FB (FLo ++ FLc) m -> munch (W ++ WX ++ WS) m m' -> wmono asegs m m' -> (ATOP + 4096 <= SP)%Z ->
    GIOA L RNG s (CLc ++ PB) FB (FLo ++ FLc) m' /\ agrees_on (fun a => client_keeps FLc CLc SP a /\ outside (WX ++ WS) a) m m'.
  Proof.
    intros L RNG s CLc PB FB FLc FLo m m' W WX WS SP FW FX FS G MU WM HSP. split.
    - eapply (gl_client_frame _ _ _ GL); [exact G| exact MU| exact WM|]. apply Forall_app. split; [| apply Forall_app; split].
      + eapply Forall_impl; [|exact FW]. intros iv [Hs|[Hb|[Hf|Hf]]]; unfold client_ivA.
        * left. lia.
        * right; left. unfold iv_in_block in *. apply Exists_app. right. exact Hb.
        * right; right; left. unfold iv_in_frames in *. apply Exists_app. left. exact Hf.
        * right; right; right. unfold iv_in_frame_shadow in *. apply Exists_app. left. exact Hf.
      + eapply Forall_impl; [|exact FX]. intros [lo hi] [LOC LT]. cbn [fst snd] in *.
        replace hi with (lo + (hi - lo))%Z at 1 by lia. eapply clocA_iv. eapply clocA_incl; [exact LOC| apply incl_appl; apply incl_refl| apply incl_appr; apply incl_refl].
      + eapply Forall_impl; [|exact FS]. intros iv Hs. cbv beta in Hs. unfold client_ivA. left. lia.
    - eapply (gl_keepsx _ _ _ GL) with (W := W) (WX := (WX ++ WS)%list); [exact G| exact MU| exact WM| exact FW| exact HSP].
  Qed.
End RbKit.
End CANSEC1.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Strings.String.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Bytes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ZBridge OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Frame OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.StoreFast.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Fmt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Stdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPrelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapTypes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPure OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Pcap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prog.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ExecF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ITreeA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.Shadow OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.StepF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.SysStepF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AMalloc_iface.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.CkTac.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_iface_ngA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FrameKit__A3P.FrameKit.TwB. Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition rb_shadow : list cell :=
  [C1 (Z_to_bv 8 18446744073709551601); C1 (Z_to_bv 8 18446744073709551601); C1 (Z_to_bv 8 18446744073709551601); C1 (Z_to_bv 8 18446744073709551601);
   C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 18446744073709551603); C1 (Z_to_bv 8 18446744073709551603); C1 (Z_to_bv 8 18446744073709551603)].

Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
Section RbModel.
  Context {H hptr : Type} (HO : HeapOps H hptr) (FO : @FrameOps H hptr) (sites : stack_site -> Z).
  #[local] Abbreviation PS := (PState H hptr).
  #[local] Abbreviation pcapT := (PcapTypes.pcap hptr hptr).
  #[local] Abbreviation PR := (prims HO FO sites).

  (* [comment removed for export] *)
  Definition rb_bodyA (f : hptr) (bt tl : Z) (p0 : pcapT) : Monad.M PS block_result :=
    let p1 := set_bufdata (le_bytes 4 bt ++ le_bytes 4 tl) p0 in
    mo_bind MOps (read_bytes MOps PR f (DHeap (pc_buffer p1) 8) (tl - 8) true) (fun x => let '(st, data) := x in
    let p2 := set_bufdata (pc_bufdata p1 ++ data) p1 in
    match st with
    | RBS_Err m => e_fret PR FF_READ_BLOCK (RB_Err m p2)
    | RBS_Eof => e_fret PR FF_READ_BLOCK (RB_Err [] p2)
    | RBS_Ok =>
      let toff := tl - 4 in
      let p3 := if pc_swapped p2 then set_bufdata (swap_field 4 toff (pc_bufdata p2)) p2 else p2 in
      let trailer_length := get_le32 (pc_bufdata p3) toff in
      if negb (tl =? trailer_length)
      then e_fret PR FF_READ_BLOCK (RB_Err (Msg.header_trailer_mismatch tl trailer_length) p3)
      else e_fret PR FF_READ_BLOCK (RB_Ok (mkCursor 8 (tl - 12) bt) p3)
    end).

  Definition rb_tailA (f : hptr) (bt tl : Z) (p : pcapT) : Monad.M PS block_result :=
    if tl <? 12 then e_fret PR FF_READ_BLOCK (RB_Err (Msg.block_length_lt tl) p)
    else if negb (tl mod 4 =? 0) then e_fret PR FF_READ_BLOCK (RB_Err (Msg.block_length_not_mult4 tl) p)
    else
    mo_bind MOps
      (if pc_bufsize p <? tl then
         if ng_max_blocksize (ng_of p) <? tl
         then mo_ret MOps (Some (Msg.block_size_gt_max tl (ng_max_blocksize (ng_of p))), p)
         else
           mo_bind MOps (e_realloc PR (pc_buffer p) tl) (fun r =>
           match r with
           | None => mo_ret MOps (Some Msg.out_of_memory, p)
           | Some b => mo_ret MOps (@None (list Z), set_buffer b (pc_bufsize p) tl (zfirstn tl (pc_bufdata p)) p)
           end)
       else mo_ret MOps (@None (list Z), p))
      (fun x => let '(gerr, p0) := x in
       match gerr with
       | Some m => e_fret PR FF_READ_BLOCK (RB_Err m p0)
       | None => rb_bodyA f bt tl p0
       end).

  #[using="Type"] Lemma read_block_eqA : forall a_bhdr (p : pcapT),
    read_block MOps PR a_bhdr p =
    e_fenter PR FF_READ_BLOCK
      (mo_bind MOps (read_bytes MOps PR (pc_rfile p) a_bhdr 8 false) (fun x => let '(st, bh) := x in
        match st with
        | RBS_Eof => e_fret PR FF_READ_BLOCK (RB_Eof p)
        | RBS_Err m => e_fret PR FF_READ_BLOCK (RB_Err m p)
        | RBS_Ok => rb_tailA (pc_rfile p)
                      (if pc_swapped p then bswap32 (get_le32 bh 0) else get_le32 bh 0)
                      (if pc_swapped p then bswap32 (get_le32 bh 4) else get_le32 bh 4) p
        end)).
  Proof. intros. reflexivity. Qed.
End RbModel.
Section RbDefs.
  Context {H hptr : Type} (HO : HeapOps H hptr) (FO : @FrameOps H hptr) (sites : stack_site -> Z).
  Variable GIOA : alayout -> footprint -> PState H hptr -> list (@cblock hptr) -> list (@cblock hptr) -> list fblock -> mem -> Prop.
  Variable TP : tparams.
  Variable fflagA : alayout -> fframe -> Z -> Z.
  #[local] Abbreviation pcapT := (PcapTypes.pcap hptr hptr).

  (* [comment removed for export] *)
  Definition rb_ctx (ra sp tp s0 : word) (L : alayout) (RNG : footprint) (C1 C2 FB : list (@cblock hptr)) (FL : list fblock) (trC : list Z)
      (lo P CUR EB Af SPA : Z) (self f : hptr) (m : mem) : Prop :=
    (ATOP + 4096 <= lo)%Z /\ (lo + READ_BLOCK_STACK <= bv_unsigned sp)%Z /\ (bv_unsigned sp + 16 < al_top L /\ al_top L <= 2^47)%Z
    /\ tp = Z_to_bv 64 ATP /\ (bv_unsigned sp mod 16 = 0)%Z
    /\ (rng RNG lo (al_top L - lo) /\ rng_aimg RNG /\ rng_aimg_sh RNG /\ rng_atls RNG)
    /\ ucallerA depth_read_block L m sp s0 ra trC /\ traces_read_block TP L (bv_unsigned ra) trC
    /\ nofr frames_read_block FL /\ In (f, Af, FILE_BLOCK) FB
    /\ In (self, P, PCAP_NG_SF_TOTAL) (C1 ++ C2)
    /\ (bv_unsigned sp <= CUR /\ CUR + 24 <= al_top L)%Z /\ (CUR mod 8 = 0)%Z
    /\ ((cobjA RNG m FL (C1 ++ C2) EB 256 /\ (EB + 256 <= CUR \/ CUR + 24 <= EB)%Z /\ (EB + 256 <= P \/ P + PCAP_NG_SF_TOTAL <= EB)%Z) \/ (P + 216 = EB)%Z)
    /\ (EB mod 8 = 0)%Z
    /\ (bv_unsigned sp - 208 <= SPA <= bv_unsigned sp - 192)%Z /\ (SPA mod 32 = 0)%Z.

  (* [comment removed for export] *)
  Definition rb_inv (ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (L : alayout) (RNG : footprint) (C1 C2 FB : list (@cblock hptr)) (FL : list fblock)
      (lo P CUR EB SPA Fb : Z) (o : option hptr) (m : mem)
      (RNGx : footprint) (sx : PState H hptr) (bq : hptr) (B alloc : Z) (mm : mem) : Prop :=
    fp_le RNG RNGx /\ GIOA L RNGx sx ((C1 ++ C2) ++ [(bq, B, alloc)]) FB ((FF_READ_BLOCK, Fb, 64%Z) :: FL) mm /\ ps_outfile sx = o /\ mem_inv asegs mm
    /\ stk asegs mm lo SPA /\ stk asegs mm (SPA + 88) (bv_unsigned sp + -104)
    /\ rw_cells asegs mm (bv_unsigned sp + -104) [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
    /\ agrees_on (fun a => client_keeps FL (C1 ++ C2) (bv_unsigned sp) a /\ ~ (P + 24 <= a < P + 32) /\ ~ (CUR <= a < CUR + 24) /\ ~ (EB <= a < EB + 256))%Z m mm
    /\ (exists (k0 k1 k2 : word) (pre : list byte), rw_cells asegs mm Fb [C8 k0; C8 k1; C8 k2; CB 8 pre])
    /\ (exists post : list byte, rw_cells asegs mm (Fb + 40) [CB 16 post; C8 (Z_to_bv 64 (fflagA L FF_READ_BLOCK Fb))])
    /\ rw_cells asegs mm (Z.shiftr Fb 3 + 2147450880) rb_shadow.

  (* [comment removed for export] *)
  Definition rb_handle (p p' : pcapT) (s : pcap_ng_sf) (P B' : Z) (mm : mem) : Prop :=
    blk_handle p' s P B' mm
    /\ (exists bs', rw_cells asegs mm B' [CB (Z.to_nat (pc_bufalloc p')) bs'] /\ firstn (length (pc_bufdata p')) bs' = map b8 (pc_bufdata p'))
    /\ (Z.of_nat (length (pc_bufdata p')) <= pc_bufalloc p')%Z
    /\ pc_priv p' = pc_priv p /\ pc_rfile p' = pc_rfile p /\ pc_self p' = pc_self p /\ pc_bufsize p' = pc_bufsize p /\ pc_swapped p' = pc_swapped p
    /\ same_meta p' p.

  (* [comment removed for export] *)
  Definition rb_result (r : block_result) (av : word) (p' : pcapT) (B' CUR EB : Z) (ej : list byte) (mm : mem) : Prop :=
    match r with
    | RB_Ok c p'' => p'' = p' /\ av = Z_to_bv 64 1 /\ rw_cells asegs mm EB [CB 256 ej]
        /\ (exists cpad, rw_cells asegs mm CUR [C8 (Z_to_bv 64 (B' + 8)); C8 (Z_to_bv 64 (cur_remaining c)); C4 (Z_to_bv 64 (cur_block_type c)); CB 4 cpad])
        /\ cur_off c = 8%Z /\ (0 <= cur_remaining c)%Z /\ (cur_remaining c + 12 <= pc_bufalloc p')%Z /\ (cur_remaining c + 12 <= 2^30)%Z /\ (0 <= cur_block_type c < 2^32)%Z
        /\ Z.of_nat (length (pc_bufdata p')) = (cur_remaining c + 12)%Z /\ Forall (fun z => 0 <= z < 256)%Z (pc_bufdata p')
    | RB_Eof p'' => p'' = p' /\ av = Z_to_bv 64 0 /\ rw_cells asegs mm EB [CB 256 ej]
        /\ (exists ccs', rw_cells asegs mm CUR ccs' /\ cells_size ccs' = 24%nat)
    | RB_Err msg p'' => p'' = p' /\ av = Z_to_bv 64 (-1)
        /\ (exists junk'', rw_cells asegs mm EB [CB (length msg + 1) (map b8 msg ++ [Z_to_bv 8 0]); CB (255 - length msg) junk''])
        /\ (Z.of_nat (length msg) < 256)%Z /\ Forall (fun z => 0 < z < 256)%Z msg
        /\ (exists ccs', rw_cells asegs mm CUR ccs' /\ cells_size ccs' = 24%nat)
    end.
End RbDefs.

Section RbKit.
  Context {H hptr : Type} (FO : @FrameOps H hptr).
  Variable GIOA : alayout -> footprint -> PState H hptr -> list (@cblock hptr) -> list (@cblock hptr) -> list fblock -> mem -> Prop.
  Variable fflagA : alayout -> fframe -> Z -> Z.
  Hypothesis GL : gia_laws FO GIOA fflagA.

  (* [comment removed for export] *)
  #[using="tlsI FO fflagA GL"] Lemma own_writes_s : forall L RNG s (CLc PB FB : list (@cblock hptr)) FLc FLo m m' W WX WS SP,
    Forall (own_ivA FLo PB SP) W -> Forall (cobj_iv FLc CLc) WX -> Forall (fun iv : Z * Z => SP <= fst iv)%Z WS ->
    GIOA L RNG s (CLc ++ PB) FB (FLo ++ FLc) m -> munch (W ++ WX ++ WS) m m' -> wmono asegs m m' -> (ATOP + 4096 <= SP)%Z ->
    GIOA L RNG s (CLc ++ PB) FB (FLo ++ FLc) m' /\ agrees_on (fun a => client_keeps FLc CLc SP a /\ outside (WX ++ WS) a) m m'.
  Proof.
    intros L RNG s CLc PB FB FLc FLo m m' W WX WS SP FW FX FS G MU WM HSP. split.
    - eapply (gl_client_frame _ _ _ GL); [exact G| exact MU| exact WM|]. apply Forall_app. split; [| apply Forall_app; split].
      + eapply Forall_impl; [|exact FW]. intros iv [Hs|[Hb|[Hf|Hf]]]; unfold client_ivA.
        * left. lia.
        * right; left. unfold iv_in_block in *. apply Exists_app. right. exact Hb.
        * right; right; left. unfold iv_in_frames in *. apply Exists_app. left. exact Hf.
        * right; right; right. unfold iv_in_frame_shadow in *. apply Exists_app. left. exact Hf.
      + eapply Forall_impl; [|exact FX]. intros [lo hi] [LOC LT]. cbn [fst snd] in *.
        replace hi with (lo + (hi - lo))%Z at 1 by lia. eapply clocA_iv. eapply clocA_incl; [exact LOC| apply incl_appl; apply incl_refl| apply incl_appr; apply incl_refl].
      + eapply Forall_impl; [|exact FS]. intros iv Hs. cbv beta in Hs. unfold client_ivA. left. lia.
    - eapply (gl_keepsx _ _ _ GL) with (W := W) (WX := (WX ++ WS)%list); [exact G| exact MU| exact WM| exact FW| exact HSP].
  Qed.
End RbKit.
End CANSEC1.
End TwB.
End F_ngblk_defsA.

(* [comment removed for export] *)
Module F_ngblk_exitA.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr Bytes ZBridge ITree Nodes Decode SysStep Frame StoreFast.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import Prelim Monad Fmt StdioCore Stdio PcapPrelim PcapTypes PcapPure Pcap Prog.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_kit__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import ExecF ITreeA Shadow StepF SysStepF RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import AImg ABase AMalloc_iface.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require CkTac__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadG GIA PcapRepA UnwKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadGX__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require Pcap_ifaceA Pcap_iface_ngA. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.CkTac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_iface_ngA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FrameKit__A3P.FrameKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FrameKit__A3P.F_ngblk_defsA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FrameKit__A3P.F_ngblk_epiA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_chunks_extra m a bs n Hn Ha Hl ::= unp_store m a bs n Hn Ha Hl.
Local Ltac transport_call_extra segs W m m' MU WM ::= unp_call W m m' MU.

Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
Section RbExit.
  Context {H hptr : Type} (HO : HeapOps H hptr) (FO : @FrameOps H hptr) (sites : stack_site -> Z).
  Variable GIOA : alayout -> footprint -> PState H hptr -> list (@cblock hptr) -> list (@cblock hptr) -> list fblock -> mem -> Prop.
  Variable TP : tparams.
  Variable fflagA : alayout -> fframe -> Z -> Z.
  Hypothesis GL : gia_laws FO GIOA fflagA.
  Hypothesis GPL : gia_perm_law GIOA.
  Hypothesis FRET : fret_inline_law FO GIOA fflagA.

  Definition rb_exit__stmt : Prop := forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (L : alayout) (RNG : footprint) (C1 C2 FB : list (@cblock hptr)) (FL : list fblock) (trC : list Z)
      (lo P CUR EB Af SPA Fb : Z) (self f : hptr) (m : mem) (o : option hptr)
      (RNGx : footprint) (sx : PState H hptr) (mm : mem)
      (ra0 sp0 t0 t1 t2 r9 av a1 a2 a3 a4 a5 a6 a7 r19 r21 r22 r23 r24 r25 r26 t3 t4 t5 t6 : word)
      (scs : list cell) (p p' : PcapTypes.pcap hptr hptr) (s : pcap_ng_sf) (B' : Z) (ej : list byte) (r : block_result),
    rb_ctx TP ra sp tp s0 L RNG C1 C2 FB FL trC lo P CUR EB Af SPA self f m ->
    rb_inv GIOA fflagA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG C1 C2 FB FL lo P CUR EB SPA Fb o m RNGx sx (pc_buffer p') B' (pc_bufalloc p') mm ->
    rw_cells asegs mm SPA scs -> cells_size scs = 88%nat ->
    rb_handle p p' s P B' mm -> rb_result r av p' B' CUR EB ej mm ->
    implMG RNGx (fo_ret FO _ FF_READ_BLOCK r) sx
      (read_block_post GIOA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG FL C1 C2 FB lo P CUR EB p s ej m o)
      (MS (mkR ra0 sp0 gp tp t0 t1 t2 sp r9 av a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 Fb) r19 (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450880)) r21 r22 r23 r24 r25 r26 (Z_to_bv 64 Fb) t3 t4 t5 t6)
          F (Z_to_bv 64 0x8bdb0) fc None mm (seg_rom asegs)).
  Section Sz1.
  Variables ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG C1 C2 FB FL trC lo P CUR EB Af SPA Fb self f m o RNGx sx mm ra0 sp0 t0 t1 t2 r9 av a1 a2 a3 a4 a5 a6 a7 r19 r21 r22 r23 r24 r25 r26 t3 t4 t5 t6 scs p p' s B' ej r : ltac2:(SecDiet.SzSec.tyM 'rb_exit__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma rb_exit__body : ltac2:(SecDiet.SzSec.bodyP 'rb_exit__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using GL GPL FRET.
 intros CTX INV FRA Hscs HDL RES.
    destruct CTX as (LO & BU & (SPT & TOP47) & TPE & ALN & (RSTK & RIMG & RISH & RTLS) & UC & TR & NF & HinF & HinP & CURS & CUR8 & EBM & EB8 & SPAB & SPA32).
    destruct INV as (FP & G & OF & MI & ST & STG & FR & AG & (k0 & k1 & k2 & pre & FRC1) & (post & FRC3) & SHC).
    unfold READ_BLOCK_STACK, PCAP_L1_STACK in BU.
    destruct (rw_cells_forget _ _ _ _ FRA) as [jS FRA']. rewrite Hscs in FRA'. clear FRA.
    unfold rb_shadow in SHC.
    apply (rng_fp_le _ _ _ _ FP) in RSTK.
    eapply implMG_mono.
    { eapply (rb_epi FO GIOA fflagA GL FRET ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNGx sx (C1 ++ C2) [(pc_buffer p', B', pc_bufalloc p')] FB FL lo SPA Fb mm);
        [exact SPAB| exact SPA32| exact LO| lia| exact SPT| exact TOP47| exact G| exact MI| exact ST| exact STG| exact FRA'| exact FR| exact FRC1| exact FRC3| exact SHC| exact RSTK]. }
    intros r' s3' RNG3 ms3 (-> & -> & PO). destruct_exs PO. destruct PO as (-> & MI7 & ST7 & AG7 & AGP7 & G7 & OF7).
    (* [comment removed for export] *)
    assert (INP : forall a, (P <= a < P + 680)%Z -> in_block ((C1 ++ C2) ++ [(pc_buffer p', B', pc_bufalloc p')]) a).
    { intros a Ha. apply in_block_app. left. apply in_block_In. exists (self, P, PCAP_NG_SF_TOTAL). split; [exact HinP|].
      cbn [cb_addr cb_size fst snd]. unfold PCAP_NG_SF_TOTAL. lia. }
    assert (INB : forall a, (B' <= a < B' + pc_bufalloc p')%Z -> in_block ((C1 ++ C2) ++ [(pc_buffer p', B', pc_bufalloc p')]) a).
    { intros a Ha. apply in_block_app. right. unfold in_block. apply Exists_cons_hd. cbn [cb_addr cb_size fst snd]. lia. }
    lazymatch goal with |- context [MS _ _ _ _ _ ?m7 _] => set (m7' := m7) in * end.
    assert (KP : forall A cs, rw_cells asegs mm A cs -> (P <= A)%Z -> (A + Z.of_nat (cells_size cs) <= P + 680)%Z -> rw_cells asegs m7' A cs).
    { intros A cs HC H1 H2. eapply agrees_rw_cells; [exact AGP7| exact HC|]. intros a Ha. apply INP. lia. }
    assert (KCUR : forall cs, rw_cells asegs mm CUR cs -> rw_cells asegs m7' CUR cs).
    { intros cs HC. eapply agrees_rw_cells; [exact AG7| exact HC|]. intros a Ha. left. lia. }
    assert (KEB : forall cs, rw_cells asegs mm EB cs -> cells_size cs = 256%nat -> rw_cells asegs m7' EB cs).
    { intros cs HC HS. destruct EBM as [(OEB & _)|EBP].
      - eapply agrees_rw_cells; [exact AG7| exact HC|]. intros a Ha. eapply clocA_keeps; [exact (proj1 OEB)| rewrite HS in Ha; lia].
      - apply KP; [exact HC| lia| rewrite HS; lia]. }
    destruct HDL as ((HBS & HPV & HMB & WBS & WMB & WBA & BSA) & (bs' & HBUF & PFX) & LENB & E1 & E2 & E3 & E4 & E5 & E6).
    unfold read_block_post. split; [exact FP|].
    exists av, m7', p', B', bs'.
    split. { unfold hpost_regs. repeat (lazymatch goal with |- ex _ => eexists end). reflexivity. }
    split; [congruence|]. split; [exact MI7|]. split; [exact ST7|].
    split. { eapply agrees_on_trans; [exact AG|]. eapply agrees_on_weaken; [exact AG7|]. intros a (K & _); exact K. }
    split. { eapply GPL; [exact G7|]. apply Permutation.Permutation_sym. apply Permutation.Permutation_cons_append. }
    split. { unfold blk_handle. split; [apply KP; [exact HBS| lia| cbn [cells_size csize Nat.add]; lia]|].
             split; [apply KP; [exact HPV| lia| cbn [cells_size csize Nat.add]; lia]|].
             split; [apply KP; [exact HMB| lia| cbn [cells_size csize Nat.add]; lia]|]. repeat (split; [assumption|]). assumption. }
    split. { eapply agrees_rw_cells; [exact AGP7| exact HBUF|]. intros a Ha. cbn [cells_size csize Nat.add] in Ha. apply INB. lia. }
    split; [exact PFX|]. split; [exact LENB|]. split; [exact E1|]. split; [exact E2|]. split; [exact E3|]. split; [exact E4|]. split; [exact E5|]. split; [exact E6|].
    destruct r as [p''|msg p''|c p'']; cbn [rb_result] in RES.
    - destruct RES as (X1 & X2 & X3 & (ccs' & X4 & X5)). split; [exact X1|]. split; [exact X2|]. split; [apply KEB; [exact X3| reflexivity]|].
      exists ccs'. split; [apply KCUR; exact X4| exact X5].
    - destruct RES as (X1 & X2 & (junk'' & X3) & X4 & X4b & (ccs' & X5 & X6)). split; [exact X1|]. split; [exact X2|].
      split; [exists junk''; apply KEB; [exact X3| cbn [cells_size csize Nat.add]; lia]|]. split; [exact X4|]. split; [exact X4b|].
      exists ccs'. split; [apply KCUR; exact X5| exact X6].
    - destruct RES as (X1 & X2 & X3 & (cpad & X4) & X5 & X6 & X7 & X7b & X8 & X9 & X10). split; [exact X1|]. split; [exact X2|].
      split; [apply KEB; [exact X3| reflexivity]|]. split; [exists cpad; apply KCUR; exact X4|].
      split; [exact X5|]. split; [exact X6|]. split; [exact X7|]. split; [exact X7b|]. split; [exact X8|]. split; [exact X9| exact X10].
  Qed.
  End Sz1.
  Lemma rb_exit : ltac:(let t := eval cbv delta [rb_exit__stmt] in rb_exit__stmt in exact t).
  Proof using GL GPL FRET. intros ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG C1 C2 FB FL trC lo P CUR EB Af SPA Fb self f m o RNGx sx mm ra0 sp0 t0 t1 t2 r9 av a1 a2 a3 a4 a5 a6 a7 r19 r21 r22 r23 r24 r25 r26 t3 t4 t5 t6 scs p p' s B' ej r. ltac2:(SecDiet.SzSec.closeP 'rb_exit__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End RbExit.
End CANSEC1.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Bytes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ZBridge OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Frame OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.StoreFast.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Fmt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Stdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPrelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapTypes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPure OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Pcap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prog.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ExecF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ITreeA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.Shadow OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.StepF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.SysStepF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AMalloc_iface.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.CkTac.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_iface_ngA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FrameKit__A3P.FrameKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FrameKit__A3P.F_ngblk_defsA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FrameKit__A3P.F_ngblk_epiA.TwB.
(* [comment removed for export] *) Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_chunks_extra m a bs n Hn Ha Hl ::= unp_store m a bs n Hn Ha Hl.
Local Ltac transport_call_extra segs W m m' MU WM ::= unp_call W m m' MU.

Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
Section RbExit.
  Context {H hptr : Type} (HO : HeapOps H hptr) (FO : @FrameOps H hptr) (sites : stack_site -> Z).
  Variable GIOA : alayout -> footprint -> PState H hptr -> list (@cblock hptr) -> list (@cblock hptr) -> list fblock -> mem -> Prop.
  Variable TP : tparams.
  Variable fflagA : alayout -> fframe -> Z -> Z.
  Hypothesis GL : gia_laws FO GIOA fflagA.
  Hypothesis GPL : gia_perm_law GIOA.
  Hypothesis FRET : fret_inline_law FO GIOA fflagA.

  Definition rb_exit__stmt : Prop := forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (L : alayout) (RNG : footprint) (C1 C2 FB : list (@cblock hptr)) (FL : list fblock) (trC : list Z)
      (lo P CUR EB Af SPA Fb : Z) (self f : hptr) (m : mem) (o : option hptr)
      (RNGx : footprint) (sx : PState H hptr) (mm : mem)
      (ra0 sp0 t0 t1 t2 r9 av a1 a2 a3 a4 a5 a6 a7 r19 r21 r22 r23 r24 r25 r26 t3 t4 t5 t6 : word)
      (scs : list cell) (p p' : PcapTypes.pcap hptr hptr) (s : pcap_ng_sf) (B' : Z) (ej : list byte) (r : block_result),
    rb_ctx TP ra sp tp s0 L RNG C1 C2 FB FL trC lo P CUR EB Af SPA self f m ->
    rb_inv GIOA fflagA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG C1 C2 FB FL lo P CUR EB SPA Fb o m RNGx sx (pc_buffer p') B' (pc_bufalloc p') mm ->
    rw_cells asegs mm SPA scs -> cells_size scs = 88%nat ->
    rb_handle p p' s P B' mm -> rb_result r av p' B' CUR EB ej mm ->
    implMG RNGx (fo_ret FO _ FF_READ_BLOCK r) sx
      (read_block_post GIOA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG FL C1 C2 FB lo P CUR EB p s ej m o)
      (MS (mkR ra0 sp0 gp tp t0 t1 t2 sp r9 av a1 a2 a3 a4 a5 a7 a6
               (Z_to_bv 64 Fb) r26 (Z_to_bv 64 Fb) r21 r22 r24 r23 r25 r19 (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450880)) t3 t4 t5 t6)
          F (Z_to_bv 64 0x8bd70) fc None mm (seg_rom asegs)).
  Section Sz1.
  Variables ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG C1 C2 FB FL trC lo P CUR EB Af SPA Fb self f m o RNGx sx mm ra0 sp0 t0 t1 t2 r9 av a1 a2 a3 a4 a5 a6 a7 r19 r21 r22 r23 r24 r25 r26 t3 t4 t5 t6 scs p p' s B' ej r : ltac2:(SecDiet.SzSec.tyM 'rb_exit__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma rb_exit__body : ltac2:(SecDiet.SzSec.bodyP 'rb_exit__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using GL GPL FRET.
 intros CTX INV FRA Hscs HDL RES.
    destruct CTX as (LO & BU & (SPT & TOP47) & TPE & ALN & (RSTK & RIMG & RISH & RTLS) & UC & TR & NF & HinF & HinP & CURS & CUR8 & EBM & EB8 & SPAB & SPA32).
    destruct INV as (FP & G & OF & MI & ST & STG & FR & AG & (k0 & k1 & k2 & pre & FRC1) & (post & FRC3) & SHC).
    unfold READ_BLOCK_STACK, PCAP_L1_STACK in BU.
    destruct (rw_cells_forget _ _ _ _ FRA) as [jS FRA']. rewrite Hscs in FRA'. clear FRA.
    unfold rb_shadow in SHC.
    apply (rng_fp_le _ _ _ _ FP) in RSTK.
    eapply implMG_mono.
    { eapply (rb_epi FO GIOA fflagA GL FRET ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNGx sx (C1 ++ C2) [(pc_buffer p', B', pc_bufalloc p')] FB FL lo SPA Fb mm);
        [exact SPAB| exact SPA32| exact LO| lia| exact SPT| exact TOP47| exact G| exact MI| exact ST| exact STG| exact FRA'| exact FR| exact FRC1| exact FRC3| exact SHC| exact RSTK]. }
    intros r' s3' RNG3 ms3 (-> & -> & PO). destruct_exs PO. destruct PO as (-> & MI7 & ST7 & AG7 & AGP7 & G7 & OF7).
    (* [comment removed for export] *)
    assert (INP : forall a, (P <= a < P + 680)%Z -> in_block ((C1 ++ C2) ++ [(pc_buffer p', B', pc_bufalloc p')]) a).
    { intros a Ha. apply in_block_app. left. apply in_block_In. exists (self, P, PCAP_NG_SF_TOTAL). split; [exact HinP|].
      cbn [cb_addr cb_size fst snd]. unfold PCAP_NG_SF_TOTAL. lia. }
    assert (INB : forall a, (B' <= a < B' + pc_bufalloc p')%Z -> in_block ((C1 ++ C2) ++ [(pc_buffer p', B', pc_bufalloc p')]) a).
    { intros a Ha. apply in_block_app. right. unfold in_block. apply Exists_cons_hd. cbn [cb_addr cb_size fst snd]. lia. }
    lazymatch goal with |- context [MS _ _ _ _ _ ?m7 _] => set (m7' := m7) in * end.
    assert (KP : forall A cs, rw_cells asegs mm A cs -> (P <= A)%Z -> (A + Z.of_nat (cells_size cs) <= P + 680)%Z -> rw_cells asegs m7' A cs).
    { intros A cs HC H1 H2. eapply agrees_rw_cells; [exact AGP7| exact HC|]. intros a Ha. apply INP. lia. }
    assert (KCUR : forall cs, rw_cells asegs mm CUR cs -> rw_cells asegs m7' CUR cs).
    { intros cs HC. eapply agrees_rw_cells; [exact AG7| exact HC|]. intros a Ha. left. lia. }
    assert (KEB : forall cs, rw_cells asegs mm EB cs -> cells_size cs = 256%nat -> rw_cells asegs m7' EB cs).
    { intros cs HC HS. destruct EBM as [(OEB & _)|EBP].
      - eapply agrees_rw_cells; [exact AG7| exact HC|]. intros a Ha. eapply clocA_keeps; [exact (proj1 OEB)| rewrite HS in Ha; lia].
      - apply KP; [exact HC| lia| rewrite HS; lia]. }
    destruct HDL as ((HBS & HPV & HMB & WBS & WMB & WBA & BSA) & (bs' & HBUF & PFX) & LENB & E1 & E2 & E3 & E4 & E5 & E6).
    unfold read_block_post. split; [exact FP|].
    exists av, m7', p', B', bs'.
    split. { unfold hpost_regs. repeat (lazymatch goal with |- ex _ => eexists end). reflexivity. }
    split; [congruence|]. split; [exact MI7|]. split; [exact ST7|].
    split. { eapply agrees_on_trans; [exact AG|]. eapply agrees_on_weaken; [exact AG7|]. intros a (K & _); exact K. }
    split. { eapply GPL; [exact G7|]. apply Permutation.Permutation_sym. apply Permutation.Permutation_cons_append. }
    split. { unfold blk_handle. split; [apply KP; [exact HBS| lia| cbn [cells_size csize Nat.add]; lia]|].
             split; [apply KP; [exact HPV| lia| cbn [cells_size csize Nat.add]; lia]|].
             split; [apply KP; [exact HMB| lia| cbn [cells_size csize Nat.add]; lia]|]. repeat (split; [assumption|]). assumption. }
    split. { eapply agrees_rw_cells; [exact AGP7| exact HBUF|]. intros a Ha. cbn [cells_size csize Nat.add] in Ha. apply INB. lia. }
    split; [exact PFX|]. split; [exact LENB|]. split; [exact E1|]. split; [exact E2|]. split; [exact E3|]. split; [exact E4|]. split; [exact E5|]. split; [exact E6|].
    destruct r as [p''|msg p''|c p'']; cbn [rb_result] in RES.
    - destruct RES as (X1 & X2 & X3 & (ccs' & X4 & X5)). split; [exact X1|]. split; [exact X2|]. split; [apply KEB; [exact X3| reflexivity]|].
      exists ccs'. split; [apply KCUR; exact X4| exact X5].
    - destruct RES as (X1 & X2 & (junk'' & X3) & X4 & X4b & (ccs' & X5 & X6)). split; [exact X1|]. split; [exact X2|].
      split; [exists junk''; apply KEB; [exact X3| cbn [cells_size csize Nat.add]; lia]|]. split; [exact X4|]. split; [exact X4b|].
      exists ccs'. split; [apply KCUR; exact X5| exact X6].
    - destruct RES as (X1 & X2 & X3 & (cpad & X4) & X5 & X6 & X7 & X7b & X8 & X9 & X10). split; [exact X1|]. split; [exact X2|].
      split; [apply KEB; [exact X3| reflexivity]|]. split; [exists cpad; apply KCUR; exact X4|].
      split; [exact X5|]. split; [exact X6|]. split; [exact X7|]. split; [exact X7b|]. split; [exact X8|]. split; [exact X9| exact X10].
  Qed.
  End Sz1.
  Lemma rb_exit : ltac:(let t := eval cbv delta [rb_exit__stmt] in rb_exit__stmt in exact t).
  Proof using GL GPL FRET. intros ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG C1 C2 FB FL trC lo P CUR EB Af SPA Fb self f m o RNGx sx mm ra0 sp0 t0 t1 t2 r9 av a1 a2 a3 a4 a5 a6 a7 r19 r21 r22 r23 r24 r25 r26 t3 t4 t5 t6 scs p p' s B' ej r. ltac2:(SecDiet.SzSec.closeP 'rb_exit__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End RbExit.
End CANSEC1.
End TwB.
End F_ngblk_exitA.

(* [comment removed for export] *)
Module F_ngblk_psegA.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr Bytes ZBridge ITree Nodes Decode SysStep Frame StoreFast.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_kit__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import ExecF ITreeA Shadow StepF SysStepF RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import AImg ABase.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require CkTac__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require GIA PcapRepA. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.CkTac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FrameKit__A3P.FrameKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FrameKit__A3P.F_ngblk_defsA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac qfold := try (lazymatch goal with |- evtF ?s ?r ?Q ?st => let QQ := fresh "QQ" in pose (QQ := Q); change Q with QQ end).
Import ListNotations.
Open Scope Z_scope.
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_chunks_extra m a bs n Hn Ha Hl ::= unp_store m a bs n Hn Ha Hl.

(* [comment removed for export] *)
Lemma le8_of_bytesB : forall l : list byte, length l = 8%nat -> le8 (le_bytes_to_word l) = l.
Proof.
  intros l Hl. unfold le8, word_to_le_bytes, le_bytes_to_word. rewrite Z_to_bv_unsigned.
  change (bv_wrap 64 ?z) with (z mod 2^64)%Z. rewrite (Z_to_le_bytes_mod 8 _ 64) by (cbn; lia).
  rewrite <- Hl. apply Z_to_le_bytes_to_Z.
Qed.

Section CANSEC0. Context {rc : runConstT}.
(* [comment removed for export] *)
Definition spill_words11__stmt : Prop := forall m A l, rw_cells asegs m A [CB 88 l] ->
  exists w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 : word,
    rw_cells asegs m A [C8 w0; C8 w1; C8 w2; C8 w3; C8 w4; C8 w5; C8 w6; C8 w7; C8 w8; C8 w9; C8 w10].
Section Sz2.
Variables m A l : ltac2:(SecDiet.SzSec.tyM 'spill_words11__stmt "vvv" @m).
#[using="Type"] Lemma spill_words11__body : ltac2:(SecDiet.SzSec.bodyP 'spill_words11__stmt "vvv").
Proof.
  intros HC.
  qfold.
  apply (rw_cells_split_CB asegs _ _ [] 88 _ [] [8;8;8;8;8;8;8;8;8;8;8]%nat) in HC; [|reflexivity].
  cbn [mk_CB_cells app] in HC.
  repeat match type of HC with context [CB 8 ?t] => lazymatch t with firstn _ _ => idtac end; let j := fresh "jk" in set (j := t) in HC; clearbody j end.
  pose proof HC as [[WF _] _]. cbn [cells_wf cell_wf] in WF.
  destruct WF as (L0 & L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8 & L9 & L10 & _).
  exists (le_bytes_to_word jk), (le_bytes_to_word jk0), (le_bytes_to_word jk1), (le_bytes_to_word jk2), (le_bytes_to_word jk3),
         (le_bytes_to_word jk4), (le_bytes_to_word jk5), (le_bytes_to_word jk6), (le_bytes_to_word jk7), (le_bytes_to_word jk8),
         (le_bytes_to_word jk9).
  eapply rw_cells_recell; [exact HC| cbn; repeat split|].
  cbn [cells_bytes cbytes]. rewrite !le8_of_bytesB by assumption. reflexivity.
Qed.
End Sz2.
#[using="Type"] Lemma spill_words11 : ltac:(let t := eval cbv delta [spill_words11__stmt] in spill_words11__stmt in exact t).
Proof. intros m A l. ltac2:(SecDiet.SzSec.closeP 'spill_words11__body "vvv"). Qed.
End CANSEC0.

Section CANSEC1. Context {rc : runConstT}.
Section RbSeg.
  Variables (gp tp s0 : word) (F : bvmap 5 word) (fc : bv 32) (RNG : footprint).

  Definition rb_poison_seq__stmt : Prop := forall (m : mem) (ra sp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s1 s2 s3 s4 s5 s6 s8 s9 s11 t3 t4 t5 t6 : word) (Fb bF P : Z)
      (j0 j1 j2 flagw : word) (fj : list byte),
    mem_inv asegs m ->
    rw_cells asegs m Fb [C8 j0; C8 j1; C8 j2; CB 32 fj; C8 flagw] ->
    rw_cells asegs m (Z.shiftr Fb 3 + 2147450880) (repeat (C1 (Z_to_bv 8 0)) 8) ->
    rng RNG Fb 64 -> rng RNG (Z.shiftr Fb 3 + 2147450880) 8 ->
    (0 < Fb)%Z -> (Fb + 64 <= 2147446784 + bF * 140737479966720)%Z -> (17594333495296 * bF <= Fb)%Z -> (0 <= bF <= 1)%Z ->
    (2147450880 <= Z.shiftr Fb 3 + 2147450880)%Z -> (Z.shiftr Fb 3 + 2147450880 + 8 <= 17594333495296)%Z ->
    (0 < P)%Z -> (P + 680 <= 2^47)%Z ->
    evtF asegs RNG (fun ms' => exists m',
        ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (P + 48)) (Z_to_bv 64 18446744073709551601)
                      (Z_to_bv 64 572228) (Z_to_bv 64 18446744073709551603) a4 a5 a6 a7
                      (Z_to_bv 64 Fb) s3 (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450880)) s5 s6 (Z_to_bv 64 P) s8 s9 (Z_to_bv 64 2147450880) (Z_to_bv 64 Fb) t3 t4 t5 t6)
                 F (Z_to_bv 64 0x8bc50) fc None m' (seg_rom asegs)
        /\ munch [(Fb, Fb + 24); (Z.shiftr Fb 3 + 2147450880, Z.shiftr Fb 3 + 2147450888)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
        /\ rw_cells asegs m' Fb [C8 (Z_to_bv 64 1102416563); C8 (Z_to_bv 64 122740); C8 (Z_to_bv 64 572228); CB 32 fj; C8 flagw]
        /\ rw_cells asegs m' (Z.shiftr Fb 3 + 2147450880) rb_shadow)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 Fb) a1 a2 a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 (Z_to_bv 64 P) s8 s9 (Z_to_bv 64 2147450880) s11 t3 t4 t5 t6) F (Z_to_bv 64 0x8bbc0) fc None m (seg_rom asegs)).
  Section Sz3.
  Variables m ra sp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s1 s2 s3 s4 s5 s6 s8 s9 s11 t3 t4 t5 t6 Fb bF P j0 j1 j2 flagw fj : ltac2:(SecDiet.SzSec.tyM 'rb_poison_seq__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @m).
  #[using="Type"] Lemma rb_poison_seq__body : ltac2:(SecDiet.SzSec.bodyP 'rb_poison_seq__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof.
 intros MI FRC SH8 FRNG FSRNG Fb0 bFhi bFlo bFr SLO SHI P0 PHI.
 qfold.
    cbn [repeat] in SH8.
    pose proof (munch_refl [(Fb, Fb + 24); (Z.shiftr Fb 3 + 2147450880, Z.shiftr Fb 3 + 2147450888)]%Z m) as MU.
    pose proof (wmono_refl asegs m) as WM.
    do 2 zstep.
    zstep. if_true_by (nez_true Fb ltac:(lia)).
    do 5 zstep. neg_lits.
    do 3 zstep.
    do 3 zstep.
    zstep. neg_lits.
    zstep.
    zstep_sh0. do 3 zstep.
    zstep.
    do 4 zstep.
    apply evtF_done. eexists. split; [reflexivity|].
    unfold rb_shadow. repeat (split; [assumption|]). assumption.
  Qed.
  End Sz3.
  #[using="Type"] Lemma rb_poison_seq : ltac:(let t := eval cbv delta [rb_poison_seq__stmt] in rb_poison_seq__stmt in exact t).
  Proof. intros m ra sp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s1 s2 s3 s4 s5 s6 s8 s9 s11 t3 t4 t5 t6 Fb bF P j0 j1 j2 flagw fj. ltac2:(SecDiet.SzSec.closeP 'rb_poison_seq__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  Definition rb_s1_seq__stmt : Prop := forall (m : mem) (ra t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s8 s9 t3 t4 t5 t6 : word) (SPA Fb P Af bP : Z)
      (c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 : word),
    mem_inv asegs m ->
    rw_cells asegs m SPA [C8 c0; C8 c1; C8 c2; C8 c3; C8 c4; C8 c5; C8 c6; C8 c7; C8 c8; C8 c9; C8 c10] ->
    rw_cells asegs m (P + 48) [C8 (Z_to_bv 64 (P + 648))] ->
    unpoisoned m P (P + 680) -> rng RNG P 680 -> rng RNG (shad P) (nshad 680) -> rng RNG SPA 88 ->
    (P mod 16 = 0)%Z -> (0 < P)%Z -> (P + 680 <= 2147446784 + bP * 140737479966720)%Z -> (17594333495296 * bP <= P)%Z -> (0 <= bP <= 1)%Z -> (6303744 <= P)%Z ->
    (17594333495296 <= SPA)%Z -> (SPA + 88 <= 2^47)%Z -> (P + 680 <= SPA)%Z -> (0 < Fb)%Z -> (Fb + 64 <= 2^47)%Z ->
    evtF asegs RNG (fun ms' => exists m',
        ms' = MS (mkR (Z_to_bv 64 0x8bc84) (Z_to_bv 64 SPA) gp tp t0 t1 t2 s0 (Z_to_bv 64 SPA) (Z_to_bv 64 (Fb + 32)) (Z_to_bv 64 1)
                      (Z_to_bv 64 8) (Z_to_bv 64 Af) a4 a5 a6 a7
                      s2 (Z_to_bv 64 (P + 648)) s4 (Z_to_bv 64 (Fb + 32)) (Z_to_bv 64 Af) (Z_to_bv 64 P) s8 (Z_to_bv 64 8) (Z_to_bv 64 2147450880) (Z_to_bv 64 Fb) t3 t4 t5 t6)
                 F (Z_to_bv 64 0x4448c) fc None m' (seg_rom asegs)
        /\ munch [(SPA, SPA + 88)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
        /\ rw_cells asegs m' SPA [C8 c0; C8 c1; C8 c2; C8 c3; C8 c4; C8 c5; C8 c6; C8 c7; C8 c8; C8 c9; C8 (Z_to_bv 64 Fb)])
      (MS (mkR ra (Z_to_bv 64 SPA) gp tp t0 t1 t2 s0 (Z_to_bv 64 SPA) (Z_to_bv 64 (P + 48)) a1 a2 a3 a4 a5 a6 a7
               s2 s3 s4 s5 (Z_to_bv 64 Af) (Z_to_bv 64 P) s8 s9 (Z_to_bv 64 2147450880) (Z_to_bv 64 Fb) t3 t4 t5 t6) F (Z_to_bv 64 0x8bc50) fc None m (seg_rom asegs)).
  Section Sz4.
  Variables m ra t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s8 s9 t3 t4 t5 t6 SPA Fb P Af bP c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 : ltac2:(SecDiet.SzSec.tyM 'rb_s1_seq__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @m).
  #[using="Type"] Lemma rb_s1_seq__body : ltac2:(SecDiet.SzSec.bodyP 'rb_s1_seq__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof.
 intros MI FRA C48 PUNP PRNG PRSH RSPA P16 P0 bPhi bPlo bPr bPimg SPALO SPAHI PSP Fb0 FbHI.
 qfold.
    pose proof (munch_refl [(SPA, SPA + 88)]%Z m) as MU.
    pose proof (wmono_refl asegs m) as WM.
    ck0 PUNP; ck_go.
    zstep.
    do 6 zstep.
    zstep.
    apply evtF_done. eexists. split; [reflexivity|].
    repeat (split; [assumption|]). assumption.
  Qed.
  End Sz4.
  #[using="Type"] Lemma rb_s1_seq : ltac:(let t := eval cbv delta [rb_s1_seq__stmt] in rb_s1_seq__stmt in exact t).
  Proof. intros m ra t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s8 s9 t3 t4 t5 t6 SPA Fb P Af bP c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10. ltac2:(SecDiet.SzSec.closeP 'rb_s1_seq__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End RbSeg.
End CANSEC1.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Bytes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ZBridge OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Frame OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.StoreFast.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ExecF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ITreeA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.Shadow OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.StepF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.SysStepF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.CkTac.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FrameKit__A3P.FrameKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FrameKit__A3P.F_ngblk_defsA.TwB.
(* [comment removed for export] *) Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac qfold := try (lazymatch goal with |- evtF ?s ?r ?Q ?st => let QQ := fresh "QQ" in pose (QQ := Q); change Q with QQ end).
Import ListNotations.
Open Scope Z_scope.
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_chunks_extra m a bs n Hn Ha Hl ::= unp_store m a bs n Hn Ha Hl.

(* [comment removed for export] *)
Lemma le8_of_bytesB : forall l : list byte, length l = 8%nat -> le8 (le_bytes_to_word l) = l.
Proof.
  intros l Hl. unfold le8, word_to_le_bytes, le_bytes_to_word. rewrite Z_to_bv_unsigned.
  change (bv_wrap 64 ?z) with (z mod 2^64)%Z. rewrite (Z_to_le_bytes_mod 8 _ 64) by (cbn; lia).
  rewrite <- Hl. apply Z_to_le_bytes_to_Z.
Qed.

Section CANSEC0. Context {rc : runConstT}.
(* [comment removed for export] *)
Definition spill_words11__stmt : Prop := forall m A l, rw_cells asegs m A [CB 88 l] ->
  exists w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 : word,
    rw_cells asegs m A [C8 w0; C8 w1; C8 w2; C8 w3; C8 w4; C8 w5; C8 w6; C8 w7; C8 w8; C8 w9; C8 w10].
Section Sz2.
Variables m A l : ltac2:(SecDiet.SzSec.tyM 'spill_words11__stmt "vvv" @m).
#[using="Type"] Lemma spill_words11__body : ltac2:(SecDiet.SzSec.bodyP 'spill_words11__stmt "vvv").
Proof.
  intros HC.
  qfold.
  apply (rw_cells_split_CB asegs _ _ [] 88 _ [] [8;8;8;8;8;8;8;8;8;8;8]%nat) in HC; [|reflexivity].
  cbn [mk_CB_cells app] in HC.
  repeat match type of HC with context [CB 8 ?t] => lazymatch t with firstn _ _ => idtac end; let j := fresh "jk" in set (j := t) in HC; clearbody j end.
  pose proof HC as [[WF _] _]. cbn [cells_wf cell_wf] in WF.
  destruct WF as (L0 & L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8 & L9 & L10 & _).
  exists (le_bytes_to_word jk), (le_bytes_to_word jk0), (le_bytes_to_word jk1), (le_bytes_to_word jk2), (le_bytes_to_word jk3),
         (le_bytes_to_word jk4), (le_bytes_to_word jk5), (le_bytes_to_word jk6), (le_bytes_to_word jk7), (le_bytes_to_word jk8),
         (le_bytes_to_word jk9).
  eapply rw_cells_recell; [exact HC| cbn; repeat split|].
  cbn [cells_bytes cbytes]. rewrite !le8_of_bytesB by assumption. reflexivity.
Qed.
End Sz2.
#[using="Type"] Lemma spill_words11 : ltac:(let t := eval cbv delta [spill_words11__stmt] in spill_words11__stmt in exact t).
Proof. intros m A l. ltac2:(SecDiet.SzSec.closeP 'spill_words11__body "vvv"). Qed.
End CANSEC0.

Section CANSEC1. Context {rc : runConstT}.
Section RbSeg.
  Variables (gp tp s0 : word) (F : bvmap 5 word) (fc : bv 32) (RNG : footprint).

  Definition rb_poison_seq__stmt : Prop := forall (m : mem) (ra sp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s1 s2 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (Fb bF : Z)
      (j0 j1 j2 flagw : word) (fj : list byte),
    mem_inv asegs m ->
    rw_cells asegs m Fb [C8 j0; C8 j1; C8 j2; CB 32 fj; C8 flagw] ->
    rw_cells asegs m (Z.shiftr Fb 3 + 2147450880) (repeat (C1 (Z_to_bv 8 0)) 8) ->
    rng RNG Fb 64 -> rng RNG (Z.shiftr Fb 3 + 2147450880) 8 ->
    (0 < Fb)%Z -> (Fb + 64 <= 2147446784 + bF * 140737479966720)%Z -> (17594333495296 * bF <= Fb)%Z -> (0 <= bF <= 1)%Z ->
    (2147450880 <= Z.shiftr Fb 3 + 2147450880)%Z -> (Z.shiftr Fb 3 + 2147450880 + 8 <= 17594333495296)%Z ->
    evtF asegs RNG (fun ms' => exists m',
        ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 18446744073709551601) (Z_to_bv 64 122740)
                      (Z_to_bv 64 572144) a3 a4 a5 a6 a7
                      (Z_to_bv 64 Fb) (Z_to_bv 64 2147450880) (Z_to_bv 64 Fb) s5 s6 s7 s8 s9 s10 (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450880)) t3 t4 t5 t6)
                 F (Z_to_bv 64 0x8bbf8) fc None m' (seg_rom asegs)
        /\ munch [(Fb, Fb + 24); (Z.shiftr Fb 3 + 2147450880, Z.shiftr Fb 3 + 2147450888)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
        /\ rw_cells asegs m' Fb [C8 (Z_to_bv 64 1102416563); C8 (Z_to_bv 64 122740); C8 (Z_to_bv 64 572144); CB 32 fj; C8 flagw]
        /\ rw_cells asegs m' (Z.shiftr Fb 3 + 2147450880) rb_shadow)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 Fb) a1 a2 a3 a4 a5 a6 a7
               s2 (Z_to_bv 64 2147450880) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x8bb6c) fc None m (seg_rom asegs)).
  Section Sz3.
  Variables m ra sp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s1 s2 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 Fb bF j0 j1 j2 flagw fj : ltac2:(SecDiet.SzSec.tyM 'rb_poison_seq__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @m).
  #[using="Type"] Lemma rb_poison_seq__body : ltac2:(SecDiet.SzSec.bodyP 'rb_poison_seq__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof.
 intros MI FRC SH8 FRNG FSRNG Fb0 bFhi bFlo bFr SLO SHI.
 qfold.
    cbn [repeat] in SH8.
    pose proof (munch_refl [(Fb, Fb + 24); (Z.shiftr Fb 3 + 2147450880, Z.shiftr Fb 3 + 2147450888)]%Z m) as MU.
    pose proof (wmono_refl asegs m) as WM.
    do 2 zstep.
    zstep. if_true_by (nez_true Fb ltac:(lia)).
    do 5 zstep.
    do 2 zstep.
    do 3 zstep.
    zstep. neg_lits.
    zstep.
    zstep_sh0. do 3 zstep.
    zstep. neg_lits.
    do 4 zstep.
    apply evtF_done. eexists. split; [reflexivity|].
    unfold rb_shadow. repeat (split; [assumption|]). assumption.
  Qed.
  End Sz3.
  #[using="Type"] Lemma rb_poison_seq : ltac:(let t := eval cbv delta [rb_poison_seq__stmt] in rb_poison_seq__stmt in exact t).
  Proof. intros m ra sp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s1 s2 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 Fb bF j0 j1 j2 flagw fj. ltac2:(SecDiet.SzSec.closeP 'rb_poison_seq__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Definition rb_s1_seq__stmt : Prop := forall (m : mem) (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s7 s9 s10 s11 t3 t4 t5 t6 : word) (SPA Fb P Af bP : Z)
      (c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 : word),
    mem_inv asegs m ->
    rw_cells asegs m SPA [C8 c0; C8 c1; C8 c2; C8 c3; C8 c4; C8 c5; C8 c6; C8 c7; C8 c8; C8 c9; C8 c10] ->
    rw_cells asegs m (P + 48) [C8 (Z_to_bv 64 (P + 648))] ->
    unpoisoned m P (P + 680) -> rng RNG P 680 -> rng RNG (shad P) (nshad 680) -> rng RNG SPA 88 ->
    (P mod 16 = 0)%Z -> (0 < P)%Z -> (P + 680 <= 2147446784 + bP * 140737479966720)%Z -> (17594333495296 * bP <= P)%Z -> (0 <= bP <= 1)%Z -> (6307840 <= P)%Z ->
    (17594333495296 <= SPA)%Z -> (SPA + 88 <= 2^47)%Z -> (P + 680 <= SPA)%Z -> (0 < Fb)%Z -> (Fb + 64 <= 2^47)%Z ->
    evtF asegs RNG (fun ms' => exists m',
        ms' = MS (mkR (Z_to_bv 64 0x8bc38) (Z_to_bv 64 SPA) gp tp t0 t1 t2 s0 (Z_to_bv 64 SPA) (Z_to_bv 64 (Fb + 32)) (Z_to_bv 64 1)
                      (Z_to_bv 64 8) (Z_to_bv 64 Af) a4 a5 a6 a7
                      (Z_to_bv 64 Fb) (Z_to_bv 64 2147450880) s4 (Z_to_bv 64 (Fb + 32)) (Z_to_bv 64 Af) s7 (Z_to_bv 64 P) (Z_to_bv 64 8) (Z_to_bv 64 (P + 648)) s11 t3 t4 t5 t6)
                 F (Z_to_bv 64 0x444f4) fc None m' (seg_rom asegs)
        /\ munch [(SPA, SPA + 88)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
        /\ rw_cells asegs m' SPA [C8 c0; C8 c1; C8 c2; C8 c3; C8 c4; C8 c5; C8 c6; C8 c7; C8 c8; C8 c9; C8 (Z_to_bv 64 Fb)])
      (MS (mkR ra (Z_to_bv 64 SPA) gp tp t0 t1 t2 s0 (Z_to_bv 64 SPA) a0 a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 Fb) (Z_to_bv 64 2147450880) s4 s5 (Z_to_bv 64 Af) s7 (Z_to_bv 64 P) s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x8bbf8) fc None m (seg_rom asegs)).
  Section Sz4.
  Variables m ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s7 s9 s10 s11 t3 t4 t5 t6 SPA Fb P Af bP c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 : ltac2:(SecDiet.SzSec.tyM 'rb_s1_seq__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @m).
  #[using="Type"] Lemma rb_s1_seq__body : ltac2:(SecDiet.SzSec.bodyP 'rb_s1_seq__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof.
 intros MI FRA C48 PUNP PRNG PRSH RSPA P16 P0 bPhi bPlo bPr bPimg SPALO SPAHI PSP Fb0 FbHI.
 qfold.
    pose proof (munch_refl [(SPA, SPA + 88)]%Z m) as MU.
    pose proof (wmono_refl asegs m) as WM.
    do 2 zstep.
    replace (Z.land P 7) with 0%Z by (rewrite land7_mod; Z.div_mod_to_equations; lia).
    zstep. if_false.
    zstep.
    ck0 PUNP; ck_go.
    zstep.
    do 6 zstep.
    zstep.
    apply evtF_done. eexists. split; [reflexivity|].
    repeat (split; [assumption|]). assumption.
  Qed.
  End Sz4.
  #[using="Type"] Lemma rb_s1_seq : ltac:(let t := eval cbv delta [rb_s1_seq__stmt] in rb_s1_seq__stmt in exact t).
  Proof. intros m ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s7 s9 s10 s11 t3 t4 t5 t6 SPA Fb P Af bP c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10. ltac2:(SecDiet.SzSec.closeP 'rb_s1_seq__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End RbSeg.
End CANSEC1.
End TwB.
End F_ngblk_psegA.
