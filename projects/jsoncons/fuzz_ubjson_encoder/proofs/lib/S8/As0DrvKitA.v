(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import AsanAcct.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import PropExec CatExec CatSim StoreOk ShapeAlg SpinAlg AsanAcctShape SymExec2 SymExec2Sound SymRun SymDrive SymDriveX.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Import SX2. Import SX2S.

Section FPX_1. Context {fx : PropExec.FPState}.
Section KitA.
Variable segs : list Segment.
Variable scfg : SpuriousCfg.

Lemma mrestrict_munrestrict : forall (H : word -> bool) (M M' : word -> option byte),
  (forall a, H a = true -> M' a = None) -> mrestrict H (munrestrict H M M') = M'.
Proof.
  intros H M M' Hc. apply functional_extensionality. intros a. unfold mrestrict, munrestrict.
  destruct (H a) eqn:E; [symmetry; apply Hc; exact E | reflexivity].
Qed.

Theorem rz_run_lz : forall (H : word -> bool) (A : list (Z * Z)) fuel stops scr pc sr kn nx ss' scs scr' kn' scs2 hs2
                            E M R model T,
  H_off_segments segs H -> wx_segs_nowrap segs ->
  lazy_cover H (m_vm_lazy model) A -> A_wf A -> MInv A model ->
  sym_exec segs fuel true stops scr (SS pc sr [] kn nx) [] = (ss', scs, scr') ->
  carry (s_log ss') kn [] = (kn', scs2, hs2) ->
  regs_ok E sr R -> know_ok segs E (mrestrict H M) kn ->
  scs_denot segs (mrestrict H M) E scs -> scs_denot segs (mrestrict H M) E scs2 ->
  m_halted model = None ->
  (forall R' MV' model', regs_ok E (s_regs ss') R' -> know_ok segs E MV' kn' ->
     MV' = mem_denot E (mrestrict H M) (s_log ss') ->
     mrestrict H (munrestrict H M MV') = MV' ->
     MInv A model' -> same_but_materialized model model' ->
     srealizes segs scfg (mkCfg (mkst R' (Z_to_bv 64 (s_pc ss')) (munrestrict H M MV') (seg_rom segs)) model') T) ->
  srealizes segs scfg (mkCfg (mkst R (Z_to_bv 64 pc) M (seg_rom segs)) model) T.
Proof.
  intros H A fuel stops scr pc sr kn nx ss' scs scr' kn' scs2 hs2 E M R model T
         HH Hwx HL HA HI Hex Hc HR HK Hsc Hsc2 Hh Hcont.
  destruct (run_sound segs fuel stops scr pc sr kn nx ss' scs scr' E (mrestrict H M) (seg_rom segs) R Hex HR HK Hsc)
    as (R' & HR' & Hlf & Hms).
  apply (srz_msteps_restricted_T segs scfg H HH Hwx A (mkst R (Z_to_bv 64 pc) M (seg_rom segs)) _ model T HL HA HI Hh Hms).
  intros model' HI' HS HC.
  change (unrestrict H (ms_mem (mkst R (Z_to_bv 64 pc) M (seg_rom segs)))
            (mkst R' (Z_to_bv 64 (s_pc ss')) (mem_denot E (mrestrict H M) (s_log ss')) (seg_rom segs)))
    with (mkst R' (Z_to_bv 64 (s_pc ss')) (munrestrict H M (mem_denot E (mrestrict H M) (s_log ss'))) (seg_rom segs)).
  apply (Hcont R' _ model' HR'); [ | reflexivity | | exact HI' | exact HS].
  - eapply carry_after; eassumption.
  - apply mrestrict_munrestrict. intros a Ha. exact (HC a Ha).
Qed.

Theorem rz_msteps_lz : forall (H : word -> bool) (A : list (Z * Z)) R pc M R' pc' MV' model T,
  H_off_segments segs H -> wx_segs_nowrap segs ->
  lazy_cover H (m_vm_lazy model) A -> A_wf A -> MInv A model -> m_halted model = None ->
  msteps segs (mkst R pc (mrestrict H M) (seg_rom segs)) (mkst R' pc' MV' (seg_rom segs)) ->
  (forall model', MInv A model' -> same_but_materialized model model' ->
     mrestrict H (munrestrict H M MV') = MV' ->
     srealizes segs scfg (mkCfg (mkst R' pc' (munrestrict H M MV') (seg_rom segs)) model') T) ->
  srealizes segs scfg (mkCfg (mkst R pc M (seg_rom segs)) model) T.
Proof.
  intros H A R pc M R' pc' MV' model T HH Hwx HL HA HI Hh Hms Hcont.
  apply (srz_msteps_restricted_T segs scfg H HH Hwx A (mkst R pc M (seg_rom segs)) _ model T HL HA HI Hh Hms).
  intros model' HI' HS HC.
  change (unrestrict H (ms_mem (mkst R pc M (seg_rom segs))) (mkst R' pc' MV' (seg_rom segs)))
    with (mkst R' pc' (munrestrict H M MV') (seg_rom segs)).
  apply (Hcont model' HI' HS). apply mrestrict_munrestrict. intros a Ha. exact (HC a Ha).
Qed.

Definition lzinv (H : word -> bool) (A : list (Z * Z)) (model : Model) : Prop :=
  H_off_segments segs H /\ lazy_cover H (m_vm_lazy model) A /\ A_wf A /\ MInv A model /\ m_halted model = None.

Lemma sbm_lazy_eq : forall m m', same_but_materialized m m' -> m_vm_lazy m' = m_vm_lazy m.
Proof. intros m m' ->. destruct m as [fd [maps lazy mat] io fsy pr lim tm]. reflexivity. Qed.
Lemma sbm_halted_eq : forall m m', same_but_materialized m m' -> m_halted m' = m_halted m.
Proof. intros m m' ->. destruct m as [fd [maps lazy mat] io fsy pr lim tm]. reflexivity. Qed.

Lemma lzinv_sbm : forall H A model model',
  lzinv H A model -> MInv A model' -> same_but_materialized model model' -> lzinv H A model'.
Proof.
  intros H A model model' (H1 & H2 & H3 & _ & H5) HI HS.
  split; [exact H1|]. split; [rewrite (sbm_lazy_eq _ _ HS); exact H2|]. split; [exact H3|]. split; [exact HI|].
  rewrite (sbm_halted_eq _ _ HS); exact H5.
Qed.

Lemma mrestrict_some : forall (H : word -> bool) (M : word -> option byte) a b, mrestrict H M a = Some b -> M a = Some b.
Proof. intros H M a b. unfold mrestrict. destruct (H a); [discriminate | auto]. Qed.

Lemma store_ok_of_mrestrict : forall (H : word -> bool) (M : word -> option byte) n (a : word),
  store_ok segs (mrestrict H M) a n = true -> store_ok segs M a n = true.
Proof.
  intros H M n. induction n as [|n IH]; intros a Hs; [reflexivity|]. cbn [store_ok] in *.
  unfold wview in *. unfold mrestrict in Hs at 1. destruct (H a) eqn:EH.
  - destruct (M a) as [b|]; [apply IH | ].
    + destruct (find_segment segs (bv_unsigned a) 1) as [sg|]; [|discriminate]. destruct (seg_writable sg); [|discriminate].
      destruct (segment_byte_at _ _); [exact Hs | discriminate].
    + destruct (find_segment segs (bv_unsigned a) 1) as [sg|]; [|discriminate]. destruct (seg_writable sg); [|discriminate].
      destruct (segment_byte_at _ _); [apply IH; exact Hs | discriminate].
  - destruct (M a) as [b|]; [apply IH; exact Hs|].
    destruct (find_segment segs (bv_unsigned a) 1) as [sg|]; [|discriminate]. destruct (seg_writable sg); [|discriminate].
    destruct (segment_byte_at _ _); [apply IH; exact Hs | discriminate].
Qed.

Lemma rdn_of_mrestrict : forall (H : word -> bool) (M : word -> option byte), H_off_segments segs H ->
  forall n (a : word) bs, rdn segs (mrestrict H M) a n = Some bs -> rdn segs M a n = Some bs.
Proof.
  intros H M HH n. induction n as [|n IH]; intros a bs Hr; [exact Hr|]. cbn [rdn] in *.
  unfold mrestrict in Hr at 1. destruct (H a) eqn:EH.
  -
    exfalso. unfold seg_rom, memory_read in Hr. change (Z.of_N 1) with 1 in Hr. rewrite (HH a EH) in Hr. discriminate.
  - destruct (M a) as [b|].
    + destruct (rdn segs (mrestrict H M) (a + 1)%bv n) as [r|] eqn:E2; [|discriminate]. rewrite (IH _ _ E2). exact Hr.
    + destruct (seg_rom segs a) as [b|]; [|discriminate].
      destruct (rdn segs (mrestrict H M) (a + 1)%bv n) as [r|] eqn:E2; [|discriminate]. rewrite (IH _ _ E2). exact Hr.
Qed.

Theorem rz_run_lz2 : forall (H : word -> bool) (A : list (Z * Z)) fuel stops scr pc sr kn nx ss' scs scr' kn' scs2 hs2
                            E M R model T,
  wx_segs_nowrap segs -> lzinv H A model ->
  sym_exec segs fuel true stops scr (SS pc sr [] kn nx) [] = (ss', scs, scr') ->
  carry (s_log ss') kn [] = (kn', scs2, hs2) ->
  regs_ok E sr R -> know_ok segs E (mrestrict H M) kn ->
  scs_denot segs (mrestrict H M) E scs -> scs_denot segs (mrestrict H M) E scs2 ->
  (forall R' M' model', regs_ok E (s_regs ss') R' -> know_ok segs E (mrestrict H M') kn' ->
     mrestrict H M' = mem_denot E (mrestrict H M) (s_log ss') ->
     (forall a, H a = true -> M' a = M a) ->
     lzinv H A model' -> same_but_materialized model model' ->
     srealizes segs scfg (mkCfg (mkst R' (Z_to_bv 64 (s_pc ss')) M' (seg_rom segs)) model') T) ->
  srealizes segs scfg (mkCfg (mkst R (Z_to_bv 64 pc) M (seg_rom segs)) model) T.
Proof.
  intros H A fuel stops scr pc sr kn nx ss' scs scr' kn' scs2 hs2 E M R model T Hwx HZ Hex Hc HR HK Hsc Hsc2 Hcont.
  pose proof HZ as (H1 & H2 & H3 & H4 & H5).
  apply (rz_run_lz H A fuel stops scr pc sr kn nx ss' scs scr' kn' scs2 hs2 E M R model T H1 Hwx H2 H3 H4 Hex Hc HR HK Hsc Hsc2 H5).
  intros R' MV' model' HR' HK' EQ EQV HI' HS.
  apply (Hcont R' (munrestrict H M MV') model' HR').
  - rewrite EQV. exact HK'.
  - rewrite EQV. exact EQ.
  - intros a Ha. unfold munrestrict. rewrite Ha. reflexivity.
  - exact (lzinv_sbm H A model model' HZ HI' HS).
  - exact HS.
Qed.

End KitA.
End FPX_1.

Ltac run_block_lz_with HR HK HZ Hwx fuel stops scr NX keep :=
  lazymatch type of HR with
  | regs_ok ?E ?sr ?R =>
    lazymatch type of HK with
    | know_ok ?segs _ (mrestrict ?H ?M) ?kn =>
      lazymatch type of HZ with
      | lzinv _ _ ?A ?model =>
      lazymatch goal with
      | |- srealizes _ ?scfg (mkCfg (mkst R (Z_to_bv 64 ?pc) M _) model) ?T =>
        let r := eval vm_compute in (sym_exec segs fuel true stops scr (SS pc sr [] kn NX) []) in
        lazymatch r with
        | (?ss', ?scs, ?scr') =>
          let c := eval vm_compute in (carry (s_log ss') kn []) in
          lazymatch c with
          | (?kn', ?scs2, ?hs2) =>
            eapply (rz_run_lz2 segs scfg H A fuel stops scr pc sr kn NX ss' scs scr' kn' scs2 hs2 E M R model T Hwx HZ);
            [ vm_compute; reflexivity
            | vm_compute; reflexivity
            | exact HR | exact HK
            | split_foralls
            | split_foralls
            | let R' := fresh "R" in let M' := fresh "M" in let model' := fresh "model" in
              let EQM := fresh "EQM" in let EQH := fresh "EQH" in let SBM := fresh "SBM" in
              let HR' := fresh "HR" in let HK' := fresh "HK" in let HZ' := fresh "HZ" in
              intros R' M' model' HR' HK' EQM EQH HZ' SBM; cbn [s_pc s_regs s_log] in HR', EQM |- *;
              lazymatch keep with
              | true => idtac
              | false => clear EQM EQH SBM HR HK HZ; try clear R; try clear M; try clear model;
                         try rename R' into R; try rename M' into M; try rename model' into model;
                         rename HR' into HR; rename HK' into HK; rename HZ' into HZ
              end ]
          end
        end
      end
      end
    end
  end.
