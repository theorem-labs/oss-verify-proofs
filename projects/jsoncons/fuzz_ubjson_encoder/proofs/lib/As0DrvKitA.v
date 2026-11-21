(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3: recorded proofs replaced by tactic proofs. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import AsanAcct.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import
  PropExec CatExec CatSim StoreOk ShapeAlg SpinAlg AsanAcctShape SymExec2 SymExec2Sound SymRun SymDrive SymDriveX.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require KReplay.
Ltac2 kr_t_As0DrvKitA () := "C4ELinuxProcessSemantics?LinuxProcessSem2Fs4pathC47Corelib4Init5Logic8eq_ind_rC4ELinuxProcessSemantics?LinuxProcessSem2Fs2FsC4ELinuxProcessSemantics?LinuxProcessSem5State7PipeBufK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00I47Corelib4Init5Logic2eq00K47Corelib4Init9Datatypes6option02C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8AsanAcct;munrestrictC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8AsanAcct9mrestrictC13~~~K47Corelib4Init5Logic2eq01C47Corelib4Init5Logic6eq_symC46Stdlib5LogicHFunctionalExtensionalityIfunctional_extensionalityK47Corelib7Numbers7BinNums8positive03I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K47Corelib4Init9Datatypes4bool02I47Corelib4Init9Datatypes4prod00I47Corelib4Init9Datatypes4list00K47Corelib7Numbers7BinNums8positive01C4ELinuxProcessSemantics5Riscv7Prelude5bvmapC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8AsanAcct>H_off_segmentsC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8AsanAcct>wx_segs_nowrapC13~~~C4ELinuxProcessSemantics?LinuxProcessSem5State9m_vm_lazyC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8AsanAcct:lazy_coverC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8AsanAcct4A_wfC13~~~I79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8AsanAcct4MInv00C13~~~K47Corelib4Init9Datatypes4list01K89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX29sym_state01C13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX28sym_execC13~~~K47Corelib4Init9Datatypes4prod01C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX25s_logC13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX25carryC13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib=SymExec2Sound4SX2S7regs_okC13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib=SymExec2Sound4SX2S7know_okC13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib=SymExec2Sound4SX2S9scs_denotC13~~~C4ELinuxProcessSemantics?LinuxProcessSem5State8m_haltedC89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX26s_regsC13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib=SymExec2Sound4SX2S9mem_denotC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8AsanAcctEsame_but_materializedC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec7seg_romC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec4mkstC13~~~K4ELinuxProcessSemantics?LinuxProcessSem3Run6config01C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7SpinAlg9srealizesC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib6SymRun9run_soundC13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib=SymExec2Sound4SX2S8log_flatC13~~~I79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib6CatSim6msteps00C13~~~I47Corelib4Init5Logic3and00I47Corelib4Init5Logic2ex00C45stdpp9bitvector;definitions7Z_to_bvC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8AsanAcct6hcleanC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib6SymRun;carry_afterC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:As0DrvKitAEmrestrict_munrestrictC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib=AsanAcctShapeGsrz_msteps_restricted_TC13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX24s_pcC13~~~I47Corelib7Numbers7BinNums1Z00I47Corelib4Init9Datatypes3nat00I89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX27scripts00C13~~~I89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX24expr00C13~~~I89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX26kentry00C13~~~I89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX29sym_state00C13~~~I89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX28sidecond00C13~~~I89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX23env00C13~~~I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8ShapeAlg4TSetC13~~~I89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX26sentry00C13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib5BMode;bm_off_instC13~~~C4ELinuxProcessSemantics?LinuxProcessSem5StateAm_vm_materializedC4ELinuxProcessSemantics?LinuxProcessSem5State?with_vm_backingK4ELinuxProcessSemantics?LinuxProcessSem5State5Model01K4ELinuxProcessSemantics?LinuxProcessSem5State7VmState01I4ELinuxProcessSemantics?LinuxProcessSem5State7FdState00I4ELinuxProcessSemantics?LinuxProcessSem5State7VmState00I4ELinuxProcessSemantics?LinuxProcessSem5State7IoState00I4ELinuxProcessSemantics?LinuxProcessSem5State7FsState00I4ELinuxProcessSemantics?LinuxProcessSem5State9ProcState00I4ELinuxProcessSemantics?LinuxProcessSem5State8LimState00I4ELinuxProcessSemantics?LinuxProcessSem5State9TimeState00I4ELinuxProcessSemantics?LinuxProcessSem5State6VmMaps00c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:As0DrvKitA5lzinvC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:As0DrvKitA;sbm_lazy_eqC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:As0DrvKitA=sbm_halted_eqC13~~~K47Corelib4Init5Logic3and01K47Corelib4Init9Datatypes6option01C47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic9False_indI47Corelib4Init5Logic5False00I47Corelib4Init5Logic4True00K47Corelib4Init5Logic4True01C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8store_okK47Corelib4Init9Datatypes3nat02C45stdpp9bitvector;definitions;bv_unsignedK47Corelib7Numbers7BinNums1Z02C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics<find_segmentC4ELinuxProcessSemantics?LinuxProcessSem<MemImageType<seg_writableC4ELinuxProcessSemantics?LinuxProcessSem<MemImageType9seg_bytesC4ELinuxProcessSemantics?LinuxProcessSem<MemImageType8seg_baseC56Stdlib6ZArith6BinInt1Z4of_NK45stdpp9bitvector;definitions2bv01C45stdpp9bitvector;definitions6bv_addC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics5wviewC47Corelib4Init9Datatypes7nat_indC56Stdlib6ZArith6BinInt1Z3subC56Stdlib6ZArith6BinInt1Z4to_NC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics?segment_byte_atK47Corelib4Init9Datatypes3nat01I4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00K47Corelib4Init9Datatypes4list02C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec3rdnC13~~~C4ELinuxProcessSemantics?LinuxProcessSem<MemImageType<seg_readableC56Stdlib6NArith6BinNat1N6to_natC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemanticsBsegment_read_bytesc79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:As0DrvKitA9lzinv_sbmC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:As0DrvKitA9rz_run_lzC13~~~".
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Import SX2. Import SX2S.

Section FPX_1. Context {fx : PropExec.FPState}.
Section KitA.
Variable segs : list Segment.
Variable scfg : SpuriousCfg.

(* [comment removed for export] *)
Lemma mrestrict_munrestrict : forall (H : word -> bool) (M M' : word -> option byte),
  (forall a, H a = true -> M' a = None) -> mrestrict H (munrestrict H M M') = M'.
Proof.
  intros H M M' Hc. apply functional_extensionality. intros a. unfold mrestrict, munrestrict.
  destruct (H a) eqn:E; [symmetry; apply Hc; exact E | reflexivity].
Qed.

(* [comment removed for export] *)
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


(* [comment removed for export] *)
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

(* [comment removed for export] *)
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

(* [comment removed for export] *)
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

(* [comment removed for export] *)
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


(* [comment removed for export] *)
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
