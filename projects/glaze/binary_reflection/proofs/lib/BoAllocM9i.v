(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
Require Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Logic.FunctionalExtensionality LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mprotect LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocSim OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys6 OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.BackingAlgebra OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8m OSSVerify.Proofs.glaze.binary_reflection.lib.BoDrvIStrlen OSSVerify.glaze.binary_reflection.images.AsanUbsan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac tauto ::= OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac.wd_tauto.   (* [comment removed for export] *)
Module BoAllocM8k.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import Stdlib.Logic.FunctionalExtensionality.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mprotect.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.DivergeSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.SpinAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes.AgentNodes OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocSim OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys6.MhKSys OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsK OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys6.AsKSys OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys6.AsKSys2 OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsRtK OSSVerify.Proofs.glaze.binary_reflection.lib.Common.BackingAlgebra OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys6.AsanNodesLibE OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8m OSSVerify.Proofs.glaze.binary_reflection.lib.BoDrvIStrlen.Bo_code_80b0c_815a0.
Import OSSVerify.glaze.binary_reflection.images.AsanUbsan.
Import ListNotations.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation BSEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).
#[local] Abbreviation LE4 z := (word_to_le_bytes 4 (Z_to_bv 64 z)).
#[local] Abbreviation U := bv_unsigned.

Section FPGen1.
Context {fx : FPState}.

Lemma mk_munrestrict_same : forall (Hd : word -> bool) (M M' : word -> option byte),
  (forall a, Hd a = true -> M' a = M a) -> munrestrict Hd M (mrestrict Hd M') = M'.
Proof using.
  intros Hd M M' E. apply functional_extensionality. intros a. (lazymatch goal with |- ?G => let G' := eval unfold munrestrict, mrestrict in G in change_no_check G' end).
  destruct (Hd a) eqn:Ha; [symmetry; apply E; exact Ha | reflexivity].
Qed.
Lemma mk_unrestrict_mkst : forall (Hd : word -> bool) (M : word -> option byte) regs pc m rom,
  unrestrict Hd M (mkst regs pc m rom) = mkst regs pc (munrestrict Hd M m) rom.
Proof using. intros. reflexivity. Qed.
Lemma mk_restrict_mkst : forall (Hd : word -> bool) regs pc m rom,
  restrict Hd (mkst regs pc m rom) = mkst regs pc (mrestrict Hd m) rom.
Proof using. intros. reflexivity. Qed.

(* [comment removed for export] *)
Lemma store_ok_ext : forall segs n (m m' : word -> option byte) (a : word),
  (U a + Z.of_nat n <= 2 ^ 64) ->
  (forall x : word, U a <= U x < U a + Z.of_nat n -> m' x = m x) ->
  store_ok segs m' a n = store_ok segs m a n.
Proof using.
  intros segs n. induction n as [|n IH]; intros m m' a Hnw E; [reflexivity|].
  (lazymatch goal with |- ?G => let G' := eval cbn [store_ok] in G in change_no_check G' end). pose proof (u64_range a) as Ha.
  assert (Ea : m' a = m a) by (apply E; lia).
  (lazymatch goal with |- ?G => let G' := eval unfold wview in G in change_no_check G' end). rewrite Ea.
  destruct n as [|n'].
  - reflexivity.
  - assert (Hu1 : U (a + 1)%bv = U a + 1) by (apply u_add1; lia).
    rewrite (IH m m' (a + 1)%bv); [reflexivity | rewrite Hu1; lia | intros x Hx; apply E; rewrite Hu1 in Hx; lia].
Qed.

(* [comment removed for export] *)
Definition mfi_ret (regs r : bvmap 5 word) (sp ra s0v s1v s2v s3v s4v res : word) : Prop :=
  getr r 10 = res /\ getr r 2 = sp /\ getr r 1 = ra
  /\ getr r 8 = s0v /\ getr r 9 = s1v /\ getr r 18 = s2v /\ getr r 19 = s3v /\ getr r 20 = s4v
  /\ regs_agree (fun i : reg => In i mfi_clob2) regs r.

Section MAPK.
  Variable Hd : word -> bool.
  Hypothesis HOFFSEG : H_off_segments BSEGS Hd.
  Hypothesis WX : wx_segs_nowrap BSEGS.



  (* [comment removed for export] *)
  Theorem rarmap_katsD :
    forall (A : list (Z * Z)) regs (mem rom : word -> option byte) (model : Model)
           (sp ra s0v s1v s2v s3v s4v s5v addr size name : word) (PGP CF : Z) (Qok Qf : config -> Prop)
           (MOK MKP MDS : Model -> Model),
    let M1 := mfi_m1 mem sp ra s0v s1v s2v s3v s4v s5v addr size name PGP in
    let ENOMEMw : word := Z_to_bv 64 (2 ^ 64 - 12) in
    let SCR := LE4 0xffffffffaaaaaaaa in
    (* [comment removed for export] *)
    getr regs 1 = ra -> getr regs 2 = sp -> getr regs 11 = addr -> getr regs 12 = size -> getr regs 13 = name ->
    getr regs 8 = s0v -> getr regs 9 = s1v -> getr regs 18 = s2v -> getr regs 19 = s3v -> getr regs 20 = s4v -> getr regs 21 = s5v ->
    (2 ^ 24 <= U sp /\ U sp + 16 <= 2 ^ 47) -> ret_ok ra ->
    U addr mod 4096 = 0 -> (U size mod 4096 = 0 /\ U size + 4096 < 2 ^ 63) -> U name <> 0 ->
    (AIMGLO <= PGP /\ PGP + 8 <= AIMGHI) -> (AIMGLO <= CF /\ CF + 264 <= AIMGHI) ->
    store_ok BSEGS mem (at_ sp (-400)) 400 = true ->
    rdn BSEGS mem (Z_to_bv 64 0x105ef8) 8 = Some (LE8 (Z_to_bv 64 PGP)) ->
    rdn BSEGS mem (Z_to_bv 64 PGP) 8 = Some (LE8 (Z_to_bv 64 4096)) ->
    rdn BSEGS mem (Z_to_bv 64 0x105f08) 8 = Some (LE8 (Z_to_bv 64 CF)) ->
    rdn BSEGS mem (Z_to_bv 64 (CF + 260)) 1 = Some [Z_to_bv 8 0] ->
    rdn BSEGS mem (Z_to_bv 64 (CF + 144)) 8 = Some (LE8 (Z_to_bv 64 0)) ->
    (* [comment removed for export] *)
    (AIMGHI <= U addr /\ U addr + U size < 2 ^ 63 /\ (U addr + U size <= U sp - 400 \/ U sp <= U addr)) ->
    (* [comment removed for export] *)
    hid_off Hd 0x105ef8 8 -> hid_off Hd PGP 8 -> hid_off Hd 0x105f08 8 -> hid_off Hd (CF + 260) 1 -> hid_off Hd (CF + 144) 8 ->
    hid_off Hd (U sp - 400) 400 ->
    (* [comment removed for export] *)
    m_halted model = None -> lazy_cover Hd (m_vm_lazy model) A -> A_wf A -> MInv A model ->
    (* [comment removed for export] *)
    (forall mdlm (r1 : bvmap 5 word), same_but_materialized model mdlm -> MInv A mdlm -> m_halted mdlm = None ->
        getr r1 10 = addr -> getr r1 11 = size -> getr r1 12 = Z_to_bv 64 3 -> getr r1 13 = Z_to_bv 64 50 ->
        getr r1 14 = Z_to_bv 64 (2 ^ 64 - 1) -> getr r1 15 = Z_to_bv 64 0 ->
        forall Qok' Qf' : config -> Prop,
          katwD BSEGS (mkCfg (mkst (regupd r1 10 addr) (0x811b0 : word) (zfill addr size M1) rom) (MOK mdlm)) Qok' Qf' ->
          katsD BSEGS (mkCfg (epend r1 (0x811ac : word) M1 rom (Z_to_bv 64 222)) mdlm) Qok' Qf') ->
    (* [comment removed for export] *)
    (forall mdlm, same_but_materialized model mdlm -> MInv A mdlm ->
        (m_halted (MOK mdlm) = None /\ lazy_cover Hd (m_vm_lazy (MOK mdlm)) A /\ MInv A (MOK mdlm))
        /\ (m_halted (MKP mdlm) = None /\ lazy_cover Hd (m_vm_lazy (MKP mdlm)) A /\ MInv A (MKP mdlm))
        /\ (m_halted (MDS mdlm) = None /\ lazy_cover Hd (m_vm_lazy (MDS mdlm)) A /\ MInv A (MDS mdlm))) ->
    (* [comment removed for export] *)
    (forall (r' : bvmap 5 word) mdlm mdl4,
        same_but_materialized model mdlm -> MInv A mdlm -> same_but_materialized (MOK mdlm) mdl4 -> MInv A mdl4 ->
        mfi_ret regs r' sp ra s0v s1v s2v s3v s4v addr ->
        katwD BSEGS (mkCfg (mkst r' ra (wbytes (zfill addr size M1) (at_ sp (-84)) SCR) rom) mdl4) Qok Qf) ->
    (* [comment removed for export] *)
    (forall (r' : bvmap 5 word) mdlm mdl4,
        same_but_materialized model mdlm -> MInv A mdlm -> same_but_materialized (MKP mdlm) mdl4 -> MInv A mdl4 ->
        mfi_ret regs r' sp ra s0v s1v s2v s3v s4v (Z_to_bv 64 0) ->
        katD BSEGS (mkCfg (mkst r' ra (wbytes (wbytes M1 (at_ sp (-84)) SCR) (at_ sp (-84)) (LE4 12)) rom) mdl4) Qf) ->
    (* [comment removed for export] *)
    (forall (r' : bvmap 5 word) mdlm mdl4,
        same_but_materialized model mdlm -> MInv A mdlm -> same_but_materialized (MDS mdlm) mdl4 -> MInv A mdl4 ->
        mfi_ret regs r' sp ra s0v s1v s2v s3v s4v (Z_to_bv 64 0) ->
        katD BSEGS (mkCfg (mkst r' ra (wbytes (wbytes (unfill addr size M1) (at_ sp (-84)) SCR) (at_ sp (-84)) (LE4 12)) rom) mdl4) Qf) ->
    katsD BSEGS (mkCfg (mkst regs (0x8b0f8 : word) mem rom) model) Qok Qf.
  Proof using WX HOFFSEG.
    intros A regs mem rom model sp ra s0v s1v s2v s3v s4v s5v addr size name PGP CF Qok Qf MOK MKP MDS M1 ENOMEMw SCR
           H1 H2 H11 H12 H13 H8 H9 H18 H19 H20 H21 Hsp Hret Haddr Hsize Hname HPGP HCF Hstk Rgpg Rpg Rgcf Rdpm Rlim
           Hslot HDgpg HDpg HDgcf HDdpm HDlim HDscr HALT LC AWF MI NODE CHILD CONTOK CONTKP CONTDS.
    pose proof (u64_range sp) as Hspr. pose proof (u64_range addr) as Har. pose proof (u64_range size) as Hszr.
    destruct Hslot as (SL1 & SL2 & SL3). destruct HPGP as [PG1 PG2]. destruct HCF as [CF1 CF2].
    (* [comment removed for export] *)
    assert (Hstk' : store_ok BSEGS (mrestrict Hd mem) (at_ sp (-400)) 400 = true).
    { rewrite store_ok_mrestrict; [exact Hstk | first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); exact HDscr]. }
    assert (CELLR : forall (c : Z) (k : nat) v, 0 <= c < 2 ^ 32 -> Z.of_nat k <= 8 -> hid_off Hd c (Z.of_nat k) ->
               rdn BSEGS mem (Z_to_bv 64 c) k = Some v -> rdn BSEGS (mrestrict Hd mem) (Z_to_bv 64 c) k = Some v).
    { intros c k v Hc0 Hc1 Hh Hr. rewrite rdn_mrestrict; [exact Hr | first [ solve [ wd_unorm1; wd_zofnat; lia ] | rewrite u_Z2bv by lia; lia ] | rewrite u_Z2bv by lia; exact Hh]. }
    destruct (mfi_pre (mrestrict Hd mem) rom sp ra s0v s1v s2v s3v s4v s5v addr size name PGP CF regs
                H1 H2 H11 H12 H13 H8 H9 H18 H19 H20 H21 Hsp Haddr Hsize Hname (conj PG1 PG2) (conj CF1 CF2) Hstk'
                (CELLR 0x105ef8 8%nat _ ltac:(lia) ltac:((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia) HDgpg Rgpg) (CELLR PGP 8%nat _ ltac:(lia) ltac:((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia) HDpg Rpg)
                (CELLR 0x105f08 8%nat _ ltac:(lia) ltac:((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia) HDgcf Rgcf) (CELLR (CF + 260) 1%nat _ ltac:(lia) ltac:((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia) HDdpm Rdpm))
      as (r1 & RUN1 & B1 & B2 & B8 & B9 & B18 & B19 & B20 & B10 & B11 & B12 & B13 & B14 & B15 & B17 & AG1).
    assert (EM1 : mfi_m1 (mrestrict Hd mem) sp ra s0v s1v s2v s3v s4v s5v addr size name PGP = mrestrict Hd M1).
    { (lazymatch goal with |- ?G => let G' := eval unfold M1, mfi_m1, mfi_m0 in G in change_no_check G' end).
      rewrite !wbytes_mrestrict; [reflexivity | ..];
        wd_lenlit; rewrite ?length_N_to_le_bytes, ?at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn [length Z.of_nat Pos.of_succ_nat Pos.succ Pos.to_nat] in G in change_no_check G' end); first [lia | intros x Hx; apply HDscr; lia]. }
    rewrite EM1 in RUN1.
    assert (M1hid : forall a : word, Hd a = true -> M1 a = mem a).
    { intros a Ha. (lazymatch goal with |- ?G => let G' := eval unfold M1 in G in change_no_check G' end). apply (mfi_m1_outside mem sp ra s0v s1v s2v s3v s4v s5v addr size name PGP Hsp).
      destruct (Z_lt_le_dec (U a) (U sp - 400)) as [C1|C1]; [left; exact C1|].
      destruct (Z_lt_le_dec (U a) (U sp)) as [C2|C2]; [| right; exact C2].
      exfalso. rewrite (HDscr a) in Ha by lia. discriminate Ha. }
    apply (katsD_msteps_acct BSEGS Hd HOFFSEG WX A (mkst regs (0x8b0f8 : word) mem rom)
             (mkst r1 (0x811ac : word) (mrestrict Hd M1) rom) model Qok Qf LC AWF MI HALT).
    { rewrite mk_restrict_mkst. exact RUN1. }
    intros mdlm MIm SBMm HC1. rewrite mk_unrestrict_mkst.
    replace (RiscvSemantics.ms_mem (mkst regs (0x8b0f8 : word) mem rom)) with mem by reflexivity.
    rewrite (mk_munrestrict_same Hd mem M1 M1hid).
    pose proof (same_but_materialized_frame model mdlm SBMm) as FRm.
    assert (HALTm : m_halted mdlm = None) by (destruct FRm as (_&_&_&_&_&_&_&_&_&_&_&_&Hh&_); rewrite Hh; exact HALT).
    (* [comment removed for export] *)
    apply (katsD_ecall BSEGS r1 (0x811ac : word) M1 rom mdlm W_811ac Qok Qf HALTm F_811ac E_811ac).
    rewrite B17.
    destruct (CHILD mdlm SBMm MIm) as ((HOK1 & HOK2 & HOK3) & _ & _).
    (* [comment removed for export] *)
    assert (POSTF : forall MZ : word -> option byte,
               (forall x : word, U sp - 400 <= U x < U sp -> MZ x = M1 x) ->
               store_ok BSEGS (mrestrict Hd MZ) (at_ sp (-84)) 4 = true
               /\ (forall (k : Z) (v : word), In (k, v) [(-8, ra); (-16, s0v); (-24, s1v); (-32, s2v); (-40, Z_to_bv 64 0x8b124); (-48, size);
                                                         (-56, addr); (-64, s2v); (-72, s3v); (-80, s4v)] ->
                      rdn BSEGS (mrestrict Hd MZ) (at_ sp k) 8 = Some (LE8 v))).
    { intros MZ EZ. split.
      - rewrite store_ok_mrestrict; [| first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); intros x Hx; apply HDscr; lia].
        rewrite (store_ok_ext BSEGS 4 M1 MZ); [| first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | intros x Hx; apply EZ; rewrite at_u in Hx by lia; cbn in Hx; lia].
        eapply store_ok_mono; [apply mfi_m1_grows|].
        eapply (store_ok_sub BSEGS mem (at_ sp (-400)) _ 400); [first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | exact Hstk | first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite !at_u by lia; lia ] | first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite !at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ]].
      - intros k v Hin.
        assert (Hk : -80 <= k <= -8) by (cbn [In] in Hin; repeat (destruct Hin as [E|Hin]; [injection E as <- <-; lia|]); destruct Hin).
        rewrite rdn_mrestrict; [| first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); intros x Hx; apply HDscr; lia].
        rewrite <- (mfi_m1_slots mem sp ra s0v s1v s2v s3v s4v s5v addr size name PGP Hsp k v Hin). fold M1.
        apply rdn_ext; [first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | intros x Hx; apply EZ; rewrite at_u in Hx by lia; cbn in Hx; lia]. }
    assert (Q1 : forall v : word, getr (regupd r1 10 v) 1 = Z_to_bv 64 0x82f6c) by (intros v; rewrite getr_other by (intros E; discriminate E); exact B1).
    assert (Q2 : forall v : word, getr (regupd r1 10 v) 2 = at_ sp (-128)) by (intros v; rewrite getr_other by (intros E; discriminate E); exact B2).
    assert (Q8 : forall v : word, getr (regupd r1 10 v) 8 = size) by (intros v; rewrite getr_other by (intros E; discriminate E); exact B8).
    assert (Q9 : forall v : word, getr (regupd r1 10 v) 9 = Z_to_bv 64 1) by (intros v; rewrite getr_other by (intros E; discriminate E); exact B9).
    assert (Q10 : forall v : word, getr (regupd r1 10 v) 10 = v) by (intros v; rewrite getr_same by (intros E; discriminate E); reflexivity).
    assert (AGC : forall (v : word) (r2 : bvmap 5 word), regs_agree (fun i : reg => In i mfi_clob2) (regupd r1 10 v) r2 ->
                    regs_agree (fun i : reg => In i mfi_clob2) regs r2).
    { intros v r2 AG2 x Hx. rewrite (AG2 x Hx).
      assert (NE10 : x <> 10%bv) by (intros ->; apply Hx; (lazymatch goal with |- ?G => let G' := eval unfold mfi_clob2, mfi_clob in G in change_no_check G' end); (lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); solve [repeat (first [left; reflexivity | right])]).
      rewrite getr_other by (intros E; apply NE10; exact E). apply AG1. exact Hx. }
    assert (HIDW : forall (MM : word -> option byte) bs (a : word), Hd a = true -> Z.of_nat (length bs) = 4 -> wbytes MM (at_ sp (-84)) bs a = MM a).
    { intros MM bs a Ha Hl.
      destruct (Z_lt_le_dec (U a) (U sp - 84)) as [C|C]; [apply wbytes_below; rewrite ?Hl, ?at_u by lia; lia|].
      destruct (Z_lt_le_dec (U a) (U sp - 80)) as [C'|C']; [exfalso; rewrite (HDscr a) in Ha by lia; discriminate Ha|].
      apply wbytes_above. rewrite Hl, at_u by lia. lia. }
    apply (NODE mdlm r1 SBMm MIm HALTm B10 B11 B12 B13 B14 B15 Qok Qf).
    - (* [comment removed for export] *)
      set (MZ := zfill addr size M1).
      assert (EZ : forall x : word, U sp - 400 <= U x < U sp -> MZ x = M1 x) by (intros x Hx; (lazymatch goal with |- ?G => let G' := eval unfold MZ in G in change_no_check G' end); apply zfill_out; lia).
      destruct (POSTF MZ EZ) as [SOKZ SLZ].
      assert (CELLZ : forall (c : Z) (k : nat) v, 0 <= c -> c + Z.of_nat k <= AIMGHI -> hid_off Hd c (Z.of_nat k) ->
                 rdn BSEGS mem (Z_to_bv 64 c) k = Some v -> rdn BSEGS (mrestrict Hd MZ) (Z_to_bv 64 c) k = Some v).
      { intros c k v Hc0 Hc1 Hh Hr. rewrite rdn_mrestrict; [| first [ solve [ wd_unorm1; wd_zofnat; lia ] | rewrite u_Z2bv by lia; lia ] | rewrite u_Z2bv by lia; exact Hh].
        rewrite <- Hr. apply rdn_ext; [first [ solve [ wd_unorm1; wd_zofnat; lia ] | rewrite u_Z2bv by lia; lia ]|]. intros x Hx. rewrite u_Z2bv in Hx by lia.
        (lazymatch goal with |- ?G => let G' := eval unfold MZ in G in change_no_check G' end). rewrite zfill_out by lia. (lazymatch goal with |- ?G => let G' := eval unfold M1 in G in change_no_check G' end). apply (mfi_m1_outside mem sp ra s0v s1v s2v s3v s4v s5v addr size name PGP Hsp). left. lia. }
      destruct (mfi_ok (mrestrict Hd MZ) rom sp ra s0v s1v s2v s3v s4v addr size CF (regupd r1 10 addr)
                  (Q1 addr) (Q2 addr) (Q8 addr) Hsp Hret (conj CF1 CF2) SOKZ
                  (SLZ (-8) ra ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); repeat (first [left; reflexivity | right]))) (SLZ (-16) s0v ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); repeat (first [left; reflexivity | right]))) (SLZ (-24) s1v ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); repeat (first [left; reflexivity | right])))
                  (SLZ (-32) s2v ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); repeat (first [left; reflexivity | right]))) (SLZ (-40) (Z_to_bv 64 0x8b124) ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); repeat (first [left; reflexivity | right]))) (SLZ (-48) size ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); repeat (first [left; reflexivity | right])))
                  (SLZ (-56) addr ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); repeat (first [left; reflexivity | right]))) (SLZ (-64) s2v ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); repeat (first [left; reflexivity | right]))) (SLZ (-72) s3v ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); repeat (first [left; reflexivity | right]))) (SLZ (-80) s4v ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); repeat (first [left; reflexivity | right])))
                  (Q10 addr) ltac:(lia) ltac:(lia)
                  (CELLZ 0x105f08 8%nat _ ltac:(lia) ltac:((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia) HDgcf Rgcf) (CELLZ (CF + 144) 8%nat _ ltac:(lia) ltac:((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia) HDlim Rlim))
        as (r2 & RUN2 & C10 & C2 & C1 & C8 & C9 & C18 & C19 & C20 & AG2).
      rewrite wbytes_mrestrict in RUN2; [| rewrite length_N_to_le_bytes, at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia
                                          | rewrite length_N_to_le_bytes, at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); intros x Hx; apply HDscr; lia].
      apply (katwD_msteps_acct BSEGS Hd HOFFSEG WX A (mkst (regupd r1 10 addr) (0x811b0 : word) MZ rom)
               (mkst r2 ra (mrestrict Hd (wbytes MZ (at_ sp (-84)) SCR)) rom) (MOK mdlm) Qok Qf HOK2 AWF HOK3 HOK1).
      { rewrite mk_restrict_mkst. exact RUN2. }
      intros mdl4 MI4 SBM4 HC4. rewrite mk_unrestrict_mkst.
      replace (RiscvSemantics.ms_mem (mkst (regupd r1 10 addr) (0x811b0 : word) MZ rom)) with MZ by reflexivity.
      rewrite (mk_munrestrict_same Hd MZ (wbytes MZ (at_ sp (-84)) SCR)).
      2:{ intros a Ha. apply HIDW; [exact Ha | (lazymatch goal with |- ?G => let G' := eval unfold SCR in G in change_no_check G' end); rewrite length_N_to_le_bytes; reflexivity]. }
      apply (CONTOK r2 mdlm mdl4 SBMm MIm SBM4 MI4).
      (lazymatch goal with |- ?G => let G' := eval unfold mfi_ret in G in change_no_check G' end). repeat (split; [assumption|]). exact (AGC addr r2 AG2).
  Qed.

End MAPK.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section NODE3.


  Lemma node3_of_fixedin3_dm :
    forall (r1 : bvmap 5 word) (M1 rom : word -> option byte) (mdlm : Model) (addr size : word) (Q' : config -> Prop),
    m_halted mdlm = None ->
    getr r1 10 = addr -> getr r1 11 = size -> getr r1 12 = Z_to_bv 64 3 -> getr r1 13 = Z_to_bv 64 50 ->
    getr r1 14 = Z_to_bv 64 (2 ^ 64 - 1) -> getr r1 15 = Z_to_bv 64 0 ->
    U addr mod 4096 = 0 -> 0 < U addr -> 0 < U size -> U size mod 4096 = 0 ->
    U addr + U size <= alloc_top (m_vmmaps mdlm) -> alloc_top (m_vmmaps mdlm) < two_pow_64 ->
    region_free (vm_reserved (m_vmmaps mdlm)) addr size = true ->
    map_contains (vm_maps (m_vmmaps mdlm)) addr size = true ->
    mmap_fixed_rw_budget_ok (Z_to_bv 64 50) mdlm addr size = true ->
    katD BSEGS (mkCfg (mkst (regupd r1 10 addr) (0x811b0 : word) (zfill addr size M1) rom)
                      (fixedin_ok_model 3 (Z_to_bv 64 50) addr size mdlm)) Q' ->
    doomed BSEGS (mkCfg (mkst (regupd r1 10 (Z_to_bv 64 (2 ^ 64 - 12))) (0x811b0 : word) M1 rom) mdlm) ->
    doomed BSEGS (mkCfg (mkst (regupd r1 10 (Z_to_bv 64 (2 ^ 64 - 12))) (0x811b0 : word) (unfill addr size M1) rom)
                      (fixedin_destroyed_model addr size mdlm)) ->
    katD BSEGS (mkCfg (epend r1 (0x811ac : word) M1 rom (Z_to_bv 64 222)) mdlm) Q'.
  Proof using.
    intros r1 M1 rom mdlm addr size Q' HALT B10 B11 B12 B13 B14 B15 Hal Hpos Hsz Hszal Htop Htop64 Hrf Hmc Hbud KOK KKP KDS.
    pose proof (u64_range size) as Hszr.
    set (ms := epend r1 (0x811ac : word) M1 rom (Z_to_bv 64 222)).
    assert (PRU : page_round_up_Z (U size) = U size) by (apply page_round_up_Z_aligned; [lia | (lazymatch goal with |- ?G => let G' := eval unfold page_size in G in change_no_check G' end); exact Hszal]).
    assert (EN : Z_to_bv 64 (page_round_up_Z (U size)) = size) by (rewrite PRU; apply Z_to_bv_bv_unsigned).
    assert (E0 : ms_gpr ms 0 = addr) by ((lazymatch goal with |- ?G => let G' := eval unfold ms in G in change_no_check G' end); rewrite AsKSys6.MhKSys.ms_gpr_epend0; exact B10).
    assert (E1 : ms_gpr ms 1 = Z_to_bv 64 (U size)) by ((lazymatch goal with |- ?G => let G' := eval unfold ms in G in change_no_check G' end); rewrite AsKSys6.MhKSys.ms_gpr_epend1, Z_to_bv_bv_unsigned; exact B11).
    assert (E2 : ms_gpr ms 2 = Z_to_bv 64 3) by ((lazymatch goal with |- ?G => let G' := eval unfold ms in G in change_no_check G' end); rewrite AsKSys6.MhKSys.ms_gpr_epend2; exact B12).
    assert (E3 : ms_gpr ms 3 = Z_to_bv 64 50) by ((lazymatch goal with |- ?G => let G' := eval unfold ms in G in change_no_check G' end); rewrite AsKSys6.MhKSys.ms_gpr_epend3; exact B13).
    assert (E4 : ms_gpr ms 4 = Z_to_bv 64 (-1)) by ((lazymatch goal with |- ?G => let G' := eval unfold ms in G in change_no_check G' end); rewrite AsKSys6.MhKSys.ms_gpr_epend4, B14; apply bv_eq; reflexivity).
    assert (E5 : ms_gpr ms 5 = Z_to_bv 64 0) by ((lazymatch goal with |- ?G => let G' := eval unfold ms in G in change_no_check G' end); rewrite AsKSys6.MhKSys.ms_gpr_epend5; exact B15).
    apply (katD_mmap_fixedin3_dm BSEGS ms mdlm (Z_to_bv 64 222) 3 (Z_to_bv 64 50) addr (U size) HALT eq_refl
             ltac:(rewrite u_Z2bv by lia; reflexivity) ltac:(right; reflexivity) ltac:(vm_compute; reflexivity)
             E0 ltac:((lazymatch goal with |- ?G => let G' := eval unfold page_size in G in change_no_check G' end); exact Hal) Hpos E1 Hsz E2 E3 E4 E5 ltac:(rewrite PRU; exact Htop) Htop64
             ltac:(rewrite EN; exact Hrf) ltac:(rewrite EN; exact Hmc) ltac:(intros _; rewrite EN; exact Hbud) Q').
    - (* [comment removed for export] *)
      (lazymatch goal with |- ?G => let G' := eval unfold fxin_nx, fxin_effs, fxin_ms' in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval unfold ms in G in change_no_check G' end). rewrite AsKSys6.MhKSys.adv_retU_epend.
      replace (errno_ret ENOMEM) with (Z_to_bv 64 (2 ^ 64 - 12) : word) by (apply bv_eq; vm_compute; reflexivity).
      replace (v_addi (0x811ac%bv : word) 4) with (0x811b0%bv : word) by (apply bv_eq; vm_compute; reflexivity).
      exact KKP.
    - (* [comment removed for export] *)
      (lazymatch goal with |- ?G => let G' := eval unfold fxin_nx, fxin_effs, fxin_ms' in G in change_no_check G' end). rewrite EN. (lazymatch goal with |- ?G => let G' := eval unfold fixedin_ok_eff in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [Z.eqb] in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval unfold ms in G in change_no_check G' end).
      rewrite (AsKSys6.MhKSys.adv_zerosr_epend r1 (0x811ac%bv : word) M1 rom (Z_to_bv 64 222) addr addr size).
      replace (v_addi (0x811ac%bv : word) 4) with (0x811b0%bv : word) by (apply bv_eq; vm_compute; reflexivity).
      exact KOK.
    - (* [comment removed for export] *)
      (lazymatch goal with |- ?G => let G' := eval unfold fxin_nx, fxin_effs, fxin_ms' in G in change_no_check G' end). rewrite EN. (lazymatch goal with |- ?G => let G' := eval unfold ms in G in change_no_check G' end). rewrite AsKSys6.MhKSys.adv_unmaps1_epend.
      replace (errno_ret ENOMEM) with (Z_to_bv 64 (2 ^ 64 - 12) : word) by (apply bv_eq; vm_compute; reflexivity).
      replace (v_addi (0x811ac%bv : word) 4) with (0x811b0%bv : word) by (apply bv_eq; vm_compute; reflexivity).
      exact KDS.
  Qed.




  Lemma node1_of_fixedin3_s :
    forall (r1 : bvmap 5 word) (M1 rom : word -> option byte) (mdlm : Model) (addr size : word) (Qok' Qf' : config -> Prop),
    m_halted mdlm = None ->
    getr r1 10 = addr -> getr r1 11 = size -> getr r1 12 = Z_to_bv 64 3 -> getr r1 13 = Z_to_bv 64 50 ->
    getr r1 14 = Z_to_bv 64 (2 ^ 64 - 1) -> getr r1 15 = Z_to_bv 64 0 ->
    U addr mod 4096 = 0 -> 0 < U addr -> 0 < U size -> U size mod 4096 = 0 ->
    U addr + U size <= alloc_top (m_vmmaps mdlm) -> alloc_top (m_vmmaps mdlm) < two_pow_64 ->
    region_free (vm_reserved (m_vmmaps mdlm)) addr size = true ->
    map_contains (vm_maps (m_vmmaps mdlm)) addr size = true ->
    mmap_fixed_rw_budget_ok (Z_to_bv 64 50) mdlm addr size = true ->
    katwD BSEGS (mkCfg (mkst (regupd r1 10 addr) (0x811b0 : word) (zfill addr size M1) rom)
                      (fixedin_ok_model 3 (Z_to_bv 64 50) addr size mdlm)) Qok' Qf' ->
    katsD BSEGS (mkCfg (epend r1 (0x811ac : word) M1 rom (Z_to_bv 64 222)) mdlm) Qok' Qf'.
  Proof using.
    intros r1 M1 rom mdlm addr size Qok' Qf' HALT B10 B11 B12 B13 B14 B15 Hal Hpos Hsz Hszal Htop Htop64 Hrf Hmc Hbud KOK.
    pose proof (u64_range size) as Hszr.
    set (ms := epend r1 (0x811ac : word) M1 rom (Z_to_bv 64 222)).
    assert (PRU : page_round_up_Z (U size) = U size) by (apply page_round_up_Z_aligned; [lia | (lazymatch goal with |- ?G => let G' := eval unfold page_size in G in change_no_check G' end); exact Hszal]).
    assert (EN : Z_to_bv 64 (page_round_up_Z (U size)) = size) by (rewrite PRU; apply Z_to_bv_bv_unsigned).
    assert (E0 : ms_gpr ms 0 = addr) by ((lazymatch goal with |- ?G => let G' := eval unfold ms in G in change_no_check G' end); rewrite AsKSys6.MhKSys.ms_gpr_epend0; exact B10).
    assert (E1 : ms_gpr ms 1 = Z_to_bv 64 (U size)) by ((lazymatch goal with |- ?G => let G' := eval unfold ms in G in change_no_check G' end); rewrite AsKSys6.MhKSys.ms_gpr_epend1, Z_to_bv_bv_unsigned; exact B11).
    assert (E2 : ms_gpr ms 2 = Z_to_bv 64 3) by ((lazymatch goal with |- ?G => let G' := eval unfold ms in G in change_no_check G' end); rewrite AsKSys6.MhKSys.ms_gpr_epend2; exact B12).
    assert (E3 : ms_gpr ms 3 = Z_to_bv 64 50) by ((lazymatch goal with |- ?G => let G' := eval unfold ms in G in change_no_check G' end); rewrite AsKSys6.MhKSys.ms_gpr_epend3; exact B13).
    assert (E4 : ms_gpr ms 4 = Z_to_bv 64 (-1)) by ((lazymatch goal with |- ?G => let G' := eval unfold ms in G in change_no_check G' end); rewrite AsKSys6.MhKSys.ms_gpr_epend4, B14; apply bv_eq; reflexivity).
    assert (E5 : ms_gpr ms 5 = Z_to_bv 64 0) by ((lazymatch goal with |- ?G => let G' := eval unfold ms in G in change_no_check G' end); rewrite AsKSys6.MhKSys.ms_gpr_epend5; exact B15).
    apply katsD_of_katwD.
    apply (katwD_node BSEGS _ _ tt _ Qok' Qf'
             (node_mmap_fixedin1 BSEGS ms mdlm (Z_to_bv 64 222) 3 (Z_to_bv 64 50) addr (U size) HALT eq_refl
                ltac:(rewrite u_Z2bv by lia; reflexivity) ltac:(right; reflexivity) ltac:(vm_compute; reflexivity)
                E0 ltac:((lazymatch goal with |- ?G => let G' := eval unfold page_size in G in change_no_check G' end); exact Hal) Hpos E1 Hsz E2 E3 E4 E5 ltac:(rewrite PRU; exact Htop) Htop64
                ltac:(rewrite EN; exact Hrf) ltac:(rewrite EN; exact Hmc) ltac:(intros _; rewrite EN; exact Hbud))).
    intros [].
    (lazymatch goal with |- ?G => let G' := eval unfold fxin_nx, fxin_effs, fxin_ms' in G in change_no_check G' end). rewrite EN. (lazymatch goal with |- ?G => let G' := eval unfold fixedin_ok_eff in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [Z.eqb] in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval unfold ms in G in change_no_check G' end).
    rewrite (AsKSys6.MhKSys.adv_zerosr_epend r1 (0x811ac%bv : word) M1 rom (Z_to_bv 64 222) addr addr size).
    replace (v_addi (0x811ac%bv : word) 4) with (0x811b0%bv : word) by (apply bv_eq; vm_compute; reflexivity).
    exact KOK.
  Qed.
End NODE3.
End FPGen1.
End BoAllocM8k.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.WalkLetEv OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtFlush OSSVerify.Proofs.glaze.binary_reflection.lib.Bo_code_82b14_83760 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module BoAllocM9h.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.WalkLetEv.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtFlush OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8m OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8m.Bo_code_8ae68_8b254 OSSVerify.Proofs.glaze.binary_reflection.lib.Bo_code_82b14_83760 OSSVerify.Proofs.glaze.binary_reflection.lib.BoDrvIStrlen.Bo_code_80b0c_815a0 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM0.Bo_code_7d08c_7db0c.
Import OSSVerify.glaze.binary_reflection.images.AsanUbsan.
Import ListNotations.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac wd_setR ::= wd_setR_on.   (* [comment removed for export] *)
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation BSEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).
#[local] Abbreviation LE4 z := (word_to_le_bytes 4 (Z_to_bv 64 z)).
#[local] Abbreviation U := bv_unsigned.

(* [comment removed for export] *)
Ltac sltu0 :=
  match goal with |- context [v_sltu ?a ?b] =>
    replace (v_sltu a b) with (Z_to_bv 64 0)
      by (symmetry; rwH; (lazymatch goal with |- ?G => let G' := eval unfold v_sltu in G in change_no_check G' end); rewrite c_ltu_ltb; unorm; rewrite (proj2 (Z.ltb_ge _ _)) by lia; reflexivity) end.

Ltac av_and F D vv tac :=
  chain_step;
  [ reflexivity
  | eapply step_and_at with (v := vv); [ exact F | reflexivity | exact D | reflexivity | gres; rwH; imm_norm; tac ]
  | step_simpl ]; vn.

Section FPGen.
Context {fx : FPState}.

(* [comment removed for export] *)
Definition mfo_m0 (mem : word -> option byte) (sp ra s0v s1v s2v s3v s4v : word) : word -> option byte :=
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes mem
    (at_ sp (-8)) (LE8 ra))
    (at_ sp (-16)) (LE8 s0v))
    (at_ sp (-24)) (LE8 s1v))
    (at_ sp (-32)) (LE8 s2v))
    (at_ sp (-40)) (LE8 s3v))
    (at_ sp (-48)) (LE8 s4v).
Definition mfo_m1 (mem : word -> option byte) (sp ra s0v s1v s2v s3v s4v s5v addr size name : word) (PGP : Z) : word -> option byte :=
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (mfo_m0 mem sp ra s0v s1v s2v s3v s4v)
    (at_ sp (-96)) (LE4 50))
    (at_ sp (-104)) (LE8 (Z_to_bv 64 0x82f50)))
    (at_ sp (-112)) (LE8 size))
    (at_ sp (-120)) (LE8 (Z_to_bv 64 0)))
    (at_ sp (-128)) (LE8 addr))
    (at_ sp (-136)) (LE8 name))
    (at_ sp (-144)) (LE8 (Z_to_bv 64 PGP)))
    (at_ sp (-152)) (LE8 s5v).
#[local] Hint Unfold mfo_m0 mfo_m1 : asfr.

Section MFOPRE.
  Variables (mem rom : word -> option byte) (sp ra s0v s1v s2v s3v s4v s5v addr size name : word) (PGP CF : Z).
  Variable regs : bvmap 5 word.
  Hypothesis H1 : getr regs 1 = ra.
  Hypothesis H2 : getr regs 2 = sp.
  Hypothesis H11 : getr regs 11 = addr.
  Hypothesis H12 : getr regs 12 = size.
  Hypothesis H13 : getr regs 13 = name.
  Hypothesis H8 : getr regs 8 = s0v.   Hypothesis H9 : getr regs 9 = s1v.   Hypothesis H18 : getr regs 18 = s2v.
  Hypothesis H19 : getr regs 19 = s3v. Hypothesis H20 : getr regs 20 = s4v. Hypothesis H21 : getr regs 21 = s5v.
  Hypothesis Hsp : (2 ^ 24 <= U sp /\ U sp + 16 <= 2 ^ 47)%Z.
  Hypothesis Haddr : (U addr mod 4096 = 0)%Z.
  Hypothesis Hsize : (U size mod 4096 = 0 /\ U size + 4096 < 2 ^ 63)%Z.
  Hypothesis Hname : (U name = 0)%Z.
  Hypothesis HPGP : (AIMGLO <= PGP /\ PGP + 8 <= AIMGHI)%Z.
  Hypothesis HCF : (AIMGLO <= CF /\ CF + 264 <= AIMGHI)%Z.
  Hypothesis Hstk : store_ok BSEGS mem (at_ sp (-368)) 368 = true.
  Hypothesis Rgpg : rdn BSEGS mem (Z_to_bv 64 0x105ef8) 8 = Some (LE8 (Z_to_bv 64 PGP)).
  Hypothesis Rpg : rdn BSEGS mem (Z_to_bv 64 PGP) 8 = Some (LE8 (Z_to_bv 64 4096)).

  #[local] Abbreviation M1 := (mfo_m1 mem sp ra s0v s1v s2v s3v s4v s5v addr size name PGP).

  Lemma mfo_pre :
    exists r, msteps BSEGS (mkst regs (0x8b244 : word) mem rom) (mkst r (0x811ac : word) M1 rom)
      /\ getr r 1 = Z_to_bv 64 0x82f6c /\ getr r 2 = at_ sp (-96)
      /\ getr r 8 = size /\ getr r 9 = Z_to_bv 64 0 /\ getr r 18 = addr /\ getr r 19 = name /\ getr r 20 = Z_to_bv 64 PGP
      /\ getr r 10 = addr /\ getr r 11 = size /\ getr r 12 = Z_to_bv 64 3 /\ getr r 13 = Z_to_bv 64 50
      /\ getr r 14 = Z_to_bv 64 (2 ^ 64 - 1) /\ getr r 15 = Z_to_bv 64 0 /\ getr r 17 = Z_to_bv 64 222
      /\ regs_agree (fun i : reg => In i (1%bv :: 2%bv :: 8%bv :: 9%bv :: 18%bv :: 19%bv :: 20%bv :: mfi_clob)) regs r.
  Proof using Rpg Rgpg Hstk HPGP Hname Hsize Haddr Hsp H21 H20 H19 H18 H9 H8 H13 H12 H11 H2 H1.
    pose proof (u64_range sp) as Hspr. pose proof (u64_range addr) as Har. pose proof (u64_range size) as Hsr. pose proof (u64_range name) as Hnr.
    destruct Hsize as [Hsz1 Hsz2].
    wd_eexists. split.
    - an F_8b244 D_8b244.                              (* [comment removed for export] *)
      an F_8b248 D_8b248.                              (* [comment removed for export] *)
      an F_8b24c D_8b24c.                              (* [comment removed for export] *)
      an F_8b250 D_8b250.                              (* [comment removed for export] *)
      an F_82eb4 D_82eb4.                              (* [comment removed for export] *)
      an F_82eb8 D_82eb8.                              (* [comment removed for export] *)
      an F_82ebc D_82ebc.                              (* [comment removed for export] *)
      an F_82ec0 D_82ec0.                              (* [comment removed for export] *)
      fsd F_82ec4 D_82ec4 (at_ sp (-8)).               (* [comment removed for export] *)
      fsd F_82ec8 D_82ec8 (at_ sp (-16)).              (* [comment removed for export] *)
      fsd F_82ecc D_82ecc (at_ sp (-24)).              (* [comment removed for export] *)
      fsd F_82ed0 D_82ed0 (at_ sp (-32)).              (* [comment removed for export] *)
      fsd F_82ed4 D_82ed4 (at_ sp (-40)).              (* [comment removed for export] *)
      fsd F_82ed8 D_82ed8 (at_ sp (-48)).              (* [comment removed for export] *)
      an F_82edc D_82edc.                              (* [comment removed for export] *)
      an F_82ee0 D_82ee0.                              (* [comment removed for export] *)
      an F_82ee4 D_82ee4.                              (* [comment removed for export] *)
      an F_82ee8 D_82ee8.                              (* [comment removed for export] *)
      cld8 F_82eec D_82eec (Z_to_bv 64 PGP) Rgpg.      (* [comment removed for export] *)
      cld8 F_82ef0 D_82ef0 (Z_to_bv 64 4096) Rpg.      (* [comment removed for export] *)
      an F_82ef4 D_82ef4.                              (* [comment removed for export] *)
      ab_tk F_82ef8 D_82ef8 ltac:(condz).              (* [comment removed for export] *)
      an F_82f08 D_82f08.                              (* [comment removed for export] *)
      an F_82f0c D_82f0c.                              (* [comment removed for export] *)
      ab_ft F_82f10 D_82f10 ltac:(condz).              (* [comment removed for export] *)
      av F_82f14 D_82f14 (Z_to_bv 64 (U size + 4096)) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_add in G in change_no_check G' end); unorm; f_equal; lia).   (* [comment removed for export] *)
      av F_82f18 D_82f18 (Z_to_bv 64 (U size + 4095)) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_addi in G in change_no_check G' end); unorm; f_equal; lia).   (* [comment removed for export] *)
      av F_82f1c D_82f1c (Z_to_bv 64 (2 ^ 64 - 2 ^ 12)) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_sub in G in change_no_check G' end); unorm; apply bv_eq; vm_compute; reflexivity).   (* [comment removed for export] *)
      av_and F_82f20 D_82f20 size
        ltac:(rewrite v_and_m4k; unorm; replace (U size + 4095 - (U size + 4095) mod 4096)%Z with (U size) by (Z.div_mod_to_equations; lia); apply Z_to_bv_bv_unsigned).   (* [comment removed for export] *)
      ab_tk F_82f24 D_82f24 ltac:(condz).              (* [comment removed for export] *)
      av_and F_82f34 D_82f34 addr
        ltac:(rewrite v_and_m4k; replace (U addr - U addr mod 4096)%Z with (U addr) by lia; apply Z_to_bv_bv_unsigned).   (* [comment removed for export] *)
      an F_82f38 D_82f38.                              (* [comment removed for export] *)
      fsw F_82f3c D_82f3c (at_ sp (-96)).              (* [comment removed for export] *)
      an F_82f40 D_82f40.                              (* [comment removed for export] *)
      an F_82f44 D_82f44.                              (* [comment removed for export] *)
      an F_82f48 D_82f48.                              (* [comment removed for export] *)
      an F_82f4c D_82f4c.                              (* [comment removed for export] *)
      an F_83554 D_83554.                              (* [comment removed for export] *)
      fsd F_83558 D_83558 (at_ sp (-104)).             (* [comment removed for export] *)
      fsd F_8355c D_8355c (at_ sp (-112)).             (* [comment removed for export] *)
      fsd F_83560 D_83560 (at_ sp (-120)).             (* [comment removed for export] *)
      fsd F_83564 D_83564 (at_ sp (-128)).             (* [comment removed for export] *)
      fsd F_83568 D_83568 (at_ sp (-136)).             (* [comment removed for export] *)
      fsd F_8356c D_8356c (at_ sp (-144)).             (* [comment removed for export] *)
      fsd F_83570 D_83570 (at_ sp (-152)).             (* [comment removed for export] *)
      change (wbytes _ _ _) with M1.
      an F_83574 D_83574.                              (* [comment removed for export] *)
      an F_83578 D_83578.                              (* [comment removed for export] *)
      ab_tk F_8357c D_8357c ltac:(condz).              (* [comment removed for export] *)
      an F_836a4 D_836a4.                              (* [comment removed for export] *)
      fld F_836a8 D_836a8 (Z_to_bv 64 0x82f50).        (* [comment removed for export] *)
      fld F_836ac D_836ac size.                        (* [comment removed for export] *)
      fld F_836b0 D_836b0 (Z_to_bv 64 0).              (* [comment removed for export] *)
      fld F_836b4 D_836b4 addr.                        (* [comment removed for export] *)
      fld F_836b8 D_836b8 name.                        (* [comment removed for export] *)
      fld F_836bc D_836bc (Z_to_bv 64 PGP).            (* [comment removed for export] *)
      fld F_836c0 D_836c0 s5v.                         (* [comment removed for export] *)
      an F_836c4 D_836c4.                              (* [comment removed for export] *)
      rt F_836c8 D_836c8.                              (* [comment removed for export] *)
      chain_step; [reflexivity
        | eapply step_lw with (bs := LE4 50) (v := Z_to_bv 64 50);
          [exact F_82f50 | reflexivity | exact D_82f50
          | gres; rwH; imm_norm; rewrite ?at_addi; zlit_at; (lazymatch goal with |- ?G => let G' := eval unfold mfo_m1 in G in change_no_check G' end);
            repeat (rewrite wc_rdn_wbytes_out3; [ | rd8_side ]);
            apply rdn_wbytes_hit4; (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_ulia
          | reflexivity]
        | step_simpl]; rewrite (v_lw_small 50) by lia; vn.   (* [comment removed for export] *)
      an F_82f54 D_82f54.                              (* [comment removed for export] *)
      an F_82f58 D_82f58.                              (* [comment removed for export] *)
      an F_82f5c D_82f5c.                              (* [comment removed for export] *)
      an F_82f60 D_82f60.                              (* [comment removed for export] *)
      an F_82f64 D_82f64.                              (* [comment removed for export] *)
      an F_82f68 D_82f68.                              (* [comment removed for export] *)
      an F_811a8 D_811a8.                              (* [comment removed for export] *)
      wd_refl.
    - post. ra_solve.
  Qed.

  (* [comment removed for export] *)
  Lemma mfo_m1_outside : forall x : word, (U x < U sp - 368 \/ U sp <= U x)%Z -> M1 x = mem x.
  Proof using Hsp.
    intros x Hx. pose proof (u64_range sp) as Hspr. (lazymatch goal with |- ?G => let G' := eval unfold mfo_m1, mfo_m0 in G in change_no_check G' end).
    repeat (rewrite wbytes_outside; [ | rewrite length_N_to_le_bytes, at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite length_N_to_le_bytes, at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia]).
    reflexivity.
  Qed.
  Lemma mfo_m1_grows : mem_grows mem M1.
  Proof using. (lazymatch goal with |- ?G => let G' := eval unfold mfo_m1, mfo_m0 in G in change_no_check G' end). repeat (eapply mem_grows_trans; [|apply wbytes_grows]). apply mem_grows_refl. Qed.
  Lemma mfo_m1_slots : forall (k : Z) (v : word),
    In (k, v) [(-8, ra); (-16, s0v); (-24, s1v); (-32, s2v); (-40, s3v); (-48, s4v)]%Z -> rdn BSEGS M1 (at_ sp k) 8 = Some (LE8 v).
  Proof using Hsp.
    intros k v Hin. pose proof (u64_range sp) as Hspr. (lazymatch goal with |- ?G => let G' := eval unfold mfo_m1, mfo_m0 in G in change_no_check G' end). cbn [In] in Hin.
    repeat (destruct Hin as [E|Hin]; [injection E as <- <-; rd8_chain|]). destruct Hin.
  Qed.
End MFOPRE.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section MFOPOST.
  Variables (M2 rom : word -> option byte) (sp ra s0v s1v s2v s3v s4v addr size name : word) (PGP CF : Z).
  Variable regs : bvmap 5 word.
  Hypothesis H1 : getr regs 1 = Z_to_bv 64 0x82f6c.
  Hypothesis H2 : getr regs 2 = at_ sp (-96).
  Hypothesis H8 : getr regs 8 = size.
  Hypothesis H9 : getr regs 9 = Z_to_bv 64 0.
  Hypothesis Hsp : (2 ^ 24 <= U sp /\ U sp + 16 <= 2 ^ 47)%Z.
  Hypothesis Hret : ret_ok ra.
  Hypothesis HCF : (AIMGLO <= CF /\ CF + 264 <= AIMGHI)%Z.
  Hypothesis Hsok : store_ok BSEGS M2 (at_ sp (-52)) 4 = true.
  Hypothesis S_ra : rdn BSEGS M2 (at_ sp (-8)) 8 = Some (LE8 ra).
  Hypothesis S_s0 : rdn BSEGS M2 (at_ sp (-16)) 8 = Some (LE8 s0v).
  Hypothesis S_s1 : rdn BSEGS M2 (at_ sp (-24)) 8 = Some (LE8 s1v).
  Hypothesis S_s2 : rdn BSEGS M2 (at_ sp (-32)) 8 = Some (LE8 s2v).
  Hypothesis S_s3 : rdn BSEGS M2 (at_ sp (-40)) 8 = Some (LE8 s3v).
  Hypothesis S_s4 : rdn BSEGS M2 (at_ sp (-48)) 8 = Some (LE8 s4v).

  
  (* [comment removed for export] *)
  Section OK.
    Hypothesis H10 : getr regs 10 = addr.
    Hypothesis Haddr : (U addr < 2 ^ 63)%Z.
    Hypothesis Rgcf : rdn BSEGS M2 (Z_to_bv 64 0x105f08) 8 = Some (LE8 (Z_to_bv 64 CF)).
    Hypothesis Rlim : rdn BSEGS M2 (Z_to_bv 64 (CF + 144)) 8 = Some (LE8 (Z_to_bv 64 0)).
    Lemma mfo_ok :
      exists r, msteps BSEGS (mkst regs (0x811b0 : word) M2 rom)
                             (mkst r ra (wbytes M2 (at_ sp (-52)) (LE4 0xffffffffaaaaaaaa)) rom)
        /\ getr r 10 = addr /\ getr r 2 = sp /\ getr r 1 = ra
        /\ getr r 8 = s0v /\ getr r 9 = s1v /\ getr r 18 = s2v /\ getr r 19 = s3v /\ getr r 20 = s4v
        /\ regs_agree (fun i : reg => In i mfi_clob2) regs r.
    Proof using Rlim Rgcf Haddr H10 S_s4 S_s3 S_s2 S_s1 S_s0 S_ra Hsok HCF Hret Hsp H8 H2 H1 CF size.
      pose proof (u64_range sp) as Hspr. pose proof (u64_range addr) as Har.
      wd_eexists. split.
      - rt F_811b0 D_811b0.                            (* [comment removed for export] *)
        an F_82f6c D_82f6c.                            (* [comment removed for export] *)
        an F_82f70 D_82f70.                            (* [comment removed for export] *)
        an F_82f74 D_82f74.                            (* [comment removed for export] *)
        an F_81188 D_81188.                            (* [comment removed for export] *)
        an F_8118c D_8118c.                            (* [comment removed for export] *)
        ab_tk F_81190 D_81190 ltac:(condz).            (* [comment removed for export] *)
        an F_811a0 D_811a0. sltu0.                     (* [comment removed for export] *)
        rt F_811a4 D_811a4.                            (* [comment removed for export] *)
        an F_82f78 D_82f78.                            (* [comment removed for export] *)
        an F_82f7c D_82f7c.                            (* [comment removed for export] *)
        fsw F_82f80 D_82f80 (at_ sp (-52)).            (* [comment removed for export] *)
        an F_82f84 D_82f84.                            (* [comment removed for export] *)
        an F_82f88 D_82f88.                            (* [comment removed for export] *)
        an F_82f8c D_82f8c.                            (* [comment removed for export] *)
        an F_81188 D_81188.                            (* [comment removed for export] *)
        an F_8118c D_8118c.                            (* [comment removed for export] *)
        ab_tk F_81190 D_81190 ltac:(condz).            (* [comment removed for export] *)
        an F_811a0 D_811a0. sltu0.                     (* [comment removed for export] *)
        rt F_811a4 D_811a4.                            (* [comment removed for export] *)
        ab_ft F_82f90 D_82f90 ltac:(condz).            (* [comment removed for export] *)
        an F_82f94 D_82f94.                            (* [comment removed for export] *)
        an F_82f98 D_82f98.                            (* [comment removed for export] *)
        an F_7d08c D_7d08c.                            (* [comment removed for export] *)
        cld8 F_7d090 D_7d090 (Z_to_bv 64 CF) Rgcf.     (* [comment removed for export] *)
        cld8 F_7d094 D_7d094 (Z_to_bv 64 0) Rlim.      (* [comment removed for export] *)
        ab_tk F_7d098 D_7d098 ltac:(condz).            (* [comment removed for export] *)
        rt F_7d0b4 D_7d0b4.                            (* [comment removed for export] *)
        an F_82f9c D_82f9c.                            (* [comment removed for export] *)
        cld8 F_82fa0 D_82fa0 ra S_ra.                  (* [comment removed for export] *)
        cld8 F_82fa4 D_82fa4 s0v S_s0.                 (* [comment removed for export] *)
        cld8 F_82fa8 D_82fa8 s1v S_s1.                 (* [comment removed for export] *)
        cld8 F_82fac D_82fac s2v S_s2.                 (* [comment removed for export] *)
        cld8 F_82fb0 D_82fb0 s3v S_s3.                 (* [comment removed for export] *)
        cld8 F_82fb4 D_82fb4 s4v S_s4.                 (* [comment removed for export] *)
        an F_82fb8 D_82fb8.                            (* [comment removed for export] *)
        aret F_82fbc D_82fbc ra.                       (* [comment removed for export] *)
        wd_refl.
      - post. (lazymatch goal with |- ?G => let G' := eval unfold mfi_clob2, mfi_clob in G in change_no_check G' end). ra_solve.
    Qed.
  End OK.

  (* [comment removed for export] *)
  Section FAIL.
    Hypothesis H10 : getr regs 10 = Z_to_bv 64 (2 ^ 64 - 12).
    Lemma mfo_fail :
      exists r, msteps BSEGS (mkst regs (0x811b0 : word) M2 rom)
                             (mkst r (0x82fe8 : word) (wbytes (wbytes M2 (at_ sp (-52)) (LE4 0xffffffffaaaaaaaa)) (at_ sp (-52)) (LE4 12)) rom)
        /\ getr r 2 = at_ sp (-96) /\ getr r 8 = size /\ getr r 9 = Z_to_bv 64 0 /\ getr r 19 = Z_to_bv 64 (2 ^ 64 - 12)
        /\ getr r 18 = getr regs 18 /\ getr r 20 = getr regs 20
        /\ regs_agree (fun i : reg => In i (19%bv :: mfi_clob2)) regs r.
    Proof using H10 Hsok Hsp H9 H8 H2 H1.
      pose proof (u64_range sp) as Hspr.
      wd_eexists. split.
      - rt F_811b0 D_811b0.                            (* [comment removed for export] *)
        an F_82f6c D_82f6c.                            (* [comment removed for export] *)
        an F_82f70 D_82f70.                            (* [comment removed for export] *)
        an F_82f74 D_82f74.                            (* [comment removed for export] *)
        an F_81188 D_81188.                            (* [comment removed for export] *)
        an F_8118c D_8118c.                            (* [comment removed for export] *)
        ab_ft F_81190 D_81190 ltac:(condz).            (* [comment removed for export] *)
        ab_tk F_81194 D_81194 ltac:(condz).            (* [comment removed for export] *)
        an F_811a0 D_811a0.                            (* [comment removed for export] *)
        rt F_811a4 D_811a4.                            (* [comment removed for export] *)
        an F_82f78 D_82f78.                            (* [comment removed for export] *)
        an F_82f7c D_82f7c.                            (* [comment removed for export] *)
        fsw F_82f80 D_82f80 (at_ sp (-52)).            (* [comment removed for export] *)
        an F_82f84 D_82f84.                            (* [comment removed for export] *)
        an F_82f88 D_82f88.                            (* [comment removed for export] *)
        an F_82f8c D_82f8c.                            (* [comment removed for export] *)
        an F_81188 D_81188.                            (* [comment removed for export] *)
        an F_8118c D_8118c.                            (* [comment removed for export] *)
        ab_ft F_81190 D_81190 ltac:(condz).            (* [comment removed for export] *)
        ab_ft F_81194 D_81194 ltac:(condz).            (* [comment removed for export] *)
        an F_81198 D_81198.                            (* [comment removed for export] *)
        fsw F_8119c D_8119c (at_ sp (-52)).            (* [comment removed for export] *)
        an F_811a0 D_811a0.                            (* [comment removed for export] *)
        rt F_811a4 D_811a4.                            (* [comment removed for export] *)
        ab_tk F_82f90 D_82f90 ltac:(condz).            (* [comment removed for export] *)
        ab_tk F_82fd0 D_82fd0 ltac:(condz).            (* [comment removed for export] *)
        wd_refl.
      - post. (lazymatch goal with |- ?G => let G' := eval unfold mfi_clob2, mfi_clob in G in change_no_check G' end). ra_solve.
    Qed.
  End FAIL.
End MFOPOST.
End FPGen.
End BoAllocM9h.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Bo_code_81fbc_82b14.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module BoAllocM9m.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.WalkLetEv.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtFlush OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8m OSSVerify.Proofs.glaze.binary_reflection.lib.Bo_code_81fbc_82b14 OSSVerify.Proofs.glaze.binary_reflection.lib.Bo_code_82b14_83760 OSSVerify.Proofs.glaze.binary_reflection.lib.BoDrvIStrlen.Bo_code_80b0c_815a0 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM0.Bo_code_7d08c_7db0c.
Import OSSVerify.glaze.binary_reflection.images.AsanUbsan.
Import ListNotations.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac wd_setR ::= wd_setR_on.   (* [comment removed for export] *)
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation BSEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).
#[local] Abbreviation LE4 z := (word_to_le_bytes 4 (Z_to_bv 64 z)).
#[local] Abbreviation U := bv_unsigned.

Section FPGen.
Context {fx : FPState}.

Definition mod_clob : list reg := [1; 2; 8; 9; 18; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 28; 29; 30; 31].

Definition mod_m1 (mem : word -> option byte) (sp ra s0v s1v s2v s3v s4v s5v size name : word) (PGP : Z) : word -> option byte :=
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes mem
    (at_ sp (-8)) (LE8 ra))
    (at_ sp (-16)) (LE8 s0v))
    (at_ sp (-24)) (LE8 s1v))
    (at_ sp (-32)) (LE8 s2v))
    (at_ sp (-36)) (LE4 34))
    (at_ sp (-56)) (LE8 (Z_to_bv 64 0x82ae0)))
    (at_ sp (-64)) (LE8 name))
    (at_ sp (-72)) (LE8 size))
    (at_ sp (-80)) (LE8 (Z_to_bv 64 PGP)))
    (at_ sp (-88)) (LE8 s3v))
    (at_ sp (-96)) (LE8 s4v))
    (at_ sp (-104)) (LE8 s5v).
#[local] Hint Unfold mod_m1 : asfr.

Section MODPRE.
  Variables (mem rom : word -> option byte) (sp ra s0v s1v s2v s3v s4v s5v size name : word) (PGP CF : Z).
  Variable regs : bvmap 5 word.
  Hypothesis H1 : getr regs 1 = ra.
  Hypothesis H2 : getr regs 2 = sp.
  Hypothesis H10 : getr regs 10 = size.
  Hypothesis H11 : getr regs 11 = name.
  Hypothesis H8 : getr regs 8 = s0v.   Hypothesis H9 : getr regs 9 = s1v.   Hypothesis H18 : getr regs 18 = s2v.
  Hypothesis H19 : getr regs 19 = s3v. Hypothesis H20 : getr regs 20 = s4v. Hypothesis H21 : getr regs 21 = s5v.
  Hypothesis Hsp : (2 ^ 24 <= U sp /\ U sp + 16 <= 2 ^ 47)%Z.
  Hypothesis Hsize : (U size mod 4096 = 0 /\ U size + 4096 < 2 ^ 63)%Z.
  Hypothesis Hname : (U name <> 0)%Z.
  Hypothesis HPGP : (AIMGLO <= PGP /\ PGP + 8 <= AIMGHI)%Z.
  Hypothesis HCF : (AIMGLO <= CF /\ CF + 264 <= AIMGHI)%Z.
  Hypothesis Hstk : store_ok BSEGS mem (at_ sp (-320)) 320 = true.
  Hypothesis Rgpg : rdn BSEGS mem (Z_to_bv 64 0x105ef8) 8 = Some (LE8 (Z_to_bv 64 PGP)).
  Hypothesis Rpg : rdn BSEGS mem (Z_to_bv 64 PGP) 8 = Some (LE8 (Z_to_bv 64 4096)).
  Hypothesis Rgcf : rdn BSEGS mem (Z_to_bv 64 0x105f08) 8 = Some (LE8 (Z_to_bv 64 CF)).
  Hypothesis Rdpm : rdn BSEGS mem (Z_to_bv 64 (CF + 260)) 1 = Some [Z_to_bv 8 0].

  #[local] Abbreviation M1 := (mod_m1 mem sp ra s0v s1v s2v s3v s4v s5v size name PGP).

  Lemma mod_pre :
    exists r, msteps BSEGS (mkst regs (0x82a74 : word) mem rom) (mkst r (0x811ac : word) M1 rom)
      /\ getr r 1 = Z_to_bv 64 0x82afc /\ getr r 2 = at_ sp (-48)
      /\ getr r 8 = name /\ getr r 9 = size /\ getr r 18 = Z_to_bv 64 PGP
      /\ getr r 10 = Z_to_bv 64 0 /\ getr r 11 = size /\ getr r 12 = Z_to_bv 64 3 /\ getr r 13 = Z_to_bv 64 34
      /\ getr r 14 = Z_to_bv 64 (2 ^ 64 - 1) /\ getr r 15 = Z_to_bv 64 0 /\ getr r 17 = Z_to_bv 64 222
      /\ regs_agree (fun i : reg => In i mod_clob) regs r.
  Proof using Rdpm Rgcf Rpg Rgpg Hstk HCF HPGP Hname Hsize Hsp H21 H20 H19 H18 H9 H8 H11 H10 H2 H1 CF.
    pose proof (u64_range sp) as Hspr. pose proof (u64_range size) as Hsr. pose proof (u64_range name) as Hnr.
    destruct Hsize as [Hsz1 Hsz2].
    wd_eexists. split.
    - an F_82a74 D_82a74.                              (* [comment removed for export] *)
      fsd F_82a78 D_82a78 (at_ sp (-8)).               (* [comment removed for export] *)
      fsd F_82a7c D_82a7c (at_ sp (-16)).              (* [comment removed for export] *)
      fsd F_82a80 D_82a80 (at_ sp (-24)).              (* [comment removed for export] *)
      fsd F_82a84 D_82a84 (at_ sp (-32)).              (* [comment removed for export] *)
      an F_82a88 D_82a88.                              (* [comment removed for export] *)
      an F_82a8c D_82a8c.                              (* [comment removed for export] *)
      cld8 F_82a90 D_82a90 (Z_to_bv 64 PGP) Rgpg.      (* [comment removed for export] *)
      cld8 F_82a94 D_82a94 (Z_to_bv 64 4096) Rpg.      (* [comment removed for export] *)
      an F_82a98 D_82a98.                              (* [comment removed for export] *)
      ab_tk F_82a9c D_82a9c ltac:(condz).              (* [comment removed for export] *)
      an F_82aac D_82aac.                              (* [comment removed for export] *)
      an F_82ab0 D_82ab0.                              (* [comment removed for export] *)
      ab_ft F_82ab4 D_82ab4 ltac:(condz).              (* [comment removed for export] *)
      av F_82ab8 D_82ab8 (Z_to_bv 64 (U size + 4096)) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_add in G in change_no_check G' end); unorm; f_equal; lia).   (* [comment removed for export] *)
      av F_82abc D_82abc (Z_to_bv 64 (2 ^ 64 - 2 ^ 12)) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_sub in G in change_no_check G' end); unorm; apply bv_eq; vm_compute; reflexivity).   (* [comment removed for export] *)
      av F_82ac0 D_82ac0 (Z_to_bv 64 (U size + 4095)) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_addi in G in change_no_check G' end); unorm; f_equal; lia).   (* [comment removed for export] *)
      av_and F_82ac4 D_82ac4 size
        ltac:(rewrite v_and_m4k; unorm; replace (U size + 4095 - (U size + 4095) mod 4096)%Z with (U size) by (Z.div_mod_to_equations; lia); apply Z_to_bv_bv_unsigned).   (* [comment removed for export] *)
      an F_82ac8 D_82ac8.                              (* [comment removed for export] *)
      fsw F_82acc D_82acc (at_ sp (-36)).              (* [comment removed for export] *)
      an F_82ad0 D_82ad0.                              (* [comment removed for export] *)
      an F_82ad4 D_82ad4.                              (* [comment removed for export] *)
      an F_82ad8 D_82ad8.                              (* [comment removed for export] *)
      an F_82adc D_82adc.                              (* [comment removed for export] *)
      an F_83554 D_83554.                              (* [comment removed for export] *)
      fsd F_83558 D_83558 (at_ sp (-56)).              (* [comment removed for export] *)
      fsd F_8355c D_8355c (at_ sp (-64)).              (* [comment removed for export] *)
      fsd F_83560 D_83560 (at_ sp (-72)).              (* [comment removed for export] *)
      fsd F_83564 D_83564 (at_ sp (-80)).              (* [comment removed for export] *)
      fsd F_83568 D_83568 (at_ sp (-88)).              (* [comment removed for export] *)
      fsd F_8356c D_8356c (at_ sp (-96)).              (* [comment removed for export] *)
      fsd F_83570 D_83570 (at_ sp (-104)).             (* [comment removed for export] *)
      change (wbytes _ _ _) with M1.
      an F_83574 D_83574.                              (* [comment removed for export] *)
      an F_83578 D_83578.                              (* [comment removed for export] *)
      ab_ft F_8357c D_8357c ltac:(condz).              (* [comment removed for export] *)
      an F_83580 D_83580.                              (* [comment removed for export] *)
      an F_83584 D_83584.                              (* [comment removed for export] *)
      cld8 F_83588 D_83588 (Z_to_bv 64 CF) Rgcf.       (* [comment removed for export] *)
      clbu F_8358c D_8358c (Z_to_bv 8 0) Rdpm.         (* [comment removed for export] *)
      an F_83590 D_83590.                              (* [comment removed for export] *)
      ab_tk F_83594 D_83594 ltac:(condz).              (* [comment removed for export] *)
      an F_836a4 D_836a4.                              (* [comment removed for export] *)
      fld F_836a8 D_836a8 (Z_to_bv 64 0x82ae0).        (* [comment removed for export] *)
      fld F_836ac D_836ac name.                        (* [comment removed for export] *)
      fld F_836b0 D_836b0 size.                        (* [comment removed for export] *)
      fld F_836b4 D_836b4 (Z_to_bv 64 PGP).            (* [comment removed for export] *)
      fld F_836b8 D_836b8 s3v.                         (* [comment removed for export] *)
      fld F_836bc D_836bc s4v.                         (* [comment removed for export] *)
      fld F_836c0 D_836c0 s5v.                         (* [comment removed for export] *)
      an F_836c4 D_836c4.                              (* [comment removed for export] *)
      rt F_836c8 D_836c8.                              (* [comment removed for export] *)
      chain_step; [reflexivity
        | eapply step_lw with (bs := LE4 34) (v := Z_to_bv 64 34);
          [exact F_82ae0 | reflexivity | exact D_82ae0
          | gres; rwH; imm_norm; rewrite ?at_addi; zlit_at; (lazymatch goal with |- ?G => let G' := eval unfold mod_m1 in G in change_no_check G' end);
            repeat (rewrite wc_rdn_wbytes_out3; [ | rd8_side ]);
            apply rdn_wbytes_hit4; (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_ulia
          | reflexivity]
        | step_simpl]; rewrite (v_lw_small 34) by lia; vn.   (* [comment removed for export] *)
      an F_82ae4 D_82ae4.                              (* [comment removed for export] *)
      an F_82ae8 D_82ae8.                              (* [comment removed for export] *)
      an F_82aec D_82aec.                              (* [comment removed for export] *)
      an F_82af0 D_82af0.                              (* [comment removed for export] *)
      an F_82af4 D_82af4.                              (* [comment removed for export] *)
      an F_82af8 D_82af8.                              (* [comment removed for export] *)
      an F_811a8 D_811a8.                              (* [comment removed for export] *)
      wd_refl.
    - post. (lazymatch goal with |- ?G => let G' := eval unfold mod_clob in G in change_no_check G' end). ra_solve.
  Qed.

  Lemma mod_m1_outside : forall x : word, (U x < U sp - 320 \/ U sp <= U x)%Z -> M1 x = mem x.
  Proof using Hsp.
    intros x Hx. pose proof (u64_range sp) as Hspr. (lazymatch goal with |- ?G => let G' := eval unfold mod_m1 in G in change_no_check G' end).
    repeat (rewrite wbytes_outside; [ | rewrite length_N_to_le_bytes, at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite length_N_to_le_bytes, at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia]).
    reflexivity.
  Qed.
  Lemma mod_m1_grows : mem_grows mem M1.
  Proof using. (lazymatch goal with |- ?G => let G' := eval unfold mod_m1 in G in change_no_check G' end). repeat (eapply mem_grows_trans; [|apply wbytes_grows]). apply mem_grows_refl. Qed.
  Lemma mod_m1_slots : forall (k : Z) (v : word),
    In (k, v) [(-8, ra); (-16, s0v); (-24, s1v); (-32, s2v)]%Z -> rdn BSEGS M1 (at_ sp k) 8 = Some (LE8 v).
  Proof using Hsp.
    intros k v Hin. pose proof (u64_range sp) as Hspr. (lazymatch goal with |- ?G => let G' := eval unfold mod_m1 in G in change_no_check G' end). cbn [In] in Hin.
    repeat (destruct Hin as [E|Hin]; [injection E as <- <-; rd8_chain|]). destruct Hin.
  Qed.
End MODPRE.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section MODPOST.
  Variables (M2 rom : word -> option byte) (sp ra s0v s1v s2v size : word) (CF : Z).
  Variable regs : bvmap 5 word.
  Hypothesis H1 : getr regs 1 = Z_to_bv 64 0x82afc.
  Hypothesis H2 : getr regs 2 = at_ sp (-48).
  Hypothesis H9 : getr regs 9 = size.
  Hypothesis Hsp : (2 ^ 24 <= U sp /\ U sp + 16 <= 2 ^ 47)%Z.
  Hypothesis Hret : ret_ok ra.
  Hypothesis HCF : (AIMGLO <= CF /\ CF + 264 <= AIMGHI)%Z.
  Hypothesis Hsok : store_ok BSEGS M2 (at_ sp (-40)) 4 = true.
  Hypothesis S_ra : rdn BSEGS M2 (at_ sp (-8)) 8 = Some (LE8 ra).
  Hypothesis S_s0 : rdn BSEGS M2 (at_ sp (-16)) 8 = Some (LE8 s0v).
  Hypothesis S_s1 : rdn BSEGS M2 (at_ sp (-24)) 8 = Some (LE8 s1v).
  Hypothesis S_s2 : rdn BSEGS M2 (at_ sp (-32)) 8 = Some (LE8 s2v).

  Ltac mod_epi :=
      an F_82b2c D_82b2c;                              (* [comment removed for export] *)
      cld8 F_82b30 D_82b30 ra S_ra;                    (* [comment removed for export] *)
      cld8 F_82b34 D_82b34 s0v S_s0;                   (* [comment removed for export] *)
      cld8 F_82b38 D_82b38 s1v S_s1;                   (* [comment removed for export] *)
      cld8 F_82b3c D_82b3c s2v S_s2;                   (* [comment removed for export] *)
      an F_82b40 D_82b40;                              (* [comment removed for export] *)
      aret F_82b44 D_82b44 ra.                         (* [comment removed for export] *)

  Definition mod_ret (r : bvmap 5 word) (res : word) : Prop :=
    getr r 10 = res /\ getr r 2 = sp /\ getr r 1 = ra /\ getr r 8 = s0v /\ getr r 9 = s1v /\ getr r 18 = s2v
    /\ regs_agree (fun i : reg => In i mod_clob) regs r.

  (* [comment removed for export] *)
  Section OK.
    Variable map : word.
    Hypothesis H10 : getr regs 10 = map.
    Hypothesis Hmap : (U map < 2 ^ 63)%Z.
    Hypothesis Rgcf : rdn BSEGS M2 (Z_to_bv 64 0x105f08) 8 = Some (LE8 (Z_to_bv 64 CF)).
    Hypothesis Rlim : rdn BSEGS M2 (Z_to_bv 64 (CF + 144)) 8 = Some (LE8 (Z_to_bv 64 0)).
    Lemma mod_ok :
      exists r, msteps BSEGS (mkst regs (0x811b0 : word) M2 rom)
                             (mkst r ra (wbytes M2 (at_ sp (-40)) (LE4 0xffffffffaaaaaaaa)) rom) /\ mod_ret r map.
    Proof using Rlim Rgcf Hmap H10 S_s2 S_s1 S_s0 S_ra Hsok HCF Hret Hsp H9 H2 H1 CF size.
      (lazymatch goal with |- ?G => let G' := eval unfold mod_ret in G in change_no_check G' end). pose proof (u64_range sp) as Hspr. pose proof (u64_range map) as Har.
      wd_eexists. split.
      - rt F_811b0 D_811b0.                            (* [comment removed for export] *)
        an F_82afc D_82afc.                            (* [comment removed for export] *)
        an F_82b00 D_82b00.                            (* [comment removed for export] *)
        an F_82b04 D_82b04.                            (* [comment removed for export] *)
        an F_81188 D_81188.                            (* [comment removed for export] *)
        an F_8118c D_8118c.                            (* [comment removed for export] *)
        ab_tk F_81190 D_81190 ltac:(condz).            (* [comment removed for export] *)
        an F_811a0 D_811a0. sltu0.                     (* [comment removed for export] *)
        rt F_811a4 D_811a4.                            (* [comment removed for export] *)
        an F_82b08 D_82b08.                            (* [comment removed for export] *)
        an F_82b0c D_82b0c.                            (* [comment removed for export] *)
        fsw F_82b10 D_82b10 (at_ sp (-40)).            (* [comment removed for export] *)
        an F_82b14 D_82b14.                            (* [comment removed for export] *)
        an F_82b18 D_82b18.                            (* [comment removed for export] *)
        an F_82b1c D_82b1c.                            (* [comment removed for export] *)
        an F_81188 D_81188.                            (* [comment removed for export] *)
        an F_8118c D_8118c.                            (* [comment removed for export] *)
        ab_tk F_81190 D_81190 ltac:(condz).            (* [comment removed for export] *)
        an F_811a0 D_811a0. sltu0.                     (* [comment removed for export] *)
        rt F_811a4 D_811a4.                            (* [comment removed for export] *)
        ab_ft F_82b20 D_82b20 ltac:(condz).            (* [comment removed for export] *)
        an F_82b24 D_82b24.                            (* [comment removed for export] *)
        an F_82b28 D_82b28.                            (* [comment removed for export] *)
        an F_7d08c D_7d08c.                            (* [comment removed for export] *)
        cld8 F_7d090 D_7d090 (Z_to_bv 64 CF) Rgcf.     (* [comment removed for export] *)
        cld8 F_7d094 D_7d094 (Z_to_bv 64 0) Rlim.      (* [comment removed for export] *)
        ab_tk F_7d098 D_7d098 ltac:(condz).            (* [comment removed for export] *)
        rt F_7d0b4 D_7d0b4.                            (* [comment removed for export] *)
        mod_epi.
        wd_refl.
      - post. (lazymatch goal with |- ?G => let G' := eval unfold mod_clob in G in change_no_check G' end). ra_solve.
    Qed.
  End OK.

  (* [comment removed for export] *)
  Section FAIL.
    Hypothesis H10 : getr regs 10 = Z_to_bv 64 (2 ^ 64 - 12).
    Lemma mod_fail :
      exists r, msteps BSEGS (mkst regs (0x811b0 : word) M2 rom)
                             (mkst r ra (wbytes (wbytes M2 (at_ sp (-40)) (LE4 0xffffffffaaaaaaaa)) (at_ sp (-40)) (LE4 12)) rom)
        /\ mod_ret r (Z_to_bv 64 0).
    Proof using H10 S_s2 S_s1 S_s0 S_ra Hsok Hret Hsp H2 H1.
      (lazymatch goal with |- ?G => let G' := eval unfold mod_ret in G in change_no_check G' end). pose proof (u64_range sp) as Hspr.
      wd_eexists. split.
      - rt F_811b0 D_811b0.                            (* [comment removed for export] *)
        an F_82afc D_82afc.                            (* [comment removed for export] *)
        an F_82b00 D_82b00.                            (* [comment removed for export] *)
        an F_82b04 D_82b04.                            (* [comment removed for export] *)
        an F_81188 D_81188.                            (* [comment removed for export] *)
        an F_8118c D_8118c.                            (* [comment removed for export] *)
        ab_ft F_81190 D_81190 ltac:(condz).            (* [comment removed for export] *)
        ab_tk F_81194 D_81194 ltac:(condz).            (* [comment removed for export] *)
        an F_811a0 D_811a0.                            (* [comment removed for export] *)
        rt F_811a4 D_811a4.                            (* [comment removed for export] *)
        an F_82b08 D_82b08.                            (* [comment removed for export] *)
        an F_82b0c D_82b0c.                            (* [comment removed for export] *)
        fsw F_82b10 D_82b10 (at_ sp (-40)).            (* [comment removed for export] *)
        an F_82b14 D_82b14.                            (* [comment removed for export] *)
        an F_82b18 D_82b18.                            (* [comment removed for export] *)
        an F_82b1c D_82b1c.                            (* [comment removed for export] *)
        an F_81188 D_81188.                            (* [comment removed for export] *)
        an F_8118c D_8118c.                            (* [comment removed for export] *)
        ab_ft F_81190 D_81190 ltac:(condz).            (* [comment removed for export] *)
        ab_ft F_81194 D_81194 ltac:(condz).            (* [comment removed for export] *)
        an F_81198 D_81198.                            (* [comment removed for export] *)
        fsw F_8119c D_8119c (at_ sp (-40)).            (* [comment removed for export] *)
        an F_811a0 D_811a0.                            (* [comment removed for export] *)
        rt F_811a4 D_811a4.                            (* [comment removed for export] *)
        ab_tk F_82b20 D_82b20 ltac:(condz).            (* [comment removed for export] *)
        chain_step; [reflexivity
          | eapply step_lw with (bs := LE4 12) (v := Z_to_bv 64 12);
            [exact F_82b58 | reflexivity | exact D_82b58
            | gres; rwH; imm_norm; rewrite ?at_addi; zlit_at;
              apply rdn_wbytes_hit4; (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_ulia
            | reflexivity]
          | step_simpl]; rewrite (v_lw_small 12) by lia; vn.   (* [comment removed for export] *)
        an F_82b5c D_82b5c.                            (* [comment removed for export] *)
        ab_ft F_82b60 D_82b60 ltac:(condz).            (* [comment removed for export] *)
        an F_82b64 D_82b64.                            (* [comment removed for export] *)
        an F_82b68 D_82b68.                            (* [comment removed for export] *)
        mod_epi.
        wd_refl.
      - post. (lazymatch goal with |- ?G => let G' := eval unfold mod_clob in G in change_no_check G' end). ra_solve.
    Qed.
  End FAIL.
End MODPOST.
End FPGen.
End BoAllocM9m.
Module BoAllocM9k.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import Stdlib.Logic.FunctionalExtensionality.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mprotect.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.DivergeSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.SpinAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes.AgentNodes OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocSim OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys6.MhKSys OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsK OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys6.AsKSys OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys6.AsKSys2 OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsRtK OSSVerify.Proofs.glaze.binary_reflection.lib.Common.BackingAlgebra OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys6.AsanNodesLibE OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8m BoAllocM8k BoAllocM9m OSSVerify.Proofs.glaze.binary_reflection.lib.BoDrvIStrlen.Bo_code_80b0c_815a0.
Import OSSVerify.glaze.binary_reflection.images.AsanUbsan.
Import ListNotations.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation BSEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).
#[local] Abbreviation LE4 z := (word_to_le_bytes 4 (Z_to_bv 64 z)).
#[local] Abbreviation U := bv_unsigned.

Section FPGen1.
Context {fx : FPState}.

Definition mod_ret' (regs r : bvmap 5 word) (sp ra s0v s1v s2v res : word) : Prop :=
  getr r 10 = res /\ getr r 2 = sp /\ getr r 1 = ra /\ getr r 8 = s0v /\ getr r 9 = s1v /\ getr r 18 = s2v
  /\ regs_agree (fun i : reg => In i mod_clob) regs r.

Section MODK.
  Variable Hd : word -> bool.
  Hypothesis HOFFSEG : H_off_segments BSEGS Hd.
  Hypothesis WX : wx_segs_nowrap BSEGS.

  Theorem mmapordie_katsD :
    forall (A : list (Z * Z)) regs (mem rom : word -> option byte) (model : Model)
           (sp ra s0v s1v s2v s3v s4v s5v size name : word) (PGP CF : Z) (Qok Qf : config -> Prop)
           (GRANT : Model -> word -> Prop) (MOK : Model -> word -> Model),
    let M1 := mod_m1 mem sp ra s0v s1v s2v s3v s4v s5v size name PGP in
    let ENOMEMw : word := Z_to_bv 64 (2 ^ 64 - 12) in
    let SCR := LE4 0xffffffffaaaaaaaa in
    getr regs 1 = ra -> getr regs 2 = sp -> getr regs 10 = size -> getr regs 11 = name ->
    getr regs 8 = s0v -> getr regs 9 = s1v -> getr regs 18 = s2v -> getr regs 19 = s3v -> getr regs 20 = s4v -> getr regs 21 = s5v ->
    (2 ^ 24 <= U sp /\ U sp + 16 <= 2 ^ 47) -> ret_ok ra ->
    (U size mod 4096 = 0 /\ U size + 4096 < 2 ^ 63) -> U name <> 0 ->
    (AIMGLO <= PGP /\ PGP + 8 <= AIMGHI) -> (AIMGLO <= CF /\ CF + 264 <= AIMGHI) ->
    store_ok BSEGS mem (at_ sp (-320)) 320 = true ->
    rdn BSEGS mem (Z_to_bv 64 0x105ef8) 8 = Some (LE8 (Z_to_bv 64 PGP)) ->
    rdn BSEGS mem (Z_to_bv 64 PGP) 8 = Some (LE8 (Z_to_bv 64 4096)) ->
    rdn BSEGS mem (Z_to_bv 64 0x105f08) 8 = Some (LE8 (Z_to_bv 64 CF)) ->
    rdn BSEGS mem (Z_to_bv 64 (CF + 260)) 1 = Some [Z_to_bv 8 0] ->
    rdn BSEGS mem (Z_to_bv 64 (CF + 144)) 8 = Some (LE8 (Z_to_bv 64 0)) ->
    hid_off Hd 0x105ef8 8 -> hid_off Hd PGP 8 -> hid_off Hd 0x105f08 8 -> hid_off Hd (CF + 260) 1 -> hid_off Hd (CF + 144) 8 ->
    hid_off Hd (U sp - 320) 320 ->
    m_halted model = None -> lazy_cover Hd (m_vm_lazy model) A -> A_wf A -> MInv A model ->
    (* [comment removed for export] *)
    (forall mdlm (a : word), same_but_materialized model mdlm -> GRANT mdlm a ->
        AIMGHI <= U a /\ U a + U size < 2 ^ 63 /\ (U a + U size <= U sp - 320 \/ U sp <= U a)) ->
    (* [comment removed for export] *)
    (forall mdlm (r1 : bvmap 5 word), same_but_materialized model mdlm -> MInv A mdlm -> m_halted mdlm = None ->
        getr r1 10 = Z_to_bv 64 0 -> getr r1 11 = size -> getr r1 12 = Z_to_bv 64 3 -> getr r1 13 = Z_to_bv 64 34 ->
        getr r1 14 = Z_to_bv 64 (2 ^ 64 - 1) -> getr r1 15 = Z_to_bv 64 0 ->
        forall Qok' Qf' : config -> Prop,
          (forall a : word, GRANT mdlm a ->
              katwD BSEGS (mkCfg (mkst (regupd r1 10 a) (0x811b0 : word) (zfill a size M1) rom) (MOK mdlm a)) Qok' Qf') ->
          katD BSEGS (mkCfg (mkst (regupd r1 10 ENOMEMw) (0x811b0 : word) M1 rom) mdlm) Qf' ->
          katsD BSEGS (mkCfg (epend r1 (0x811ac : word) M1 rom (Z_to_bv 64 222)) mdlm) Qok' Qf') ->
    (* [comment removed for export] *)
    (forall mdlm (a : word), same_but_materialized model mdlm -> MInv A mdlm -> GRANT mdlm a ->
        m_halted (MOK mdlm a) = None /\ lazy_cover Hd (m_vm_lazy (MOK mdlm a)) A /\ MInv A (MOK mdlm a)) ->
    (* [comment removed for export] *)
    (forall (a : word) (r' : bvmap 5 word) mdlm mdl4,
        same_but_materialized model mdlm -> MInv A mdlm -> GRANT mdlm a -> same_but_materialized (MOK mdlm a) mdl4 -> MInv A mdl4 ->
        mod_ret' regs r' sp ra s0v s1v s2v a ->
        katwD BSEGS (mkCfg (mkst r' ra (wbytes (zfill a size M1) (at_ sp (-40)) SCR) rom) mdl4) Qok Qf) ->
    (* [comment removed for export] *)
    (forall (r' : bvmap 5 word) mdlm mdl4,
        same_but_materialized model mdlm -> MInv A mdlm -> same_but_materialized mdlm mdl4 -> MInv A mdl4 ->
        mod_ret' regs r' sp ra s0v s1v s2v (Z_to_bv 64 0) ->
        katD BSEGS (mkCfg (mkst r' ra (wbytes (wbytes M1 (at_ sp (-40)) SCR) (at_ sp (-40)) (LE4 12)) rom) mdl4) Qf) ->
    katsD BSEGS (mkCfg (mkst regs (0x82a74 : word) mem rom) model) Qok Qf.
  Proof using WX HOFFSEG.
    intros A regs mem rom model sp ra s0v s1v s2v s3v s4v s5v size name PGP CF Qok Qf GRANT MOK M1 ENOMEMw SCR
           H1 H2 H10 H11 H8 H9 H18 H19 H20 H21 Hsp Hret Hsize Hname HPGP HCF Hstk Rgpg Rpg Rgcf Rdpm Rlim
           HDgpg HDpg HDgcf HDdpm HDlim HDscr HALT LC AWF MI SEP NODE CHILD CONTOK CONTKP.
    pose proof (u64_range sp) as Hspr. pose proof (u64_range size) as Hszr.
    destruct HPGP as [PG1 PG2]. destruct HCF as [CF1 CF2].
    assert (Hstk' : store_ok BSEGS (mrestrict Hd mem) (at_ sp (-320)) 320 = true).
    { rewrite store_ok_mrestrict; [exact Hstk | first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); exact HDscr]. }
    assert (CELLR : forall (c : Z) (k : nat) v, 0 <= c < 2 ^ 32 -> Z.of_nat k <= 8 -> hid_off Hd c (Z.of_nat k) ->
               rdn BSEGS mem (Z_to_bv 64 c) k = Some v -> rdn BSEGS (mrestrict Hd mem) (Z_to_bv 64 c) k = Some v).
    { intros c k v Hc0 Hc1 Hh Hr. rewrite rdn_mrestrict; [exact Hr | first [ solve [ wd_unorm1; wd_zofnat; lia ] | rewrite u_Z2bv by lia; lia ] | rewrite u_Z2bv by lia; exact Hh]. }
    destruct (mod_pre (mrestrict Hd mem) rom sp ra s0v s1v s2v s3v s4v s5v size name PGP CF regs
                H1 H2 H10 H11 H8 H9 H18 H19 H20 H21 Hsp Hsize Hname (conj PG1 PG2) (conj CF1 CF2) Hstk'
                (CELLR 0x105ef8 8%nat _ ltac:(lia) ltac:((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia) HDgpg Rgpg) (CELLR PGP 8%nat _ ltac:(lia) ltac:((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia) HDpg Rpg)
                (CELLR 0x105f08 8%nat _ ltac:(lia) ltac:((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia) HDgcf Rgcf) (CELLR (CF + 260) 1%nat _ ltac:(lia) ltac:((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia) HDdpm Rdpm))
      as (r1 & RUN1 & B1 & B2 & B8 & B9 & B18 & B10 & B11 & B12 & B13 & B14 & B15 & B17 & AG1).
    assert (EM1 : mod_m1 (mrestrict Hd mem) sp ra s0v s1v s2v s3v s4v s5v size name PGP = mrestrict Hd M1).
    { (lazymatch goal with |- ?G => let G' := eval unfold M1, mod_m1 in G in change_no_check G' end).
      rewrite !wbytes_mrestrict; [reflexivity | | | | | | | | | | | | | | | | | | | | | | | |];
        wd_lenlit; rewrite ?length_N_to_le_bytes, ?at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn [length Z.of_nat Pos.of_succ_nat Pos.succ Pos.to_nat] in G in change_no_check G' end); first [lia | intros x Hx; apply HDscr; lia]. }
    rewrite EM1 in RUN1.
    assert (M1hid : forall a : word, Hd a = true -> M1 a = mem a).
    { intros a Ha. (lazymatch goal with |- ?G => let G' := eval unfold M1 in G in change_no_check G' end). apply (mod_m1_outside mem sp ra s0v s1v s2v s3v s4v s5v size name PGP Hsp).
      destruct (Z_lt_le_dec (U a) (U sp - 320)) as [C1|C1]; [left; exact C1|].
      destruct (Z_lt_le_dec (U a) (U sp)) as [C2|C2]; [| right; exact C2].
      exfalso. rewrite (HDscr a) in Ha by lia. discriminate Ha. }
    apply (katsD_msteps_acct BSEGS Hd HOFFSEG WX A (mkst regs (0x82a74 : word) mem rom)
             (mkst r1 (0x811ac : word) (mrestrict Hd M1) rom) model Qok Qf LC AWF MI HALT).
    { rewrite mk_restrict_mkst. exact RUN1. }
    intros mdlm MIm SBMm HC1. rewrite mk_unrestrict_mkst.
    replace (RiscvSemantics.ms_mem (mkst regs (0x82a74 : word) mem rom)) with mem by reflexivity.
    rewrite (mk_munrestrict_same Hd mem M1 M1hid).
    pose proof (same_but_materialized_frame model mdlm SBMm) as FRm.
    assert (HALTm : m_halted mdlm = None) by (destruct FRm as (_&_&_&_&_&_&_&_&_&_&_&_&Hh&_); rewrite Hh; exact HALT).
    apply (katsD_ecall BSEGS r1 (0x811ac : word) M1 rom mdlm W_811ac Qok Qf HALTm F_811ac E_811ac).
    rewrite B17.
    assert (POSTF : forall MZ : word -> option byte,
               (forall x : word, U sp - 320 <= U x < U sp -> MZ x = M1 x) ->
               store_ok BSEGS (mrestrict Hd MZ) (at_ sp (-40)) 4 = true
               /\ (forall (k : Z) (v : word), In (k, v) [(-8, ra); (-16, s0v); (-24, s1v); (-32, s2v)] ->
                      rdn BSEGS (mrestrict Hd MZ) (at_ sp k) 8 = Some (LE8 v))).
    { intros MZ EZ. split.
      - rewrite store_ok_mrestrict; [| first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); intros x Hx; apply HDscr; lia].
        rewrite (store_ok_ext BSEGS 4 M1 MZ); [| first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | intros x Hx; apply EZ; rewrite at_u in Hx by lia; cbn in Hx; lia].
        eapply store_ok_mono; [apply mod_m1_grows|].
        eapply (store_ok_sub BSEGS mem (at_ sp (-320)) _ 320); [first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | exact Hstk | first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite !at_u by lia; lia ] | first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite !at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ]].
      - intros k v Hin.
        assert (Hk : -32 <= k <= -8) by (cbn [In] in Hin; repeat (destruct Hin as [E|Hin]; [injection E as <- <-; lia|]); destruct Hin).
        rewrite rdn_mrestrict; [| first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); intros x Hx; apply HDscr; lia].
        rewrite <- (mod_m1_slots mem sp ra s0v s1v s2v s3v s4v s5v size name PGP Hsp k v Hin). fold M1.
        apply rdn_ext; [first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | intros x Hx; apply EZ; rewrite at_u in Hx by lia; cbn in Hx; lia]. }
    assert (Q1 : forall v : word, getr (regupd r1 10 v) 1 = Z_to_bv 64 0x82afc) by (intros v; rewrite getr_other by (intros E; discriminate E); exact B1).
    assert (Q2 : forall v : word, getr (regupd r1 10 v) 2 = at_ sp (-48)) by (intros v; rewrite getr_other by (intros E; discriminate E); exact B2).
    assert (Q9 : forall v : word, getr (regupd r1 10 v) 9 = size) by (intros v; rewrite getr_other by (intros E; discriminate E); exact B9).
    assert (Q10 : forall v : word, getr (regupd r1 10 v) 10 = v) by (intros v; rewrite getr_same by (intros E; discriminate E); reflexivity).
    assert (AGC : forall (v : word) (r2 : bvmap 5 word), regs_agree (fun i : reg => In i mod_clob) (regupd r1 10 v) r2 ->
                    regs_agree (fun i : reg => In i mod_clob) regs r2).
    { intros v r2 AG2 x Hx. rewrite (AG2 x Hx).
      assert (NE10 : x <> 10%bv) by (intros ->; apply Hx; (lazymatch goal with |- ?G => let G' := eval unfold mod_clob in G in change_no_check G' end); (lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); tauto).
      rewrite getr_other by (intros E; apply NE10; exact E). apply AG1. exact Hx. }
    assert (HIDW : forall (MM : word -> option byte) bs (a : word), Hd a = true -> Z.of_nat (length bs) = 4 -> wbytes MM (at_ sp (-40)) bs a = MM a).
    { intros MM bs a Ha Hl.
      destruct (Z_lt_le_dec (U a) (U sp - 40)) as [C|C]; [apply wbytes_below; rewrite ?Hl, ?at_u by lia; lia|].
      destruct (Z_lt_le_dec (U a) (U sp - 36)) as [C'|C']; [exfalso; rewrite (HDscr a) in Ha by lia; discriminate Ha|].
      apply wbytes_above. rewrite Hl, at_u by lia. lia. }
    assert (L4a : Z.of_nat (length SCR) = 4) by ((lazymatch goal with |- ?G => let G' := eval unfold SCR in G in change_no_check G' end); rewrite length_N_to_le_bytes; reflexivity).
    assert (L4b : Z.of_nat (length (LE4 12)) = 4) by (rewrite length_N_to_le_bytes; reflexivity).
    apply (NODE mdlm r1 SBMm MIm HALTm B10 B11 B12 B13 B14 B15 Qok Qf).
    - (* [comment removed for export] *)
      intros a GR. destruct (SEP mdlm a SBMm GR) as (SL1 & SL2 & SL3). pose proof (u64_range a) as Har.
      destruct (CHILD mdlm a SBMm MIm GR) as (HOK1 & HOK2 & HOK3).
      set (MZ := zfill a size M1).
      assert (EZ : forall x : word, U sp - 320 <= U x < U sp -> MZ x = M1 x) by (intros x Hx; (lazymatch goal with |- ?G => let G' := eval unfold MZ in G in change_no_check G' end); apply zfill_out; lia).
      destruct (POSTF MZ EZ) as [SOKZ SLZ].
      assert (CELLZ : forall (c : Z) (k : nat) v, 0 <= c -> c + Z.of_nat k <= AIMGHI -> hid_off Hd c (Z.of_nat k) ->
                 rdn BSEGS mem (Z_to_bv 64 c) k = Some v -> rdn BSEGS (mrestrict Hd MZ) (Z_to_bv 64 c) k = Some v).
      { intros c k v Hc0 Hc1 Hh Hr. rewrite rdn_mrestrict; [| first [ solve [ wd_unorm1; wd_zofnat; lia ] | rewrite u_Z2bv by lia; lia ] | rewrite u_Z2bv by lia; exact Hh].
        rewrite <- Hr. apply rdn_ext; [first [ solve [ wd_unorm1; wd_zofnat; lia ] | rewrite u_Z2bv by lia; lia ]|]. intros x Hx. rewrite u_Z2bv in Hx by lia.
        (lazymatch goal with |- ?G => let G' := eval unfold MZ in G in change_no_check G' end). rewrite zfill_out by lia. (lazymatch goal with |- ?G => let G' := eval unfold M1 in G in change_no_check G' end). apply (mod_m1_outside mem sp ra s0v s1v s2v s3v s4v s5v size name PGP Hsp). left. lia. }
      destruct (mod_ok (mrestrict Hd MZ) rom sp ra s0v s1v s2v size CF (regupd r1 10 a)
                  (Q1 a) (Q2 a) (Q9 a) Hsp Hret (conj CF1 CF2) SOKZ
                  (SLZ (-8) ra ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); tauto)) (SLZ (-16) s0v ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); tauto)) (SLZ (-24) s1v ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); tauto))
                  (SLZ (-32) s2v ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); tauto))
                  a (Q10 a) ltac:(lia)
                  (CELLZ 0x105f08 8%nat _ ltac:(lia) ltac:((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia) HDgcf Rgcf) (CELLZ (CF + 144) 8%nat _ ltac:(lia) ltac:((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia) HDlim Rlim))
        as (r2 & RUN2 & C10 & C2 & C1 & C8 & C9 & C18 & AG2).
      rewrite wbytes_mrestrict in RUN2; [| rewrite length_N_to_le_bytes, at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia
                                          | rewrite length_N_to_le_bytes, at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); intros x Hx; apply HDscr; lia].
      apply (katwD_msteps_acct BSEGS Hd HOFFSEG WX A (mkst (regupd r1 10 a) (0x811b0 : word) MZ rom)
               (mkst r2 ra (mrestrict Hd (wbytes MZ (at_ sp (-40)) SCR)) rom) (MOK mdlm a) Qok Qf HOK2 AWF HOK3 HOK1).
      { rewrite mk_restrict_mkst. exact RUN2. }
      intros mdl4 MI4 SBM4 HC4. rewrite mk_unrestrict_mkst.
      replace (RiscvSemantics.ms_mem (mkst (regupd r1 10 a) (0x811b0 : word) MZ rom)) with MZ by reflexivity.
      rewrite (mk_munrestrict_same Hd MZ (wbytes MZ (at_ sp (-40)) SCR)).
      2:{ intros x Hx. apply HIDW; [exact Hx | exact L4a]. }
      apply (CONTOK a r2 mdlm mdl4 SBMm MIm GR SBM4 MI4).
      (lazymatch goal with |- ?G => let G' := eval unfold mod_ret' in G in change_no_check G' end). repeat (split; [assumption|]). exact (AGC a r2 AG2).
    - (* [comment removed for export] *)
      set (MZ := M1).
      assert (EZ : forall x : word, U sp - 320 <= U x < U sp -> MZ x = M1 x) by (intros x Hx; reflexivity).
      destruct (POSTF MZ EZ) as [SOKZ SLZ].
      destruct (mod_fail (mrestrict Hd MZ) rom sp ra s0v s1v s2v (regupd r1 10 ENOMEMw)
                  (Q1 ENOMEMw) (Q2 ENOMEMw) Hsp Hret SOKZ
                  (SLZ (-8) ra ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); tauto)) (SLZ (-16) s0v ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); tauto)) (SLZ (-24) s1v ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); tauto))
                  (SLZ (-32) s2v ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); tauto))
                  (Q10 ENOMEMw))
        as (r2 & RUN2 & C10 & C2 & C1 & C8 & C9 & C18 & AG2).
      rewrite !wbytes_mrestrict in RUN2; [| wd_lenlit; rewrite ?length_N_to_le_bytes, at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia
                                           | wd_lenlit; rewrite ?length_N_to_le_bytes, at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); intros x Hx; apply HDscr; lia
                                           | wd_lenlit; rewrite ?length_N_to_le_bytes, at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia
                                           | wd_lenlit; rewrite ?length_N_to_le_bytes, at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); intros x Hx; apply HDscr; lia].
      apply (katD_msteps_acct BSEGS Hd HOFFSEG WX A (mkst (regupd r1 10 ENOMEMw) (0x811b0 : word) MZ rom)
               (mkst r2 ra (mrestrict Hd (wbytes (wbytes MZ (at_ sp (-40)) SCR) (at_ sp (-40)) (LE4 12))) rom) mdlm Qf).
      { destruct FRm as (_ & _ & Hl & _). rewrite Hl. exact LC. }
      { exact AWF. } { exact MIm. } { exact HALTm. }
      { rewrite mk_restrict_mkst. exact RUN2. }
      intros mdl4 MI4 SBM4 HC4. rewrite mk_unrestrict_mkst.
      replace (RiscvSemantics.ms_mem (mkst (regupd r1 10 ENOMEMw) (0x811b0 : word) MZ rom)) with MZ by reflexivity.
      rewrite (mk_munrestrict_same Hd MZ (wbytes (wbytes MZ (at_ sp (-40)) SCR) (at_ sp (-40)) (LE4 12))).
      2:{ intros x Hx. rewrite (HIDW _ _ x Hx L4b). apply (HIDW _ _ x Hx L4a). }
      apply (CONTKP r2 mdlm mdl4 SBMm MIm SBM4 MI4).
      (lazymatch goal with |- ?G => let G' := eval unfold mod_ret' in G in change_no_check G' end). repeat (split; [assumption|]). exact (AGC ENOMEMw r2 AG2).
  Qed.
End MODK.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section NODE2.
  Lemma node2_of_mmap_rw :
    forall (r1 : bvmap 5 word) (M1 rom : word -> option byte) (mdlm : Model) (size : word) (Qok' Qf' : config -> Prop),
    m_halted mdlm = None ->
    getr r1 10 = Z_to_bv 64 0 -> getr r1 11 = size -> getr r1 12 = Z_to_bv 64 3 -> getr r1 13 = Z_to_bv 64 34 ->
    getr r1 14 = Z_to_bv 64 (2 ^ 64 - 1) -> getr r1 15 = Z_to_bv 64 0 ->
    0 < U size -> U size mod 4096 = 0 ->
    (exists a : word, grant_ok (Z_to_bv 64 0) mdlm a (U size) = true) ->
    (forall a : word, grant_ok (Z_to_bv 64 0) mdlm a (U size) = true ->
        katwD BSEGS (mkCfg (mkst (regupd r1 10 a) (0x811b0 : word) (zfill a size M1) rom) (mmap_model a size mdlm)) Qok' Qf') ->
    katD BSEGS (mkCfg (mkst (regupd r1 10 (Z_to_bv 64 (2 ^ 64 - 12))) (0x811b0 : word) M1 rom) mdlm) Qf' ->
    katsD BSEGS (mkCfg (epend r1 (0x811ac : word) M1 rom (Z_to_bv 64 222)) mdlm) Qok' Qf'.
  Proof using.
    intros r1 M1 rom mdlm size Qok' Qf' HALT B10 B11 B12 B13 B14 B15 Hsz Hszal EX KOK KKP.
    pose proof (u64_range size) as Hszr.
    set (ms := epend r1 (0x811ac%bv : word) M1 rom (Z_to_bv 64 222)).
    assert (E0 : ms_gpr ms 0 = Z_to_bv 64 0) by ((lazymatch goal with |- ?G => let G' := eval unfold ms in G in change_no_check G' end); rewrite AsKSys6.MhKSys.ms_gpr_epend0; exact B10).
    assert (E1 : ms_gpr ms 1 = size) by ((lazymatch goal with |- ?G => let G' := eval unfold ms in G in change_no_check G' end); rewrite AsKSys6.MhKSys.ms_gpr_epend1; exact B11).
    assert (PRU : page_round_up_Z (U size) = U size) by (apply page_round_up_Z_aligned; [lia | (lazymatch goal with |- ?G => let G' := eval unfold page_size in G in change_no_check G' end); exact Hszal]).
    assert (PRW : page_round_up (ms_gpr ms 1) = size).
    { (lazymatch goal with |- ?G => let G' := eval unfold page_round_up in G in change_no_check G' end). rewrite E1, PRU. apply Z_to_bv_bv_unsigned. }
    assert (ARGS : mmap_args_ok ms).
    { (lazymatch goal with |- ?G => let G' := eval unfold mmap_args_ok in G in change_no_check G' end). rewrite E1. (lazymatch goal with |- ?G => let G' := eval unfold ms in G in change_no_check G' end). rewrite AsKSys6.MhKSys.ms_gpr_epend2, AsKSys6.MhKSys.ms_gpr_epend3, AsKSys6.MhKSys.ms_gpr_epend4, AsKSys6.MhKSys.ms_gpr_epend5.
      split; [intros X; apply (f_equal bv_unsigned) in X; rewrite u_Z2bv in X by lia; lia|].
      split; [exact B12|]. split; [exact B13|]. split; [rewrite B14; apply bv_eq; reflexivity | exact B15]. }
    apply (katsD_mmap_rw BSEGS ms mdlm (Z_to_bv 64 222) HALT eq_refl ltac:(rewrite u_Z2bv by lia; reflexivity) ARGS Qok' Qf').
    - rewrite E0, E1, PRU. exact EX.
    - intros e He. (lazymatch goal with |- ?G => let G' := eval unfold mmrw_fail, ms in G in change_no_check G' end). rewrite AsKSys6.MhKSys.adv_set_epend.
      assert (Ee : e = ENOMEM) by (destruct He as [<-|[]]; reflexivity). subst e.
      replace (errno_ret ENOMEM) with (Z_to_bv 64 (2 ^ 64 - 12) : word) by (apply bv_eq; vm_compute; reflexivity).
      replace (v_addi (0x811ac%bv : word) 4) with (0x811b0%bv : word) by (apply bv_eq; vm_compute; reflexivity).
      exact KKP.
    - intros a Ha. rewrite E0, E1, PRU in Ha. (lazymatch goal with |- ?G => let G' := eval unfold mmrw_grant in G in change_no_check G' end). rewrite PRW. (lazymatch goal with |- ?G => let G' := eval unfold ms in G in change_no_check G' end). rewrite AsKSys6.MhKSys.adv_zeros1_epend.
      replace (v_addi (0x811ac%bv : word) 4) with (0x811b0%bv : word) by (apply bv_eq; vm_compute; reflexivity).
      exact (KOK a Ha).
  Qed.
End NODE2.
End FPGen1.
End BoAllocM9k.
Module BoDepotMnr.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.WalkLetEv.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtFlush OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8m BoAllocM9m OSSVerify.Proofs.glaze.binary_reflection.lib.Bo_code_82b14_83760 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8m.Bo_code_7c9f4_7cb58 OSSVerify.Proofs.glaze.binary_reflection.lib.BoDrvIStrlen.Bo_code_80b0c_815a0 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM0.Bo_code_7d08c_7db0c.
Import OSSVerify.glaze.binary_reflection.images.AsanUbsan.
Import ListNotations.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac wd_setR ::= wd_setR_on.   (* [comment removed for export] *)
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation BSEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).
#[local] Abbreviation LE4 z := (word_to_le_bytes 4 (Z_to_bv 64 z)).
#[local] Abbreviation U := bv_unsigned.

Section FPGen.
Context {fx : FPState}.

Definition mnr_clob : list reg := [1; 2; 8; 9; 18; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 28; 29; 30; 31].

Definition mnr_m1 (mem : word -> option byte) (sp ra s0v s1v s2v s3v s4v s5v size name : word) (PGP : Z) : word -> option byte :=
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes mem
    (at_ sp (-8)) (LE8 ra))
    (at_ sp (-16)) (LE8 s0v))
    (at_ sp (-24)) (LE8 s1v))
    (at_ sp (-32)) (LE8 s2v))
    (at_ sp (-36)) (LE4 16418))
    (at_ sp (-56)) (LE8 (Z_to_bv 64 0x82e20)))
    (at_ sp (-64)) (LE8 name))
    (at_ sp (-72)) (LE8 size))
    (at_ sp (-80)) (LE8 (Z_to_bv 64 PGP)))
    (at_ sp (-88)) (LE8 s3v))
    (at_ sp (-96)) (LE8 s4v))
    (at_ sp (-104)) (LE8 s5v).
#[local] Hint Unfold mnr_m1 : asfr.

Section MODPRE.
  Variables (mem rom : word -> option byte) (sp ra s0v s1v s2v s3v s4v s5v size name : word) (PGP CF : Z).
  Variable regs : bvmap 5 word.
  Hypothesis H1 : getr regs 1 = ra.
  Hypothesis H2 : getr regs 2 = sp.
  Hypothesis H10 : getr regs 10 = size.
  Hypothesis H11 : getr regs 11 = name.
  Hypothesis H8 : getr regs 8 = s0v.   Hypothesis H9 : getr regs 9 = s1v.   Hypothesis H18 : getr regs 18 = s2v.
  Hypothesis H19 : getr regs 19 = s3v. Hypothesis H20 : getr regs 20 = s4v. Hypothesis H21 : getr regs 21 = s5v.
  Hypothesis Hsp : (2 ^ 24 <= U sp /\ U sp + 16 <= 2 ^ 47)%Z.
  Hypothesis Hsize : (U size mod 4096 = 0 /\ U size + 4096 < 2 ^ 63)%Z.
  Hypothesis Hname : (U name <> 0)%Z.
  Hypothesis HPGP : (AIMGLO <= PGP /\ PGP + 8 <= AIMGHI)%Z.
  Hypothesis HCF : (AIMGLO <= CF /\ CF + 264 <= AIMGHI)%Z.
  Hypothesis Hstk : store_ok BSEGS mem (at_ sp (-320)) 320 = true.
  Hypothesis Rgpg : rdn BSEGS mem (Z_to_bv 64 0x105ef8) 8 = Some (LE8 (Z_to_bv 64 PGP)).
  Hypothesis Rpg : rdn BSEGS mem (Z_to_bv 64 PGP) 8 = Some (LE8 (Z_to_bv 64 4096)).
  Hypothesis Rgcf : rdn BSEGS mem (Z_to_bv 64 0x105f08) 8 = Some (LE8 (Z_to_bv 64 CF)).
  Hypothesis Rdpm : rdn BSEGS mem (Z_to_bv 64 (CF + 260)) 1 = Some [Z_to_bv 8 0].

  #[local] Abbreviation M1 := (mnr_m1 mem sp ra s0v s1v s2v s3v s4v s5v size name PGP).

  Lemma mnr_pre :
    exists r, msteps BSEGS (mkst regs (0x82db0 : word) mem rom) (mkst r (0x811ac : word) M1 rom)
      /\ getr r 1 = Z_to_bv 64 0x82e3c /\ getr r 2 = at_ sp (-48)
      /\ getr r 8 = name /\ getr r 9 = size /\ getr r 18 = Z_to_bv 64 PGP
      /\ getr r 10 = Z_to_bv 64 0 /\ getr r 11 = size /\ getr r 12 = Z_to_bv 64 3 /\ getr r 13 = Z_to_bv 64 16418
      /\ getr r 14 = Z_to_bv 64 (2 ^ 64 - 1) /\ getr r 15 = Z_to_bv 64 0 /\ getr r 17 = Z_to_bv 64 222
      /\ regs_agree (fun i : reg => In i mnr_clob) regs r.
  Proof using Rdpm Rgcf Rpg Rgpg Hstk HCF HPGP Hname Hsize Hsp H21 H20 H19 H18 H9 H8 H11 H10 H2 H1 CF.
    pose proof (u64_range sp) as Hspr. pose proof (u64_range size) as Hsr. pose proof (u64_range name) as Hnr.
    destruct Hsize as [Hsz1 Hsz2].
    wd_eexists. split.
    - an F_82db0 D_82db0.                              (* [comment removed for export] *)
      fsd F_82db4 D_82db4 (at_ sp (-8)).               (* [comment removed for export] *)
      fsd F_82db8 D_82db8 (at_ sp (-16)).              (* [comment removed for export] *)
      fsd F_82dbc D_82dbc (at_ sp (-24)).              (* [comment removed for export] *)
      fsd F_82dc0 D_82dc0 (at_ sp (-32)).              (* [comment removed for export] *)
      an F_82dc4 D_82dc4.                              (* [comment removed for export] *)
      an F_82dc8 D_82dc8.                              (* [comment removed for export] *)
      cld8 F_82dcc D_82dcc (Z_to_bv 64 PGP) Rgpg.      (* [comment removed for export] *)
      cld8 F_82dd0 D_82dd0 (Z_to_bv 64 4096) Rpg.      (* [comment removed for export] *)
      an F_82dd4 D_82dd4.                              (* [comment removed for export] *)
      ab_tk F_82dd8 D_82dd8 ltac:(condz).              (* [comment removed for export] *)
      an F_82de8 D_82de8.                              (* [comment removed for export] *)
      an F_82dec D_82dec.                              (* [comment removed for export] *)
      ab_ft F_82df0 D_82df0 ltac:(condz).              (* [comment removed for export] *)
      av F_82df4 D_82df4 (Z_to_bv 64 (U size + 4096)) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_add in G in change_no_check G' end); unorm; f_equal; lia).   (* [comment removed for export] *)
      av F_82df8 D_82df8 (Z_to_bv 64 (2 ^ 64 - 2 ^ 12)) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_sub in G in change_no_check G' end); unorm; apply bv_eq; vm_compute; reflexivity).   (* [comment removed for export] *)
      av F_82dfc D_82dfc (Z_to_bv 64 (U size + 4095)) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_addi in G in change_no_check G' end); unorm; f_equal; lia).   (* [comment removed for export] *)
      av_and F_82e00 D_82e00 size
        ltac:(rewrite v_and_m4k; unorm; replace (U size + 4095 - (U size + 4095) mod 4096)%Z with (U size) by (Z.div_mod_to_equations; lia); apply Z_to_bv_bv_unsigned).   (* [comment removed for export] *)
      an F_82e04 D_82e04.                              (* [comment removed for export] *)
      av F_82e08 D_82e08 (Z_to_bv 64 16418) ltac:(apply bv_eq; reflexivity).   (* [comment removed for export] *)
      fsw F_82e0c D_82e0c (at_ sp (-36)).              (* [comment removed for export] *)
      an F_82e10 D_82e10.                              (* [comment removed for export] *)
      an F_82e14 D_82e14.                              (* [comment removed for export] *)
      an F_82e18 D_82e18.                              (* [comment removed for export] *)
      an F_82e1c D_82e1c.                              (* [comment removed for export] *)
      an F_83554 D_83554.                              (* [comment removed for export] *)
      fsd F_83558 D_83558 (at_ sp (-56)).              (* [comment removed for export] *)
      fsd F_8355c D_8355c (at_ sp (-64)).              (* [comment removed for export] *)
      fsd F_83560 D_83560 (at_ sp (-72)).              (* [comment removed for export] *)
      fsd F_83564 D_83564 (at_ sp (-80)).              (* [comment removed for export] *)
      fsd F_83568 D_83568 (at_ sp (-88)).              (* [comment removed for export] *)
      fsd F_8356c D_8356c (at_ sp (-96)).              (* [comment removed for export] *)
      fsd F_83570 D_83570 (at_ sp (-104)).             (* [comment removed for export] *)
      change (wbytes _ _ _) with M1.
      an F_83574 D_83574.                              (* [comment removed for export] *)
      an F_83578 D_83578.                              (* [comment removed for export] *)
      ab_ft F_8357c D_8357c ltac:(condz).              (* [comment removed for export] *)
      an F_83580 D_83580.                              (* [comment removed for export] *)
      an F_83584 D_83584.                              (* [comment removed for export] *)
      cld8 F_83588 D_83588 (Z_to_bv 64 CF) Rgcf.       (* [comment removed for export] *)
      clbu F_8358c D_8358c (Z_to_bv 8 0) Rdpm.         (* [comment removed for export] *)
      an F_83590 D_83590.                              (* [comment removed for export] *)
      ab_tk F_83594 D_83594 ltac:(condz).              (* [comment removed for export] *)
      an F_836a4 D_836a4.                              (* [comment removed for export] *)
      fld F_836a8 D_836a8 (Z_to_bv 64 0x82e20).        (* [comment removed for export] *)
      fld F_836ac D_836ac name.                        (* [comment removed for export] *)
      fld F_836b0 D_836b0 size.                        (* [comment removed for export] *)
      fld F_836b4 D_836b4 (Z_to_bv 64 PGP).            (* [comment removed for export] *)
      fld F_836b8 D_836b8 s3v.                         (* [comment removed for export] *)
      fld F_836bc D_836bc s4v.                         (* [comment removed for export] *)
      fld F_836c0 D_836c0 s5v.                         (* [comment removed for export] *)
      an F_836c4 D_836c4.                              (* [comment removed for export] *)
      rt F_836c8 D_836c8.                              (* [comment removed for export] *)
      chain_step; [reflexivity
        | eapply step_lw with (bs := LE4 16418) (v := Z_to_bv 64 16418);
          [exact F_82e20 | reflexivity | exact D_82e20
          | gres; rwH; imm_norm; rewrite ?at_addi; zlit_at; (lazymatch goal with |- ?G => let G' := eval unfold mnr_m1 in G in change_no_check G' end);
            repeat (rewrite wc_rdn_wbytes_out3; [ | rd8_side ]);
            apply rdn_wbytes_hit4; (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_ulia
          | reflexivity]
        | step_simpl]; rewrite (v_lw_small 16418) by lia; vn.   (* [comment removed for export] *)
      an F_82e24 D_82e24.                              (* [comment removed for export] *)
      an F_82e28 D_82e28.                              (* [comment removed for export] *)
      an F_82e2c D_82e2c.                              (* [comment removed for export] *)
      an F_82e30 D_82e30.                              (* [comment removed for export] *)
      an F_82e34 D_82e34.                              (* [comment removed for export] *)
      an F_82e38 D_82e38.                              (* [comment removed for export] *)
      an F_811a8 D_811a8.                              (* [comment removed for export] *)
      wd_refl.
    - post. (lazymatch goal with |- ?G => let G' := eval unfold mnr_clob in G in change_no_check G' end). ra_solve.
  Qed.

  Lemma mnr_m1_outside : forall x : word, (U x < U sp - 320 \/ U sp <= U x)%Z -> M1 x = mem x.
  Proof using Hsp.
    intros x Hx. pose proof (u64_range sp) as Hspr. (lazymatch goal with |- ?G => let G' := eval unfold mnr_m1 in G in change_no_check G' end).
    repeat (rewrite wbytes_outside; [ | rewrite length_N_to_le_bytes, at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite length_N_to_le_bytes, at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia]).
    reflexivity.
  Qed.
  Lemma mnr_m1_grows : mem_grows mem M1.
  Proof using. (lazymatch goal with |- ?G => let G' := eval unfold mnr_m1 in G in change_no_check G' end). repeat (eapply mem_grows_trans; [|apply wbytes_grows]). apply mem_grows_refl. Qed.
  Lemma mnr_m1_slots : forall (k : Z) (v : word),
    In (k, v) [(-8, ra); (-16, s0v); (-24, s1v); (-32, s2v)]%Z -> rdn BSEGS M1 (at_ sp k) 8 = Some (LE8 v).
  Proof using Hsp.
    intros k v Hin. pose proof (u64_range sp) as Hspr. (lazymatch goal with |- ?G => let G' := eval unfold mnr_m1 in G in change_no_check G' end). cbn [In] in Hin.
    repeat (destruct Hin as [E|Hin]; [injection E as <- <-; rd8_chain|]). destruct Hin.
  Qed.
End MODPRE.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section MODPOST.
  Variables (M2 rom : word -> option byte) (sp ra s0v s1v s2v size : word) (CF : Z).
  Variable regs : bvmap 5 word.
  Hypothesis H1 : getr regs 1 = Z_to_bv 64 0x82e3c.
  Hypothesis H2 : getr regs 2 = at_ sp (-48).
  Hypothesis H9 : getr regs 9 = size.
  Hypothesis Hsp : (2 ^ 24 <= U sp /\ U sp + 16 <= 2 ^ 47)%Z.
  Hypothesis Hret : ret_ok ra.
  Hypothesis HCF : (AIMGLO <= CF /\ CF + 264 <= AIMGHI)%Z.
  Hypothesis Hsok : store_ok BSEGS M2 (at_ sp (-40)) 4 = true.
  Hypothesis S_ra : rdn BSEGS M2 (at_ sp (-8)) 8 = Some (LE8 ra).
  Hypothesis S_s0 : rdn BSEGS M2 (at_ sp (-16)) 8 = Some (LE8 s0v).
  Hypothesis S_s1 : rdn BSEGS M2 (at_ sp (-24)) 8 = Some (LE8 s1v).
  Hypothesis S_s2 : rdn BSEGS M2 (at_ sp (-32)) 8 = Some (LE8 s2v).

  Ltac mnr_epi :=
      an F_82e6c D_82e6c;                              (* [comment removed for export] *)
      cld8 F_82e70 D_82e70 ra S_ra;                    (* [comment removed for export] *)
      cld8 F_82e74 D_82e74 s0v S_s0;                   (* [comment removed for export] *)
      cld8 F_82e78 D_82e78 s1v S_s1;                   (* [comment removed for export] *)
      cld8 F_82e7c D_82e7c s2v S_s2;                   (* [comment removed for export] *)
      an F_82e80 D_82e80;                              (* [comment removed for export] *)
      aret F_82e84 D_82e84 ra.                         (* [comment removed for export] *)

  Definition mnr_ret (r : bvmap 5 word) (res : word) : Prop :=
    getr r 10 = res /\ getr r 2 = sp /\ getr r 1 = ra /\ getr r 8 = s0v /\ getr r 9 = s1v /\ getr r 18 = s2v
    /\ regs_agree (fun i : reg => In i mnr_clob) regs r.

  (* [comment removed for export] *)
  Section OK.
    Variable map : word.
    Hypothesis H10 : getr regs 10 = map.
    Hypothesis Hmap : (U map < 2 ^ 63)%Z.
    Hypothesis Rgcf : rdn BSEGS M2 (Z_to_bv 64 0x105f08) 8 = Some (LE8 (Z_to_bv 64 CF)).
    Hypothesis Rlim : rdn BSEGS M2 (Z_to_bv 64 (CF + 144)) 8 = Some (LE8 (Z_to_bv 64 0)).
    Lemma mnr_ok :
      exists r, msteps BSEGS (mkst regs (0x811b0 : word) M2 rom)
                             (mkst r ra (wbytes M2 (at_ sp (-40)) (LE4 0xffffffffaaaaaaaa)) rom) /\ mnr_ret r map.
    Proof using Rlim Rgcf Hmap H10 S_s2 S_s1 S_s0 S_ra Hsok HCF Hret Hsp H9 H2 H1 CF size.
      (lazymatch goal with |- ?G => let G' := eval unfold mnr_ret in G in change_no_check G' end). pose proof (u64_range sp) as Hspr. pose proof (u64_range map) as Har.
      wd_eexists. split.
      - rt F_811b0 D_811b0.                            (* [comment removed for export] *)
        an F_82e3c D_82e3c.                            (* [comment removed for export] *)
        an F_82e40 D_82e40.                            (* [comment removed for export] *)
        an F_82e44 D_82e44.                            (* [comment removed for export] *)
        an F_81188 D_81188.                            (* [comment removed for export] *)
        an F_8118c D_8118c.                            (* [comment removed for export] *)
        ab_tk F_81190 D_81190 ltac:(condz).            (* [comment removed for export] *)
        an F_811a0 D_811a0. sltu0.                     (* [comment removed for export] *)
        rt F_811a4 D_811a4.                            (* [comment removed for export] *)
        an F_82e48 D_82e48.                            (* [comment removed for export] *)
        an F_82e4c D_82e4c.                            (* [comment removed for export] *)
        fsw F_82e50 D_82e50 (at_ sp (-40)).            (* [comment removed for export] *)
        an F_82e54 D_82e54.                            (* [comment removed for export] *)
        an F_82e58 D_82e58.                            (* [comment removed for export] *)
        an F_82e5c D_82e5c.                            (* [comment removed for export] *)
        an F_81188 D_81188.                            (* [comment removed for export] *)
        an F_8118c D_8118c.                            (* [comment removed for export] *)
        ab_tk F_81190 D_81190 ltac:(condz).            (* [comment removed for export] *)
        an F_811a0 D_811a0. sltu0.                     (* [comment removed for export] *)
        rt F_811a4 D_811a4.                            (* [comment removed for export] *)
        ab_ft F_82e60 D_82e60 ltac:(condz).            (* [comment removed for export] *)
        an F_82e64 D_82e64.                            (* [comment removed for export] *)
        an F_82e68 D_82e68.                            (* [comment removed for export] *)
        an F_7d08c D_7d08c.                            (* [comment removed for export] *)
        cld8 F_7d090 D_7d090 (Z_to_bv 64 CF) Rgcf.     (* [comment removed for export] *)
        cld8 F_7d094 D_7d094 (Z_to_bv 64 0) Rlim.      (* [comment removed for export] *)
        ab_tk F_7d098 D_7d098 ltac:(condz).            (* [comment removed for export] *)
        rt F_7d0b4 D_7d0b4.                            (* [comment removed for export] *)
        mnr_epi.
        wd_refl.
      - post. (lazymatch goal with |- ?G => let G' := eval unfold mnr_clob in G in change_no_check G' end). ra_solve.
    Qed.
  End OK.

  (* [comment removed for export] *)
  Section DIE.
    Hypothesis H10 : getr regs 10 = Z_to_bv 64 (2 ^ 64 - 12).
    Hypothesis Hstk2 : store_ok BSEGS M2 (at_ sp (-96)) 48 = true.
    Hypothesis Rdie1 : rdn BSEGS M2 (Z_to_bv 64 0x105f58) 8 = Some (LE8 (Z_to_bv 64 1)).
    Hypothesis Rdie2 : rdn BSEGS M2 (Z_to_bv 64 0x19fcdc) 4 = Some (LE4 0).
    Lemma mnr_die :
      exists r M', msteps BSEGS (mkst regs (0x811b0 : word) M2 rom) (mkst r (0x7ca24 : word) M' rom).
    Proof using Rdie2 Rdie1 Hstk2 H10 Hsok Hsp H9 H2 H1 size sp.
      pose proof (u64_range sp) as Hspr.
      wd_eexists. wd_eexists.
      rt F_811b0 D_811b0.                            (* [comment removed for export] *)
      an F_82e3c D_82e3c.                            (* [comment removed for export] *)
      an F_82e40 D_82e40.                            (* [comment removed for export] *)
      an F_82e44 D_82e44.                            (* [comment removed for export] *)
      an F_81188 D_81188.                            (* [comment removed for export] *)
      an F_8118c D_8118c.                            (* [comment removed for export] *)
      ab_ft F_81190 D_81190 ltac:(condz).            (* [comment removed for export] *)
      ab_tk F_81194 D_81194 ltac:(condz).            (* [comment removed for export] *)
      an F_811a0 D_811a0.                            (* [comment removed for export] *)
      rt F_811a4 D_811a4.                            (* [comment removed for export] *)
      an F_82e48 D_82e48.                            (* [comment removed for export] *)
      an F_82e4c D_82e4c.                            (* [comment removed for export] *)
      fsw F_82e50 D_82e50 (at_ sp (-40)).            (* [comment removed for export] *)
      an F_82e54 D_82e54.                            (* [comment removed for export] *)
      an F_82e58 D_82e58.                            (* [comment removed for export] *)
      an F_82e5c D_82e5c.                            (* [comment removed for export] *)
      an F_81188 D_81188.                            (* [comment removed for export] *)
      an F_8118c D_8118c.                            (* [comment removed for export] *)
      ab_ft F_81190 D_81190 ltac:(condz).            (* [comment removed for export] *)
      ab_ft F_81194 D_81194 ltac:(condz).            (* [comment removed for export] *)
      an F_81198 D_81198.                            (* [comment removed for export] *)
      fsw F_8119c D_8119c (at_ sp (-40)).            (* [comment removed for export] *)
      an F_811a0 D_811a0.                            (* [comment removed for export] *)
      rt F_811a4 D_811a4.                            (* [comment removed for export] *)
      ab_tk F_82e60 D_82e60 ltac:(condz).            (* [comment removed for export] *)
      chain_step; [reflexivity
        | eapply step_lw with (bs := LE4 12) (v := Z_to_bv 64 12);
          [exact F_82e98 | reflexivity | exact D_82e98
          | gres; rwH; imm_norm; rewrite ?at_addi; zlit_at;
            apply rdn_wbytes_hit4; (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_ulia
          | reflexivity]
        | step_simpl]; rewrite (v_lw_small 12) by lia; vn.   (* [comment removed for export] *)
      an F_82e9c D_82e9c.                            (* [comment removed for export] *)
      an F_82ea0 D_82ea0.                            (* [comment removed for export] *)
      an F_82ea4 D_82ea4.                            (* [comment removed for export] *)
      an F_82ea8 D_82ea8.                            (* [comment removed for export] *)
      an F_82eac D_82eac.                            (* [comment removed for export] *)
      an F_82eb0 D_82eb0.                            (* [comment removed for export] *)
      an F_7c9f4 D_7c9f4.                            (* [comment removed for export] *)
      fsd F_7c9f8 D_7c9f8 (at_ sp (-56)).            (* [comment removed for export] *)
      fsd F_7c9fc D_7c9fc (at_ sp (-64)).            (* [comment removed for export] *)
      fsd F_7ca00 D_7ca00 (at_ sp (-72)).            (* [comment removed for export] *)
      fsd F_7ca04 D_7ca04 (at_ sp (-80)).            (* [comment removed for export] *)
      fsd F_7ca08 D_7ca08 (at_ sp (-88)).            (* [comment removed for export] *)
      an F_7ca0c D_7ca0c.                            (* [comment removed for export] *)
      cld8 F_7ca10 D_7ca10 (Z_to_bv 64 1) Rdie1.     (* [comment removed for export] *)
      ab_ft F_7ca14 D_7ca14 ltac:(condz).            (* [comment removed for export] *)
      an F_7ca18 D_7ca18.                            (* [comment removed for export] *)
      clw F_7ca1c D_7ca1c (LE4 0) (Z_to_bv 64 0) Rdie2 (eq_refl : bytes_le_to_Z (LE4 0) = U (Z_to_bv 64 0)).   (* [comment removed for export] *)
      try (rewrite (v_lw_small 0) by lia).
      ab_ft F_7ca20 D_7ca20 ltac:(condz).            (* [comment removed for export] *)
      wd_refl.
    Qed.

  End DIE.
End MODPOST.
End FPGen.
End BoDepotMnr.
Module BoDepotMod.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.WalkLetEv.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtFlush OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8m OSSVerify.Proofs.glaze.binary_reflection.lib.Bo_code_81fbc_82b14 OSSVerify.Proofs.glaze.binary_reflection.lib.Bo_code_82b14_83760 OSSVerify.Proofs.glaze.binary_reflection.lib.BoDrvIStrlen.Bo_code_80b0c_815a0 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM0.Bo_code_7d08c_7db0c OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8m.Bo_code_7c9f4_7cb58.
Import OSSVerify.glaze.binary_reflection.images.AsanUbsan.
Import ListNotations.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac wd_setR ::= wd_setR_on.   (* [comment removed for export] *)
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation BSEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).
#[local] Abbreviation LE4 z := (word_to_le_bytes 4 (Z_to_bv 64 z)).
#[local] Abbreviation U := bv_unsigned.

Section FPGen.
Context {fx : FPState}.

Definition mo_clob : list reg := [1; 2; 8; 9; 18; 19; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 28; 29; 30; 31].

Definition mo_m1 (mem : word -> option byte) (sp ra s0v s1v s2v s3v s4v s5v size name raw : word) (PGP : Z) : word -> option byte :=
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes mem
    (at_ sp (-8)) (LE8 ra))
    (at_ sp (-16)) (LE8 s0v))
    (at_ sp (-24)) (LE8 s1v))
    (at_ sp (-32)) (LE8 s2v))
    (at_ sp (-40)) (LE8 s3v))
    (at_ sp (-44)) (LE4 34))
    (at_ sp (-56)) (LE8 (Z_to_bv 64 0x828ec)))
    (at_ sp (-64)) (LE8 raw))
    (at_ sp (-72)) (LE8 name))
    (at_ sp (-80)) (LE8 size))
    (at_ sp (-88)) (LE8 (Z_to_bv 64 PGP)))
    (at_ sp (-96)) (LE8 s4v))
    (at_ sp (-104)) (LE8 s5v).
#[local] Hint Unfold mo_m1 : asfr.

Section MOPRE.
  Variables (mem rom : word -> option byte) (sp ra s0v s1v s2v s3v s4v s5v size name raw : word) (PGP CF : Z).
  Variable regs : bvmap 5 word.
  Hypothesis H1 : getr regs 1 = ra.
  Hypothesis H2 : getr regs 2 = sp.
  Hypothesis H10 : getr regs 10 = size.
  Hypothesis H11 : getr regs 11 = name.
  Hypothesis H12 : getr regs 12 = raw.
  Hypothesis H8 : getr regs 8 = s0v.   Hypothesis H9 : getr regs 9 = s1v.   Hypothesis H18 : getr regs 18 = s2v.
  Hypothesis H19 : getr regs 19 = s3v. Hypothesis H20 : getr regs 20 = s4v. Hypothesis H21 : getr regs 21 = s5v.
  Hypothesis Hsp : (2 ^ 24 <= U sp /\ U sp + 16 <= 2 ^ 47)%Z.
  Hypothesis Hsize : (U size mod 4096 = 0 /\ U size + 4096 < 2 ^ 63)%Z.
  Hypothesis Hname : (U name <> 0)%Z.
  Hypothesis HPGP : (AIMGLO <= PGP /\ PGP + 8 <= AIMGHI)%Z.
  Hypothesis HCF : (AIMGLO <= CF /\ CF + 264 <= AIMGHI)%Z.
  Hypothesis Hstk : store_ok BSEGS mem (at_ sp (-320)) 320 = true.
  Hypothesis Rgpg : rdn BSEGS mem (Z_to_bv 64 0x105ef8) 8 = Some (LE8 (Z_to_bv 64 PGP)).
  Hypothesis Rpg : rdn BSEGS mem (Z_to_bv 64 PGP) 8 = Some (LE8 (Z_to_bv 64 4096)).
  Hypothesis Rgcf : rdn BSEGS mem (Z_to_bv 64 0x105f08) 8 = Some (LE8 (Z_to_bv 64 CF)).
  Hypothesis Rdpm : rdn BSEGS mem (Z_to_bv 64 (CF + 260)) 1 = Some [Z_to_bv 8 0].

  #[local] Abbreviation M1 := (mo_m1 mem sp ra s0v s1v s2v s3v s4v s5v size name raw PGP).

  Lemma mo_pre :
    exists r, msteps BSEGS (mkst regs (0x82878 : word) mem rom) (mkst r (0x811ac : word) M1 rom)
      /\ getr r 1 = Z_to_bv 64 0x82908 /\ getr r 2 = at_ sp (-48)
      /\ getr r 8 = raw /\ getr r 9 = name /\ getr r 18 = size /\ getr r 19 = Z_to_bv 64 PGP
      /\ getr r 10 = Z_to_bv 64 0 /\ getr r 11 = size /\ getr r 12 = Z_to_bv 64 3 /\ getr r 13 = Z_to_bv 64 34
      /\ getr r 14 = Z_to_bv 64 (2 ^ 64 - 1) /\ getr r 15 = Z_to_bv 64 0 /\ getr r 17 = Z_to_bv 64 222
      /\ regs_agree (fun i : reg => In i mo_clob) regs r.
  Proof using Rdpm Rgcf Rpg Rgpg Hstk HCF HPGP Hname Hsize Hsp H21 H20 H19 H18 H9 H8 H12 H11 H10 H2 H1 CF.
    pose proof (u64_range sp) as Hspr. pose proof (u64_range size) as Hsr. pose proof (u64_range name) as Hnr.
    destruct Hsize as [Hsz1 Hsz2].
    wd_eexists. split.
    - an F_82878 D_82878.                              (* [comment removed for export] *)
      fsd F_8287c D_8287c (at_ sp (-8)).               (* [comment removed for export] *)
      fsd F_82880 D_82880 (at_ sp (-16)).              (* [comment removed for export] *)
      fsd F_82884 D_82884 (at_ sp (-24)).              (* [comment removed for export] *)
      fsd F_82888 D_82888 (at_ sp (-32)).              (* [comment removed for export] *)
      fsd F_8288c D_8288c (at_ sp (-40)).              (* [comment removed for export] *)
      an F_82890 D_82890.                              (* [comment removed for export] *)
      an F_82894 D_82894.                              (* [comment removed for export] *)
      an F_82898 D_82898.                              (* [comment removed for export] *)
      cld8 F_8289c D_8289c (Z_to_bv 64 PGP) Rgpg.      (* [comment removed for export] *)
      cld8 F_828a0 D_828a0 (Z_to_bv 64 4096) Rpg.      (* [comment removed for export] *)
      an F_828a4 D_828a4.                              (* [comment removed for export] *)
      ab_tk F_828a8 D_828a8 ltac:(condz).              (* [comment removed for export] *)
      an F_828b8 D_828b8.                              (* [comment removed for export] *)
      an F_828bc D_828bc.                              (* [comment removed for export] *)
      ab_ft F_828c0 D_828c0 ltac:(condz).              (* [comment removed for export] *)
      av F_828c4 D_828c4 (Z_to_bv 64 (U size + 4096)) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_add in G in change_no_check G' end); unorm; f_equal; lia).   (* [comment removed for export] *)
      av F_828c8 D_828c8 (Z_to_bv 64 (2 ^ 64 - 2 ^ 12)) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_sub in G in change_no_check G' end); unorm; apply bv_eq; vm_compute; reflexivity).   (* [comment removed for export] *)
      av F_828cc D_828cc (Z_to_bv 64 (U size + 4095)) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_addi in G in change_no_check G' end); unorm; f_equal; lia).   (* [comment removed for export] *)
      av_and F_828d0 D_828d0 size
        ltac:(rewrite v_and_m4k; unorm; replace (U size + 4095 - (U size + 4095) mod 4096)%Z with (U size) by (Z.div_mod_to_equations; lia); apply Z_to_bv_bv_unsigned).   (* [comment removed for export] *)
      an F_828d4 D_828d4.                              (* [comment removed for export] *)
      fsw F_828d8 D_828d8 (at_ sp (-44)).              (* [comment removed for export] *)
      an F_828dc D_828dc.                              (* [comment removed for export] *)
      an F_828e0 D_828e0.                              (* [comment removed for export] *)
      an F_828e4 D_828e4.                              (* [comment removed for export] *)
      an F_828e8 D_828e8.                              (* [comment removed for export] *)
      an F_83554 D_83554.                              (* [comment removed for export] *)
      fsd F_83558 D_83558 (at_ sp (-56)).              (* [comment removed for export] *)
      fsd F_8355c D_8355c (at_ sp (-64)).              (* [comment removed for export] *)
      fsd F_83560 D_83560 (at_ sp (-72)).              (* [comment removed for export] *)
      fsd F_83564 D_83564 (at_ sp (-80)).              (* [comment removed for export] *)
      fsd F_83568 D_83568 (at_ sp (-88)).              (* [comment removed for export] *)
      fsd F_8356c D_8356c (at_ sp (-96)).              (* [comment removed for export] *)
      fsd F_83570 D_83570 (at_ sp (-104)).             (* [comment removed for export] *)
      change (wbytes _ _ _) with M1.
      an F_83574 D_83574.                              (* [comment removed for export] *)
      an F_83578 D_83578.                              (* [comment removed for export] *)
      ab_ft F_8357c D_8357c ltac:(condz).              (* [comment removed for export] *)
      an F_83580 D_83580.                              (* [comment removed for export] *)
      an F_83584 D_83584.                              (* [comment removed for export] *)
      cld8 F_83588 D_83588 (Z_to_bv 64 CF) Rgcf.       (* [comment removed for export] *)
      clbu F_8358c D_8358c (Z_to_bv 8 0) Rdpm.         (* [comment removed for export] *)
      an F_83590 D_83590.                              (* [comment removed for export] *)
      ab_tk F_83594 D_83594 ltac:(condz).              (* [comment removed for export] *)
      an F_836a4 D_836a4.                              (* [comment removed for export] *)
      fld F_836a8 D_836a8 (Z_to_bv 64 0x828ec).        (* [comment removed for export] *)
      fld F_836ac D_836ac raw.                         (* [comment removed for export] *)
      fld F_836b0 D_836b0 name.                        (* [comment removed for export] *)
      fld F_836b4 D_836b4 size.                        (* [comment removed for export] *)
      fld F_836b8 D_836b8 (Z_to_bv 64 PGP).            (* [comment removed for export] *)
      fld F_836bc D_836bc s4v.                         (* [comment removed for export] *)
      fld F_836c0 D_836c0 s5v.                         (* [comment removed for export] *)
      an F_836c4 D_836c4.                              (* [comment removed for export] *)
      rt F_836c8 D_836c8.                              (* [comment removed for export] *)
      chain_step; [reflexivity
        | eapply step_lw with (bs := LE4 34) (v := Z_to_bv 64 34);
          [exact F_828ec | reflexivity | exact D_828ec
          | gres; rwH; imm_norm; rewrite ?at_addi; zlit_at; (lazymatch goal with |- ?G => let G' := eval unfold mo_m1 in G in change_no_check G' end);
            repeat (rewrite wc_rdn_wbytes_out3; [ | rd8_side ]);
            apply rdn_wbytes_hit4; (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_ulia
          | reflexivity]
        | step_simpl]; rewrite (v_lw_small 34) by lia; vn.   (* [comment removed for export] *)
      an F_828f0 D_828f0.                              (* [comment removed for export] *)
      an F_828f4 D_828f4.                              (* [comment removed for export] *)
      an F_828f8 D_828f8.                              (* [comment removed for export] *)
      an F_828fc D_828fc.                              (* [comment removed for export] *)
      an F_82900 D_82900.                              (* [comment removed for export] *)
      an F_82904 D_82904.                              (* [comment removed for export] *)
      an F_811a8 D_811a8.                              (* [comment removed for export] *)
      wd_refl.
    - post. (lazymatch goal with |- ?G => let G' := eval unfold mo_clob in G in change_no_check G' end). ra_solve.
  Qed.

  Lemma mo_m1_outside : forall x : word, (U x < U sp - 320 \/ U sp <= U x)%Z -> M1 x = mem x.
  Proof using Hsp.
    intros x Hx. pose proof (u64_range sp) as Hspr. (lazymatch goal with |- ?G => let G' := eval unfold mo_m1 in G in change_no_check G' end).
    repeat (rewrite wbytes_outside; [ | rewrite length_N_to_le_bytes, at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite length_N_to_le_bytes, at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia]).
    reflexivity.
  Qed.
  Lemma mo_m1_grows : mem_grows mem M1.
  Proof using. (lazymatch goal with |- ?G => let G' := eval unfold mo_m1 in G in change_no_check G' end). repeat (eapply mem_grows_trans; [|apply wbytes_grows]). apply mem_grows_refl. Qed.
  Lemma mo_m1_slots : forall (k : Z) (v : word),
    In (k, v) [(-8, ra); (-16, s0v); (-24, s1v); (-32, s2v); (-40, s3v)]%Z -> rdn BSEGS M1 (at_ sp k) 8 = Some (LE8 v).
  Proof using Hsp.
    intros k v Hin. pose proof (u64_range sp) as Hspr. (lazymatch goal with |- ?G => let G' := eval unfold mo_m1 in G in change_no_check G' end). cbn [In] in Hin.
    repeat (destruct Hin as [E|Hin]; [injection E as <- <-; rd8_chain|]). destruct Hin.
  Qed.
End MOPRE.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section MOPOST.
  Variables (M2 rom : word -> option byte) (sp ra s0v s1v s2v s3v size : word) (CF : Z).
  Variable regs : bvmap 5 word.
  Hypothesis H1 : getr regs 1 = Z_to_bv 64 0x82908.
  Hypothesis H2 : getr regs 2 = at_ sp (-48).
  Hypothesis H18 : getr regs 18 = size.
  Hypothesis Hsp : (2 ^ 24 <= U sp /\ U sp + 16 <= 2 ^ 47)%Z.
  Hypothesis Hret : ret_ok ra.
  Hypothesis HCF : (AIMGLO <= CF /\ CF + 264 <= AIMGHI)%Z.
  Hypothesis Hsok : store_ok BSEGS M2 (at_ sp (-48)) 4 = true.
  Hypothesis S_ra : rdn BSEGS M2 (at_ sp (-8)) 8 = Some (LE8 ra).
  Hypothesis S_s0 : rdn BSEGS M2 (at_ sp (-16)) 8 = Some (LE8 s0v).
  Hypothesis S_s1 : rdn BSEGS M2 (at_ sp (-24)) 8 = Some (LE8 s1v).
  Hypothesis S_s2 : rdn BSEGS M2 (at_ sp (-32)) 8 = Some (LE8 s2v).
  Hypothesis S_s3 : rdn BSEGS M2 (at_ sp (-40)) 8 = Some (LE8 s3v).

  Definition mo_ret (r : bvmap 5 word) (res : word) : Prop :=
    getr r 10 = res /\ getr r 2 = sp /\ getr r 1 = ra /\ getr r 8 = s0v /\ getr r 9 = s1v /\ getr r 18 = s2v /\ getr r 19 = s3v
    /\ regs_agree (fun i : reg => In i mo_clob) regs r.

  (* [comment removed for export] *)
  Section OK.
    Variable map : word.
    Hypothesis H10 : getr regs 10 = map.
    Hypothesis Hmap : (U map < 2 ^ 63)%Z.
    Hypothesis Rgcf : rdn BSEGS M2 (Z_to_bv 64 0x105f08) 8 = Some (LE8 (Z_to_bv 64 CF)).
    Hypothesis Rlim : rdn BSEGS M2 (Z_to_bv 64 (CF + 144)) 8 = Some (LE8 (Z_to_bv 64 0)).
    Lemma mo_ok :
      exists r, msteps BSEGS (mkst regs (0x811b0 : word) M2 rom)
                             (mkst r ra (wbytes M2 (at_ sp (-48)) (LE4 0xffffffffaaaaaaaa)) rom) /\ mo_ret r map.
    Proof using Rlim Rgcf Hmap H10 S_s3 S_s2 S_s1 S_s0 S_ra Hsok HCF Hret Hsp H18 H2 H1 CF size.
      (lazymatch goal with |- ?G => let G' := eval unfold mo_ret in G in change_no_check G' end). pose proof (u64_range sp) as Hspr. pose proof (u64_range map) as Har.
      wd_eexists. split.
      - rt F_811b0 D_811b0.                            (* [comment removed for export] *)
        an F_82908 D_82908.                            (* [comment removed for export] *)
        an F_8290c D_8290c.                            (* [comment removed for export] *)
        an F_82910 D_82910.                            (* [comment removed for export] *)
        an F_81188 D_81188.                            (* [comment removed for export] *)
        an F_8118c D_8118c.                            (* [comment removed for export] *)
        ab_tk F_81190 D_81190 ltac:(condz).            (* [comment removed for export] *)
        an F_811a0 D_811a0. sltu0.                     (* [comment removed for export] *)
        rt F_811a4 D_811a4.                            (* [comment removed for export] *)
        an F_82914 D_82914.                            (* [comment removed for export] *)
        an F_82918 D_82918.                            (* [comment removed for export] *)
        fsw F_8291c D_8291c (at_ sp (-48)).            (* [comment removed for export] *)
        an F_82920 D_82920.                            (* [comment removed for export] *)
        an F_82924 D_82924.                            (* [comment removed for export] *)
        an F_82928 D_82928.                            (* [comment removed for export] *)
        an F_81188 D_81188.                            (* [comment removed for export] *)
        an F_8118c D_8118c.                            (* [comment removed for export] *)
        ab_tk F_81190 D_81190 ltac:(condz).            (* [comment removed for export] *)
        an F_811a0 D_811a0. sltu0.                     (* [comment removed for export] *)
        rt F_811a4 D_811a4.                            (* [comment removed for export] *)
        ab_ft F_8292c D_8292c ltac:(condz).            (* [comment removed for export] *)
        an F_82930 D_82930.                            (* [comment removed for export] *)
        an F_82934 D_82934.                            (* [comment removed for export] *)
        an F_7d08c D_7d08c.                            (* [comment removed for export] *)
        cld8 F_7d090 D_7d090 (Z_to_bv 64 CF) Rgcf.     (* [comment removed for export] *)
        cld8 F_7d094 D_7d094 (Z_to_bv 64 0) Rlim.      (* [comment removed for export] *)
        ab_tk F_7d098 D_7d098 ltac:(condz).            (* [comment removed for export] *)
        rt F_7d0b4 D_7d0b4.                            (* [comment removed for export] *)
        an F_82938 D_82938.                            (* [comment removed for export] *)
        cld8 F_8293c D_8293c ra S_ra.                  (* [comment removed for export] *)
        cld8 F_82940 D_82940 s0v S_s0.                 (* [comment removed for export] *)
        cld8 F_82944 D_82944 s1v S_s1.                 (* [comment removed for export] *)
        cld8 F_82948 D_82948 s2v S_s2.                 (* [comment removed for export] *)
        cld8 F_8294c D_8294c s3v S_s3.                 (* [comment removed for export] *)
        an F_82950 D_82950.                            (* [comment removed for export] *)
        aret F_82954 D_82954 ra.                       (* [comment removed for export] *)
        wd_refl.
      - post. (lazymatch goal with |- ?G => let G' := eval unfold mo_clob in G in change_no_check G' end). ra_solve.
    Qed.
  End OK.

  (* [comment removed for export] *)
  Section DIE.
    Hypothesis H10 : getr regs 10 = Z_to_bv 64 (2 ^ 64 - 12).
    Hypothesis Hstk2 : store_ok BSEGS M2 (at_ sp (-96)) 48 = true.
    Hypothesis Rdie1 : rdn BSEGS M2 (Z_to_bv 64 0x105f58) 8 = Some (LE8 (Z_to_bv 64 1)).
    Hypothesis Rdie2 : rdn BSEGS M2 (Z_to_bv 64 0x19fcdc) 4 = Some (LE4 0).
    Lemma mo_die :
      exists r M', msteps BSEGS (mkst regs (0x811b0 : word) M2 rom) (mkst r (0x7ca24 : word) M' rom).
    Proof using Rdie2 Rdie1 Hstk2 H10 Hsok Hsp H18 H2 H1 size sp.
      pose proof (u64_range sp) as Hspr.
      wd_eexists. wd_eexists.
      rt F_811b0 D_811b0.                            (* [comment removed for export] *)
      an F_82908 D_82908.                            (* [comment removed for export] *)
      an F_8290c D_8290c.                            (* [comment removed for export] *)
      an F_82910 D_82910.                            (* [comment removed for export] *)
      an F_81188 D_81188.                            (* [comment removed for export] *)
      an F_8118c D_8118c.                            (* [comment removed for export] *)
      ab_ft F_81190 D_81190 ltac:(condz).            (* [comment removed for export] *)
      ab_tk F_81194 D_81194 ltac:(condz).            (* [comment removed for export] *)
      an F_811a0 D_811a0.                            (* [comment removed for export] *)
      rt F_811a4 D_811a4.                            (* [comment removed for export] *)
      an F_82914 D_82914.                            (* [comment removed for export] *)
      an F_82918 D_82918.                            (* [comment removed for export] *)
      fsw F_8291c D_8291c (at_ sp (-48)).            (* [comment removed for export] *)
      an F_82920 D_82920.                            (* [comment removed for export] *)
      an F_82924 D_82924.                            (* [comment removed for export] *)
      an F_82928 D_82928.                            (* [comment removed for export] *)
      an F_81188 D_81188.                            (* [comment removed for export] *)
      an F_8118c D_8118c.                            (* [comment removed for export] *)
      ab_ft F_81190 D_81190 ltac:(condz).            (* [comment removed for export] *)
      ab_ft F_81194 D_81194 ltac:(condz).            (* [comment removed for export] *)
      an F_81198 D_81198.                            (* [comment removed for export] *)
      fsw F_8119c D_8119c (at_ sp (-48)).            (* [comment removed for export] *)
      an F_811a0 D_811a0.                            (* [comment removed for export] *)
      rt F_811a4 D_811a4.                            (* [comment removed for export] *)
      ab_tk F_8292c D_8292c ltac:(condz).            (* [comment removed for export] *)
      chain_step; [reflexivity
        | eapply step_lw with (bs := LE4 12) (v := Z_to_bv 64 12);
          [exact F_82968 | reflexivity | exact D_82968
          | gres; rwH; imm_norm; rewrite ?at_addi; zlit_at;
            apply rdn_wbytes_hit4; (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_ulia
          | reflexivity]
        | step_simpl]; rewrite (v_lw_small 12) by lia; vn.   (* [comment removed for export] *)
      an F_8296c D_8296c.                            (* [comment removed for export] *)
      an F_82970 D_82970.                            (* [comment removed for export] *)
      an F_82974 D_82974.                            (* [comment removed for export] *)
      an F_82978 D_82978.                            (* [comment removed for export] *)
      an F_8297c D_8297c.                            (* [comment removed for export] *)
      an F_82980 D_82980.                            (* [comment removed for export] *)
      an F_7c9f4 D_7c9f4.                            (* [comment removed for export] *)
      fsd F_7c9f8 D_7c9f8 (at_ sp (-56)).            (* [comment removed for export] *)
      fsd F_7c9fc D_7c9fc (at_ sp (-64)).            (* [comment removed for export] *)
      fsd F_7ca00 D_7ca00 (at_ sp (-72)).            (* [comment removed for export] *)
      fsd F_7ca04 D_7ca04 (at_ sp (-80)).            (* [comment removed for export] *)
      fsd F_7ca08 D_7ca08 (at_ sp (-88)).            (* [comment removed for export] *)
      an F_7ca0c D_7ca0c.                            (* [comment removed for export] *)
      cld8 F_7ca10 D_7ca10 (Z_to_bv 64 1) Rdie1.     (* [comment removed for export] *)
      ab_ft F_7ca14 D_7ca14 ltac:(condz).            (* [comment removed for export] *)
      an F_7ca18 D_7ca18.                            (* [comment removed for export] *)
      clw F_7ca1c D_7ca1c (LE4 0) (Z_to_bv 64 0) Rdie2 (eq_refl : bytes_le_to_Z (LE4 0) = U (Z_to_bv 64 0)).   (* [comment removed for export] *)
      try (rewrite (v_lw_small 0) by lia).
      ab_ft F_7ca20 D_7ca20 ltac:(condz).            (* [comment removed for export] *)
      wd_refl.
    Qed.
  End DIE.
End MOPOST.
End FPGen.
End BoDepotMod.
Module BoDepotModK.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import Stdlib.Logic.FunctionalExtensionality.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mprotect.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.DivergeSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.SpinAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes.AgentNodes OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocSim OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys6.MhKSys OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsK OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys6.AsKSys OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys6.AsKSys2 OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsRtK OSSVerify.Proofs.glaze.binary_reflection.lib.Common.BackingAlgebra OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys6.AsanNodesLibE OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8m BoAllocM8k BoAllocM9m BoAllocM9k OSSVerify.Proofs.glaze.binary_reflection.lib.BoDrvIStrlen.Bo_code_80b0c_815a0 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8m.Bo_code_7c9f4_7cb58 BoDepotMod.
Import OSSVerify.glaze.binary_reflection.images.AsanUbsan.
Import ListNotations.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation BSEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).
#[local] Abbreviation LE4 z := (word_to_le_bytes 4 (Z_to_bv 64 z)).
#[local] Abbreviation U := bv_unsigned.

Section FPGen1.
Context {fx : FPState}.

Definition mo_ret' (regs r : bvmap 5 word) (sp ra s0v s1v s2v s3v res : word) : Prop :=
  getr r 10 = res /\ getr r 2 = sp /\ getr r 1 = ra /\ getr r 8 = s0v /\ getr r 9 = s1v /\ getr r 18 = s2v /\ getr r 19 = s3v
  /\ regs_agree (fun i : reg => In i mo_clob) regs r.

(* [comment removed for export] *)
Lemma mo_spin : forall (r : bvmap 5 word) (M rom : word -> option byte) (model : Model),
  to_spin BSEGS (mkst r (0x7ca24%bv : word) M rom) model.
Proof using.
  intros r M rom model.
  apply (ts_spin_of_step_j BSEGS (mkst r (0x7ca24%bv : word) M rom) model W_7ca24 0 0 4%Z);
    [reflexivity | exact F_7ca24 | reflexivity | exact D_7ca24 | reflexivity | reflexivity].
Qed.

Section MOK.
  Variable Hd : word -> bool.
  Hypothesis HOFFSEG : H_off_segments BSEGS Hd.
  Hypothesis WX : wx_segs_nowrap BSEGS.

  Theorem mo_katD :
    forall (A : list (Z * Z)) regs (mem rom : word -> option byte) (model : Model)
           (sp ra s0v s1v s2v s3v s4v s5v size name raw : word) (PGP CF : Z) (Q : config -> Prop)
           (GRANT : Model -> word -> Prop) (MOK : Model -> word -> Model),
    let M1 := mo_m1 mem sp ra s0v s1v s2v s3v s4v s5v size name raw PGP in
    let ENOMEMw : word := Z_to_bv 64 (2 ^ 64 - 12) in
    let SCR := LE4 0xffffffffaaaaaaaa in
    getr regs 1 = ra -> getr regs 2 = sp -> getr regs 10 = size -> getr regs 11 = name -> getr regs 12 = raw ->
    getr regs 8 = s0v -> getr regs 9 = s1v -> getr regs 18 = s2v -> getr regs 19 = s3v -> getr regs 20 = s4v -> getr regs 21 = s5v ->
    (2 ^ 24 <= U sp /\ U sp + 16 <= 2 ^ 47) -> ret_ok ra ->
    (U size mod 4096 = 0 /\ U size + 4096 < 2 ^ 63) -> U name <> 0 ->
    (AIMGLO <= PGP /\ PGP + 8 <= AIMGHI) -> (AIMGLO <= CF /\ CF + 264 <= AIMGHI) ->
    store_ok BSEGS mem (at_ sp (-320)) 320 = true ->
    rdn BSEGS mem (Z_to_bv 64 0x105ef8) 8 = Some (LE8 (Z_to_bv 64 PGP)) ->
    rdn BSEGS mem (Z_to_bv 64 PGP) 8 = Some (LE8 (Z_to_bv 64 4096)) ->
    rdn BSEGS mem (Z_to_bv 64 0x105f08) 8 = Some (LE8 (Z_to_bv 64 CF)) ->
    rdn BSEGS mem (Z_to_bv 64 (CF + 260)) 1 = Some [Z_to_bv 8 0] ->
    rdn BSEGS mem (Z_to_bv 64 (CF + 144)) 8 = Some (LE8 (Z_to_bv 64 0)) ->
    rdn BSEGS mem (Z_to_bv 64 0x105f58) 8 = Some (LE8 (Z_to_bv 64 1)) ->
    rdn BSEGS mem (Z_to_bv 64 0x19fcdc) 4 = Some (LE4 0) ->
    hid_off Hd 0x105ef8 8 -> hid_off Hd PGP 8 -> hid_off Hd 0x105f08 8 -> hid_off Hd (CF + 260) 1 -> hid_off Hd (CF + 144) 8 ->
    hid_off Hd 0x105f58 8 -> hid_off Hd 0x19fcdc 4 ->
    hid_off Hd (U sp - 320) 320 ->
    m_halted model = None -> lazy_cover Hd (m_vm_lazy model) A -> A_wf A -> MInv A model ->
    (* [comment removed for export] *)
    (forall mdlm (a : word), same_but_materialized model mdlm -> GRANT mdlm a ->
        AIMGHI <= U a /\ U a + U size < 2 ^ 63 /\ (U a + U size <= U sp - 320 \/ U sp <= U a)) ->
    (* [comment removed for export] *)
    (forall mdlm (r1 : bvmap 5 word), same_but_materialized model mdlm -> MInv A mdlm -> m_halted mdlm = None ->
        getr r1 10 = Z_to_bv 64 0 -> getr r1 11 = size -> getr r1 12 = Z_to_bv 64 3 -> getr r1 13 = Z_to_bv 64 34 ->
        getr r1 14 = Z_to_bv 64 (2 ^ 64 - 1) -> getr r1 15 = Z_to_bv 64 0 ->
        forall Q' : config -> Prop,
          (forall a : word, GRANT mdlm a ->
              katD BSEGS (mkCfg (mkst (regupd r1 10 a) (0x811b0 : word) (zfill a size M1) rom) (MOK mdlm a)) Q') ->
          doomed BSEGS (mkCfg (mkst (regupd r1 10 ENOMEMw) (0x811b0 : word) M1 rom) mdlm) ->
          katD BSEGS (mkCfg (epend r1 (0x811ac : word) M1 rom (Z_to_bv 64 222)) mdlm) Q') ->
    (* [comment removed for export] *)
    (forall mdlm (a : word), same_but_materialized model mdlm -> MInv A mdlm -> GRANT mdlm a ->
        m_halted (MOK mdlm a) = None /\ lazy_cover Hd (m_vm_lazy (MOK mdlm a)) A /\ MInv A (MOK mdlm a)) ->
    (* [comment removed for export] *)
    (forall (a : word) (r' : bvmap 5 word) mdlm mdl4,
        same_but_materialized model mdlm -> MInv A mdlm -> GRANT mdlm a -> same_but_materialized (MOK mdlm a) mdl4 -> MInv A mdl4 ->
        mo_ret' regs r' sp ra s0v s1v s2v s3v a ->
        katD BSEGS (mkCfg (mkst r' ra (wbytes (zfill a size M1) (at_ sp (-48)) SCR) rom) mdl4) Q) ->
    katD BSEGS (mkCfg (mkst regs (0x82878 : word) mem rom) model) Q.
  Proof using WX HOFFSEG.
    intros A regs mem rom model sp ra s0v s1v s2v s3v s4v s5v size name raw PGP CF Q GRANT MOK M1 ENOMEMw SCR
           H1 H2 H10 H11 H12 H8 H9 H18 H19 H20 H21 Hsp Hret Hsize Hname HPGP HCF Hstk Rgpg Rpg Rgcf Rdpm Rlim Rd1 Rd2
           HDgpg HDpg HDgcf HDdpm HDlim HDd1 HDd2 HDscr HALT LC AWF MI SEP NODE CHILD CONTOK.
    pose proof (u64_range sp) as Hspr. pose proof (u64_range size) as Hszr.
    destruct HPGP as [PG1 PG2]. destruct HCF as [CF1 CF2].
    assert (Hstk' : store_ok BSEGS (mrestrict Hd mem) (at_ sp (-320)) 320 = true).
    { rewrite store_ok_mrestrict; [exact Hstk | first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); exact HDscr]. }
    assert (CELLR : forall (c : Z) (k : nat) v, 0 <= c < 2 ^ 32 -> Z.of_nat k <= 8 -> hid_off Hd c (Z.of_nat k) ->
               rdn BSEGS mem (Z_to_bv 64 c) k = Some v -> rdn BSEGS (mrestrict Hd mem) (Z_to_bv 64 c) k = Some v).
    { intros c k v Hc0 Hc1 Hh Hr. rewrite rdn_mrestrict; [exact Hr | first [ solve [ wd_unorm1; wd_zofnat; lia ] | rewrite u_Z2bv by lia; lia ] | rewrite u_Z2bv by lia; exact Hh]. }
    destruct (mo_pre (mrestrict Hd mem) rom sp ra s0v s1v s2v s3v s4v s5v size name raw PGP CF regs
                H1 H2 H10 H11 H12 H8 H9 H18 H19 H20 H21 Hsp Hsize Hname (conj PG1 PG2) (conj CF1 CF2) Hstk'
                (CELLR 0x105ef8 8%nat _ ltac:(lia) ltac:((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia) HDgpg Rgpg) (CELLR PGP 8%nat _ ltac:(lia) ltac:((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia) HDpg Rpg)
                (CELLR 0x105f08 8%nat _ ltac:(lia) ltac:((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia) HDgcf Rgcf) (CELLR (CF + 260) 1%nat _ ltac:(lia) ltac:((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia) HDdpm Rdpm))
      as (r1 & RUN1 & B1 & B2 & B8 & B9 & B18 & B19 & B10 & B11 & B12 & B13 & B14 & B15 & B17 & AG1).
    assert (EM1 : mo_m1 (mrestrict Hd mem) sp ra s0v s1v s2v s3v s4v s5v size name raw PGP = mrestrict Hd M1).
    { (lazymatch goal with |- ?G => let G' := eval unfold M1, mo_m1 in G in change_no_check G' end).
      rewrite !wbytes_mrestrict; [reflexivity | | | | | | | | | | | | | | | | | | | | | | | | | |];
        wd_lenlit; rewrite ?length_N_to_le_bytes, ?at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn [length Z.of_nat Pos.of_succ_nat Pos.succ Pos.to_nat] in G in change_no_check G' end); first [lia | intros x Hx; apply HDscr; lia]. }
    rewrite EM1 in RUN1.
    assert (M1hid : forall a : word, Hd a = true -> M1 a = mem a).
    { intros a Ha. (lazymatch goal with |- ?G => let G' := eval unfold M1 in G in change_no_check G' end). apply (mo_m1_outside mem sp ra s0v s1v s2v s3v s4v s5v size name raw PGP Hsp).
      destruct (Z_lt_le_dec (U a) (U sp - 320)) as [C1|C1]; [left; exact C1|].
      destruct (Z_lt_le_dec (U a) (U sp)) as [C2|C2]; [| right; exact C2].
      exfalso. rewrite (HDscr a) in Ha by lia. discriminate Ha. }
    apply (katD_msteps_acct BSEGS Hd HOFFSEG WX A (mkst regs (0x82878 : word) mem rom)
             (mkst r1 (0x811ac : word) (mrestrict Hd M1) rom) model Q LC AWF MI HALT).
    { rewrite mk_restrict_mkst. exact RUN1. }
    intros mdlm MIm SBMm HC1. rewrite mk_unrestrict_mkst.
    replace (RiscvSemantics.ms_mem (mkst regs (0x82878 : word) mem rom)) with mem by reflexivity.
    rewrite (mk_munrestrict_same Hd mem M1 M1hid).
    pose proof (same_but_materialized_frame model mdlm SBMm) as FRm.
    assert (HALTm : m_halted mdlm = None) by (destruct FRm as (_&_&_&_&_&_&_&_&_&_&_&_&Hh&_); rewrite Hh; exact HALT).
    apply (katD_ecall BSEGS r1 (0x811ac : word) M1 rom mdlm W_811ac Q HALTm F_811ac E_811ac).
    rewrite B17.
    assert (POSTF : forall MZ : word -> option byte,
               (forall x : word, U sp - 320 <= U x < U sp -> MZ x = M1 x) ->
               store_ok BSEGS (mrestrict Hd MZ) (at_ sp (-48)) 4 = true
               /\ store_ok BSEGS (mrestrict Hd MZ) (at_ sp (-96)) 48 = true
               /\ (forall (k : Z) (v : word), In (k, v) [(-8, ra); (-16, s0v); (-24, s1v); (-32, s2v); (-40, s3v)] ->
                      rdn BSEGS (mrestrict Hd MZ) (at_ sp k) 8 = Some (LE8 v))).
    { intros MZ EZ.
      assert (SOKZ : forall (o : Z) (n : nat), -320 <= o -> o + Z.of_nat n <= 0 -> store_ok BSEGS (mrestrict Hd MZ) (at_ sp o) n = true).
      { intros o n Ho1 Ho2.
        rewrite store_ok_mrestrict; [| first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ] | rewrite at_u by lia; intros x Hx; apply HDscr; lia].
        rewrite (store_ok_ext BSEGS n M1 MZ); [| first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ] | intros x Hx; apply EZ; rewrite at_u in Hx by lia; lia].
        eapply store_ok_mono; [apply mo_m1_grows|].
        eapply (store_ok_sub BSEGS mem (at_ sp (-320)) _ 320); [first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | exact Hstk | first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite !at_u by lia; lia ] | first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite !at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ]]. }
      split; [apply SOKZ; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia|]. split; [apply SOKZ; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia|].
      intros k v Hin.
      assert (Hk : -40 <= k <= -8) by (cbn [In] in Hin; repeat (destruct Hin as [E|Hin]; [injection E as <- <-; lia|]); destruct Hin).
      rewrite rdn_mrestrict; [| first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); intros x Hx; apply HDscr; lia].
      rewrite <- (mo_m1_slots mem sp ra s0v s1v s2v s3v s4v s5v size name raw PGP Hsp k v Hin). fold M1.
      apply rdn_ext; [first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | intros x Hx; apply EZ; rewrite at_u in Hx by lia; cbn in Hx; lia]. }
    assert (Q1 : forall v : word, getr (regupd r1 10 v) 1 = Z_to_bv 64 0x82908) by (intros v; rewrite getr_other by (intros E; discriminate E); exact B1).
    assert (Q2 : forall v : word, getr (regupd r1 10 v) 2 = at_ sp (-48)) by (intros v; rewrite getr_other by (intros E; discriminate E); exact B2).
    assert (Q18 : forall v : word, getr (regupd r1 10 v) 18 = size) by (intros v; rewrite getr_other by (intros E; discriminate E); exact B18).
    assert (Q10 : forall v : word, getr (regupd r1 10 v) 10 = v) by (intros v; rewrite getr_same by (intros E; discriminate E); reflexivity).
    assert (AGC : forall (v : word) (r2 : bvmap 5 word), regs_agree (fun i : reg => In i mo_clob) (regupd r1 10 v) r2 ->
                    regs_agree (fun i : reg => In i mo_clob) regs r2).
    { intros v r2 AG2 x Hx. rewrite (AG2 x Hx).
      assert (NE10 : x <> 10%bv) by (intros ->; apply Hx; (lazymatch goal with |- ?G => let G' := eval unfold mo_clob in G in change_no_check G' end); (lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); tauto).
      rewrite getr_other by (intros E; apply NE10; exact E). apply AG1. exact Hx. }
    assert (L4a : Z.of_nat (length SCR) = 4) by ((lazymatch goal with |- ?G => let G' := eval unfold SCR in G in change_no_check G' end); rewrite length_N_to_le_bytes; reflexivity).
    assert (HIDW : forall (MM : word -> option byte) bs (a : word), Hd a = true -> Z.of_nat (length bs) = 4 -> wbytes MM (at_ sp (-48)) bs a = MM a).
    { intros MM bs a Ha Hl.
      destruct (Z_lt_le_dec (U a) (U sp - 48)) as [C|C]; [apply wbytes_below; rewrite ?Hl, ?at_u by lia; lia|].
      destruct (Z_lt_le_dec (U a) (U sp - 44)) as [C'|C']; [exfalso; rewrite (HDscr a) in Ha by lia; discriminate Ha|].
      apply wbytes_above. rewrite Hl, at_u by lia. lia. }
    apply (NODE mdlm r1 SBMm MIm HALTm B10 B11 B12 B13 B14 B15 Q).
    - (* [comment removed for export] *)
      intros a GR. destruct (SEP mdlm a SBMm GR) as (SL1 & SL2 & SL3). pose proof (u64_range a) as Har.
      destruct (CHILD mdlm a SBMm MIm GR) as (HOK1 & HOK2 & HOK3).
      set (MZ := zfill a size M1).
      assert (EZ : forall x : word, U sp - 320 <= U x < U sp -> MZ x = M1 x) by (intros x Hx; (lazymatch goal with |- ?G => let G' := eval unfold MZ in G in change_no_check G' end); apply zfill_out; lia).
      destruct (POSTF MZ EZ) as (SOKZ & _ & SLZ).
      assert (CELLZ : forall (c : Z) (k : nat) v, 0 <= c -> c + Z.of_nat k <= AIMGHI -> hid_off Hd c (Z.of_nat k) ->
                 rdn BSEGS mem (Z_to_bv 64 c) k = Some v -> rdn BSEGS (mrestrict Hd MZ) (Z_to_bv 64 c) k = Some v).
      { intros c k v Hc0 Hc1 Hh Hr. rewrite rdn_mrestrict; [| first [ solve [ wd_unorm1; wd_zofnat; lia ] | rewrite u_Z2bv by lia; lia ] | rewrite u_Z2bv by lia; exact Hh].
        rewrite <- Hr. apply rdn_ext; [first [ solve [ wd_unorm1; wd_zofnat; lia ] | rewrite u_Z2bv by lia; lia ]|]. intros x Hx. rewrite u_Z2bv in Hx by lia.
        (lazymatch goal with |- ?G => let G' := eval unfold MZ in G in change_no_check G' end). rewrite zfill_out by lia. (lazymatch goal with |- ?G => let G' := eval unfold M1 in G in change_no_check G' end). apply (mo_m1_outside mem sp ra s0v s1v s2v s3v s4v s5v size name raw PGP Hsp). left. lia. }
      destruct (mo_ok (mrestrict Hd MZ) rom sp ra s0v s1v s2v s3v size CF (regupd r1 10 a)
                  (Q1 a) (Q2 a) (Q18 a) Hsp Hret (conj CF1 CF2) SOKZ
                  (SLZ (-8) ra ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); tauto)) (SLZ (-16) s0v ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); tauto)) (SLZ (-24) s1v ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); tauto))
                  (SLZ (-32) s2v ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); tauto)) (SLZ (-40) s3v ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); tauto))
                  a (Q10 a) ltac:(lia)
                  (CELLZ 0x105f08 8%nat _ ltac:(lia) ltac:((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia) HDgcf Rgcf) (CELLZ (CF + 144) 8%nat _ ltac:(lia) ltac:((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia) HDlim Rlim))
        as (r2 & RUN2 & C10 & C2 & C1 & C8 & C9 & C18 & C19 & AG2).
      rewrite wbytes_mrestrict in RUN2; [| rewrite length_N_to_le_bytes, at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia
                                          | rewrite length_N_to_le_bytes, at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); intros x Hx; apply HDscr; lia].
      apply (katD_msteps_acct BSEGS Hd HOFFSEG WX A (mkst (regupd r1 10 a) (0x811b0 : word) MZ rom)
               (mkst r2 ra (mrestrict Hd (wbytes MZ (at_ sp (-48)) SCR)) rom) (MOK mdlm a) Q HOK2 AWF HOK3 HOK1).
      { rewrite mk_restrict_mkst. exact RUN2. }
      intros mdl4 MI4 SBM4 HC4. rewrite mk_unrestrict_mkst.
      replace (RiscvSemantics.ms_mem (mkst (regupd r1 10 a) (0x811b0 : word) MZ rom)) with MZ by reflexivity.
      rewrite (mk_munrestrict_same Hd MZ (wbytes MZ (at_ sp (-48)) SCR)).
      2:{ intros x Hx. apply HIDW; [exact Hx | exact L4a]. }
      apply (CONTOK a r2 mdlm mdl4 SBMm MIm GR SBM4 MI4).
      (lazymatch goal with |- ?G => let G' := eval unfold mo_ret' in G in change_no_check G' end). repeat (split; [assumption|]). exact (AGC a r2 AG2).
    - (* [comment removed for export] *)
      set (MZ := M1).
      assert (EZ : forall x : word, U sp - 320 <= U x < U sp -> MZ x = M1 x) by (intros x Hx; reflexivity).
      destruct (POSTF MZ EZ) as (SOKZ & SOKZ2 & _).
      assert (CELLM : forall (c : Z) (k : nat) v, 0 <= c -> c + Z.of_nat k <= AIMGHI -> hid_off Hd c (Z.of_nat k) ->
                 rdn BSEGS mem (Z_to_bv 64 c) k = Some v -> rdn BSEGS (mrestrict Hd MZ) (Z_to_bv 64 c) k = Some v).
      { intros c k v Hc0 Hc1 Hh Hr. rewrite rdn_mrestrict; [| first [ solve [ wd_unorm1; wd_zofnat; lia ] | rewrite u_Z2bv by lia; lia ] | rewrite u_Z2bv by lia; exact Hh].
        rewrite <- Hr. apply rdn_ext; [first [ solve [ wd_unorm1; wd_zofnat; lia ] | rewrite u_Z2bv by lia; lia ]|]. intros x Hx. rewrite u_Z2bv in Hx by lia.
        (lazymatch goal with |- ?G => let G' := eval unfold MZ, M1 in G in change_no_check G' end). apply (mo_m1_outside mem sp ra s0v s1v s2v s3v s4v s5v size name raw PGP Hsp). left. lia. }
      destruct (mo_die (mrestrict Hd MZ) rom sp size (regupd r1 10 ENOMEMw) (Q1 ENOMEMw) (Q2 ENOMEMw) (Q18 ENOMEMw) Hsp SOKZ (Q10 ENOMEMw) SOKZ2
                  (CELLM 0x105f58 8%nat _ ltac:(lia) ltac:((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia) HDd1 Rd1) (CELLM 0x19fcdc 4%nat _ ltac:(lia) ltac:((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia) HDd2 Rd2))
        as (r2 & M'2 & RUN2).
      apply (doomed_msteps_acct BSEGS Hd HOFFSEG WX A (mkst (regupd r1 10 ENOMEMw) (0x811b0 : word) MZ rom) (mkst r2 (0x7ca24 : word) M'2 rom) mdlm).
      { destruct FRm as (_ & _ & Hl & _). rewrite Hl. exact LC. }
      { exact AWF. } { exact MIm. } { exact HALTm. }
      { rewrite mk_restrict_mkst. exact RUN2. }
      intros mdl4 MI4 SBM4 HC4. rewrite mk_unrestrict_mkst.
      apply doomed_to_spin; [apply mo_spin|].
      pose proof (same_but_materialized_frame mdlm mdl4 SBM4) as (_&_&_&_&_&_&_&_&_&_&_&_&Hh4&_). rewrite Hh4. exact HALTm.
  Qed.
End MOK.

(* [comment removed for export] *)
Section NODEDM.
  Lemma node_dm_of_mmap_rw :
    forall (r1 : bvmap 5 word) (M1 rom : word -> option byte) (mdlm : Model) (size : word) (Q' : config -> Prop),
    m_halted mdlm = None ->
    getr r1 10 = Z_to_bv 64 0 -> getr r1 11 = size -> getr r1 12 = Z_to_bv 64 3 -> getr r1 13 = Z_to_bv 64 34 ->
    getr r1 14 = Z_to_bv 64 (2 ^ 64 - 1) -> getr r1 15 = Z_to_bv 64 0 ->
    0 < U size -> U size mod 4096 = 0 ->
    (exists a : word, grant_ok (Z_to_bv 64 0) mdlm a (U size) = true) ->
    (forall a : word, grant_ok (Z_to_bv 64 0) mdlm a (U size) = true ->
        katD BSEGS (mkCfg (mkst (regupd r1 10 a) (0x811b0 : word) (zfill a size M1) rom) (mmap_model a size mdlm)) Q') ->
    doomed BSEGS (mkCfg (mkst (regupd r1 10 (Z_to_bv 64 (2 ^ 64 - 12))) (0x811b0 : word) M1 rom) mdlm) ->
    katD BSEGS (mkCfg (epend r1 (0x811ac : word) M1 rom (Z_to_bv 64 222)) mdlm) Q'.
  Proof using.
    intros r1 M1 rom mdlm size Q' HALT B10 B11 B12 B13 B14 B15 Hsz Hszal EX KOK KKP.
    pose proof (u64_range size) as Hszr.
    set (ms := epend r1 (0x811ac%bv : word) M1 rom (Z_to_bv 64 222)).
    assert (E0 : ms_gpr ms 0 = Z_to_bv 64 0) by ((lazymatch goal with |- ?G => let G' := eval unfold ms in G in change_no_check G' end); rewrite AsKSys6.MhKSys.ms_gpr_epend0; exact B10).
    assert (E1 : ms_gpr ms 1 = size) by ((lazymatch goal with |- ?G => let G' := eval unfold ms in G in change_no_check G' end); rewrite AsKSys6.MhKSys.ms_gpr_epend1; exact B11).
    assert (PRU : page_round_up_Z (U size) = U size) by (apply page_round_up_Z_aligned; [lia | (lazymatch goal with |- ?G => let G' := eval unfold page_size in G in change_no_check G' end); exact Hszal]).
    assert (PRW : page_round_up (ms_gpr ms 1) = size).
    { (lazymatch goal with |- ?G => let G' := eval unfold page_round_up in G in change_no_check G' end). rewrite E1, PRU. apply Z_to_bv_bv_unsigned. }
    assert (ARGS : mmap_args_ok ms).
    { (lazymatch goal with |- ?G => let G' := eval unfold mmap_args_ok in G in change_no_check G' end). rewrite E1. (lazymatch goal with |- ?G => let G' := eval unfold ms in G in change_no_check G' end). rewrite AsKSys6.MhKSys.ms_gpr_epend2, AsKSys6.MhKSys.ms_gpr_epend3, AsKSys6.MhKSys.ms_gpr_epend4, AsKSys6.MhKSys.ms_gpr_epend5.
      split; [intros X; apply (f_equal bv_unsigned) in X; rewrite u_Z2bv in X by lia; lia|].
      split; [exact B12|]. split; [exact B13|]. split; [rewrite B14; apply bv_eq; reflexivity | exact B15]. }
    apply (katD_mmap_rw_dm BSEGS ms mdlm (Z_to_bv 64 222) Q' HALT eq_refl ltac:(rewrite u_Z2bv by lia; reflexivity) ARGS).
    - rewrite E0, E1, PRU. exact EX.
    - intros e He. (lazymatch goal with |- ?G => let G' := eval unfold mmrw_fail, ms in G in change_no_check G' end). rewrite AsKSys6.MhKSys.adv_set_epend.
      assert (Ee : e = ENOMEM) by (destruct He as [<-|[]]; reflexivity). subst e.
      replace (errno_ret ENOMEM) with (Z_to_bv 64 (2 ^ 64 - 12) : word) by (apply bv_eq; vm_compute; reflexivity).
      replace (v_addi (0x811ac%bv : word) 4) with (0x811b0%bv : word) by (apply bv_eq; vm_compute; reflexivity).
      exact KKP.
    - intros a Ha. rewrite E0, E1, PRU in Ha. (lazymatch goal with |- ?G => let G' := eval unfold mmrw_grant in G in change_no_check G' end). rewrite PRW. (lazymatch goal with |- ?G => let G' := eval unfold ms in G in change_no_check G' end). rewrite AsKSys6.MhKSys.adv_zeros1_epend.
      replace (v_addi (0x811ac%bv : word) 4) with (0x811b0%bv : word) by (apply bv_eq; vm_compute; reflexivity).
      exact (KOK a Ha).
  Qed.
End NODEDM.
End FPGen1.
End BoDepotModK.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap Mprotect.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocSim OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys6 OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.BackingAlgebra OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8m OSSVerify.Proofs.glaze.binary_reflection.lib.BoDrvIStrlen. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.DivergeSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.SpinAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes.AgentNodes OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocSim OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys6.MhKSys OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsK OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys6.AsKSys OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys6.AsKSys2 OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsRtK OSSVerify.Proofs.glaze.binary_reflection.lib.Common.BackingAlgebra OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys6.AsanNodesLibE OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8m BoAllocM8k BoAllocM9m BoAllocM9k BoAllocM9h OSSVerify.Proofs.glaze.binary_reflection.lib.BoDrvIStrlen.Bo_code_80b0c_815a0 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8m.Bo_code_7c9f4_7cb58 BoDepotMod BoDepotModK.
From OSSVerify.glaze.binary_reflection.images Require Import AsanUbsan.
Import ListNotations.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation BSEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).
#[local] Abbreviation LE4 z := (word_to_le_bytes 4 (Z_to_bv 64 z)).
#[local] Abbreviation U := bv_unsigned.

Section FPGen1.
Context {fx : FPState}.

Section MAPOK.
  Variable Hd : word -> bool.
  Hypothesis HOFFSEG : H_off_segments BSEGS Hd.
  Hypothesis WX : wx_segs_nowrap BSEGS.

  (* [comment removed for export] *)
  Theorem rarmapo_katD :
    forall (A : list (Z * Z)) regs (mem rom : word -> option byte) (model : Model)
           (sp ra s0v s1v s2v s3v s4v s5v addr size name : word) (PGP CF : Z) (Q : config -> Prop)
           (MOK MKP MDS : Model -> Model),
    let M1 := mfo_m1 mem sp ra s0v s1v s2v s3v s4v s5v addr size name PGP in
    let ENOMEMw : word := Z_to_bv 64 (2 ^ 64 - 12) in
    let SCR := LE4 0xffffffffaaaaaaaa in
    (* [comment removed for export] *)
    getr regs 1 = ra -> getr regs 2 = sp -> getr regs 11 = addr -> getr regs 12 = size -> getr regs 13 = name ->
    getr regs 8 = s0v -> getr regs 9 = s1v -> getr regs 18 = s2v -> getr regs 19 = s3v -> getr regs 20 = s4v -> getr regs 21 = s5v ->
    (2 ^ 24 <= U sp /\ U sp + 16 <= 2 ^ 47) -> ret_ok ra ->
    U addr mod 4096 = 0 -> (U size mod 4096 = 0 /\ U size + 4096 < 2 ^ 63) -> U name = 0 ->
    (AIMGLO <= PGP /\ PGP + 8 <= AIMGHI) -> (AIMGLO <= CF /\ CF + 264 <= AIMGHI) ->
    store_ok BSEGS mem (at_ sp (-368)) 368 = true ->
    rdn BSEGS mem (Z_to_bv 64 0x105ef8) 8 = Some (LE8 (Z_to_bv 64 PGP)) ->
    rdn BSEGS mem (Z_to_bv 64 PGP) 8 = Some (LE8 (Z_to_bv 64 4096)) ->
    rdn BSEGS mem (Z_to_bv 64 0x105f08) 8 = Some (LE8 (Z_to_bv 64 CF)) ->
    rdn BSEGS mem (Z_to_bv 64 (CF + 144)) 8 = Some (LE8 (Z_to_bv 64 0)) ->
    (* [comment removed for export] *)
    (AIMGHI <= U addr /\ U addr + U size < 2 ^ 63 /\ (U addr + U size <= U sp - 368 \/ U sp <= U addr)) ->
    (* [comment removed for export] *)
    hid_off Hd 0x105ef8 8 -> hid_off Hd PGP 8 -> hid_off Hd 0x105f08 8 -> hid_off Hd (CF + 144) 8 ->
    hid_off Hd (U sp - 368) 368 ->
    (* [comment removed for export] *)
    m_halted model = None -> lazy_cover Hd (m_vm_lazy model) A -> A_wf A -> MInv A model ->
    (* [comment removed for export] *)
    (forall mdlm (r1 : bvmap 5 word), same_but_materialized model mdlm -> MInv A mdlm -> m_halted mdlm = None ->
        getr r1 10 = addr -> getr r1 11 = size -> getr r1 12 = Z_to_bv 64 3 -> getr r1 13 = Z_to_bv 64 50 ->
        getr r1 14 = Z_to_bv 64 (2 ^ 64 - 1) -> getr r1 15 = Z_to_bv 64 0 ->
        forall Q' : config -> Prop,
          katD BSEGS (mkCfg (mkst (regupd r1 10 addr) (0x811b0 : word) (zfill addr size M1) rom) (MOK mdlm)) Q' ->
          doomed BSEGS (mkCfg (mkst (regupd r1 10 ENOMEMw) (0x811b0 : word) M1 rom) (MKP mdlm)) ->
          doomed BSEGS (mkCfg (mkst (regupd r1 10 ENOMEMw) (0x811b0 : word) (unfill addr size M1) rom) (MDS mdlm)) ->
          katD BSEGS (mkCfg (epend r1 (0x811ac : word) M1 rom (Z_to_bv 64 222)) mdlm) Q') ->
    (* [comment removed for export] *)
    (forall mdlm, same_but_materialized model mdlm -> MInv A mdlm ->
        (m_halted (MOK mdlm) = None /\ lazy_cover Hd (m_vm_lazy (MOK mdlm)) A /\ MInv A (MOK mdlm))
        /\ (m_halted (MKP mdlm) = None /\ lazy_cover Hd (m_vm_lazy (MKP mdlm)) A /\ MInv A (MKP mdlm))
        /\ (m_halted (MDS mdlm) = None /\ lazy_cover Hd (m_vm_lazy (MDS mdlm)) A /\ MInv A (MDS mdlm))) ->
    (* [comment removed for export] *)
    (forall (r' : bvmap 5 word) mdlm mdl4,
        same_but_materialized model mdlm -> MInv A mdlm -> same_but_materialized (MOK mdlm) mdl4 -> MInv A mdl4 ->
        mfi_ret regs r' sp ra s0v s1v s2v s3v s4v addr ->
        katD BSEGS (mkCfg (mkst r' ra (wbytes (zfill addr size M1) (at_ sp (-52)) SCR) rom) mdl4) Q) ->
    (* [comment removed for export] *)
    (forall (MZ : word -> option byte) (r2 : bvmap 5 word), (MZ = M1 \/ MZ = unfill addr size M1) ->
        getr r2 2 = at_ sp (-96) -> getr r2 8 = size -> getr r2 9 = Z_to_bv 64 0 -> getr r2 18 = addr -> getr r2 19 = ENOMEMw ->
        exists fx' (r3 : bvmap 5 word) (M3 : word -> option byte),
          msteps BSEGS (@mkst fx r2 (0x82fe8 : word) (mrestrict Hd (wbytes (wbytes MZ (at_ sp (-52)) SCR) (at_ sp (-52)) (LE4 12))) rom)
                       (@mkst fx' r3 (0x7ca24 : word) M3 rom)) ->
    katD BSEGS (mkCfg (mkst regs (0x8b244 : word) mem rom) model) Q.
  Proof using WX HOFFSEG.
    intros A regs mem rom model sp ra s0v s1v s2v s3v s4v s5v addr size name PGP CF Q MOK MKP MDS M1 ENOMEMw SCR
           H1 H2 H11 H12 H13 H8 H9 H18 H19 H20 H21 Hsp Hret Haddr Hsize Hname HPGP HCF Hstk Rgpg Rpg Rgcf Rlim
           Hslot HDgpg HDpg HDgcf HDlim HDscr HALT LC AWF MI NODE CHILD CONTOK DIE.
    pose proof (u64_range sp) as Hspr. pose proof (u64_range addr) as Har. pose proof (u64_range size) as Hszr.
    destruct Hslot as (SL1 & SL2 & SL3). destruct HPGP as [PG1 PG2]. destruct HCF as [CF1 CF2].
    (* [comment removed for export] *)
    assert (Hstk' : store_ok BSEGS (mrestrict Hd mem) (at_ sp (-368)) 368 = true).
    { rewrite store_ok_mrestrict; [exact Hstk | first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); exact HDscr]. }
    assert (CELLR : forall (c : Z) (k : nat) v, 0 <= c < 2 ^ 32 -> Z.of_nat k <= 8 -> hid_off Hd c (Z.of_nat k) ->
               rdn BSEGS mem (Z_to_bv 64 c) k = Some v -> rdn BSEGS (mrestrict Hd mem) (Z_to_bv 64 c) k = Some v).
    { intros c k v Hc0 Hc1 Hh Hr. rewrite rdn_mrestrict; [exact Hr | first [ solve [ wd_unorm1; wd_zofnat; lia ] | rewrite u_Z2bv by lia; lia ] | rewrite u_Z2bv by lia; exact Hh]. }
    destruct (mfo_pre (mrestrict Hd mem) rom sp ra s0v s1v s2v s3v s4v s5v addr size name PGP regs
                H1 H2 H11 H12 H13 H8 H9 H18 H19 H20 H21 Hsp Haddr Hsize Hname (conj PG1 PG2) Hstk'
                (CELLR 0x105ef8 8%nat _ ltac:(lia) ltac:((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia) HDgpg Rgpg) (CELLR PGP 8%nat _ ltac:(lia) ltac:((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia) HDpg Rpg))
      as (r1 & RUN1 & B1 & B2 & B8 & B9 & B18 & B19 & B20 & B10 & B11 & B12 & B13 & B14 & B15 & B17 & AG1).
    assert (EM1 : mfo_m1 (mrestrict Hd mem) sp ra s0v s1v s2v s3v s4v s5v addr size name PGP = mrestrict Hd M1).
    { (lazymatch goal with |- ?G => let G' := eval unfold M1, mfo_m1, mfo_m0 in G in change_no_check G' end).
      rewrite !wbytes_mrestrict; [reflexivity | | | | | | | | | | | | | | | | | | | | | | | | | | | |];
        wd_lenlit; rewrite ?length_N_to_le_bytes, ?at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn [length Z.of_nat Pos.of_succ_nat Pos.succ Pos.to_nat] in G in change_no_check G' end); first [lia | intros x Hx; apply HDscr; lia]. }
    rewrite EM1 in RUN1.
    assert (M1hid : forall a : word, Hd a = true -> M1 a = mem a).
    { intros a Ha. (lazymatch goal with |- ?G => let G' := eval unfold M1 in G in change_no_check G' end). apply (mfo_m1_outside mem sp ra s0v s1v s2v s3v s4v s5v addr size name PGP Hsp).
      destruct (Z_lt_le_dec (U a) (U sp - 368)) as [C1|C1]; [left; exact C1|].
      destruct (Z_lt_le_dec (U a) (U sp)) as [C2|C2]; [| right; exact C2].
      exfalso. rewrite (HDscr a) in Ha by lia. discriminate Ha. }
    apply (katD_msteps_acct BSEGS Hd HOFFSEG WX A (mkst regs (0x8b244 : word) mem rom)
             (mkst r1 (0x811ac : word) (mrestrict Hd M1) rom) model Q LC AWF MI HALT).
    { rewrite mk_restrict_mkst. exact RUN1. }
    intros mdlm MIm SBMm HC1. rewrite mk_unrestrict_mkst.
    replace (RiscvSemantics.ms_mem (mkst regs (0x8b244 : word) mem rom)) with mem by reflexivity.
    rewrite (mk_munrestrict_same Hd mem M1 M1hid).
    pose proof (same_but_materialized_frame model mdlm SBMm) as FRm.
    assert (HALTm : m_halted mdlm = None) by (destruct FRm as (_&_&_&_&_&_&_&_&_&_&_&_&Hh&_); rewrite Hh; exact HALT).
    (* [comment removed for export] *)
    apply (katD_ecall BSEGS r1 (0x811ac : word) M1 rom mdlm W_811ac Q HALTm F_811ac E_811ac).
    rewrite B17.
    destruct (CHILD mdlm SBMm MIm) as ((HOK1 & HOK2 & HOK3) & (HKP1 & HKP2 & HKP3) & (HDS1 & HDS2 & HDS3)).
    (* [comment removed for export] *)
    assert (POSTF : forall MZ : word -> option byte,
               (forall x : word, U sp - 368 <= U x < U sp -> MZ x = M1 x) ->
               store_ok BSEGS (mrestrict Hd MZ) (at_ sp (-52)) 4 = true
               /\ (forall (k : Z) (v : word), In (k, v) [(-8, ra); (-16, s0v); (-24, s1v); (-32, s2v); (-40, s3v); (-48, s4v)] ->
                      rdn BSEGS (mrestrict Hd MZ) (at_ sp k) 8 = Some (LE8 v))).
    { intros MZ EZ. split.
      - rewrite store_ok_mrestrict; [| first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); intros x Hx; apply HDscr; lia].
        rewrite (store_ok_ext BSEGS 4 M1 MZ); [| first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | intros x Hx; apply EZ; rewrite at_u in Hx by lia; cbn in Hx; lia].
        eapply store_ok_mono; [apply mfo_m1_grows|].
        eapply (store_ok_sub BSEGS mem (at_ sp (-368)) _ 368); [first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | exact Hstk | first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite !at_u by lia; lia ] | first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite !at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ]].
      - intros k v Hin.
        assert (Hk : -48 <= k <= -8) by (cbn [In] in Hin; repeat (destruct Hin as [E|Hin]; [injection E as <- <-; lia|]); destruct Hin).
        rewrite rdn_mrestrict; [| first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); intros x Hx; apply HDscr; lia].
        rewrite <- (mfo_m1_slots mem sp ra s0v s1v s2v s3v s4v s5v addr size name PGP Hsp k v Hin). fold M1.
        apply rdn_ext; [first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | intros x Hx; apply EZ; rewrite at_u in Hx by lia; cbn in Hx; lia]. }
    assert (Q1 : forall v : word, getr (regupd r1 10 v) 1 = Z_to_bv 64 0x82f6c) by (intros v; rewrite getr_other by (intros E; discriminate E); exact B1).
    assert (Q2 : forall v : word, getr (regupd r1 10 v) 2 = at_ sp (-96)) by (intros v; rewrite getr_other by (intros E; discriminate E); exact B2).
    assert (Q8 : forall v : word, getr (regupd r1 10 v) 8 = size) by (intros v; rewrite getr_other by (intros E; discriminate E); exact B8).
    assert (Q9 : forall v : word, getr (regupd r1 10 v) 9 = Z_to_bv 64 0) by (intros v; rewrite getr_other by (intros E; discriminate E); exact B9).
    assert (Q10 : forall v : word, getr (regupd r1 10 v) 10 = v) by (intros v; rewrite getr_same by (intros E; discriminate E); reflexivity).
    assert (AGC : forall (v : word) (r2 : bvmap 5 word), regs_agree (fun i : reg => In i mfi_clob2) (regupd r1 10 v) r2 ->
                    regs_agree (fun i : reg => In i mfi_clob2) regs r2).
    { intros v r2 AG2 x Hx. rewrite (AG2 x Hx).
      assert (NE10 : x <> 10%bv) by (intros ->; apply Hx; (lazymatch goal with |- ?G => let G' := eval unfold mfi_clob2, mfi_clob in G in change_no_check G' end); (lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); tauto).
      rewrite getr_other by (intros E; apply NE10; exact E). apply AG1. exact Hx. }
    assert (HIDW : forall (MM : word -> option byte) bs (a : word), Hd a = true -> Z.of_nat (length bs) = 4 -> wbytes MM (at_ sp (-52)) bs a = MM a).
    { intros MM bs a Ha Hl.
      destruct (Z_lt_le_dec (U a) (U sp - 52)) as [C|C]; [apply wbytes_below; rewrite ?Hl, ?at_u by lia; lia|].
      destruct (Z_lt_le_dec (U a) (U sp - 48)) as [C'|C']; [exfalso; rewrite (HDscr a) in Ha by lia; discriminate Ha|].
      apply wbytes_above. rewrite Hl, at_u by lia. lia. }
    apply (NODE mdlm r1 SBMm MIm HALTm B10 B11 B12 B13 B14 B15 Q).
    - (* [comment removed for export] *)
      set (MZ := zfill addr size M1).
      assert (EZ : forall x : word, U sp - 368 <= U x < U sp -> MZ x = M1 x) by (intros x Hx; (lazymatch goal with |- ?G => let G' := eval unfold MZ in G in change_no_check G' end); apply zfill_out; lia).
      destruct (POSTF MZ EZ) as [SOKZ SLZ].
      assert (CELLZ : forall (c : Z) (k : nat) v, 0 <= c -> c + Z.of_nat k <= AIMGHI -> hid_off Hd c (Z.of_nat k) ->
                 rdn BSEGS mem (Z_to_bv 64 c) k = Some v -> rdn BSEGS (mrestrict Hd MZ) (Z_to_bv 64 c) k = Some v).
      { intros c k v Hc0 Hc1 Hh Hr. rewrite rdn_mrestrict; [| first [ solve [ wd_unorm1; wd_zofnat; lia ] | rewrite u_Z2bv by lia; lia ] | rewrite u_Z2bv by lia; exact Hh].
        rewrite <- Hr. apply rdn_ext; [first [ solve [ wd_unorm1; wd_zofnat; lia ] | rewrite u_Z2bv by lia; lia ]|]. intros x Hx. rewrite u_Z2bv in Hx by lia.
        (lazymatch goal with |- ?G => let G' := eval unfold MZ in G in change_no_check G' end). rewrite zfill_out by lia. (lazymatch goal with |- ?G => let G' := eval unfold M1 in G in change_no_check G' end). apply (mfo_m1_outside mem sp ra s0v s1v s2v s3v s4v s5v addr size name PGP Hsp). left. lia. }
      destruct (mfo_ok (mrestrict Hd MZ) rom sp ra s0v s1v s2v s3v s4v addr size CF (regupd r1 10 addr)
                  (Q1 addr) (Q2 addr) (Q8 addr) Hsp Hret (conj CF1 CF2) SOKZ
                  (SLZ (-8) ra ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); tauto)) (SLZ (-16) s0v ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); tauto)) (SLZ (-24) s1v ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); tauto))
                  (SLZ (-32) s2v ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); tauto)) (SLZ (-40) s3v ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); tauto)) (SLZ (-48) s4v ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); tauto))
                  (Q10 addr) ltac:(lia)
                  (CELLZ 0x105f08 8%nat _ ltac:(lia) ltac:((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia) HDgcf Rgcf) (CELLZ (CF + 144) 8%nat _ ltac:(lia) ltac:((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia) HDlim Rlim))
        as (r2 & RUN2 & C10 & C2 & C1 & C8 & C9 & C18 & C19 & C20 & AG2).
      rewrite wbytes_mrestrict in RUN2; [| rewrite length_N_to_le_bytes, at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia
                                          | rewrite length_N_to_le_bytes, at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); intros x Hx; apply HDscr; lia].
      apply (katD_msteps_acct BSEGS Hd HOFFSEG WX A (mkst (regupd r1 10 addr) (0x811b0 : word) MZ rom)
               (mkst r2 ra (mrestrict Hd (wbytes MZ (at_ sp (-52)) SCR)) rom) (MOK mdlm) Q HOK2 AWF HOK3 HOK1).
      { rewrite mk_restrict_mkst. exact RUN2. }
      intros mdl4 MI4 SBM4 HC4. rewrite mk_unrestrict_mkst.
      replace (RiscvSemantics.ms_mem (mkst (regupd r1 10 addr) (0x811b0 : word) MZ rom)) with MZ by reflexivity.
      rewrite (mk_munrestrict_same Hd MZ (wbytes MZ (at_ sp (-52)) SCR)).
      2:{ intros a Ha. apply HIDW; [exact Ha | (lazymatch goal with |- ?G => let G' := eval unfold SCR in G in change_no_check G' end); rewrite length_N_to_le_bytes; reflexivity]. }
      apply (CONTOK r2 mdlm mdl4 SBMm MIm SBM4 MI4).
      (lazymatch goal with |- ?G => let G' := eval unfold mfi_ret in G in change_no_check G' end). repeat (split; [assumption|]). exact (AGC addr r2 AG2).
    - (* [comment removed for export] *)
      set (MZ := M1).
      assert (EZ : forall x : word, U sp - 368 <= U x < U sp -> MZ x = M1 x) by (intros x Hx; reflexivity).
      destruct (POSTF MZ EZ) as [SOKZ SLZ].
      destruct (mfo_fail (mrestrict Hd MZ) rom sp size (regupd r1 10 ENOMEMw) (Q1 ENOMEMw) (Q2 ENOMEMw) (Q8 ENOMEMw) (Q9 ENOMEMw) Hsp SOKZ (Q10 ENOMEMw))
        as (r2 & RUN2 & C2 & C8 & C9 & C19 & C18 & C20 & AG2).
      assert (L4a : Z.of_nat (length SCR) = 4) by ((lazymatch goal with |- ?G => let G' := eval unfold SCR in G in change_no_check G' end); rewrite length_N_to_le_bytes; reflexivity).
      assert (L4b : Z.of_nat (length (LE4 12)) = 4) by (rewrite length_N_to_le_bytes; reflexivity).
      rewrite !wbytes_mrestrict in RUN2; [| rewrite ?L4a, ?L4b, ?length_N_to_le_bytes, at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia
                                           | wd_lenlit; rewrite ?length_N_to_le_bytes, at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); intros x Hx; apply HDscr; lia
                                           | rewrite ?L4a, ?L4b, ?length_N_to_le_bytes, at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia
                                           | wd_lenlit; rewrite ?length_N_to_le_bytes, at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); intros x Hx; apply HDscr; lia].
      assert (C18' : getr r2 18 = addr) by (rewrite C18; rewrite getr_other by (intros E; discriminate E); exact B18).
      destruct (DIE MZ r2 ltac:(left; reflexivity) C2 C8 C9 C18' C19) as (fx' & r3 & M3 & RUN3).
      apply (doomed_msteps_acct BSEGS Hd HOFFSEG WX A (mkst (regupd r1 10 ENOMEMw) (0x811b0 : word) MZ rom)
               (@mkst fx' r3 (0x7ca24 : word) M3 rom) (MKP mdlm) HKP2 AWF HKP3 HKP1).
      { rewrite mk_restrict_mkst. eapply msteps_trans; [exact RUN2 | exact RUN3]. }
      intros mdl4 MI4 SBM4 HC4.
      apply doomed_to_spin; [apply mo_spin|].
      pose proof (same_but_materialized_frame (MKP mdlm) mdl4 SBM4) as (_&_&_&_&_&_&_&_&_&_&_&_&Hh4&_). rewrite Hh4. exact HKP1.
    - (* [comment removed for export] *)
      set (MZ := unfill addr size M1).
      assert (EZ : forall x : word, U sp - 368 <= U x < U sp -> MZ x = M1 x) by (intros x Hx; (lazymatch goal with |- ?G => let G' := eval unfold MZ in G in change_no_check G' end); apply unfill_out; lia).
      destruct (POSTF MZ EZ) as [SOKZ SLZ].
      destruct (mfo_fail (mrestrict Hd MZ) rom sp size (regupd r1 10 ENOMEMw) (Q1 ENOMEMw) (Q2 ENOMEMw) (Q8 ENOMEMw) (Q9 ENOMEMw) Hsp SOKZ (Q10 ENOMEMw))
        as (r2 & RUN2 & C2 & C8 & C9 & C19 & C18 & C20 & AG2).
      assert (L4a : Z.of_nat (length SCR) = 4) by ((lazymatch goal with |- ?G => let G' := eval unfold SCR in G in change_no_check G' end); rewrite length_N_to_le_bytes; reflexivity).
      assert (L4b : Z.of_nat (length (LE4 12)) = 4) by (rewrite length_N_to_le_bytes; reflexivity).
      rewrite !wbytes_mrestrict in RUN2; [| rewrite ?L4a, ?L4b, ?length_N_to_le_bytes, at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia
                                           | wd_lenlit; rewrite ?length_N_to_le_bytes, at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); intros x Hx; apply HDscr; lia
                                           | rewrite ?L4a, ?L4b, ?length_N_to_le_bytes, at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia
                                           | wd_lenlit; rewrite ?length_N_to_le_bytes, at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); intros x Hx; apply HDscr; lia].
      assert (C18' : getr r2 18 = addr) by (rewrite C18; rewrite getr_other by (intros E; discriminate E); exact B18).
      destruct (DIE MZ r2 ltac:(right; reflexivity) C2 C8 C9 C18' C19) as (fx' & r3 & M3 & RUN3).
      apply (doomed_msteps_acct BSEGS Hd HOFFSEG WX A (mkst (regupd r1 10 ENOMEMw) (0x811b0 : word) MZ rom)
               (@mkst fx' r3 (0x7ca24 : word) M3 rom) (MDS mdlm) HDS2 AWF HDS3 HDS1).
      { rewrite mk_restrict_mkst. eapply msteps_trans; [exact RUN2 | exact RUN3]. }
      intros mdl4 MI4 SBM4 HC4.
      apply doomed_to_spin; [apply mo_spin|].
      pose proof (same_but_materialized_frame (MDS mdlm) mdl4 SBM4) as (_&_&_&_&_&_&_&_&_&_&_&_&Hh4&_). rewrite Hh4. exact HDS1.
  Qed.

End MAPOK.
End FPGen1.
