(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AmLia.   (* [comment removed for export] *)
(* [comment removed for export] *)
Require Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Logic.FunctionalExtensionality LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mprotect LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocSim OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys6 OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.BackingAlgebra OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8m OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM9i OSSVerify.Proofs.glaze.binary_reflection.lib.BoDrvIStrlen OSSVerify.glaze.binary_reflection.images.AsanUbsan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac tauto ::= OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac.wd_tauto.   (* [comment removed for export] *)
Module BoDepotMnrK.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import Stdlib.Logic.FunctionalExtensionality.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mprotect.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.DivergeSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.SpinAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes.AgentNodes OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocSim OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys6.MhKSys OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsK OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys6.AsKSys OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys6.AsKSys2 OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsRtK OSSVerify.Proofs.glaze.binary_reflection.lib.Common.BackingAlgebra OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys6.AsanNodesLibE OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8m OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM9i.BoAllocM8k OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM9i.BoAllocM9m OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM9i.BoAllocM9k OSSVerify.Proofs.glaze.binary_reflection.lib.BoDrvIStrlen.Bo_code_80b0c_815a0 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8m.Bo_code_7c9f4_7cb58 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM9i.BoDepotMnr OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM9i.BoDepotModK OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.NoReserve.
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

Definition mnr_ret' (regs r : bvmap 5 word) (sp ra s0v s1v s2v res : word) : Prop :=
  getr r 10 = res /\ getr r 2 = sp /\ getr r 1 = ra /\ getr r 8 = s0v /\ getr r 9 = s1v /\ getr r 18 = s2v
  /\ regs_agree (fun i : reg => In i mnr_clob) regs r.

Section MNRK.
  Variable Hd : word -> bool.
  Hypothesis HOFFSEG : H_off_segments BSEGS Hd.
  Hypothesis WX : wx_segs_nowrap BSEGS.

  Theorem mnr_katD :
    forall (A : list (Z * Z)) regs (mem rom : word -> option byte) (model : Model)
           (sp ra s0v s1v s2v s3v s4v s5v size name : word) (PGP CF : Z) (Q : config -> Prop)
           (GRANT : Model -> word -> Prop) (MOK : Model -> word -> Model),
    let M1 := mnr_m1 mem sp ra s0v s1v s2v s3v s4v s5v size name PGP in
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
        getr r1 10 = Z_to_bv 64 0 -> getr r1 11 = size -> getr r1 12 = Z_to_bv 64 3 -> getr r1 13 = Z_to_bv 64 16418 ->
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
        mnr_ret' regs r' sp ra s0v s1v s2v a ->
        katD BSEGS (mkCfg (mkst r' ra (wbytes (zfill a size M1) (at_ sp (-40)) SCR) rom) mdl4) Q) ->
    katD BSEGS (mkCfg (mkst regs (0x82db0 : word) mem rom) model) Q.
  Proof using WX HOFFSEG.
    intros A regs mem rom model sp ra s0v s1v s2v s3v s4v s5v size name PGP CF Q GRANT MOK M1 ENOMEMw SCR
           H1 H2 H10 H11 H8 H9 H18 H19 H20 H21 Hsp Hret Hsize Hname HPGP HCF Hstk Rgpg Rpg Rgcf Rdpm Rlim Rd1 Rd2
           HDgpg HDpg HDgcf HDdpm HDlim HDd1 HDd2 HDscr HALT LC AWF MI SEP NODE CHILD CONTOK.
    pose proof (u64_range sp) as Hspr. pose proof (u64_range size) as Hszr.
    destruct HPGP as [PG1 PG2]. destruct HCF as [CF1 CF2].
    assert (Hstk' : store_ok BSEGS (mrestrict Hd mem) (at_ sp (-320)) 320 = true).
    { rewrite store_ok_mrestrict; [exact Hstk | first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); exact HDscr]. }
    assert (CELLR : forall (c : Z) (k : nat) v, 0 <= c < 2 ^ 32 -> Z.of_nat k <= 8 -> hid_off Hd c (Z.of_nat k) ->
               rdn BSEGS mem (Z_to_bv 64 c) k = Some v -> rdn BSEGS (mrestrict Hd mem) (Z_to_bv 64 c) k = Some v).
    { intros c k v Hc0 Hc1 Hh Hr. rewrite rdn_mrestrict; [exact Hr | first [ solve [ wd_unorm1; wd_zofnat; lia ] | rewrite u_Z2bv by lia; lia ] | rewrite u_Z2bv by lia; exact Hh]. }
    destruct (mnr_pre (mrestrict Hd mem) rom sp ra s0v s1v s2v s3v s4v s5v size name PGP CF regs
                H1 H2 H10 H11 H8 H9 H18 H19 H20 H21 Hsp Hsize Hname (conj PG1 PG2) (conj CF1 CF2) Hstk'
                (CELLR 0x105ef8 8%nat _ ltac:(lia) ltac:((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia) HDgpg Rgpg) (CELLR PGP 8%nat _ ltac:(lia) ltac:((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia) HDpg Rpg)
                (CELLR 0x105f08 8%nat _ ltac:(lia) ltac:((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia) HDgcf Rgcf) (CELLR (CF + 260) 1%nat _ ltac:(lia) ltac:((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia) HDdpm Rdpm))
      as (r1 & RUN1 & B1 & B2 & B8 & B9 & B18 & B10 & B11 & B12 & B13 & B14 & B15 & B17 & AG1).
    assert (EM1 : mnr_m1 (mrestrict Hd mem) sp ra s0v s1v s2v s3v s4v s5v size name PGP = mrestrict Hd M1).
    { (lazymatch goal with |- ?G => let G' := eval unfold M1, mnr_m1 in G in change_no_check G' end).
      rewrite !wbytes_mrestrict; [reflexivity | | | | | | | | | | | | | | | | | | | | | | | |];
        wd_lenlit; rewrite ?length_N_to_le_bytes, ?at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn [length Z.of_nat Pos.of_succ_nat Pos.succ Pos.to_nat] in G in change_no_check G' end); first [lia | intros x Hx; apply HDscr; lia]. }
    rewrite EM1 in RUN1.
    assert (M1hid : forall a : word, Hd a = true -> M1 a = mem a).
    { intros a Ha. (lazymatch goal with |- ?G => let G' := eval unfold M1 in G in change_no_check G' end). apply (mnr_m1_outside mem sp ra s0v s1v s2v s3v s4v s5v size name PGP Hsp).
      destruct (Z_lt_le_dec (U a) (U sp - 320)) as [C1|C1]; [left; exact C1|].
      destruct (Z_lt_le_dec (U a) (U sp)) as [C2|C2]; [| right; exact C2].
      exfalso. rewrite (HDscr a) in Ha by lia. discriminate Ha. }
    apply (katD_msteps_acct BSEGS Hd HOFFSEG WX A (mkst regs (0x82db0 : word) mem rom)
             (mkst r1 (0x811ac : word) (mrestrict Hd M1) rom) model Q LC AWF MI HALT).
    { rewrite mk_restrict_mkst. exact RUN1. }
    intros mdlm MIm SBMm HC1. rewrite mk_unrestrict_mkst.
    replace (RiscvSemantics.ms_mem (mkst regs (0x82db0 : word) mem rom)) with mem by reflexivity.
    rewrite (mk_munrestrict_same Hd mem M1 M1hid).
    pose proof (same_but_materialized_frame model mdlm SBMm) as FRm.
    assert (HALTm : m_halted mdlm = None) by (destruct FRm as (_&_&_&_&_&_&_&_&_&_&_&_&Hh&_); rewrite Hh; exact HALT).
    apply (katD_ecall BSEGS r1 (0x811ac : word) M1 rom mdlm W_811ac Q HALTm F_811ac E_811ac).
    rewrite B17.
    assert (POSTF : forall MZ : word -> option byte,
               (forall x : word, U sp - 320 <= U x < U sp -> MZ x = M1 x) ->
               store_ok BSEGS (mrestrict Hd MZ) (at_ sp (-40)) 4 = true
               /\ store_ok BSEGS (mrestrict Hd MZ) (at_ sp (-96)) 48 = true
               /\ (forall (k : Z) (v : word), In (k, v) [(-8, ra); (-16, s0v); (-24, s1v); (-32, s2v)] ->
                      rdn BSEGS (mrestrict Hd MZ) (at_ sp k) 8 = Some (LE8 v))).
    { intros MZ EZ.
      assert (SOKZ : forall (o : Z) (n : nat), -320 <= o -> o + Z.of_nat n <= 0 -> store_ok BSEGS (mrestrict Hd MZ) (at_ sp o) n = true).
      { intros o n Ho1 Ho2.
        rewrite store_ok_mrestrict; [| first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ] | rewrite at_u by lia; intros x Hx; apply HDscr; lia].
        rewrite (store_ok_ext BSEGS n M1 MZ); [| first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ] | intros x Hx; apply EZ; rewrite at_u in Hx by lia; lia].
        eapply store_ok_mono; [apply mnr_m1_grows|].
        eapply (store_ok_sub BSEGS mem (at_ sp (-320)) _ 320); [first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | exact Hstk | first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite !at_u by lia; lia ] | first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite !at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ]]. }
      split; [apply SOKZ; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia|]. split; [apply SOKZ; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia|].
      intros k v Hin.
      assert (Hk : -32 <= k <= -8) by (cbn [In] in Hin; repeat (destruct Hin as [E|Hin]; [injection E as <- <-; lia|]); destruct Hin).
      rewrite rdn_mrestrict; [| first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); intros x Hx; apply HDscr; lia].
      rewrite <- (mnr_m1_slots mem sp ra s0v s1v s2v s3v s4v s5v size name PGP Hsp k v Hin). fold M1.
      apply rdn_ext; [first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | intros x Hx; apply EZ; rewrite at_u in Hx by lia; cbn in Hx; lia]. }
    assert (Q1 : forall v : word, getr (regupd r1 10 v) 1 = Z_to_bv 64 0x82e3c) by (intros v; rewrite getr_other by (intros E; discriminate E); exact B1).
    assert (Q2 : forall v : word, getr (regupd r1 10 v) 2 = at_ sp (-48)) by (intros v; rewrite getr_other by (intros E; discriminate E); exact B2).
    assert (Q18 : forall v : word, getr (regupd r1 10 v) 9 = size) by (intros v; rewrite getr_other by (intros E; discriminate E); exact B9).
    assert (Q10 : forall v : word, getr (regupd r1 10 v) 10 = v) by (intros v; rewrite getr_same by (intros E; discriminate E); reflexivity).
    assert (AGC : forall (v : word) (r2 : bvmap 5 word), regs_agree (fun i : reg => In i mnr_clob) (regupd r1 10 v) r2 ->
                    regs_agree (fun i : reg => In i mnr_clob) regs r2).
    { intros v r2 AG2 x Hx. rewrite (AG2 x Hx).
      assert (NE10 : x <> 10%bv) by (intros ->; apply Hx; (lazymatch goal with |- ?G => let G' := eval unfold mnr_clob in G in change_no_check G' end); (lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); tauto).
      rewrite getr_other by (intros E; apply NE10; exact E). apply AG1. exact Hx. }
    assert (L4a : Z.of_nat (length SCR) = 4) by ((lazymatch goal with |- ?G => let G' := eval unfold SCR in G in change_no_check G' end); rewrite length_N_to_le_bytes; reflexivity).
    assert (HIDW : forall (MM : word -> option byte) bs (a : word), Hd a = true -> Z.of_nat (length bs) = 4 -> wbytes MM (at_ sp (-40)) bs a = MM a).
    { intros MM bs a Ha Hl.
      destruct (Z_lt_le_dec (U a) (U sp - 40)) as [C|C]; [apply wbytes_below; rewrite ?Hl, ?at_u by lia; lia|].
      destruct (Z_lt_le_dec (U a) (U sp - 36)) as [C'|C']; [exfalso; rewrite (HDscr a) in Ha by lia; discriminate Ha|].
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
        (lazymatch goal with |- ?G => let G' := eval unfold MZ in G in change_no_check G' end). rewrite zfill_out by lia. (lazymatch goal with |- ?G => let G' := eval unfold M1 in G in change_no_check G' end). apply (mnr_m1_outside mem sp ra s0v s1v s2v s3v s4v s5v size name PGP Hsp). left. lia. }
      destruct (mnr_ok (mrestrict Hd MZ) rom sp ra s0v s1v s2v size CF (regupd r1 10 a)
                  (Q1 a) (Q2 a) (Q18 a) Hsp Hret (conj CF1 CF2) SOKZ
                  (SLZ (-8) ra ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); tauto)) (SLZ (-16) s0v ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); tauto)) (SLZ (-24) s1v ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); tauto))
                  (SLZ (-32) s2v ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); tauto))
                  a (Q10 a) ltac:(lia)
                  (CELLZ 0x105f08 8%nat _ ltac:(lia) ltac:((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia) HDgcf Rgcf) (CELLZ (CF + 144) 8%nat _ ltac:(lia) ltac:((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia) HDlim Rlim))
        as (r2 & RUN2 & C10 & C2 & C1 & C8 & C9 & C18 & AG2).
      rewrite wbytes_mrestrict in RUN2; [| rewrite length_N_to_le_bytes, at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia
                                          | rewrite length_N_to_le_bytes, at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); intros x Hx; apply HDscr; lia].
      apply (katD_msteps_acct BSEGS Hd HOFFSEG WX A (mkst (regupd r1 10 a) (0x811b0 : word) MZ rom)
               (mkst r2 ra (mrestrict Hd (wbytes MZ (at_ sp (-40)) SCR)) rom) (MOK mdlm a) Q HOK2 AWF HOK3 HOK1).
      { rewrite mk_restrict_mkst. exact RUN2. }
      intros mdl4 MI4 SBM4 HC4. rewrite mk_unrestrict_mkst.
      replace (RiscvSemantics.ms_mem (mkst (regupd r1 10 a) (0x811b0 : word) MZ rom)) with MZ by reflexivity.
      rewrite (mk_munrestrict_same Hd MZ (wbytes MZ (at_ sp (-40)) SCR)).
      2:{ intros x Hx. apply HIDW; [exact Hx | exact L4a]. }
      apply (CONTOK a r2 mdlm mdl4 SBMm MIm GR SBM4 MI4).
      (lazymatch goal with |- ?G => let G' := eval unfold mnr_ret' in G in change_no_check G' end). repeat (split; [assumption|]). exact (AGC a r2 AG2).
    - (* [comment removed for export] *)
      set (MZ := M1).
      assert (EZ : forall x : word, U sp - 320 <= U x < U sp -> MZ x = M1 x) by (intros x Hx; reflexivity).
      destruct (POSTF MZ EZ) as (SOKZ & SOKZ2 & _).
      assert (CELLM : forall (c : Z) (k : nat) v, 0 <= c -> c + Z.of_nat k <= AIMGHI -> hid_off Hd c (Z.of_nat k) ->
                 rdn BSEGS mem (Z_to_bv 64 c) k = Some v -> rdn BSEGS (mrestrict Hd MZ) (Z_to_bv 64 c) k = Some v).
      { intros c k v Hc0 Hc1 Hh Hr. rewrite rdn_mrestrict; [| first [ solve [ wd_unorm1; wd_zofnat; lia ] | rewrite u_Z2bv by lia; lia ] | rewrite u_Z2bv by lia; exact Hh].
        rewrite <- Hr. apply rdn_ext; [first [ solve [ wd_unorm1; wd_zofnat; lia ] | rewrite u_Z2bv by lia; lia ]|]. intros x Hx. rewrite u_Z2bv in Hx by lia.
        (lazymatch goal with |- ?G => let G' := eval unfold MZ, M1 in G in change_no_check G' end). apply (mnr_m1_outside mem sp ra s0v s1v s2v s3v s4v s5v size name PGP Hsp). left. lia. }
      destruct (mnr_die (mrestrict Hd MZ) rom sp size (regupd r1 10 ENOMEMw) (Q1 ENOMEMw) (Q2 ENOMEMw) (Q18 ENOMEMw) Hsp SOKZ (Q10 ENOMEMw) SOKZ2
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
End MNRK.

(* [comment removed for export] *)
Section NODEDMNR.
  Lemma node_dm_of_mmap_nr :
    forall (r1 : bvmap 5 word) (M1 rom : word -> option byte) (mdlm : Model) (size : word) (Q' : config -> Prop),
    m_halted mdlm = None ->
    getr r1 10 = Z_to_bv 64 0 -> getr r1 11 = size -> getr r1 12 = Z_to_bv 64 3 -> getr r1 13 = Z_to_bv 64 16418 ->
    getr r1 14 = Z_to_bv 64 (2 ^ 64 - 1) -> getr r1 15 = Z_to_bv 64 0 ->
    0 < U size -> U size mod 4096 = 0 ->
    (exists a : word, grant_ok_nr (Z_to_bv 64 0) mdlm a (U size) = true) ->
    (forall a : word, grant_ok_nr (Z_to_bv 64 0) mdlm a (U size) = true ->
        katD BSEGS (mkCfg (mkst (regupd r1 10 a) (0x811b0 : word) (zfill a size M1) rom) (mmap_model_noreserve a size mdlm)) Q') ->
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
    assert (ARGS : mmap_args_ok_noreserve ms).
    { (lazymatch goal with |- ?G => let G' := eval unfold mmap_args_ok_noreserve in G in change_no_check G' end). rewrite E1. (lazymatch goal with |- ?G => let G' := eval unfold ms in G in change_no_check G' end). rewrite AsKSys6.MhKSys.ms_gpr_epend2, AsKSys6.MhKSys.ms_gpr_epend3, AsKSys6.MhKSys.ms_gpr_epend4, AsKSys6.MhKSys.ms_gpr_epend5.
      split; [intros X; apply (f_equal bv_unsigned) in X; rewrite u_Z2bv in X by lia; lia|].
      split; [exact B12|]. split; [exact B13|]. split; [rewrite B14; apply bv_eq; reflexivity | exact B15]. }
    apply (katD_mmap_nr_dm BSEGS ms mdlm (Z_to_bv 64 222) HALT eq_refl ltac:(rewrite u_Z2bv by lia; reflexivity) ARGS Q').
    - rewrite E0, E1, PRU. exact EX.
    - intros e He. (lazymatch goal with |- ?G => let G' := eval unfold mmnr_fail, ms in G in change_no_check G' end). rewrite AsKSys6.MhKSys.adv_set_epend.
      assert (Ee : e = ENOMEM) by (destruct He as [<-|[]]; reflexivity). subst e.
      replace (errno_ret ENOMEM) with (Z_to_bv 64 (2 ^ 64 - 12) : word) by (apply bv_eq; vm_compute; reflexivity).
      replace (v_addi (0x811ac%bv : word) 4) with (0x811b0%bv : word) by (apply bv_eq; vm_compute; reflexivity).
      exact KKP.
    - intros a Ha. rewrite E0, E1, PRU in Ha. (lazymatch goal with |- ?G => let G' := eval unfold mmnr_grant in G in change_no_check G' end). rewrite PRW. (lazymatch goal with |- ?G => let G' := eval unfold ms in G in change_no_check G' end). rewrite AsKSys6.MhKSys.adv_zeros1_epend.
      replace (v_addi (0x811ac%bv : word) 4) with (0x811b0%bv : word) by (apply bv_eq; vm_compute; reflexivity).
      exact (KOK a Ha).
  Qed.
End NODEDMNR.
End FPGen1.
End BoDepotMnrK.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.MuslMemmove OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.MemSplit OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.MuslMemmove OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.NoReserve.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3. Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsKInst OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsRtK.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsDp3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsDp23 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFree3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvZone3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsRc73. Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinv3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinvGeom3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOps3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsDp3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsDp23 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d.AsAinvFreeS OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFree3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvZone3b.AsAinvFacts3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsRc73.AsAinvRepX3.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFHyp OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8La OSSVerify.Proofs.glaze.binary_reflection.lib.BoDepotHit OSSVerify.Proofs.glaze.binary_reflection.lib.BoDepotRunI OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRc4c OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtIMemmove OSSVerify.Proofs.glaze.binary_reflection.lib.BoDepotTop3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys10 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM9i OSSVerify.Proofs.glaze.binary_reflection.lib.BoDepotTopN1b OSSVerify.Proofs.glaze.binary_reflection.lib.BoDepotBud2 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRcS3 OSSVerify.Proofs.glaze.binary_reflection.lib.BoDepotRunC3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys6. Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFHyp OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8La OSSVerify.Proofs.glaze.binary_reflection.lib.BoDepotHit OSSVerify.Proofs.glaze.binary_reflection.lib.BoDepotRunI.BoDepotIns OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRc4c.BoDepotStore OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtIMemmove.AsDepotSum OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtIMemmove.AsDepotSum2 OSSVerify.Proofs.glaze.binary_reflection.lib.BoDepotRunI.BoDepotRunT OSSVerify.Proofs.glaze.binary_reflection.lib.BoDepotRunI OSSVerify.Proofs.glaze.binary_reflection.lib.BoDepotTop3.BoDepotRunP OSSVerify.Proofs.glaze.binary_reflection.lib.BoDepotTop3.BoDepotHyp9 OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys10.AsDepotTop0 OSSVerify.Proofs.glaze.binary_reflection.lib.BoDepotTop3.BoDepotTop1 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFHyp.BoDepotImg OSSVerify.Proofs.glaze.binary_reflection.lib.BoDepotRunI.BoDepotStoreR OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM9i.BoDepotMod OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM9i.BoDepotModK OSSVerify.Proofs.glaze.binary_reflection.lib.BoDepotRunI.BoDepotMap OSSVerify.Proofs.glaze.binary_reflection.lib.BoDepotTopN1b.BoDepotRunF OSSVerify.Proofs.glaze.binary_reflection.lib.BoDepotRunI.BoDepotRunN OSSVerify.Proofs.glaze.binary_reflection.lib.BoDepotTopN1b.BoDepotRunN2 OSSVerify.Proofs.glaze.binary_reflection.lib.BoDepotTopN1b.BoDepotTopN1a OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys10.AsDepotBud OSSVerify.Proofs.glaze.binary_reflection.lib.BoDepotBud2 OSSVerify.Proofs.glaze.binary_reflection.lib.BoDepotTopN1b.BoDepotHyp9w OSSVerify.Proofs.glaze.binary_reflection.lib.BoDepotTopN1b OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRcS3.BoDepotAlloc OSSVerify.Proofs.glaze.binary_reflection.lib.BoDepotRunI.BoDepotBlk OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM9i.BoDepotMnr BoDepotMnrK OSSVerify.Proofs.glaze.binary_reflection.lib.BoDepotRunC3.BoDepotRunC1 OSSVerify.Proofs.glaze.binary_reflection.lib.BoDepotRunC3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys6.AsKSys7 OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys10.AsKSys9 OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys10.AsKSys9b.
From OSSVerify.glaze.binary_reflection.images Require Import AsanUbsan.
Import ListNotations.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Ltac wm_clear_disj_or T := lazymatch T with | _ \/ _ => idtac | ?A /\ ?B => first [wm_clear_disj_or A | wm_clear_disj_or B] | ?A <-> ?B => first [wm_clear_disj_or A | wm_clear_disj_or B] | ?A -> ?B => first [wm_clear_disj_or A | wm_clear_disj_or B] end.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AmLia.   (* [comment removed for export] *)
Ltac wm_clear_disj := am_wm_clear_disj.   (* [comment removed for export] *)
Ltac wm_lia0 := tryif noncert_goal_has_var then (Zify.zify; xlia zchecker)
                else first [ solve [noncert_clear_all; Zify.zify; xlia zchecker] | Zify.zify; xlia zchecker ].
(* [comment removed for export] *)
Tactic Notation "tclr" ident(H) := try clear H.
Ltac wm_bl := tclr D1; tclr D2; tclr D3; tclr D6; tclr D8; tclr D9; tclr D10; tclr LENP; tclr FRB1; tclr FRB2; tclr KC; tclr DEP0; tclr L10; tclr AL; tclr Htag; tclr Lbs;
  tclr DY; tclr E1; tclr E2; tclr EIDX; tclr STDQ; tclr NROOM; tclr LEAG.
#[local] Ltac lia ::= first [ solve [wm_bl; wm_clear_disj; wm_lia0] | solve [wm_clear_disj; wm_lia0] | wm_lia0 ].
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation BSEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).
#[local] Abbreviation LE4 v := (word_to_le_bytes 4 v).
#[local] Abbreviation U := bv_unsigned.

Definition nnpart (nn : option Z) : list (word * word) := List.map (fun p => (Z_to_bv 64 p, Z_to_bv 64 (2 ^ 20))) (blk_opt nn).

(* [comment removed for export] *)
Definition ledN (mdl mdlN : Model) (nn : option Z) : Prop :=
  vm_maps (m_vmmaps mdlN) = nnpart nn ++ vm_maps (m_vmmaps mdl)
  /\ vm_noaccess (m_vmmaps mdlN) = vm_noaccess (m_vmmaps mdl) /\ m_vm_lazy mdlN = m_vm_lazy mdl
  /\ vm_reserved (m_vmmaps mdlN) = vm_reserved (m_vmmaps mdl) /\ vm_brk (m_vmmaps mdlN) = vm_brk (m_vmmaps mdl)
  /\ vm_start_brk (m_vmmaps mdlN) = vm_start_brk (m_vmmaps mdl) /\ vm_mmap_base (m_vmmaps mdlN) = vm_mmap_base (m_vmmaps mdl)
  /\ vm_init_sp (m_vmmaps mdlN) = vm_init_sp (m_vmmaps mdl) /\ vm_limit (m_vmmaps mdlN) = vm_limit (m_vmmaps mdl)
  /\ eager_used mdlN <= eager_used mdl + 2 ^ 20 * Z.of_nat (length (blk_opt nn))
  /\ BackingAlgebra.model_ivs_wf mdlN /\ m_halted mdlN = None /\ same_except_vm mdl mdlN.

(* [comment removed for export] *)
Definition cls02 (sp b idx ndz qs : Z) (nn : option Z) (z : Z) : Prop :=
  (sp - 576 <= z < sp) \/ (0x1f0098 + 4 * b <= z < 0x1f0098 + 4 * b + 4) \/ (0x1f0098 + 4194304 <= z < 0x1f0098 + 4194304 + 4)
  \/ (0x1f0098 + 4194312 <= z < 0x1f0098 + 4194312 + 4) \/ (nn <> None /\ 0x1f0098 + 4194320 + 8 * idx <= z < 0x1f0098 + 4194320 + 8 * idx + 8)
  \/ (exists p, nn = Some p /\ p <= z < p + 2 ^ 20) \/ (ndz <= z < ndz + 16)
  \/ (1966216 <= z < 1966216 + 16)                                                   (* [comment removed for export] *)
  \/ (1966216 + 16 * qs + 16 <= z < 1966216 + 16 * qs + 32)                           (* [comment removed for export] *)
  \/ (1966216 + 16 * (qs - 1) + 24 <= z < 1966216 + 16 * (qs - 1) + 28).              (* [comment removed for export] *)

Section TOPS1.
  Context {RC : run_ceil}.
  Variable bt : as_boot.
  Variable FXOK : FPState -> Prop.
  Hypothesis BT_segs : bt_segs bt = BSEGS.
  Hypothesis BT_ia : bt_ia bt = both_addrs.
  Hypothesis DCELLS : depot_cells bt.
  Hypothesis DOBL : depot_obls bt.
  Hypothesis DEPOT_FRAMES_ROOM : forall st Lc FF, WF bt st Lc FF -> depot_room bt st -> a_kact st <= KCAP -> dp_frames (a_dep st) + 2 * FRW <= 2 ^ 32.
  Hypothesis DEP0 : dp_nids (bt_dep0 bt) <= 2 ^ 20.
  Hypothesis BOOTG : boot_geom bt.

  Lemma sgrow_cont : forall KD, 576 <= KD ->
    forall fx (X : Z -> Prop) st Lc FF (M M0 M2f MPr MB : mem) mdl mdlN mdlm mdl4 (R rP r' : bvmap 5 word) (sp buf ret a ndW t3 t4 : word)
           (sz tag start pk so : Z) (std' : Z -> Z) (ws : list word) (h0 nn : option Z) (W02 : Z -> Prop),
      FXOK fx -> m_halted mdl = None -> BackingAlgebra.model_ivs_wf mdl ->
      WF bt st Lc FF -> Rep bt st Lc FF M0 mdl -> (forall a : word, M a <> M0 a -> X (U a) /\ M a <> None) ->
      (forall a, X a -> ~ (ia_img_lo (bt_ia bt) <= a < ia_img_hi (bt_ia bt))) -> PX bt st X -> holes_le h0 st ->
      depot_room bt st -> a_kact st <= KCAP ->
      getr R 1 = ret -> getr R 2 = sp ->
      CEIL + KD <= U sp -> U sp + 2192 <= 2 ^ 47 -> ret_ok ret ->
      (forall a : word, U sp - KD <= U a < U sp -> M a <> None /\ store_ok BSEGS M a 1%nat = true) ->
      1 <= sz <= 8 -> 0 <= tag < 256 -> U sp <= U buf -> U buf + 8 * sz < 2 ^ 64 ->
      (forall i, U buf <= i < U buf + 8 * sz -> M (Z_to_bv 64 i) <> None) ->
      let Hd := HID st mdl in let h := sd_hashN ws tag in
      let d := a_dep st in let b := sd_bix h in let NIDS := dp_nids d in let idx := (NIDS + 1) / 2 ^ 16 in let tot := dp_frames d in
      let cnt := sz + 1 in let qs := start / 2 ^ 20 in
      let MUW : word := Z_to_bv 64 (0x1f0098 + 4194312) in let bW : word := Z_to_bv 64 (0x1f0098 + 4 * b) in
      let spS := at_ (at_ sp (-112)) (-32) in let spA := at_ spS (-64) in let spB := at_ spA (-16) in let spMn := at_ spB (-32) in
      let packp := at_ (at_ sp (-112)) (-24) in let args := at_ sp (-104) in
      let szW : word := Z_to_bv 64 8388608 in let BI : word := Z_to_bv 64 (U SSW + 16 * qs + 16) in
      let WB2 := wun (ivl (U sp - 576) 320) (ivl (U a) (2 ^ 23)) in
      (* [comment removed for export] *)
      (0 <= start /\ start + sz + 1 <= 2 ^ 32) -> start mod 2 ^ 20 + sz < 2 ^ 20 -> qs = Z.of_nat (length (store_blocks bt d)) ->
      tot <= start + cnt -> start + cnt <= tot + FRW + FRW ->
      Z.of_nat (length (dp_storeblocks d)) + 1 = Z.min (Z.max 0 ((start + cnt - 1) / 2 ^ 20)) (2 ^ 12 - 1) ->
      0 <= so < 2 ^ 32 -> (0 <= pk /\ pk + 1 < 2 ^ 32) -> (forall i, 0 <= std' i < 2 ^ 32) -> std' qs = (so + cnt) mod 2 ^ 32 ->
      (* [comment removed for export] *)
      (nn = None <-> (NIDS + 1) / 2 ^ 16 = Z.of_nat (length (dp_nodeblocks d))) ->
      (nn <> None -> idx = Z.of_nat (length (dp_nodeblocks d)) + 1) ->
      (forall p, nn = Some p -> dyn_ok (bt_ia bt) p (p + 2 ^ 20) /\ p mod PG = 0 /\ forall lo hi, In (lo, hi) (all_ranges bt st) -> p + 2 ^ 20 <= lo \/ hi <= p) ->
      (forall p b0 n0, nn = Some p -> In (b0, n0) (bt_maps0 bt) -> p + 2 ^ 20 <= U b0 \/ U b0 + U n0 <= p) ->
      (forall p z, nn = Some p -> p <= z < p + 2 ^ 20 -> Hd (Z_to_bv 64 z) = false /\ ~ X z /\ M2f (Z_to_bv 64 z) <> None) ->
      U ndW = nth (Z.to_nat idx) (node_blocks bt d ++ blk_opt nn) 0 + 16 * ((NIDS + 1) mod 2 ^ 16) ->
      (exists nb, (In nb (node_blocks bt d) \/ nn = Some nb) /\ nb <= U ndW /\ U ndW + 16 <= nb + 2 ^ 20) ->
      0 <= idx < 2 ^ 15 ->
      (* [comment removed for export] *)
      Wdec W02 -> msum W02 M M2f -> (forall z, W02 z -> cls02 (U sp) b idx (U ndW) qs nn z) -> (forall x : word, Hd x = false -> M2f x = MPr x) ->
      (forall (k : Z) (v : word), In (k, v) [(-8, (0x8d12c%bv : word)); (-16, Z_to_bv 64 start); (-24, SSW); (-32, Z_to_bv 64 cnt)]%Z -> rdn BSEGS MPr (at_ spB k) 8 = Some (LE8 v)) ->
      rdn BSEGS MPr (at_ spA (-8)) 8 = Some (LE8 (0x8cf6c%bv : word)) -> rdn BSEGS MPr (at_ spA (-16)) 8 = Some (LE8 packp) ->
      (forall (k : Z) (v : word), In (k, v) [(-8, (0x8f234%bv : word)); (-16, ndW); (-24, ndW); (-32, bW); (-40, t3); (-48, t4); (-56, Z_to_bv 64 (dp_tab d b))]%Z ->
          rdn BSEGS MPr (at_ spS k) 8 = Some (LE8 v)) ->
      rdn BSEGS MPr spA 8 = Some (LE8 (Z_to_bv 64 start)) ->
      rdn BSEGS MPr packp 8 = Some (LE8 (Z_to_bv 64 pk)) ->
      rdn BSEGS MPr (st_cell SSW start) 4 = Some (LE4 (Z_to_bv 64 so)) ->
      rdn BSEGS MPr SSW 8 = Some (LE8 (Z_to_bv 64 (start + cnt))) ->
      (forall i, 0 <= i < 2 ^ 12 -> i <> qs -> rdn BSEGS MPr (Z_to_bv 64 (1966216 + 24 + 16 * i)) 4 = Some (LE4 (Z_to_bv 64 (std' i)))) ->
      rdn BSEGS MPr args 8 = Some (LE8 buf) ->
      (forall (k : Z) (v : word),
          In (k, v) [(-8, ret); (-16, getr R 8); (-24, getr R 9); (-32, getr R 18); (-40, getr R 19); (-48, getr R 20);
                     (-56, getr R 21); (-64, getr R 22); (-72, getr R 23); (-80, getr R 24); (-88, getr R 25)]%Z ->
          rdn BSEGS MPr (at_ sp k) 8 = Some (LE8 v)) ->
      rdn BSEGS MPr (at_ (at_ sp (-112)) (-8)) 8 = Some (LE8 (0x8f718%bv : word)) -> rdn BSEGS MPr (at_ (at_ sp (-112)) (-16)) 8 = Some (LE8 (Z_to_bv 64 0)) ->
      rdn BSEGS MPr ndW 8 = Some (LE8 h) ->
      rdn BSEGS MPr (Z_to_bv 64 (0x1f0098 + 4194304)) 4 = Some (LE4 (Z_to_bv 64 (NIDS + 1))) ->
      rdn BSEGS MPr MUW 1 = Some [Z_to_bv 8 0] ->
      (forall p, nn = Some p -> rdn BSEGS MPr (Z_to_bv 64 (0x1f0098 + 4194320 + 8 * idx)) 8 = Some (LE8 (Z_to_bv 64 p))) ->
      (* [comment removed for export] *)
      getr rP 8 = at_ BI 12 -> getr rP 9 = BI -> getr rP 19 = args -> getr rP 20 = Z_to_bv 64 sz -> getr rP 21 = Z_to_bv 64 tag -> getr rP 23 = Z_to_bv 64 (NIDS + 1) ->
      (forall k, ~ In (Z_to_bv 5 k) put_clob -> ~ In (Z_to_bv 5 k) sd_clobx -> getr rP (Z_to_bv 5 k) = getr R (Z_to_bv 5 k)) ->
      (* [comment removed for export] *)
      ledN mdl mdlN nn -> same_but_materialized mdlN mdlm -> grant_ok_nr (Z_to_bv 64 0) mdlm a (2 ^ 23) = true ->
      same_but_materialized (mmap_model_noreserve a szW mdlm) mdl4 -> MInv (a_aa st) mdl4 ->
      mnr_ret' rP r' spMn (Z_to_bv 64 0x8da70) (getr rP 8) (getr rP 9) (getr rP 18) a ->
      msum WB2 M2f MB -> (forall x : word, U a <= U x < U a + 2 ^ 23 -> MB x <> None) ->
      katD BSEGS (mkCfg (@mkst fx r' (Z_to_bv 64 0x8da70) MB (seg_rom BSEGS)) mdl4)
           (depot_post_w bt FXOK KD X st Lc FF M mdl R sp ret).
  Proof using BOOTG DEP0 DOBL DCELLS BT_ia BT_segs.
    intros KD HKD fx X st Lc FF M M0 M2f MPr MB mdl mdlN mdlm mdl4 R rP r' sp buf ret a ndW t3 t4 sz tag start pk so std' ws h0 nn W02
           HFX HH MW W RP DIFF XIMG PXH HOLE ROOM KC E1 E2 SPC SPHI RET STK SZ Htag BUFS BUFW BUFD
           Hd h d b NIDS idx tot cnt qs MUW bW spS spA spB spMn packp args szW BI WB2
           ST1 FIT QSL FRB1 FRB2 LENP SO PK STD STDQ NNW NNI NNF NNM0 NNV ND NDB I16
           WD02 [FR0 GR0] CLS0 VIS2 SLbi Rara Ras0 SLst Ridx Rpk Rso Rtot' CST Rtr SLs Rq8 Rq16 Rhsh Kn0 Kmu0 Kslot0
           P8 P9 P19 P20 P21 P23 AG0 LEDN SBMm G SBM4 MI4 MR [FRB GRB] DEFA.
    pose proof ceil_rng as CR. pose proof (u64_range sp) as Hspr. pose proof (u64_range buf) as Hbufr. pose proof (u64_range a) as Har. pose proof (u64_range ndW) as Hndr.
    destruct ST1 as [ST0 ST32]. destruct PK as [PK0 PK1].
    pose proof (bix_range h) as Hbix. fold b in Hbix.
    assert (UMU : U MUW = 0x1f0098 + 4194312) by reflexivity.
    assert (UbW : U bW = 0x1f0098 + 4 * b) by ((lazymatch goal with |- ?G => let G' := eval unfold bW in G in change_no_check G' end); rewrite u_Z2bv by lia; reflexivity).
    assert (USS : U SSW = 1966216) by reflexivity.
    assert (UspS : U spS = U sp - 144) by ((lazymatch goal with |- ?G => let G' := eval unfold spS in G in change_no_check G' end); rewrite at_at, at_u by lia; lia).
    assert (UspA : U spA = U sp - 208) by ((lazymatch goal with |- ?G => let G' := eval unfold spA in G in change_no_check G' end); first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ]).
    assert (UspB : U spB = U sp - 224) by ((lazymatch goal with |- ?G => let G' := eval unfold spB in G in change_no_check G' end); first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ]).
    assert (UspMn : U spMn = U sp - 256) by ((lazymatch goal with |- ?G => let G' := eval unfold spMn in G in change_no_check G' end); first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ]).
    assert (Upk : U packp = U sp - 136) by ((lazymatch goal with |- ?G => let G' := eval unfold packp in G in change_no_check G' end); rewrite at_at, at_u by lia; lia).
    assert (Uargs : U args = U sp - 104) by ((lazymatch goal with |- ?G => let G' := eval unfold args in G in change_no_check G' end); first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ]).
    assert (Usz : U szW = 2 ^ 23) by reflexivity.
    assert (Q20 : 0 <= qs < 2 ^ 12) by ((lazymatch goal with |- ?G => let G' := eval unfold qs in G in change_no_check G' end); split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
    assert (M20 : 0 <= start mod 2 ^ 20 < 2 ^ 20) by (apply Z.mod_pos_bound; lia).
    assert (UBI : U BI = 1966216 + 16 * qs + 16) by ((lazymatch goal with |- ?G => let G' := eval unfold BI in G in change_no_check G' end); rewrite USS; rewrite u_Z2bv by lia; reflexivity).
    pose proof W as (_ & _ & _ & _ & _ & _ & (D1 & D2 & D3 & D4 & D5 & D6 & D7 & D8 & D9 & D10 & D11 & D12) & _).
    fold d in D1, D2, D3, D4, D5, D6, D7, D8, D9, D10, D11, D12. fold tot in D7, D9, D10. fold NIDS in D1, D2, D3, D4, D5, D6.
    assert (NN0 : 0 <= NIDS) by (pose proof (D4 0 ltac:(lia)) as X0; lia).
    pose proof (depot_nids_room bt st Lc FF W ROOM KC DEP0) as NROOM. fold d NIDS in NROOM.
    assert (M16 : 0 <= (NIDS + 1) mod 2 ^ 16 < 2 ^ 16) by (apply Z.mod_pos_bound; lia).
    pose proof RP as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10 & R11 & R12 & R13 & R14 & R15).
    rewrite BT_segs in R1.
    destruct R14 as (Bw1 & Bw2 & _ & _ & _ & _ & Bw7 & _).
    assert (NHs : forall z, 0 <= z < 2 ^ 64 -> (CEIL <= z \/ (AIMGLO <= z /\ z < AIMGHI)) -> Hd (Z_to_bv 64 z) = false).
    { intros z Hz Hr. apply (HID_off_zone bt st mdl z R13 Hz). rewrite BT_ia. (lazymatch goal with |- ?G => let G' := eval cbn [ia_img_lo ia_img_hi both_addrs] in G in change_no_check G' end). lia. }
    assert (NHw : forall x : word, (CEIL <= U x \/ (AIMGLO <= U x /\ U x < AIMGHI)) -> Hd x = false).
    { intros x Hx. pose proof (u64_range x) as Hxr. rewrite <- (Z_to_bv_bv_unsigned 64 x). apply NHs; [lia | exact Hx]. }
    assert (EQ0 : forall a : word, ~ X (U a) -> M a = M0 a).
    { intros x NX. destruct (decide (M x = M0 x)) as [E|NE]; [exact E|]. exfalso. exact (NX (proj1 (DIFF x NE))). }
    assert (XI : forall i, AIMGLO <= i < AIMGHI -> ~ X i).
    { intros i Hi Xi. apply (XIMG i Xi). rewrite BT_ia. (lazymatch goal with |- ?G => let G' := eval cbn [ia_img_lo ia_img_hi both_addrs] in G in change_no_check G' end). lia. }
    pose proof (HID_off_segments bt st Lc FF M0 mdl BT_ia RP) as HOFF.
    destruct DCELLS as (_ & _ & _ & C_cf & C_csd).
    destruct LEDN as (LN1 & LN2 & LN3 & LN4 & LN5 & LN6 & LN7 & LN8 & LN9 & LEAG & LNW & LNH & LNS).
    (* [comment removed for export] *)
    destruct (sbm_vmmaps _ _ SBMm) as [EVm ELm].
    assert (NNR : forall p, nn = Some p -> 0 <= p /\ p + 2 ^ 20 < 2 ^ 64).
    { intros p E. destruct (NNF p E) as ((Y1 & Y2 & Y3 & _) & _). clear - Y1 Y3 CR. lia. }
    destruct (grant_nr_facts_x bt st Lc FF M0 mdl mdlm (2 ^ 20) (2 ^ 28) (Z_to_bv 64 0) a nn h0 W RP BOOTG
                ltac:(rewrite EVm; exact LN4) ltac:(rewrite EVm; exact LN1) ltac:(rewrite EVm; exact LN8) NNR HOLE G) as (DY & AL & AP & APN & APM0).
    assert (GAC : AIMGHI <= U a /\ U a + 2 ^ 23 <= CEIL).
    { destruct DY as (Y1 & Y2 & Y3 & Y4 & Y5). rewrite BT_ia in Y4. cbn [ia_img_lo ia_img_hi both_addrs] in Y4. clear - Y3 Y4 Y1 Har. lia. }
    destruct GAC as [GA GC].
    destruct MR as (B10 & B2 & B1 & B8 & B9 & B18 & AGm).
    assert (AALp : U a mod page_size = 0) by ((lazymatch goal with |- ?G => let G' := eval unfold page_size in G in change_no_check G' end); exact AL).
    destruct (nr_child_ledger mdlN mdlm mdl4 a szW LNW EVm ELm AALp ltac:(rewrite Usz; reflexivity) ltac:(rewrite Usz; lia) ltac:(rewrite Usz; lia) SBM4)
      as (L1 & L2 & L3 & L3b & L4 & L5 & L6 & L7 & L8 & L9 & L10 & L11).
    assert (HL4 : m_halted mdl4 = None).
    { pose proof (same_but_materialized_frame _ _ SBM4) as F. destruct F as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HLa & _). rewrite HLa.
      pose proof (same_but_materialized_frame mdlN mdlm SBMm) as F. destruct F as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HLb & _).
      change (m_halted (mmap_model_noreserve a szW mdlm)) with (m_halted mdlm). rewrite HLb. exact LNH. }
    assert (NHa : forall z, U a <= z < U a + 2 ^ 23 -> Hd (Z_to_bv 64 z) = false).
    { intros z Hz. apply HID_notlazy; [lia|]. exact (grant_not_lazy bt st Lc FF M0 mdl (U a) (2 ^ 23) W RP DY AP z Hz). }
    (* [comment removed for export] *)
    destruct NDB as (nb & NBc & NB1 & NB2).
    assert (NBF : AIMGHI <= nb /\ nb + 2 ^ 20 <= CEIL /\ (forall z, nb <= z < nb + 2 ^ 20 -> Hd (Z_to_bv 64 z) = false /\ ~ X z)
                  /\ (nb + 2 ^ 20 <= U a \/ U a + 2 ^ 23 <= nb)).
    { destruct NBc as [INB | ENN].
      - destruct (node_blocks_dyn bt st Lc FF W nb INB) as ((GB0 & GB1 & GB2 & GB3 & _) & _ & INBr). rewrite BT_ia in GB3. cbn [ia_img_lo ia_img_hi both_addrs] in GB3.
        destruct DOBL as (DO1 & _).
        split; [clear - GB0 GB3; lia|]. split; [exact GB2|].
        split; [intros z Hz; split; [apply HID_notlazy; [clear - Hz GB0 GB2 CR; lia | exact (DO1 st Lc FF M0 mdl nb z W RP INB Hz)]
                                     | intros Xz; exact (px_off_nodes bt st Lc FF W X z nb PXH Xz INB Hz)]|].
        destruct (AP _ _ INBr) as [C|C]; [right; exact C | left; exact C].
      - destruct (NNF nb ENN) as ((Y1 & Y2 & Y3 & Y4 & _) & _ & _). rewrite BT_ia in Y4. cbn [ia_img_lo ia_img_hi both_addrs] in Y4.
        split; [clear - Y1 Y4; lia|]. split; [exact Y3|].
        split; [intros z Hz; destruct (NNV nb z ENN Hz) as (V1 & V2 & _); split; assumption|].
        exact (APN nb ENN). }
    destruct NBF as (NBA & NBC & NBV & NBAP).
    set (MBr := mrestrict Hd MB).
    set (Wall := wun W02 (wun WB2 (cpost_W sp ndW bW qs (U a + 8 * (start mod 2 ^ 20)) (8 + 8 * sz)))).
    (* [comment removed for export] *)
    assert (DEFB : forall x : word, M x <> None -> Hd x = false -> MBr x <> None).
    { intros x Dx Hx. (lazymatch goal with |- ?G => let G' := eval unfold MBr in G in change_no_check G' end). rewrite (mrestrict_off Hd MB x Hx). apply GRB. apply GR0. exact Dx. }
    assert (TB : forall (x : word) (n : nat) v, U x + Z.of_nat n <= 2 ^ 64 ->
                   (forall i, U x <= i < U x + Z.of_nat n -> Hd (Z_to_bv 64 i) = false /\ ~ WB2 i) -> rdn BSEGS MPr x n = Some v -> rdn BSEGS MBr x n = Some v).
    { intros x n v B0 F Hr. rewrite <- Hr. apply rdn_ext; [exact B0|]. intros y Hy. destruct (F (U y) Hy) as [NH NW]. rewrite Z_to_bv_bv_unsigned in NH.
      (lazymatch goal with |- ?G => let G' := eval unfold MBr in G in change_no_check G' end). rewrite (mrestrict_off Hd MB y NH). rewrite (FRB y NW). exact (VIS2 y NH). }
    assert (STKB : forall i, U sp - 256 <= i < 2 ^ 64 -> Hd (Z_to_bv 64 i) = false /\ ~ WB2 i).
    { intros i Hi. split; [apply NHs; [clear - Hi Hspr SPC CR HKD; lia | left; clear - Hi SPC HKD; lia] | (lazymatch goal with |- ?G => let G' := eval unfold WB2, wun, ivl in G in change_no_check G' end); clear - Hi GC SPC HKD; lia]. }
    assert (IMGB : forall i, AIMGLO <= i < AIMGHI -> Hd (Z_to_bv 64 i) = false /\ ~ WB2 i).
    { intros i Hi. split; [apply NHs; [clear - Hi; lia | right; clear - Hi; lia] | (lazymatch goal with |- ?G => let G' := eval unfold WB2, wun, ivl in G in change_no_check G' end); clear - Hi GA SPC CR HKD; lia]. }
    assert (NDVB : forall i, U ndW <= i < U ndW + 16 -> Hd (Z_to_bv 64 i) = false /\ ~ WB2 i).
    { intros i Hi. split; [apply (NBV i); clear - Hi NB1 NB2; lia | (lazymatch goal with |- ?G => let G' := eval unfold WB2, wun, ivl in G in change_no_check G' end); clear - Hi NB1 NB2 NBC NBAP SPC HKD; lia]. }
    set (CFW := Z_to_bv 64 0x19fce8 : word). assert (UCF : U CFW = 0x19fce8) by reflexivity.
    assert (Rcfp : rdn BSEGS MBr (Z_to_bv 64 1072904) 8 = Some (LE8 CFW)).
    { pose proof (const_cell bt M0 _ _ _ R1 C_cf) as C. unfold cellZ, cellN in C. refine (eq_trans _ C). apply rdn_ext; [rewrite u_Z2bv by (clear; lia); (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear; lia|].
      intros x Hx. rewrite u_Z2bv in Hx by (clear; lia). cbn in Hx. destruct (IMGB (U x) ltac:(clear - Hx; lia)) as [NH NW]. rewrite Z_to_bv_bv_unsigned in NH.
      (lazymatch goal with |- ?G => let G' := eval unfold MBr in G in change_no_check G' end). rewrite (mrestrict_off Hd MB x NH), (FRB x NW).
      rewrite (FR0 x) by (intros WZ; destruct (CLS0 _ WZ) as [C1|[C1|[C1|[C1|[[_ C1]|[(p & Ep & C1)|[C1|[C1|[C1|C1]]]]]]]]];
                            [clear - C1 Hx SPC CR HKD; lia | clear - C1 Hx Hbix; lia | clear - C1 Hx; lia | clear - C1 Hx; lia | clear - C1 Hx I16; lia
                            | destruct (NNF p Ep) as ((Y1 & _ & _ & Y4 & _) & _); rewrite BT_ia in Y4; cbn [ia_img_lo ia_img_hi both_addrs] in Y4; clear - C1 Hx Y1 Y4; lia
                            | clear - C1 Hx NB1 NBA; lia | clear - C1 Hx; lia | clear - C1 Hx Q20; lia | clear - C1 Hx Q20; lia]).
      apply EQ0. apply XI. clear - Hx. lia. }
    assert (Rflag : rdn BSEGS MBr (at_ CFW 240) 4 = Some (LE4 (Z_to_bv 64 0))).
    { replace (at_ CFW 240) with (Z_to_bv 64 0x19fdd8 : word) by (apply bv_eq; reflexivity).
      pose proof (const_cell bt M0 _ _ _ R1 C_csd) as C. unfold cellZ, cellN in C. refine (eq_trans _ C). apply rdn_ext; [rewrite u_Z2bv by (clear; lia); (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear; lia|].
      intros x Hx. rewrite u_Z2bv in Hx by (clear; lia). cbn in Hx. destruct (IMGB (U x) ltac:(clear - Hx; lia)) as [NH NW]. rewrite Z_to_bv_bv_unsigned in NH.
      (lazymatch goal with |- ?G => let G' := eval unfold MBr in G in change_no_check G' end). rewrite (mrestrict_off Hd MB x NH), (FRB x NW).
      rewrite (FR0 x) by (intros WZ; destruct (CLS0 _ WZ) as [C1|[C1|[C1|[C1|[[_ C1]|[(p & Ep & C1)|[C1|[C1|[C1|C1]]]]]]]]];
                            [clear - C1 Hx SPC CR HKD; lia | clear - C1 Hx Hbix; lia | clear - C1 Hx; lia | clear - C1 Hx; lia | clear - C1 Hx I16; lia
                            | destruct (NNF p Ep) as ((Y1 & _ & _ & Y4 & _) & _); rewrite BT_ia in Y4; cbn [ia_img_lo ia_img_hi both_addrs] in Y4; clear - C1 Hx Y1 Y4; lia
                            | clear - C1 Hx NB1 NBA; lia | clear - C1 Hx; lia | clear - C1 Hx Q20; lia | clear - C1 Hx Q20; lia]).
      apply EQ0. apply XI. clear - Hx. lia. }
    assert (SLbiB : forall (k : Z) (v : word), In (k, v) [(-8, (0x8d12c%bv : word)); (-16, Z_to_bv 64 start); (-24, SSW); (-32, Z_to_bv 64 cnt)]%Z -> rdn BSEGS MBr (at_ spB k) 8 = Some (LE8 v)).
    { intros k v Hin. assert (K : -32 <= k <= -8) by (cbn [In] in Hin; repeat (destruct Hin as [E|Hin]; [injection E as <- <-; clear; lia|]); destruct Hin).
      apply TB; [rewrite at_u by (rewrite UspB; clear - K Hspr SPC CR HKD; lia); rewrite UspB; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear - K Hspr SPHI; lia
                | intros i Hi; rewrite at_u in Hi by (rewrite UspB; clear - K Hspr SPC CR HKD; lia); rewrite UspB in Hi; cbn in Hi; apply STKB; clear - Hi K Hspr SPHI; lia | exact (SLbi k v Hin)]. }
    assert (STKT : forall (x : word) (n : nat) v, U sp - 256 <= U x -> U x + Z.of_nat n <= 2 ^ 64 -> rdn BSEGS MPr x n = Some v -> rdn BSEGS MBr x n = Some v).
    { intros x n v H1 H2 Hr. apply TB; [exact H2 | intros i Hi; apply STKB; clear - Hi H1 H2; lia | exact Hr]. }
    assert (RaraB : rdn BSEGS MBr (at_ spA (-8)) 8 = Some (LE8 (0x8cf6c%bv : word))).
    { apply STKT; [rewrite at_u by (rewrite UspA; clear - Hspr SPC CR HKD; lia); rewrite UspA; clear; lia | rewrite at_u by (rewrite UspA; clear - Hspr SPC CR HKD; lia); rewrite UspA; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear - Hspr SPHI; lia | exact Rara]. }
    assert (Ras0B : rdn BSEGS MBr (at_ spA (-16)) 8 = Some (LE8 packp)).
    { apply STKT; [rewrite at_u by (rewrite UspA; clear - Hspr SPC CR HKD; lia); rewrite UspA; clear; lia | rewrite at_u by (rewrite UspA; clear - Hspr SPC CR HKD; lia); rewrite UspA; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear - Hspr SPHI; lia | exact Ras0]. }
    assert (SLstB : forall (k : Z) (v : word), In (k, v) [(-8, (0x8f234%bv : word)); (-16, ndW); (-24, ndW); (-32, bW); (-40, t3); (-48, t4); (-56, Z_to_bv 64 (dp_tab d b))]%Z ->
                rdn BSEGS MBr (at_ spS k) 8 = Some (LE8 v)).
    { intros k v Hin. assert (K : -56 <= k <= -8) by (cbn [In] in Hin; repeat (destruct Hin as [E|Hin]; [injection E as <- <-; clear; lia|]); destruct Hin).
      apply STKT; [rewrite at_u by (rewrite UspS; clear - K Hspr SPC CR HKD; lia); rewrite UspS; clear - K; lia
                  | rewrite at_u by (rewrite UspS; clear - K Hspr SPC CR HKD; lia); rewrite UspS; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear - K Hspr SPHI; lia | exact (SLst k v Hin)]. }
    assert (RidxB : rdn BSEGS MBr spA 8 = Some (LE8 (Z_to_bv 64 start))) by (apply STKT; [rewrite UspA; clear; lia | rewrite UspA; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear - Hspr SPHI; lia | exact Ridx]).
    assert (RpkB : rdn BSEGS MBr packp 8 = Some (LE8 (Z_to_bv 64 pk))) by (apply STKT; [rewrite Upk; clear; lia | rewrite Upk; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear - Hspr SPHI; lia | exact Rpk]).
    assert (RtrB : rdn BSEGS MBr args 8 = Some (LE8 buf)) by (apply STKT; [rewrite Uargs; clear; lia | rewrite Uargs; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear - Hspr SPHI; lia | exact Rtr]).
    assert (SLB : forall (k : Z) (v : word),
                In (k, v) [(-8, ret); (-16, getr R 8); (-24, getr R 9); (-32, getr R 18); (-40, getr R 19); (-48, getr R 20);
                           (-56, getr R 21); (-64, getr R 22); (-72, getr R 23); (-80, getr R 24); (-88, getr R 25)]%Z ->
                rdn BSEGS MBr (at_ sp k) 8 = Some (LE8 v)).
    { intros k v Hin. assert (K : -88 <= k <= -8) by (cbn [In] in Hin; repeat (destruct Hin as [E|Hin]; [injection E as <- <-; clear; lia|]); destruct Hin).
      apply STKT; [rewrite at_u by (clear - K Hspr SPC CR HKD; lia); clear - K; lia | rewrite at_u by (clear - K Hspr SPC CR HKD; lia); (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear - K Hspr SPHI; lia | exact (SLs k v Hin)]. }
    assert (Rq8B : rdn BSEGS MBr (at_ (at_ sp (-112)) (-8)) 8 = Some (LE8 (0x8f718%bv : word))).
    { apply STKT; [rewrite at_at, at_u by (clear - Hspr SPC CR HKD; lia); clear; lia | rewrite at_at, at_u by (clear - Hspr SPC CR HKD; lia); (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear - Hspr SPHI; lia | exact Rq8]. }
    assert (Rq16B : rdn BSEGS MBr (at_ (at_ sp (-112)) (-16)) 8 = Some (LE8 (Z_to_bv 64 0))).
    { apply STKT; [rewrite at_at, at_u by (clear - Hspr SPC CR HKD; lia); clear; lia | rewrite at_at, at_u by (clear - Hspr SPC CR HKD; lia); (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear - Hspr SPHI; lia | exact Rq16]. }
    assert (Ucell : U (st_cell SSW start) = 1966216 + 16 * qs + 24) by ((lazymatch goal with |- ?G => let G' := eval unfold st_cell in G in change_no_check G' end); rewrite USS; fold qs; rewrite u_Z2bv by lia; reflexivity).
    assert (RsoB : rdn BSEGS MBr (st_cell SSW start) 4 = Some (LE4 (Z_to_bv 64 so))).
    { apply TB; [rewrite Ucell; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear - Q20; lia | intros i Hi; rewrite Ucell in Hi; cbn in Hi; apply IMGB; clear - Hi Q20; lia | exact Rso]. }
    destruct (rdn_defined_ex BSEGS MBr buf (Z.to_nat (8 * sz))) as (bs & Rws & Lbs).
    { intros i Hi. rewrite Z2Nat.id in Hi by lia. apply DEFB; [apply BUFD; lia|]. apply NHw. rewrite u_Z2bv by lia. left. clear - Hi BUFS SPC HKD. lia. }
    { rewrite Z2Nat.id by lia. lia. }
    assert (Lbs' : Z.of_nat (length bs) = 8 * sz) by (rewrite Lbs, Z2Nat.id by lia; reflexivity).
    rewrite <- Lbs in Rws.
    (* [comment removed for export] *)
    assert (SOKI : forall (x : word) (n : nat) v, 0x107000 <= U x -> U x + Z.of_nat n <= 2 ^ 64 -> rdn BSEGS MBr x n = Some v -> store_ok BSEGS MBr x n = true).
    { intros x n v H1 H2 Hr. exact (readable_store_ok BSEGS 0x107000 MBr x n v both_rw_above H1 H2 Hr). }
    assert (SOKSS : forall (x : word) (n : nat), 0x1e0088 <= U x -> U x + Z.of_nat n <= 0x1e0088 + 65552 -> store_ok BSEGS MBr x n = true).
    { intros x n H1 H2. exact (ss_store_ok MBr x n H1 H2). }
    assert (UBL : U (at_ BI 12) = 1966216 + 16 * qs + 28) by (rewrite at_u by (rewrite UBI; clear - Q20; lia); rewrite UBI; clear; lia).
    assert (SOKbd : store_ok BSEGS MBr BI 8 = true) by (apply SOKSS; [rewrite UBI; clear - Q20; lia | rewrite UBI; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear - Q20; lia]).
    assert (SOKbl : store_ok BSEGS MBr (at_ BI 12) 1 = true) by (apply SOKSS; [rewrite UBL; clear - Q20; lia | rewrite UBL; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear - Q20; lia]).
    assert (SOKso : store_ok BSEGS MBr (st_cell SSW start) 4 = true) by (apply SOKSS; [rewrite Ucell; clear - Q20; lia | rewrite Ucell; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear - Q20; lia]).
    assert (Udst : U (st_dst a start) = U a + 8 * (start mod 2 ^ 20)) by ((lazymatch goal with |- ?G => let G' := eval unfold st_dst in G in change_no_check G' end); rewrite u_Z2bv by (clear - Har M20 GC CR; lia); reflexivity).
    assert (SOKd : store_ok BSEGS MBr (st_dst a start) (8 + length bs) = true).
    { apply store_ok_bytes; [| rewrite Udst, Nat2Z.inj_add, Lbs'; change (Z.of_nat 8) with 8; clear - M20 FIT SZ GC CR; lia].
      intros x Hx. rewrite Udst, Nat2Z.inj_add, Lbs' in Hx. change (Z.of_nat 8) with 8 in Hx. apply store_ok1_some.
      (lazymatch goal with |- ?G => let G' := eval unfold MBr in G in change_no_check G' end). rewrite (mrestrict_off Hd MB x) by (rewrite <- (Z_to_bv_bv_unsigned 64 x); apply NHa; clear - Hx M20 FIT SZ; lia).
      apply DEFA. clear - Hx M20 FIT SZ. lia. }
    assert (SOKp : store_ok BSEGS MBr packp 8 = true).
    { apply store_ok_bytes; [| rewrite Upk; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear - Hspr SPHI; lia]. intros x Hx. rewrite Upk in Hx. cbn in Hx. apply store_ok1_some.
      apply DEFB; [apply STK; clear - Hx HKD; lia | apply NHw; left; clear - Hx SPC HKD; lia]. }
    assert (Hstk : store_ok BSEGS MBr (at_ (at_ sp (-112)) (-48)) 16 = true).
    { rewrite at_at. apply store_ok_bytes; [| rewrite at_u by (clear - Hspr SPC CR HKD; lia); (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear - Hspr SPHI; lia].
      intros x Hx. rewrite at_u in Hx by (clear - Hspr SPC CR HKD; lia). cbn in Hx. apply store_ok1_some.
      apply DEFB; [apply STK; clear - Hx HKD; lia | apply NHw; left; clear - Hx SPC HKD; lia]. }
    assert (SOKn : store_ok BSEGS MBr ndW 16 = true).
    { apply store_ok_bytes; [| (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear - Hndr NB2 NBC CR; lia]. intros x Hx. cbn in Hx. apply store_ok1_some.
      destruct (NDVB (U x) Hx) as [NH NW]. rewrite Z_to_bv_bv_unsigned in NH. (lazymatch goal with |- ?G => let G' := eval unfold MBr in G in change_no_check G' end). rewrite (mrestrict_off Hd MB x NH). apply GRB.
      destruct NBc as [INB | ENN].
      - apply GR0. destruct R9 as (_ & _ & _ & _ & _ & Dnw & _). pose proof (Dnw nb INB) as WN.
        assert (D0 : M0 x <> None) by (rewrite <- (Z_to_bv_bv_unsigned 64 x); apply (WN (U x)); clear - Hx NB1 NB2; lia).
        destruct (decide (M x = M0 x)) as [E|NE]; [rewrite E; exact D0 | exact (proj2 (DIFF x NE))].
      - destruct (NNV nb (U x) ENN ltac:(clear - Hx NB1 NB2; lia)) as (_ & _ & DM). rewrite Z_to_bv_bv_unsigned in DM. exact DM. }
    assert (SOKb : store_ok BSEGS MBr bW 4 = true).
    { assert (ETAB : DEPOT_TAB bt = 0x1f0098) by ((lazymatch goal with |- ?G => let G' := eval unfold DEPOT_TAB in G in change_no_check G' end); rewrite BT_ia; reflexivity).
      destruct R9 as (Dtab & _). pose proof (Dtab b Hbix) as Cb. rewrite ETAB, BT_segs in Cb. unfold cellZ, cellN in Cb. fold bW in Cb.
      destruct (rdn_of_bytes BSEGS MBr 4 bW) as (v1 & Rv1 & _); [rewrite UbW; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear - Hbix; lia | | refine (SOKI _ _ _ _ _ Rv1); [rewrite UbW; clear - Hbix; lia | rewrite UbW; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear - Hbix; lia]].
      intros y Hy. rewrite UbW in Hy. cbn in Hy.
      destruct (rdn_bytes BSEGS M0 4 bW _ Cb ltac:(rewrite UbW; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear - Hbix; lia) y ltac:(rewrite UbW; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); exact Hy)) as [b0 Hb0].
      assert (Hb1 : rdn BSEGS M y 1 = Some [b0]) by (cbn [rdn] in Hb0 |- *; rewrite (EQ0 y ltac:(apply XI; clear - Hy Hbix; lia)); exact Hb0).
      destruct (rdn1_grows BSEGS M MB y b0 ltac:(eapply mem_grows_trans; [exact GR0 | exact GRB]) Hb1) as [b' Hb'].
      exists b'. cbn [rdn] in Hb' |- *. (lazymatch goal with |- ?G => let G' := eval unfold MBr in G in change_no_check G' end). rewrite (mrestrict_off Hd MB y (NHw y ltac:(right; clear - Hy Hbix; lia))). exact Hb'. }
    (* [comment removed for export] *)
    assert (NIm : forall i : reg, In i [19%bv; 20%bv; 21%bv; 22%bv; 23%bv; 24%bv; 25%bv; 26%bv; 27%bv; 3%bv; 4%bv] -> ~ In i mnr_clob).
    { intros i Hi Hx. unfold mnr_clob in Hx. cbn [In] in Hi, Hx. repeat (destruct Hi as [<-|Hi]; [repeat (destruct Hx as [Hx|Hx]; [discriminate Hx|]); exact Hx|]). exact Hi. }
    assert (T19 : getr r' 19 = args) by (rewrite (AGm 19%bv) by (apply NIm; in_l); exact P19).
    assert (T20 : getr r' 20 = Z_to_bv 64 sz) by (rewrite (AGm 20%bv) by (apply NIm; in_l); exact P20).
    assert (T21 : getr r' 21 = Z_to_bv 64 tag) by (rewrite (AGm 21%bv) by (apply NIm; in_l); exact P21).
    assert (T23 : getr r' 23 = Z_to_bv 64 (NIDS + 1)) by (rewrite (AGm 23%bv) by (apply NIm; in_l); exact P23).
    pose proof (D4 b Hbix) as Htab.
    (* [comment removed for export] *)
    destruct (put_c_post MBr (seg_rom BSEGS) sp ret ndW bW a buf CFW t3 t4 (dp_tab d b) (NIDS + 1) sz tag start so pk bs
                (getr R 8) (getr R 9) (getr R 18) (getr R 19) (getr R 20) (getr R 21) (getr R 22) (getr R 23) (getr R 24) (getr R 25) r'
                B2 ltac:(rewrite B8; exact P8) ltac:(rewrite B9; exact P9) B10 T19 T20 T21 T23
                ltac:(clear - Hspr SPC CR HKD SPHI; lia) RET ltac:(rewrite UCF; clear; lia)
                ltac:(clear - NB1 NB2 NBA NBC SPC HKD; lia) ltac:(rewrite UbW; clear - Hbix NB1 NBA SPC CR HKD; lia)
                ltac:(clear - GA GC NBAP NB1 NB2 SPC HKD UbW Hbix; rewrite UbW; lia) ltac:(clear - BUFS BUFW; lia) ltac:(clear - SZ; lia) Htag
                (conj ST0 ST32) FIT SO (conj PK0 PK1) Lbs
                SLbiB RaraB Ras0B SLstB RidxB RsoB RpkB RtrB Rws Rq8B Rq16B Rcfp Rflag SLB SOKbd SOKbl SOKd SOKso SOKp SOKn SOKb Hstk)
      as (r2 & M'r & RUN2 & S2 & C10 & C2 & C1 & C8 & C9 & C18 & C19 & C20 & C21 & C22 & C23 & C24 & C25 & Kb & Kl & Ks & Kbd & Kbl & Kso & AG2).
    set (A2 := a_aa st ++ [(U a, U a + 2 ^ 23)]).
    set (W2 := cpost_W sp ndW bW qs (U a + 8 * (start mod 2 ^ 20)) (8 + 8 * sz)) in *.
    assert (CLS2 : forall z, W2 z -> (U sp - 160 <= z < U sp - 128) \/ (0x1f0098 + 4 * b <= z < 0x1f0098 + 4 * b + 4)
                                    \/ (U ndW + 8 <= z < U ndW + 16) \/ (1966216 + 16 * qs + 16 <= z < 1966216 + 16 * qs + 32)
                                    \/ (U a <= z < U a + 2 ^ 23)).
    { intros z Hz. unfold W2, cpost_W, tail_W, wun, ivl in Hz. rewrite UbW in Hz. clear - Hz M20 FIT SZ. lia. }
    assert (NHW2 : forall x : word, W2 (U x) -> Hd x = false).
    { intros x Hx. pose proof (u64_range x) as Hxr. destruct (CLS2 _ Hx) as [C|[C|[C|[C|C]]]].
      - apply NHw. left. clear - C SPC HKD. lia.
      - apply NHw. right. clear - C Hbix. lia.
      - rewrite <- (Z_to_bv_bv_unsigned 64 x). apply (NBV (U x)). clear - C NB1 NB2. lia.
      - apply NHw. right. clear - C Q20. lia.
      - rewrite <- (Z_to_bv_bv_unsigned 64 x). apply NHa. exact C. }
    (* [comment removed for export] *)
    assert (AW2 : A_wf A2).
    { (lazymatch goal with |- ?G => let G' := eval unfold A2 in G in change_no_check G' end). apply A_wf_snoc; [exact Bw1 | clear; lia | exact AL |]. pose proof AL as AL'. unfold PG in AL'. rewrite Z.add_mod by (clear; lia). rewrite AL'. reflexivity. }
    assert (LC2 : lazy_cover Hd (m_vm_lazy mdl4) A2).
    { rewrite L3, LN3. intros w Hp Hh. rewrite AsKSys6.AsanNodesMmLib.page_in_ranges_cons in Hp. cbn [fst snd] in Hp. apply orb_true_iff in Hp as [Hp | Hp].
      - (lazymatch goal with |- ?G => let G' := eval unfold A2, page_allowedb in G in change_no_check G' end). rewrite existsb_app. apply orb_true_iff. right. (lazymatch goal with |- ?G => let G' := eval cbn [existsb fst snd] in G in change_no_check G' end). rewrite orb_false_r. rewrite Usz in Hp. exact Hp.
      - assert (LCS : lazy_cover Hd (m_vm_lazy mdl) A2) by ((lazymatch goal with |- ?G => let G' := eval unfold A2 in G in change_no_check G' end); apply lazy_cover_snoc; apply lazy_cover_HID). exact (LCS w Hp Hh). }
    assert (KN : 0 <= Z.of_nat (length (blk_opt nn)) <= 1) by (destruct nn; (lazymatch goal with |- ?G => let G' := eval cbn [blk_opt length Z.of_nat Pos.of_succ_nat] in G in change_no_check G' end); clear; lia).
    pose proof (depot_grow_budget bt st Lc FF M0 mdl (2 ^ 20) (2 ^ 28) (Z.of_nat (length (blk_opt nn))) 1 RP W ltac:(clear; lia) KC KN ltac:(clear; lia)) as BUDG.
    assert (MI2 : MInv A2 mdl4).
    { (lazymatch goal with |- ?G => let G' := eval unfold A2 in G in change_no_check G' end). apply MInv_snoc; [exact MI4|]. rewrite A_bytes_snoc. rewrite L9, LN9. clear - BUDG L10 LEAG. lia. }
    (* [comment removed for export] *)
    apply (katD_msteps_acct BSEGS Hd HOFF asanF_segs_wx A2
             (@mkst fx r' (Z_to_bv 64 0x8da70) MB (seg_rom BSEGS)) (@mkst fx r2 ret M'r (seg_rom BSEGS)) mdl4).
    { exact LC2. } { exact AW2. } { exact MI2. } { exact HL4. }
    { rewrite restrict_mkst9. fold MBr. replace (Z_to_bv 64 0x8da70) with (0x8da70%bv : word) by (apply bv_eq; reflexivity). exact RUN2. }
    intros mdl5 MI5 SBM5 HC5. rewrite unrestrict_mkst.
    replace (ms_mem (@mkst fx r' (Z_to_bv 64 0x8da70) MB (seg_rom BSEGS))) with MB by reflexivity.
    set (M' := munrestrict Hd MB M'r).
    pose proof (msum_unrestrict Hd W2 MB M'r NHW2 S2) as [FR2 GR2]. fold M' in FR2, GR2.
    pose proof (same_but_materialized_frame mdl4 mdl5 SBM5) as (_ & Evm5 & Elz5 & _ & _ & _ & _ & _ & _ & _ & _ & _ & Ehl5 & _ & _ & _ & Eeg5).
    assert (VIS : forall (z : Z) (k : nat), 0 <= z -> z + Z.of_nat k < 2 ^ 64 -> (forall i, z <= i < z + Z.of_nat k -> Hd (Z_to_bv 64 i) = false) ->
              rdn BSEGS M' (Z_to_bv 64 z) k = rdn BSEGS M'r (Z_to_bv 64 z) k).
    { intros z k Hz Hk F. apply rdn_munrestrict; [first [ solve [ wd_unorm1; wd_zofnat; lia ] | rewrite u_Z2bv by lia; lia ]|]. intros x Hx. rewrite u_Z2bv in Hx by lia.
      rewrite <- (Z_to_bv_bv_unsigned 64 x). apply F. exact Hx. }
    assert (SALL : msum Wall M M') by (exact (msum_trans _ _ _ _ _ (conj FR0 GR0) (msum_trans _ _ _ _ _ (conj FRB GRB) (conj FR2 GR2)))).
    destruct SALL as [FRA GRA].
    assert (CLS : forall z, Wall z -> cls02 (U sp) b idx (U ndW) qs nn z \/ (U a <= z < U a + 2 ^ 23)).
    { intros z [Hz | [Hz | Hz]].
      - left. exact (CLS0 z Hz).
      - unfold WB2, wun, ivl in Hz. destruct Hz as [Hz | Hz]; [left; left; clear - Hz; lia | right; exact Hz].
      - destruct (CLS2 _ Hz) as [C|[C|[C|[C|C]]]]; [left; left; clear - C; lia | left; right; left; exact C | left; do 6 right; left; clear - C; lia
                                                    | left; do 8 right; left; exact C | right; exact C]. }
    (* [comment removed for export] *)
    set (st' := op_depot_insert st b (U h) (dp_tab d b) (start + 1) (start + cnt) std' nn (Some (U a))).
    assert (W' : WF bt st' Lc FF).
    { apply (OPS_WF_depot_insert_pf bt st Lc FF b (U h) (dp_tab d b) (start + 1) (start + cnt) std' nn (Some (U a)) W Hbix).
      - pose proof (u64_range h) as Hh. clear - Hh. lia.
      - clear - ST0 ST32 SZ. lia.
      - exact STD.
      - reflexivity.
      - exact ROOM.
      - exact NROOM.
      - fold d NIDS. exact NNW.
      - fold d tot. (lazymatch goal with |- ?G => let G' := eval cbn [blk_opt length Z.of_nat Pos.of_succ_nat] in G in change_no_check G' end). clear - FRB1 FRB2. lia.
      - fold d. rewrite length_app, Nat2Z.inj_add. (lazymatch goal with |- ?G => let G' := eval cbn [blk_opt length Z.of_nat Pos.of_succ_nat] in G in change_no_check G' end). replace (start + cnt - 1) with (start + cnt - 1) by reflexivity. exact LENP.
      - fold d. rewrite length_app, Nat2Z.inj_add. (lazymatch goal with |- ?G => let G' := eval cbn [blk_opt length Z.of_nat Pos.of_succ_nat] in G in change_no_check G' end).
        assert (QL : qs = Z.of_nat (length (dp_storeblocks d)) + 1) by (rewrite QSL; (lazymatch goal with |- ?G => let G' := eval unfold store_blocks in G in change_no_check G' end); (lazymatch goal with |- ?G => let G' := eval cbn [length] in G in change_no_check G' end); rewrite Nat2Z.inj_succ; clear; lia).
        clear - QL Q20. lia.
      - exact NNF.
      - intros p E. injection E as <-. exact (conj DY (conj AL AP)).
      - intros p q0 E1' E2'. injection E2' as <-. destruct (APN p E1') as [C|C]; [left; exact C | right; exact C].
      - exact NNM0.
      - intros p b0 n0 E Hin. injection E as <-. exact (APM0 b0 n0 Hin). }
    assert (EST : st' = depot_st st (a_dep st') [(U a, U a + 2 ^ 23)]) by ((lazymatch goal with |- ?G => let G' := eval unfold st', op_depot_insert, depot_st in G in change_no_check G' end); (lazymatch goal with |- ?G => let G' := eval cbn [blk_opt store_aa List.map a_dep] in G in change_no_check G' end); reflexivity).
    assert (ETAB : DEPOT_TAB bt = 0x1f0098) by ((lazymatch goal with |- ?G => let G' := eval unfold DEPOT_TAB in G in change_no_check G' end); rewrite BT_ia; reflexivity).
    assert (ENID : DEPOT_NIDS bt = 0x1f0098 + 4194304) by ((lazymatch goal with |- ?G => let G' := eval unfold DEPOT_NIDS in G in change_no_check G' end); rewrite ETAB; reflexivity).
    assert (EMAP : DEPOT_MAP1 bt = 0x1f0098 + 4194320) by ((lazymatch goal with |- ?G => let G' := eval unfold DEPOT_MAP1 in G in change_no_check G' end); rewrite ETAB; reflexivity).
    assert (ESS : SSOBJ bt = 1966216) by ((lazymatch goal with |- ?G => let G' := eval unfold SSOBJ in G in change_no_check G' end); rewrite BT_ia; reflexivity).
    assert (ENB : node_blocks bt (a_dep st') = node_blocks bt d ++ blk_opt nn) by reflexivity.
    assert (ESB : store_blocks bt (a_dep st') = store_blocks bt d ++ [U a]) by reflexivity.
    assert (ENA : node_addr bt (a_dep st') (NIDS + 1) = U ndW) by ((lazymatch goal with |- ?G => let G' := eval unfold node_addr in G in change_no_check G' end); rewrite ENB; fold idx; symmetry; exact ND).
    assert (INA : In (U a) (store_blocks bt (a_dep st'))) by (rewrite ESB; apply in_or_app; right; left; reflexivity).
    assert (INNB : In nb (node_blocks bt (a_dep st'))).
    { rewrite ENB. apply in_or_app. destruct NBc as [INB | ENN]; [left; exact INB | right; rewrite ENN; left; reflexivity]. }
    assert (NTH : forall i, 0 <= i < 2 ^ 12 -> i <> qs -> nth (Z.to_nat i) (store_blocks bt (a_dep st')) 0 = nth (Z.to_nat i) (store_blocks bt d) 0).
    { intros i Hi NE. rewrite ESB. destruct (Z_lt_le_dec i qs) as [L|L].
      - apply app_nth1. rewrite QSL in L. clear - L Hi. lia.
      - rewrite !nth_overflow; [reflexivity | rewrite QSL in L; clear - L NE QSL; lia | rewrite length_app; (lazymatch goal with |- ?G => let G' := eval cbn [length] in G in change_no_check G' end); rewrite QSL in L, NE; clear - L NE; lia]. }
    assert (NTHQ : nth (Z.to_nat qs) (store_blocks bt (a_dep st')) 0 = U a).
    { rewrite ESB, QSL, Nat2Z.id. rewrite app_nth2 by apply Nat.le_refl. rewrite Nat.sub_diag. reflexivity. }
    (* [comment removed for export] *)
    assert (XCLS : forall z, cls02 (U sp) b idx (U ndW) qs nn z \/ (U a <= z < U a + 2 ^ 23) -> z < U sp - 576 -> ~ X z).
    { intros z [[C|[C|[C|[C|[[_ C]|[(p & Ep & C)|[C|[C|[C|C]]]]]]]]] | C] Hlt Xz.
      - clear - C Hlt. lia.
      - apply (XI z); [clear - C Hbix; lia | exact Xz].
      - apply (XI z); [clear - C; lia | exact Xz].
      - apply (XI z); [clear - C; lia | exact Xz].
      - apply (XI z); [clear - C I16; lia | exact Xz].
      - destruct (NNV p z Ep C) as (_ & NX & _). exact (NX Xz).
      - exact (proj2 (NBV z ltac:(clear - C NB1 NB2; lia)) Xz).
      - apply (XI z); [clear - C; lia | exact Xz].
      - apply (XI z); [clear - C Q20; lia | exact Xz].
      - apply (XI z); [clear - C Q20; lia | exact Xz].
      - exact (px_off_fresh bt st Lc FF X (U a) (2 ^ 23) z W PXH Xz AP DY C). }
    (* [comment removed for export] *)
    assert (Kso' : rdn BSEGS M'r (Z_to_bv 64 (1966216 + 24 + 16 * qs)) 4 = Some (LE4 (Z_to_bv 64 (std' qs)))).
    { replace (Z_to_bv 64 (1966216 + 24 + 16 * qs)) with (st_cell SSW start : word) by ((lazymatch goal with |- ?G => let G' := eval unfold st_cell in G in change_no_check G' end); rewrite USS; fold qs; f_equal; clear; lia).
      rewrite Kso, STDQ. f_equal. apply stored_le4b; [exact SO | (lazymatch goal with |- ?G => let G' := eval unfold cnt in G in change_no_check G' end); clear - SZ; lia]. }
    assert (NDR : 0 <= U ndW /\ U ndW + 16 < 2 ^ 64) by (clear - Hndr NB2 NBC CR; lia).
    assert (Kl' : rdn BSEGS M'r (Z_to_bv 64 (U ndW + 8)) 4 = Some (LE4 (Z_to_bv 64 (dp_tab d b)))).
    { replace (Z_to_bv 64 (U ndW + 8)) with (at_ ndW 8 : word); [exact Kl|]. apply bv_eq. rewrite at_u by (clear - NDR; lia). rewrite u_Z2bv by (clear - NDR; lia). reflexivity. }
    assert (Ks' : rdn BSEGS M'r (Z_to_bv 64 (U ndW + 12)) 4 = Some (LE4 (Z_to_bv 64 (start + 1)))).
    { replace (Z_to_bv 64 (U ndW + 12)) with (at_ ndW 12 : word); [rewrite Ks; f_equal; apply st_id_le4; [exact ST0 | clear - ST32 SZ; lia]|].
      apply bv_eq. rewrite at_u by (clear - NDR; lia). rewrite u_Z2bv by (clear - NDR; lia). reflexivity. }
    assert (Kbd' : rdn BSEGS M'r (Z_to_bv 64 (1966216 + 16 + 16 * qs)) 8 = Some (LE8 a)).
    { replace (Z_to_bv 64 (1966216 + 16 + 16 * qs)) with BI by ((lazymatch goal with |- ?G => let G' := eval unfold BI in G in change_no_check G' end); rewrite USS; f_equal; clear; lia). exact Kbd. }
    assert (Kbl' : rdn BSEGS M'r (Z_to_bv 64 (1966216 + 28 + 16 * qs)) 1 = Some [Z_to_bv 8 0]).
    { replace (Z_to_bv 64 (1966216 + 28 + 16 * qs)) with (at_ BI 12 : word); [exact Kbl|]. apply bv_eq. rewrite UBL. rewrite u_Z2bv by (clear - Q20; lia). clear. lia. }
    assert (XIMG' : forall i, AIMGLO <= i < AIMGHI -> ~ X i /\ Hd (Z_to_bv 64 i) = false).
    { intros i Hi. split; [apply XI; exact Hi | apply NHs; [clear - Hi; lia | right; clear - Hi; lia]]. }
    assert (XND : forall i, U ndW <= i < U ndW + 16 -> ~ X i /\ Hd (Z_to_bv 64 i) = false).
    { intros i Hi. destruct (NBV i ltac:(clear - Hi NB1 NB2; lia)) as [V1 V2]. split; assumption. }
    assert (XAB : forall i, U a <= i < U a + 2 ^ 23 -> ~ X i /\ Hd (Z_to_bv 64 i) = false).
    { intros i Hi. split; [intros Xi; exact (px_off_fresh bt st Lc FF X (U a) (2 ^ 23) i W PXH Xi AP DY Hi) | apply NHa; exact Hi]. }
    (* [comment removed for export] *)
    assert (OUTW : forall z, AIMGLO <= z < AIMGHI -> ~ (0x1f0098 + 4 * b <= z < 0x1f0098 + 4 * b + 4) -> ~ (0x1f0098 + 4194304 <= z < 0x1f0098 + 4194304 + 4)
                     -> ~ (0x1f0098 + 4194312 <= z < 0x1f0098 + 4194312 + 4) -> ~ (0x1f0098 + 4194320 + 8 * idx <= z < 0x1f0098 + 4194320 + 8 * idx + 8)
                     -> ~ (1966216 <= z < 1966216 + 16) -> ~ (1966216 + 16 * qs + 16 <= z < 1966216 + 16 * qs + 32)
                     -> ~ (1966216 + 16 * (qs - 1) + 24 <= z < 1966216 + 16 * (qs - 1) + 28) -> ~ Wall z).
    { intros z Hz N1 N2 N3 N4 N5 N6 N7 WZ.
      destruct (CLS _ WZ) as [[C|[C|[C|[C|[[_ C]|[(p & Ep & C)|[C|[C|[C|C]]]]]]]]] | C].
      - clear - C Hz SPC CR HKD. lia.
      - exact (N1 C).
      - exact (N2 C).
      - exact (N3 C).
      - exact (N4 C).
      - destruct (NNF p Ep) as ((Y1 & _ & _ & Y4 & _) & _). rewrite BT_ia in Y4. cbn [ia_img_lo ia_img_hi both_addrs] in Y4. clear - C Hz Y1 Y4. lia.
      - clear - C Hz NB1 NBA. lia.
      - exact (N5 C).
      - exact (N6 C).
      - exact (N7 C).
      - clear - C Hz GA. lia. }
    (* [comment removed for export] *)
    assert (RX' : RepX bt X st' Lc FF M' mdl5).
    { apply (RepX_mono bt (fun z => X z /\ ~ False) X); [intros z [Hz _]; exact Hz|].
      apply (repx_step bt X (fun _ => False) Wall Xdec_false st st' Lc Lc FF FF M M' mdl mdl5).
      - exists M0. split; [exact RP | exact DIFF].
      - intros x NE. apply (msum_changed Wall M M'); [(lazymatch goal with |- ?G => let G' := eval unfold Wall, WB2, W2, cpost_W, tail_W in G in change_no_check G' end); repeat apply wun_dec; first [exact WD02 | apply ivl_dec] | split; [exact FRA | exact GRA] | exact NE].
      - intros x F. destruct F.
      - intros N0 N0' RPn Dn DIFF' EQX EQM.
        assert (CELLNEW : forall (z : Z) (k : nat) bz, 0 <= z -> z + Z.of_nat k < 2 ^ 64 -> (forall i, z <= i < z + Z.of_nat k -> ~ X i /\ Hd (Z_to_bv 64 i) = false) ->
                  rdn BSEGS M'r (Z_to_bv 64 z) k = Some bz -> rdn BSEGS N0' (Z_to_bv 64 z) k = Some bz).
        { intros z k bz Hz Hk F Hr. rewrite <- Hr, <- (VIS z k Hz Hk (fun i Hi => proj2 (F i Hi))). apply rdn_ext; [first [ solve [ wd_unorm1; wd_zofnat; lia ] | rewrite u_Z2bv by lia; lia ]|].
          intros x Hx. rewrite u_Z2bv in Hx by lia. apply EQX. left. exact (proj1 (F (U x) Hx)). }
        assert (CELLMID : forall (z : Z) (k : nat) bz, 0 <= z -> z + Z.of_nat k < 2 ^ 64 ->
                  (forall i, z <= i < z + Z.of_nat k -> ~ X i /\ Hd (Z_to_bv 64 i) = false /\ ~ WB2 i /\ ~ W2 i) ->
                  rdn BSEGS MPr (Z_to_bv 64 z) k = Some bz -> rdn BSEGS N0' (Z_to_bv 64 z) k = Some bz).
        { intros z k bz Hz Hk F Hr. rewrite <- Hr. apply rdn_ext; [first [ solve [ wd_unorm1; wd_zofnat; lia ] | rewrite u_Z2bv by lia; lia ]|].
          intros x Hx. rewrite u_Z2bv in Hx by lia. destruct (F (U x) Hx) as (F1 & F2 & F3 & F4). rewrite Z_to_bv_bv_unsigned in F2.
          rewrite (EQX x (or_introl F1)). rewrite (FR2 x F4). rewrite (FRB x F3). exact (VIS2 x F2). }
        assert (CELLOLD : forall (z : Z) (k : nat) bz, 0 <= z -> z + Z.of_nat k < 2 ^ 64 -> (forall i, z <= i < z + Z.of_nat k -> ~ Wall i) ->
                  rdn BSEGS N0 (Z_to_bv 64 z) k = Some bz -> rdn BSEGS N0' (Z_to_bv 64 z) k = Some bz).
        { intros z k bz Hz Hk F Hr. rewrite <- Hr. apply rdn_ext; [first [ solve [ wd_unorm1; wd_zofnat; lia ] | rewrite u_Z2bv by lia; lia ]|]. intros x Hx. rewrite u_Z2bv in Hx by lia.
          destruct (decide (N0' x = N0 x)) as [E|NE]; [exact E|]. exfalso. destruct (DIFF' x NE) as [[WA|[]] _]. exact (F (U x) Hx WA). }
        assert (IMID : forall i, AIMGLO <= i < AIMGHI -> ~ (0x1f0098 + 4 * b <= i < 0x1f0098 + 4 * b + 4) -> ~ (1966216 + 16 * qs + 16 <= i < 1966216 + 16 * qs + 32) ->
                  ~ X i /\ Hd (Z_to_bv 64 i) = false /\ ~ WB2 i /\ ~ W2 i).
        { intros i Hi N1 N2. destruct (XIMG' i Hi) as [V1 V2]. split; [exact V1|]. split; [exact V2|]. split; [exact (proj2 (IMGB i Hi))|].
          intros WZ. destruct (CLS2 _ WZ) as [C|[C|[C|[C|C]]]]; [clear - C Hi SPC CR HKD; lia | exact (N1 C) | clear - C Hi NB1 NBA; lia | exact (N2 C) | clear - C Hi GA; lia]. }
        pose proof RPn as (_ & _ & _ & _ & _ & _ & _ & _ & (Dtab' & Dnids' & Dmu' & Dmap' & Dnode' & Dnw' & Dfr' & Dblk' & Dsw') & _ & _ & _ & (_ & _ & _ & FAl & _) & _).
        fold d in Dtab', Dnids', Dmu', Dmap', Dnode', Dnw', Dfr', Dblk', Dsw'.
        apply (OPS_REP_depot_insert_pf bt st Lc FF N0 N0' mdl mdl5 b (U h) (dp_tab d b) (start + 1) (start + cnt) std' nn (Some (U a)) W W' RPn Hbix).
        + exact NNF.
        + intros p E. injection E as <-. exact (conj DY (conj AL AP)).
        + intros p q0 E1' E2'. injection E2' as <-. destruct (APN p E1') as [C|C]; [left; exact C | right; exact C].
        + intros x NE. destruct (DIFF' x NE) as [[WA|[]] DF]. split; [| exact DF]. (lazymatch goal with |- ?G => let G' := eval unfold foot_depot_ins in G in change_no_check G' end). rewrite ETAB, ENID, EMAP, ESS. fold st' d; fold NIDS; rewrite ENA, ESB.
          destruct (CLS _ WA) as [[C|[C|[C|[C|[[NNe C]|[(p & Ep & C)|[C|[C|[C|C]]]]]]]]] | C].
          * do 7 right. clear - C SPC HKD. lia.
          * left. exact C.
          * right; left. clear - C. lia.
          * right; left. clear - C. lia.
          * right; right; left. split; [exact NNe|]. (lazymatch goal with |- ?G => let G' := eval unfold nn_idx in G in change_no_check G' end). fold d. rewrite <- (NNI NNe). clear - C. lia.
          * do 6 right; left. exists p. split; [exact Ep | exact C].
          * do 4 right; left. exact C.
          * do 3 right; left. clear - C. lia.
          * do 3 right; left. clear - C Q20. lia.
          * do 3 right; left. clear - C Q20. lia.
          * do 5 right; left. exists (U a). split; [apply in_or_app; right; left; reflexivity | exact C].
        + rewrite BT_segs, ETAB. apply CELLNEW; [clear - Hbix; lia | (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); clear - Hbix; lia
                                                 | intros i Hi; apply XIMG'; cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in Hi; clear - Hi Hbix; lia | exact Kb].
        + rewrite BT_segs, ENID. (lazymatch goal with |- ?G => let G' := eval unfold cellZ, cellN in G in change_no_check G' end). apply CELLMID; [clear; lia | (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); clear; lia | | exact Kn0].
          intros i Hi. cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in Hi. apply IMID; clear - Hi Hbix Q20; lia.
        + rewrite BT_segs, ENID. (lazymatch goal with |- ?G => let G' := eval unfold byteZ, cellN in G in change_no_check G' end). change (word_to_le_bytes 1 (Z_to_bv 64 0)) with [Z_to_bv 8 0].
          replace (Z_to_bv 64 (0x1f0098 + 4194304 + 8)) with MUW by (apply bv_eq; reflexivity). (lazymatch goal with |- ?G => let G' := eval unfold MUW in G in change_no_check G' end).
          apply CELLMID; [clear; lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear; lia | | exact Kmu0]. intros i Hi. cbn in Hi. apply IMID; clear - Hi Hbix Q20; lia.
        + rewrite BT_segs. fold st' d; fold NIDS; rewrite ENA. (lazymatch goal with |- ?G => let G' := eval unfold cellZ, cellN in G in change_no_check G' end). rewrite (Z_to_bv_bv_unsigned 64 h).
          apply CELLMID; [clear - NDR; lia | (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); clear - NDR; lia | | rewrite Z_to_bv_bv_unsigned; exact Rhsh].
          intros i Hi. cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in Hi. destruct (XND i ltac:(clear - Hi; lia)) as [V1 V2]. split; [exact V1|]. split; [exact V2|].
          split; [exact (proj2 (NDVB i ltac:(clear - Hi; lia)))|].
          intros WZ. destruct (CLS2 _ WZ) as [C|[C|[C|[C|C]]]]; [clear - C Hi NB1 NB2 NBC SPC HKD; lia | clear - C Hi NB1 NBA Hbix; lia | clear - C Hi; lia
                                                               | clear - C Hi NB1 NBA Q20; lia | clear - C Hi NB1 NB2 NBAP; lia].
        + rewrite BT_segs. fold st' d; fold NIDS; rewrite ENA.
          apply CELLNEW; [clear - NDR; lia | (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); clear - NDR; lia
                          | intros i Hi; apply XND; cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in Hi; clear - Hi; lia | exact Kl'].
        + rewrite BT_segs. fold st' d; fold NIDS; rewrite ENA.
          apply CELLNEW; [clear - NDR; lia | (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); clear - NDR; lia
                          | intros i Hi; apply XND; cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in Hi; clear - Hi; lia | exact Ks'].
        + intros p E. split.
          * rewrite BT_segs, EMAP. (lazymatch goal with |- ?G => let G' := eval unfold nn_idx in G in change_no_check G' end). fold d. rewrite <- (NNI ltac:(rewrite E; discriminate)). (lazymatch goal with |- ?G => let G' := eval unfold cellZ, cellN in G in change_no_check G' end).
            apply CELLMID; [clear - I16; lia | (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); clear - I16; lia | | exact (Kslot0 p E)].
            intros i Hi. cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in Hi. apply IMID; clear - Hi Hbix Q20 I16; lia.
          * rewrite BT_segs. intros i Hi. destruct (NNV p i E Hi) as (V1 & V2 & V3). destruct (NNR p E) as [P0 P1].
            assert (DI : N0' (Z_to_bv 64 i) <> None).
            { rewrite (EQX (Z_to_bv 64 i)) by (left; rewrite u_Z2bv by (clear - Hi P0 P1; lia); exact V2). apply GR2. apply GRB. exact V3. }
            split; [exact DI | apply store_ok1_some; exact DI].
        + rewrite BT_segs, ESS. apply CELLMID; [clear; lia | (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); clear; lia | | exact Rtot'].
          intros i Hi. cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in Hi. apply IMID; clear - Hi Hbix Q20; lia.
        + intros i Hi. fold st'. fold d. destruct (Dblk' i Hi) as (Cq1 & Cq2 & Cq3). rewrite BT_segs, ESS in *.
          destruct (Z.eq_dec i qs) as [->|NEq].
          * rewrite NTHQ. split; [| split].
            -- (lazymatch goal with |- ?G => let G' := eval unfold cellZ, cellN in G in change_no_check G' end). rewrite Z_to_bv_bv_unsigned. apply CELLNEW; [clear - Q20; lia | (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); clear - Q20; lia
                                 | intros j Hj; apply XIMG'; cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in Hj; clear - Hj Q20; lia | exact Kbd'].
            -- apply CELLNEW; [clear - Q20; lia | (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); clear - Q20; lia
                               | intros j Hj; apply XIMG'; cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in Hj; clear - Hj Q20; lia | exact Kso'].
            -- (lazymatch goal with |- ?G => let G' := eval unfold byteZ, cellN in G in change_no_check G' end). change (word_to_le_bytes 1 (Z_to_bv 64 0)) with [Z_to_bv 8 0].
               apply CELLNEW; [clear - Q20; lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear - Q20; lia | intros j Hj; apply XIMG'; cbn in Hj; clear - Hj Q20; lia | exact Kbl'].
          * rewrite (NTH i Hi NEq). split; [| split].
            -- apply CELLOLD; [clear - Hi; lia | (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); clear - Hi; lia | | exact Cq1].
               intros j Hj. cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in Hj. apply OUTW; clear - Hj Hi Hbix Q20 I16 NEq; lia.
            -- (lazymatch goal with |- ?G => let G' := eval unfold cellZ, cellN in G in change_no_check G' end). apply CELLMID; [clear - Hi; lia | (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); clear - Hi; lia | | exact (CST i Hi NEq)].
               intros j Hj. cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in Hj. apply IMID; clear - Hj Hi Hbix Q20 NEq; lia.
            -- apply CELLOLD; [clear - Hi; lia | (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); clear - Hi; lia | | exact Cq3].
               intros j Hj. cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in Hj. apply OUTW; clear - Hj Hi Hbix Q20 I16 NEq; lia.
        + intros q0 E. injection E as <-. rewrite BT_segs. intros i Hi. destruct (XAB i Hi) as [V1 V2].
          assert (DI : N0' (Z_to_bv 64 i) <> None).
          { rewrite (EQX (Z_to_bv 64 i)) by (left; rewrite u_Z2bv by (clear - Hi Har GC CR; lia); exact V1). apply GR2. apply DEFA. rewrite u_Z2bv by (clear - Hi Har GC CR; lia). exact Hi. }
          split; [exact DI | apply store_ok1_some; exact DI].
        + (lazymatch goal with |- ?G => let G' := eval cbn [blk_opt List.map app] in G in change_no_check G' end). rewrite Evm5, L1, LN1. rewrite Z_to_bv_bv_unsigned. fold (nnpart nn). change (Z_to_bv 64 (2 ^ 23)) with szW. apply Permutation_middle.
        + rewrite Evm5, L2. exact LN2.
        + intros x. rewrite Elz5. rewrite (L3b x). rewrite LN3. rewrite Usz. split.
          * intros [H | [Hr H]]; [left; exact H | right; exists (U a); split; [reflexivity | exact H]].
          * intros [H | (q0 & E & H)]; [left; exact H | right; injection E as <-; split; [clear - H Har GC CR; lia | exact H]].
        + rewrite Elz5, L3, LN3. constructor; [| exact FAl]. (lazymatch goal with |- ?G => let G' := eval cbn [fst snd] in G in change_no_check G' end). rewrite Usz. destruct DY as (Y1 & Y2 & Y3 & Y4 & Y5).
          split; [exact AL|]. split; [reflexivity|]. split; [exact Y1|]. split; [exact Y3|]. rewrite BT_ia in Y4 |- *. exact Y4.
        + rewrite Evm5, L4. exact LN4.
        + rewrite Evm5, L5. exact LN5.
        + rewrite Evm5, L6. exact LN6.
        + rewrite Evm5, L7. exact LN7.
        + rewrite Evm5, L8. exact LN8.
        + rewrite Evm5, L9. exact LN9.
        + (lazymatch goal with |- ?G => let G' := eval cbn [store_aa blk_opt List.map] in G in change_no_check G' end). fold A2. exact MI5.
        + rewrite Eeg5. clear - L10 LEAG. lia. }
    (* [comment removed for export] *)
    assert (CHG : forall x : word, M' x <> M x -> Wall (U x) /\ M' x <> None).
    { intros x NE. apply (msum_changed Wall M M'); [(lazymatch goal with |- ?G => let G' := eval unfold Wall, WB2, W2, cpost_W, tail_W in G in change_no_check G' end); repeat apply wun_dec; first [exact WD02 | apply ivl_dec] | split; [exact FRA | exact GRA] | exact NE]. }
    apply katD_refl. exists fx, st', M', mdl5, r2, (NIDS + 1).
    split; [reflexivity|]. split; [exact HFX|]. split; [exists (a_dep st'), [(U a, U a + 2 ^ 23)]; exact EST|]. split; [exact W'|]. split; [exact RX'|].
    split.
    { intros x Xx OUT. apply FRA. intros WA. destruct (Z_lt_le_dec (U x) (U sp - 576)) as [L|L]; [exact (XCLS _ (CLS _ WA) L Xx)|].
      destruct (CLS _ WA) as [[C|[C|[C|[C|[[_ C]|[(p & Ep & C)|[C|[C|[C|C]]]]]]]]] | C].
      - clear - C L OUT HKD. lia.
      - clear - C L SPC CR HKD Hbix. lia.
      - clear - C L SPC CR HKD. lia.
      - clear - C L SPC CR HKD. lia.
      - clear - C L SPC CR HKD I16. lia.
      - destruct (NNF p Ep) as ((_ & _ & Y3 & _) & _). clear - C L SPC HKD Y3. lia.
      - clear - C L SPC HKD NB2 NBC. lia.
      - clear - C L SPC CR HKD. lia.
      - clear - C L SPC CR HKD Q20. lia.
      - clear - C L SPC CR HKD Q20. lia.
      - clear - C L SPC HKD GC. lia. }
    split.
    { intros x NE. destruct (CHG x NE) as [WA DF]. split; [| exact DF]. (lazymatch goal with |- ?G => let G' := eval unfold depot_foot_w, depot_foot, foot_depot_static in G in change_no_check G' end). rewrite ETAB, ENID, EMAP, ESS.
      destruct (CLS _ WA) as [[C|[C|[C|[C|[[_ C]|[(p & Ep & C)|[C|[C|[C|C]]]]]]]]] | C].
      - left. do 3 right. clear - C HKD. lia.
      - left. left. left. clear - C Hbix. lia.
      - left. left. left. clear - C. lia.
      - right. right. clear - C. lia.
      - left. left. right; right; left. clear - C I16. lia.
      - left. right; left. exists p. split; [rewrite ENB; apply in_or_app; right; rewrite Ep; left; reflexivity | exact C].
      - left. right; left. exists nb. split; [exact INNB | clear - C NB1 NB2; lia].
      - destruct (Z_lt_le_dec (U x) (1966216 + 8)) as [L|L]; [left; left; do 3 right; left; clear - C L; lia | right; left; clear - C L; lia].
      - left. left. do 4 right. clear - C Q20. lia.
      - left. left. do 4 right. assert (QS1 : 1 <= qs) by (rewrite QSL; (lazymatch goal with |- ?G => let G' := eval unfold store_blocks in G in change_no_check G' end); (lazymatch goal with |- ?G => let G' := eval cbn [length] in G in change_no_check G' end); rewrite Nat2Z.inj_succ; clear; lia). clear - C Q20 QS1. lia.
      - left. right; right; left. exists (U a). split; [exact INA | exact C]. }
    split.
    { intros x NE. destruct (CHG x NE) as [WA DF]. destruct DOBL as (_ & DO2 & DO3).
      assert (IP : forall z, 0x1a0061 <= z < 0x630810 -> in_wins (ia_priv (bt_ia bt)) z).
      { intros z Hz. rewrite BT_ia. exists 0x1a0061, 0x630810. split; [(lazymatch goal with |- ?G => let G' := eval cbn [ia_priv both_addrs In] in G in change_no_check G' end); do 6 right; left; reflexivity | exact Hz]. }
      destruct (CLS _ WA) as [[C|[C|[C|[C|[[_ C]|[(p & Ep & C)|[C|[C|[C|C]]]]]]]]] | C].
      - left. clear - C HKD. lia.
      - right; right. apply IP. clear - C Hbix. lia.
      - right; right. apply IP. clear - C. lia.
      - right; right. apply IP. clear - C. lia.
      - right; right. apply IP. clear - C I16. lia.
      - right; left. apply (DO2 st' Lc FF p (U x) W'); [rewrite ENB; apply in_or_app; right; rewrite Ep; left; reflexivity | exact C].
      - right; left. apply (DO2 st' Lc FF nb (U x) W' INNB). clear - C NB1 NB2. lia.
      - right; right. apply IP. clear - C. lia.
      - right; right. apply IP. clear - C Q20. lia.
      - right; right. apply IP. clear - C Q20. lia.
      - right; left. exact (DO3 st' Lc FF (U a) (U x) W' INA C). }
    split.
    { intros z Hz. unfold as_callee_saved in Hz. cbn [In] in Hz.
      destruct Hz as [<-|Hz]; [transitivity sp; [exact C2 | symmetry; exact E2]|].
      assert (KEEP : forall k, ~ In (Z_to_bv 5 k) put_clob -> ~ In (Z_to_bv 5 k) mnr_clob -> ~ In (Z_to_bv 5 k) sd_clobx -> getr r2 (Z_to_bv 5 k) = getr R (Z_to_bv 5 k)).
      { intros k N1 N2 N3. rewrite (AG2 _ N1), (AGm _ N2). exact (AG0 k N1 N3). }
      assert (GS : forall k, In k [8; 9; 18; 19; 20; 21; 22; 23; 24; 25] -> getr r2 (Z_to_bv 5 k) = getr R (Z_to_bv 5 k)).
      { intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [assumption|]). destruct Hk. }
      repeat (destruct Hz as [<-|Hz]; [first [apply GS; (lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); solve [repeat (first [left; reflexivity | right])] | apply KEEP; [(lazymatch goal with |- ?G => let G' := eval unfold put_clob in G in change_no_check G' end); nin5 | (lazymatch goal with |- ?G => let G' := eval unfold mnr_clob in G in change_no_check G' end); nin5 | (lazymatch goal with |- ?G => let G' := eval unfold sd_clobx in G in change_no_check G' end); nin5]]|]).
      destruct Hz. }
    split; [exact C10|]. split; [clear - NN0 NROOM; lia|].
    split.
    { apply (same_except_vm_trans mdl mdlN mdl5); [exact LNS|].
      apply (same_except_vm_trans mdlN mdlm mdl5); [exact (same_but_materialized_except_vm mdlN mdlm SBMm)|].
      apply (same_except_vm_trans mdlm (mmap_model_noreserve a szW mdlm) mdl5); [apply sev_mmap_model_nr|].
      apply (same_except_vm_trans _ mdl4 mdl5); [exact (same_but_materialized_except_vm _ _ SBM4) | exact (same_but_materialized_except_vm _ _ SBM5)]. }
    split.
    { intros x Hxr. destruct (Z_lt_le_dec x (U a)) as [Lx|Lx]; [| destruct (Z_lt_le_dec x (U a + 2 ^ 23)) as [Lx2|Lx2]].
      - left. (lazymatch goal with |- ?G => let G' := eval unfold lzb in G in change_no_check G' end). rewrite Elz5, L3, LN3. rewrite AsKSys6.AsanNodesMmLib.page_in_ranges_cons. (lazymatch goal with |- ?G => let G' := eval cbn [fst snd] in G in change_no_check G' end). rewrite Usz.
        replace ((U a <=? U (page_base (Z_to_bv 64 x))) && (U (page_base (Z_to_bv 64 x)) + page_size <=? U a + 2 ^ 23))%bool with false; [reflexivity|].
        symmetry. apply andb_false_iff. left. apply Z.leb_gt. pose proof (AsKSys6.AsanNodesMmLib.page_base_facts (Z_to_bv 64 x)) as (PB1 & _). rewrite u_Z2bv in PB1 by (clear - Hxr; lia). clear - PB1 Lx. lia.
      - right. exists (U a). split; [(lazymatch goal with |- ?G => let G' := eval unfold st', op_depot_insert in G in change_no_check G' end); (lazymatch goal with |- ?G => let G' := eval cbn [a_dep dp_storeblocks blk_opt] in G in change_no_check G' end); apply in_or_app; right; left; reflexivity|].
        split; [| clear - Lx Lx2; lia]. intros INo.
        destruct (AP (U a) (U a + 2 ^ 23) (all_ranges_dyn bt st _ (store_dyn st (U a) INo))) as [C|C]; clear - C; lia.
      - left. (lazymatch goal with |- ?G => let G' := eval unfold lzb in G in change_no_check G' end). rewrite Elz5, L3, LN3. rewrite AsKSys6.AsanNodesMmLib.page_in_ranges_cons. (lazymatch goal with |- ?G => let G' := eval cbn [fst snd] in G in change_no_check G' end). rewrite Usz.
        replace ((U a <=? U (page_base (Z_to_bv 64 x))) && (U (page_base (Z_to_bv 64 x)) + page_size <=? U a + 2 ^ 23))%bool with false; [reflexivity|].
        symmetry. apply andb_false_iff. right. apply Z.leb_gt. pose proof (AsKSys6.AsanNodesMmLib.page_base_facts (Z_to_bv 64 x)) as (_ & PB2 & _). rewrite u_Z2bv in PB2 by (clear - Hxr; lia).
        (lazymatch goal with |- ?G => let G' := eval unfold page_size in G in change_no_check G' end). clear - PB2 Lx2. lia. }
    split; [rewrite Ehl5; exact HL4 | exact (model_ivs_wf_sbm mdl4 mdl5 SBM5 L11)].
  Qed.
End TOPS1.
