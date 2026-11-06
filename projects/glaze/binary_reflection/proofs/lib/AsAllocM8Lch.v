(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AmLia.   (* [comment removed for export] *)
(* [comment removed for export] *)
Require Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Logic.FunctionalExtensionality LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mprotect LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocSim OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys6 OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.BackingAlgebra OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsP33 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM9b OSSVerify.Proofs.glaze.binary_reflection.lib.AsCodeM5 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8k OSSVerify.glaze.binary_reflection.images.Asan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module AsAllocM8kh.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import Stdlib.Logic.FunctionalExtensionality.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mprotect.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.DivergeSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.SpinAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes.AgentNodes OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocSim OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys6.MhKSys OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsK OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys6.AsKSys OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys6.AsKSys2 OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsRtK OSSVerify.Proofs.glaze.binary_reflection.lib.Common.BackingAlgebra OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys6.AsanNodesLibE OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsP33.AsKSys3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM9b.AsAllocM8m OSSVerify.Proofs.glaze.binary_reflection.lib.AsCodeM5 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8k.
Import OSSVerify.glaze.binary_reflection.images.Asan.
Import ListNotations.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation ASEGS := Asan.M.loaded_segments.
#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).
#[local] Abbreviation LE4 z := (word_to_le_bytes 4 (Z_to_bv 64 z)).
#[local] Abbreviation U := bv_unsigned.

Section FPGen1h.
Context {fx : FPState}.

Section MAPKH.
  Variable Hd : word -> bool.
  Hypothesis HOFFSEG : H_off_segments ASEGS Hd.
  Hypothesis WX : wx_segs_nowrap ASEGS.

  Theorem rarmap_katsD_h :
    forall (A : list (Z * Z)) regs (mem rom : word -> option byte) (model : Model)
           (sp ra s0v s1v s2v s3v s4v s5v addr size name : word) (PGP CF : Z) (Qok Qf : config -> Prop)
           (MOK MKP : Model -> Model),
    let M1 := mfi_m1 mem sp ra s0v s1v s2v s3v s4v s5v addr size name PGP in
    let ENOMEMw : word := Z_to_bv 64 (2 ^ 64 - 12) in
    let SCR := LE4 0xffffffffaaaaaaaa in
    (* [comment removed for export] *)
    getr regs 1 = ra -> getr regs 2 = sp -> getr regs 11 = addr -> getr regs 12 = size -> getr regs 13 = name ->
    getr regs 8 = s0v -> getr regs 9 = s1v -> getr regs 18 = s2v -> getr regs 19 = s3v -> getr regs 20 = s4v -> getr regs 21 = s5v ->
    (2 ^ 24 <= U sp /\ U sp + 16 <= 2 ^ 47) -> ret_ok ra ->
    U addr mod 4096 = 0 -> (U size mod 4096 = 0 /\ U size + 4096 < 2 ^ 63) -> U name <> 0 ->
    (AIMGLO <= PGP /\ PGP + 8 <= AIMGHI) -> (AIMGLO <= CF /\ CF + 264 <= AIMGHI) ->
    store_ok ASEGS mem (at_ sp (-400)) 400 = true ->
    rdn ASEGS mem (Z_to_bv 64 0xff250) 8 = Some (LE8 (Z_to_bv 64 PGP)) ->
    rdn ASEGS mem (Z_to_bv 64 PGP) 8 = Some (LE8 (Z_to_bv 64 4096)) ->
    rdn ASEGS mem (Z_to_bv 64 0xff260) 8 = Some (LE8 (Z_to_bv 64 CF)) ->
    rdn ASEGS mem (Z_to_bv 64 (CF + 260)) 1 = Some [Z_to_bv 8 0] ->
    rdn ASEGS mem (Z_to_bv 64 (CF + 144)) 8 = Some (LE8 (Z_to_bv 64 0)) ->
    (* [comment removed for export] *)
    (AIMGHI <= U addr /\ U addr + U size < 2 ^ 63 /\ (U addr + U size <= U sp - 400 \/ U sp <= U addr)) ->
    (* [comment removed for export] *)
    hid_off Hd 0xff250 8 -> hid_off Hd PGP 8 -> hid_off Hd 0xff260 8 -> hid_off Hd (CF + 260) 1 -> hid_off Hd (CF + 144) 8 ->
    hid_off Hd (U sp - 400) 400 ->
    (* [comment removed for export] *)
    m_halted model = None -> lazy_cover Hd (m_vm_lazy model) A -> A_wf A -> MInv A model ->
    (* [comment removed for export] *)
    (forall mdlm (r1 : bvmap 5 word), same_but_materialized model mdlm -> MInv A mdlm -> m_halted mdlm = None ->
        getr r1 10 = addr -> getr r1 11 = size -> getr r1 12 = Z_to_bv 64 3 -> getr r1 13 = Z_to_bv 64 50 ->
        getr r1 14 = Z_to_bv 64 (2 ^ 64 - 1) -> getr r1 15 = Z_to_bv 64 0 ->
        forall Qok' Qf' : config -> Prop,
          katwD ASEGS (mkCfg (mkst (regupd r1 10 addr) (0x80740 : word) (zfill addr size M1) rom) (MOK mdlm)) Qok' Qf' ->
          katsD ASEGS (mkCfg (epend r1 (0x8073c : word) M1 rom (Z_to_bv 64 222)) mdlm) Qok' Qf') ->
    (* [comment removed for export] *)
    (forall mdlm, same_but_materialized model mdlm -> MInv A mdlm ->
        (m_halted (MOK mdlm) = None /\ lazy_cover Hd (m_vm_lazy (MOK mdlm)) A /\ MInv A (MOK mdlm))
        /\ (m_halted (MKP mdlm) = None /\ lazy_cover Hd (m_vm_lazy (MKP mdlm)) A /\ MInv A (MKP mdlm))) ->
    (* [comment removed for export] *)
    (forall (r' : bvmap 5 word) mdlm mdl4,
        same_but_materialized model mdlm -> MInv A mdlm -> same_but_materialized (MOK mdlm) mdl4 -> MInv A mdl4 ->
        mfi_ret regs r' sp ra s0v s1v s2v s3v s4v addr ->
        katwD ASEGS (mkCfg (mkst r' ra (wbytes (zfill addr size M1) (at_ sp (-84)) SCR) rom) mdl4) Qok Qf) ->
    (* [comment removed for export] *)
    (forall (r' : bvmap 5 word) mdlm mdl4,
        same_but_materialized model mdlm -> MInv A mdlm -> same_but_materialized (MKP mdlm) mdl4 -> MInv A mdl4 ->
        mfi_ret regs r' sp ra s0v s1v s2v s3v s4v (Z_to_bv 64 0) ->
        katD ASEGS (mkCfg (mkst r' ra (wbytes (wbytes M1 (at_ sp (-84)) SCR) (at_ sp (-84)) (LE4 12)) rom) mdl4) Qf) ->
    katsD ASEGS (mkCfg (mkst regs (0x8a688 : word) mem rom) model) Qok Qf.
  Proof using WX HOFFSEG.
    intros A regs mem rom model sp ra s0v s1v s2v s3v s4v s5v addr size name PGP CF Qok Qf MOK MKP M1 ENOMEMw SCR
           H1 H2 H11 H12 H13 H8 H9 H18 H19 H20 H21 Hsp Hret Haddr Hsize Hname HPGP HCF Hstk Rgpg Rpg Rgcf Rdpm Rlim
           Hslot HDgpg HDpg HDgcf HDdpm HDlim HDscr HALT LC AWF MI NODE CHILD CONTOK CONTKP.
    pose proof (u64_range sp) as Hspr. pose proof (u64_range addr) as Har. pose proof (u64_range size) as Hszr.
    destruct Hslot as (SL1 & SL2 & SL3). destruct HPGP as [PG1 PG2]. destruct HCF as [CF1 CF2].
    (* [comment removed for export] *)
    assert (Hstk' : store_ok ASEGS (mrestrict Hd mem) (at_ sp (-400)) 400 = true).
    { rewrite store_ok_mrestrict; [exact Hstk | first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); exact HDscr]. }
    assert (CELLR : forall (c : Z) (k : nat) v, 0 <= c < 2 ^ 32 -> Z.of_nat k <= 8 -> hid_off Hd c (Z.of_nat k) ->
               rdn ASEGS mem (Z_to_bv 64 c) k = Some v -> rdn ASEGS (mrestrict Hd mem) (Z_to_bv 64 c) k = Some v).
    { intros c k v Hc0 Hc1 Hh Hr. rewrite rdn_mrestrict; [exact Hr | first [ solve [ wd_unorm1; wd_zofnat; lia ] | rewrite u_Z2bv by lia; lia ] | rewrite u_Z2bv by lia; exact Hh]. }
    destruct (mfi_pre (mrestrict Hd mem) rom sp ra s0v s1v s2v s3v s4v s5v addr size name PGP CF regs
                H1 H2 H11 H12 H13 H8 H9 H18 H19 H20 H21 Hsp Haddr Hsize Hname (conj PG1 PG2) (conj CF1 CF2) Hstk'
                (CELLR 0xff250 8%nat _ ltac:(lia) ltac:((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia) HDgpg Rgpg) (CELLR PGP 8%nat _ ltac:(lia) ltac:((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia) HDpg Rpg)
                (CELLR 0xff260 8%nat _ ltac:(lia) ltac:((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia) HDgcf Rgcf) (CELLR (CF + 260) 1%nat _ ltac:(lia) ltac:((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia) HDdpm Rdpm))
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
    apply (katsD_msteps_acct ASEGS Hd HOFFSEG WX A (mkst regs (0x8a688 : word) mem rom)
             (mkst r1 (0x8073c : word) (mrestrict Hd M1) rom) model Qok Qf LC AWF MI HALT).
    { rewrite mk_restrict_mkst. exact RUN1. }
    intros mdlm MIm SBMm HC1. rewrite mk_unrestrict_mkst.
    replace (RiscvSemantics.ms_mem (mkst regs (0x8a688 : word) mem rom)) with mem by reflexivity.
    rewrite (mk_munrestrict_same Hd mem M1 M1hid).
    pose proof (same_but_materialized_frame model mdlm SBMm) as FRm.
    assert (HALTm : m_halted mdlm = None) by (destruct FRm as (_&_&_&_&_&_&_&_&_&_&_&_&Hh&_); rewrite Hh; exact HALT).
    (* [comment removed for export] *)
    apply (katsD_ecall ASEGS r1 (0x8073c : word) M1 rom mdlm W_80734 Qok Qf HALTm F_80734 E_80734).
    rewrite B17.
    destruct (CHILD mdlm SBMm MIm) as ((HOK1 & HOK2 & HOK3) & _).
    (* [comment removed for export] *)
    assert (POSTF : forall MZ : word -> option byte,
               (forall x : word, U sp - 400 <= U x < U sp -> MZ x = M1 x) ->
               store_ok ASEGS (mrestrict Hd MZ) (at_ sp (-84)) 4 = true
               /\ (forall (k : Z) (v : word), In (k, v) [(-8, ra); (-16, s0v); (-24, s1v); (-32, s2v); (-40, Z_to_bv 64 0x8a6b4); (-48, size);
                                                         (-56, addr); (-64, s2v); (-72, s3v); (-80, s4v)] ->
                      rdn ASEGS (mrestrict Hd MZ) (at_ sp k) 8 = Some (LE8 v))).
    { intros MZ EZ. split.
      - rewrite store_ok_mrestrict; [| first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); intros x Hx; apply HDscr; lia].
        rewrite (store_ok_ext ASEGS 4 M1 MZ); [| first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | intros x Hx; apply EZ; rewrite at_u in Hx by lia; cbn in Hx; lia].
        eapply store_ok_mono; [apply mfi_m1_grows|].
        eapply (store_ok_sub ASEGS mem (at_ sp (-400)) _ 400); [first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | exact Hstk | first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite !at_u by lia; lia ] | first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite !at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ]].
      - intros k v Hin.
        assert (Hk : -80 <= k <= -8) by (cbn [In] in Hin; repeat (destruct Hin as [E|Hin]; [injection E as <- <-; lia|]); destruct Hin).
        rewrite rdn_mrestrict; [| first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); intros x Hx; apply HDscr; lia].
        rewrite <- (mfi_m1_slots mem sp ra s0v s1v s2v s3v s4v s5v addr size name PGP Hsp k v Hin). fold M1.
        apply rdn_ext; [first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | intros x Hx; apply EZ; rewrite at_u in Hx by lia; cbn in Hx; lia]. }
    assert (Q1 : forall v : word, getr (regupd r1 10 v) 1 = Z_to_bv 64 0x824fc) by (intros v; rewrite getr_other by (intros E; discriminate E); exact B1).
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
                 rdn ASEGS mem (Z_to_bv 64 c) k = Some v -> rdn ASEGS (mrestrict Hd MZ) (Z_to_bv 64 c) k = Some v).
      { intros c k v Hc0 Hc1 Hh Hr. rewrite rdn_mrestrict; [| first [ solve [ wd_unorm1; wd_zofnat; lia ] | rewrite u_Z2bv by lia; lia ] | rewrite u_Z2bv by lia; exact Hh].
        rewrite <- Hr. apply rdn_ext; [first [ solve [ wd_unorm1; wd_zofnat; lia ] | rewrite u_Z2bv by lia; lia ]|]. intros x Hx. rewrite u_Z2bv in Hx by lia.
        (lazymatch goal with |- ?G => let G' := eval unfold MZ in G in change_no_check G' end). rewrite zfill_out by lia. (lazymatch goal with |- ?G => let G' := eval unfold M1 in G in change_no_check G' end). apply (mfi_m1_outside mem sp ra s0v s1v s2v s3v s4v s5v addr size name PGP Hsp). left. lia. }
      destruct (mfi_ok (mrestrict Hd MZ) rom sp ra s0v s1v s2v s3v s4v addr size CF (regupd r1 10 addr)
                  (Q1 addr) (Q2 addr) (Q8 addr) Hsp Hret (conj CF1 CF2) SOKZ
                  (SLZ (-8) ra ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); repeat (first [left; reflexivity | right]))) (SLZ (-16) s0v ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); repeat (first [left; reflexivity | right]))) (SLZ (-24) s1v ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); repeat (first [left; reflexivity | right])))
                  (SLZ (-32) s2v ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); repeat (first [left; reflexivity | right]))) (SLZ (-40) (Z_to_bv 64 0x8a6b4) ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); repeat (first [left; reflexivity | right]))) (SLZ (-48) size ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); repeat (first [left; reflexivity | right])))
                  (SLZ (-56) addr ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); repeat (first [left; reflexivity | right]))) (SLZ (-64) s2v ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); repeat (first [left; reflexivity | right]))) (SLZ (-72) s3v ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); repeat (first [left; reflexivity | right]))) (SLZ (-80) s4v ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); repeat (first [left; reflexivity | right])))
                  (Q10 addr) ltac:(lia) ltac:(lia)
                  (CELLZ 0xff260 8%nat _ ltac:(lia) ltac:((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia) HDgcf Rgcf) (CELLZ (CF + 144) 8%nat _ ltac:(lia) ltac:((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia) HDlim Rlim))
        as (r2 & RUN2 & C10 & C2 & C1 & C8 & C9 & C18 & C19 & C20 & AG2).
      rewrite wbytes_mrestrict in RUN2; [| rewrite length_N_to_le_bytes, at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia
                                          | rewrite length_N_to_le_bytes, at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); intros x Hx; apply HDscr; lia].
      apply (katwD_msteps_acct ASEGS Hd HOFFSEG WX A (mkst (regupd r1 10 addr) (0x80740 : word) MZ rom)
               (mkst r2 ra (mrestrict Hd (wbytes MZ (at_ sp (-84)) SCR)) rom) (MOK mdlm) Qok Qf HOK2 AWF HOK3 HOK1).
      { rewrite mk_restrict_mkst. exact RUN2. }
      intros mdl4 MI4 SBM4 HC4. rewrite mk_unrestrict_mkst.
      replace (RiscvSemantics.ms_mem (mkst (regupd r1 10 addr) (0x80740 : word) MZ rom)) with MZ by reflexivity.
      rewrite (mk_munrestrict_same Hd MZ (wbytes MZ (at_ sp (-84)) SCR)).
      2:{ intros a Ha. apply HIDW; [exact Ha | (lazymatch goal with |- ?G => let G' := eval unfold SCR in G in change_no_check G' end); rewrite length_N_to_le_bytes; reflexivity]. }
      apply (CONTOK r2 mdlm mdl4 SBMm MIm SBM4 MI4).
      (lazymatch goal with |- ?G => let G' := eval unfold mfi_ret in G in change_no_check G' end). repeat (split; [assumption|]). exact (AGC addr r2 AG2).
  Qed.

End MAPKH.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section NODE2H.

  (* [comment removed for export] *)
  Lemma node1_of_fixfree2_s :
    forall (r1 : bvmap 5 word) (M1 rom : word -> option byte) (mdlm : Model) (addr size : word) (Qok' Qf' : config -> Prop),
    m_halted mdlm = None ->
    getr r1 10 = addr -> getr r1 11 = size -> getr r1 12 = Z_to_bv 64 3 -> getr r1 13 = Z_to_bv 64 50 ->
    getr r1 14 = Z_to_bv 64 (2 ^ 64 - 1) -> getr r1 15 = Z_to_bv 64 0 ->
    U addr mod 4096 = 0 -> 0 < U addr -> 0 < U size -> U size mod 4096 = 0 ->
    U addr + U size <= alloc_top (m_vmmaps mdlm) -> alloc_top (m_vmmaps mdlm) < two_pow_64 ->
    region_free (vm_reserved (m_vmmaps mdlm) ++ vm_maps (m_vmmaps mdlm)) addr size = true ->
    mmap_noreserve_backed_ok (Z_to_bv 64 50) mdlm (U size) = true ->
    katwD ASEGS (mkCfg (mkst (regupd r1 10 addr) (0x80740 : word) (zfill addr size M1) rom)
                      (with_mmap_backing (Z_to_bv 64 50) addr size (mmap_model addr size mdlm))) Qok' Qf' ->
    katsD ASEGS (mkCfg (epend r1 (0x8073c : word) M1 rom (Z_to_bv 64 222)) mdlm) Qok' Qf'.
  Proof using.
    intros r1 M1 rom mdlm addr size Qok' Qf' HALT B10 B11 B12 B13 B14 B15 Hal Hpos Hsz Hszal Htop Htop64 Hrf Hbk KOK.
    pose proof (u64_range size) as Hszr.
    set (ms := epend r1 (0x8073c : word) M1 rom (Z_to_bv 64 222)).
    assert (PRU : page_round_up_Z (U size) = U size) by (apply page_round_up_Z_aligned; [lia | (lazymatch goal with |- ?G => let G' := eval unfold page_size in G in change_no_check G' end); exact Hszal]).
    assert (EN : Z_to_bv 64 (page_round_up_Z (U size)) = size) by (rewrite PRU; apply Z_to_bv_bv_unsigned).
    assert (E0 : ms_gpr ms 0 = addr) by ((lazymatch goal with |- ?G => let G' := eval unfold ms in G in change_no_check G' end); rewrite AsKSys6.MhKSys.ms_gpr_epend0; exact B10).
    assert (E1 : ms_gpr ms 1 = Z_to_bv 64 (U size)) by ((lazymatch goal with |- ?G => let G' := eval unfold ms in G in change_no_check G' end); rewrite AsKSys6.MhKSys.ms_gpr_epend1, Z_to_bv_bv_unsigned; exact B11).
    assert (E2 : ms_gpr ms 2 = Z_to_bv 64 3) by ((lazymatch goal with |- ?G => let G' := eval unfold ms in G in change_no_check G' end); rewrite AsKSys6.MhKSys.ms_gpr_epend2; exact B12).
    assert (E3 : ms_gpr ms 3 = Z_to_bv 64 50) by ((lazymatch goal with |- ?G => let G' := eval unfold ms in G in change_no_check G' end); rewrite AsKSys6.MhKSys.ms_gpr_epend3; exact B13).
    assert (E4 : ms_gpr ms 4 = Z_to_bv 64 (-1)) by ((lazymatch goal with |- ?G => let G' := eval unfold ms in G in change_no_check G' end); rewrite AsKSys6.MhKSys.ms_gpr_epend4, B14; apply bv_eq; reflexivity).
    assert (E5 : ms_gpr ms 5 = Z_to_bv 64 0) by ((lazymatch goal with |- ?G => let G' := eval unfold ms in G in change_no_check G' end); rewrite AsKSys6.MhKSys.ms_gpr_epend5; exact B15).
    apply katsD_of_katwD.
    apply (katwD_node ASEGS _ _ tt _ Qok' Qf'
             (node_mmap_fixfree1 ASEGS ms mdlm (Z_to_bv 64 222) (Z_to_bv 64 50) addr (U size) HALT eq_refl
                ltac:(rewrite u_Z2bv by lia; reflexivity)
                E0 ltac:((lazymatch goal with |- ?G => let G' := eval unfold page_size in G in change_no_check G' end); exact Hal) Hpos E1 Hsz ltac:(rewrite PRU; exact Htop) Htop64 E2 E3 ltac:(vm_compute; reflexivity) E4 E5
                ltac:(rewrite EN; exact Hrf) ltac:(rewrite PRU; exact Hbk))).
    intros [].
    (lazymatch goal with |- ?G => let G' := eval unfold fxfr_nx, fxfr_effs, fxfr_ms' in G in change_no_check G' end). rewrite EN. (lazymatch goal with |- ?G => let G' := eval unfold ms in G in change_no_check G' end).
    rewrite (AsKSys6.MhKSys.adv_zerosr_epend r1 (0x8073c%bv : word) M1 rom (Z_to_bv 64 222) addr addr size).
    replace (v_addi (0x8073c%bv : word) 4) with (0x80740%bv : word) by (apply bv_eq; vm_compute; reflexivity).
    exact KOK.
  Qed.
End NODE2H.
End FPGen1h.
End AsAllocM8kh.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFRcA OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMRunS2 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8e.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module AsAllocM8rh.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import Stdlib.Logic.FunctionalExtensionality.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.DivergeSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.SpinAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes.AgentNodes OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocSim OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys6.MhKSys OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsK OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys6.AsKSys OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsRtK OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFRcA OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM9b.AsAllocM8m OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8k AsAllocM8kh OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMRunS2.AsAllocM8r OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8e.AsAllocM8p OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8e.
Import OSSVerify.glaze.binary_reflection.images.Asan.
Import ListNotations.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation ASEGS := Asan.M.loaded_segments.
#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).
#[local] Abbreviation U := bv_unsigned.

Section FPGenH.
Context {fx : FPState}.

Section USERMAPH.
  Variable Hd : word -> bool.
  Hypothesis HOFFSEG : H_off_segments ASEGS Hd.
  Hypothesis WX : wx_segs_nowrap ASEGS.

  Theorem pf_usermap_katsD_h :
    forall (A : list (Z * Z)) regs (mem rom : word -> option byte) (model : Model)
           (sp ra s0v s1v s2v s3v s4v s5v s6v stats : word) (RIz SPB c req au mu PGP CF : Z) (Qok Qf : config -> Prop)
           (MOK MKP : Model -> Model),
    let slot := SPB + c * 2 ^ 32 + mu in
    let M0 := pf_m0 mem sp ra s0v s1v s2v s3v s4v s5v s6v in
    let M1 := mfi_m1 M0 (at_ sp (-64)) (Z_to_bv 64 0x50ef4) (Z_to_bv 64 RIz) stats (Z_to_bv 64 (SPB + c * 2 ^ 32)) (Z_to_bv 64 (2 ^ 18))
                     (Z_to_bv 64 slot) (Z_to_bv 64 (csize c)) (Z_to_bv 64 slot) (Z_to_bv 64 (2 ^ 18)) (Z_to_bv 64 0x17990) PGP in
    let ENOMEMw : word := Z_to_bv 64 (2 ^ 64 - 12) in
    let SCR := word_to_le_bytes 4 (Z_to_bv 64 0xffffffffaaaaaaaa) in
    (* [comment removed for export] *)
    getr regs 1 = ra -> getr regs 2 = sp -> getr regs 10 = Z_to_bv 64 0x103f18 -> getr regs 11 = stats -> getr regs 12 = Z_to_bv 64 c ->
    getr regs 13 = Z_to_bv 64 RIz -> getr regs 14 = Z_to_bv 64 req ->
    getr regs 8 = s0v -> getr regs 9 = s1v -> getr regs 18 = s2v -> getr regs 19 = s3v -> getr regs 20 = s4v -> getr regs 21 = s5v -> getr regs 22 = s6v ->
    (2 ^ 24 + 64 <= U sp /\ U sp + 16 <= 2 ^ 47) -> 1 <= c <= 30 -> (1 <= req /\ csize c * req <= 2 ^ 18) ->
    (0 <= au <= mu /\ mu + 2 ^ 18 <= 0xE0000000) -> mu < au + csize c * req ->
    (0 <= SPB /\ SPB + 2 ^ 37 < 2 ^ 63 /\ SPB mod 4096 = 0 /\ AIMGHI <= SPB) -> mu mod 4096 = 0 ->
    (AIMGHI <= RIz /\ RIz + 128 <= U sp - 464) ->
    (AIMGLO <= PGP /\ PGP + 8 <= AIMGHI) -> (AIMGLO <= CF /\ CF + 264 <= AIMGHI) ->
    store_ok ASEGS mem (at_ sp (-464)) 464 = true ->
    (* [comment removed for export] *)
    rdn ASEGS mem (Z_to_bv 64 (0x103f18 + 32)) 8 = Some (LE8 (Z_to_bv 64 SPB)) ->
    rdn ASEGS mem (Z_to_bv 64 (RIz + 32)) 8 = Some (LE8 (Z_to_bv 64 au)) ->
    rdn ASEGS mem (Z_to_bv 64 (RIz + 48)) 8 = Some (LE8 (Z_to_bv 64 mu)) ->
    rdn ASEGS mem (Z_to_bv 64 (RIz + 56)) 8 = Some (LE8 (Z_to_bv 64 0)) ->
    rdn ASEGS mem (Z_to_bv 64 (0x103f18 + 40)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 0xffffffff)) ->
    rdn ASEGS mem (Z_to_bv 64 (0x103f18 + 56)) 1 = Some [Z_to_bv 8 0] ->
    rdn ASEGS mem (Z_to_bv 64 0xff250) 8 = Some (LE8 (Z_to_bv 64 PGP)) ->
    rdn ASEGS mem (Z_to_bv 64 PGP) 8 = Some (LE8 (Z_to_bv 64 4096)) ->
    rdn ASEGS mem (Z_to_bv 64 0xff260) 8 = Some (LE8 (Z_to_bv 64 CF)) ->
    rdn ASEGS mem (Z_to_bv 64 (CF + 260)) 1 = Some [Z_to_bv 8 0] ->
    rdn ASEGS mem (Z_to_bv 64 (CF + 144)) 8 = Some (LE8 (Z_to_bv 64 0)) ->
    (* [comment removed for export] *)
    (slot + 2 ^ 18 <= U sp - 464 \/ U sp <= slot) ->
    (* [comment removed for export] *)
    hid_off Hd (0x103f18 + 32) 8 -> hid_off Hd (RIz + 32) 8 -> hid_off Hd (RIz + 48) 8 -> hid_off Hd (RIz + 56) 8 ->
    hid_off Hd (0x103f18 + 40) 4 -> hid_off Hd (0x103f18 + 56) 1 ->
    hid_off Hd 0xff250 8 -> hid_off Hd PGP 8 -> hid_off Hd 0xff260 8 -> hid_off Hd (CF + 260) 1 -> hid_off Hd (CF + 144) 8 ->
    hid_off Hd (U sp - 464) 464 ->
    (* [comment removed for export] *)
    m_halted model = None -> lazy_cover Hd (m_vm_lazy model) A -> A_wf A -> MInv A model ->
    (* [comment removed for export] *)
    (forall mdlm (r1 : bvmap 5 word), same_but_materialized model mdlm -> MInv A mdlm -> m_halted mdlm = None ->
        getr r1 10 = Z_to_bv 64 slot -> getr r1 11 = Z_to_bv 64 (2 ^ 18) -> getr r1 12 = Z_to_bv 64 3 -> getr r1 13 = Z_to_bv 64 50 ->
        getr r1 14 = Z_to_bv 64 (2 ^ 64 - 1) -> getr r1 15 = Z_to_bv 64 0 ->
        forall Qok' Qf' : config -> Prop,
          katwD ASEGS (mkCfg (mkst (regupd r1 10 (Z_to_bv 64 slot)) (0x80740 : word) (zfill (Z_to_bv 64 slot) (Z_to_bv 64 (2 ^ 18)) M1) rom) (MOK mdlm)) Qok' Qf' ->
          katsD ASEGS (mkCfg (epend r1 (0x8073c : word) M1 rom (Z_to_bv 64 222)) mdlm) Qok' Qf') ->
    (forall mdlm, same_but_materialized model mdlm -> MInv A mdlm ->
        (m_halted (MOK mdlm) = None /\ lazy_cover Hd (m_vm_lazy (MOK mdlm)) A /\ MInv A (MOK mdlm))
        /\ (m_halted (MKP mdlm) = None /\ lazy_cover Hd (m_vm_lazy (MKP mdlm)) A /\ MInv A (MKP mdlm))) ->
    (* [comment removed for export] *)
    (forall (r' : bvmap 5 word) mdlm mdl4,
        same_but_materialized model mdlm -> MInv A mdlm -> same_but_materialized (MOK mdlm) mdl4 -> MInv A mdl4 ->
        pf_at_ret sp stats RIz SPB c mu r' (Z_to_bv 64 slot) -> regs_agree (fun i : reg => In i pf_clob) regs r' ->
        katwD ASEGS (mkCfg (mkst r' (0x50ef4 : word) (wbytes (zfill (Z_to_bv 64 slot) (Z_to_bv 64 (2 ^ 18)) M1) (at_ sp (-148)) SCR) rom) mdl4) Qok Qf) ->
    (forall (r' : bvmap 5 word) mdlm mdl4,
        same_but_materialized model mdlm -> MInv A mdlm -> same_but_materialized (MKP mdlm) mdl4 -> MInv A mdl4 ->
        pf_at_ret sp stats RIz SPB c mu r' (Z_to_bv 64 0) -> regs_agree (fun i : reg => In i pf_clob) regs r' ->
        katD ASEGS (mkCfg (mkst r' (0x50ef4 : word) (wbytes (wbytes M1 (at_ sp (-148)) SCR) (at_ sp (-148)) (word_to_le_bytes 4 (Z_to_bv 64 12))) rom) mdl4) Qf) ->
    katsD ASEGS (mkCfg (mkst regs (0x50dd4 : word) mem rom) model) Qok Qf.
  Proof using WX HOFFSEG.
    intros A regs mem rom model sp ra s0v s1v s2v s3v s4v s5v s6v stats RIz SPB c req au mu PGP CF Qok Qf MOK MKP slot M0 M1 ENOMEMw SCR
           H1 H2 H10 H11 H12 H13 H14 H8 H9 H18 H19 H20 H21 H22 Hsp Hc Hreq Hau Hmap HSPB Hmu4k HRI HPGP HCF Hstk
           C_sbeg R_au R_mu R_mm C_rel C_pre Rgpg Rpg Rgcf Rdpm Rlim Hslot
           HDsbeg HDau HDmu HDmm HDrel HDpre HDgpg HDpg HDgcf HDdpm HDlim HDscr HALT LC AWF MI NODE CHILD CONTOK CONTKP.
    pose proof (u64_range sp) as Hspr. destruct Hsp as [SP1 SP2]. destruct HSPB as (S1 & S2 & S3 & S4). destruct HRI as [RI1 RI2].
    destruct HPGP as [PG1 PG2]. destruct HCF as [CF1 CF2]. destruct Hau as [AU1 AU2]. destruct Hreq as [RQ1 RQ2].
    pose proof (csize_pos c Hc) as [CS1 CS2].
    set (spm := at_ sp (-64)).
    assert (Uspm : U spm = U sp - 64) by ((lazymatch goal with |- ?G => let G' := eval unfold spm in G in change_no_check G' end); first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ]).
    (* [comment removed for export] *)
    assert (CELLR : forall (cc : Z) (k : nat) v, 0 <= cc -> cc + Z.of_nat k <= U sp - 464 -> hid_off Hd cc (Z.of_nat k) ->
               rdn ASEGS mem (Z_to_bv 64 cc) k = Some v -> rdn ASEGS (mrestrict Hd mem) (Z_to_bv 64 cc) k = Some v).
    { intros cc k v Hc0 Hc1 Hh Hr. rewrite rdn_mrestrict; [exact Hr | first [ solve [ wd_unorm1; wd_zofnat; lia ] | rewrite u_Z2bv by lia; lia ] | rewrite u_Z2bv by lia; exact Hh]. }
    assert (Hstk' : store_ok ASEGS (mrestrict Hd mem) (at_ sp (-64)) 64 = true).
    { rewrite store_ok_mrestrict; [| first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); intros x Hx; apply HDscr; lia].
      eapply (store_ok_sub ASEGS mem (at_ sp (-464)) _ 464); [first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | exact Hstk | first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite !at_u by lia; lia ] | first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite !at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ]]. }
    destruct (pf_head_map (mrestrict Hd mem) rom sp ra s0v s1v s2v s3v s4v s5v s6v stats RIz SPB c req au mu regs
                H1 H2 H10 H11 H12 H13 H14 H8 H9 H18 H19 H20 H21 H22 ltac:(lia) Hc (conj RQ1 RQ2) (conj AU1 AU2) ltac:(lia) ltac:(lia) Hstk'
                (CELLR (0x103f18 + 32) 8%nat _ ltac:(lia) ltac:((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia) HDsbeg C_sbeg)
                (CELLR (RIz + 32) 8%nat _ ltac:(lia) ltac:((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia) HDau R_au)
                (CELLR (RIz + 48) 8%nat _ ltac:(lia) ltac:((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia) HDmu R_mu) Hmap)
      as (r1 & RUN1 & PR1 & A9 & A10 & A12 & A19 & A20 & AG1).
    rewrite pf_m0_mrestrict in RUN1 by (first [lia | intros x Hx; apply HDscr; lia]). fold M0 in RUN1.
    assert (M0out : forall x : word, (U x < U sp - 64 \/ U sp <= U x) -> M0 x = mem x) by (intros x Hx; (lazymatch goal with |- ?G => let G' := eval unfold M0 in G in change_no_check G' end); apply pf_m0_outside; [lia | exact Hx]).
    assert (CELL0 : forall (cc : Z) (k : nat) v, 0 <= cc -> cc + Z.of_nat k <= U sp - 464 ->
               rdn ASEGS mem (Z_to_bv 64 cc) k = Some v -> rdn ASEGS M0 (Z_to_bv 64 cc) k = Some v).
    { intros cc k v Hc0 Hc1 Hr. rewrite <- Hr. apply rdn_ext; [first [ solve [ wd_unorm1; wd_zofnat; lia ] | rewrite u_Z2bv by lia; lia ]|]. intros x Hx. rewrite u_Z2bv in Hx by lia. apply M0out. lia. }
    assert (CELLR0 : forall (cc : Z) (k : nat) v, 0 <= cc -> cc + Z.of_nat k <= U sp - 464 -> hid_off Hd cc (Z.of_nat k) ->
               rdn ASEGS mem (Z_to_bv 64 cc) k = Some v -> rdn ASEGS (mrestrict Hd M0) (Z_to_bv 64 cc) k = Some v).
    { intros cc k v Hc0 Hc1 Hh Hr. rewrite rdn_mrestrict; [apply CELL0; assumption | first [ solve [ wd_unorm1; wd_zofnat; lia ] | rewrite u_Z2bv by lia; lia ] | rewrite u_Z2bv by lia; exact Hh]. }
    destruct (pf_map (mrestrict Hd M0) rom sp stats RIz SPB c (au + csize c * req) mu r1 PR1 A9 A10 A19 A20 ltac:(lia) Hc ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
                (CELLR0 (0x103f18 + 40) 4%nat _ ltac:(lia) ltac:((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia) HDrel C_rel)
                (CELLR0 (0x103f18 + 56) 1%nat _ ltac:(lia) ltac:((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia) HDpre C_pre)
                (CELLR0 (RIz + 56) 8%nat _ ltac:(lia) ltac:((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia) HDmm R_mm))
      as (r2 & RUN2 & PR2 & B9 & B1 & B11 & B12 & B13 & B19 & B20 & B22 & AG2).
    assert (M0hid : forall a : word, Hd a = true -> M0 a = mem a).
    { intros a Ha. apply M0out.
      destruct (Z_lt_le_dec (U a) (U sp - 64)) as [C1|C1]; [left; exact C1|].
      destruct (Z_lt_le_dec (U a) (U sp)) as [C2|C2]; [| right; exact C2].
      exfalso. rewrite (HDscr a) in Ha by lia. discriminate Ha. }
    apply (katsD_msteps_acct ASEGS Hd HOFFSEG WX A (mkst regs (0x50dd4 : word) mem rom)
             (mkst r2 (0x8a688 : word) (mrestrict Hd M0) rom) model Qok Qf LC AWF MI HALT).
    { rewrite mk_restrict_mkst. eapply msteps_trans; [exact RUN1 | exact RUN2]. }
    intros mdlm MIm SBMm HC1. rewrite mk_unrestrict_mkst.
    replace (RiscvSemantics.ms_mem (mkst regs (0x50dd4 : word) mem rom)) with mem by reflexivity.
    rewrite (mk_munrestrict_same Hd mem M0 M0hid).
    pose proof (same_but_materialized_frame model mdlm SBMm) as FRm.
    assert (HALTm : m_halted mdlm = None) by (destruct FRm as (_&_&_&_&_&_&_&_&_&_&_&_&Hh&_); rewrite Hh; exact HALT).
    assert (LCm : lazy_cover Hd (m_vm_lazy mdlm) A) by (destruct FRm as (_ & _ & Hl & _); rewrite Hl; exact LC).
    destruct PR2 as (P2 & P8 & P18 & P21).
    assert (SUB : forall x : reg, In x mfi_clob2 -> In x pf_clob).
    { intros x Hin. unfold mfi_clob2, mfi_clob in Hin. cbn [In] in Hin. (lazymatch goal with |- ?G => let G' := eval unfold pf_clob in G in change_no_check G' end).
      repeat (destruct Hin as [<-|Hin]; [solve [in_list]|]). destruct Hin. }
    assert (RETK : forall (r' : bvmap 5 word) (res : word),
               mfi_ret r2 r' spm (Z_to_bv 64 0x50ef4) (Z_to_bv 64 RIz) stats (Z_to_bv 64 (SPB + c * 2 ^ 32)) (Z_to_bv 64 (2 ^ 18)) (Z_to_bv 64 slot) res ->
               pf_at_ret sp stats RIz SPB c mu r' res).
    { intros r' res (C10 & C2 & C1 & C8 & C9 & C18 & C19 & C20 & AGL). (lazymatch goal with |- ?G => let G' := eval unfold pf_at_ret, pf_regs in G in change_no_check G' end).
      assert (N21 : ~ In (21%bv : reg) mfi_clob2) by ((lazymatch goal with |- ?G => let G' := eval unfold mfi_clob2, mfi_clob in G in change_no_check G' end); (lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); intros X; repeat (destruct X as [X|X]; [discriminate X|]); exact X).
      assert (N22 : ~ In (22%bv : reg) mfi_clob2) by ((lazymatch goal with |- ?G => let G' := eval unfold mfi_clob2, mfi_clob in G in change_no_check G' end); (lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); intros X; repeat (destruct X as [X|X]; [discriminate X|]); exact X).
      rewrite (AGL 21%bv N21), (AGL 22%bv N22).
      repeat split; assumption. }
    assert (RETA : forall (r' : bvmap 5 word) (res : word),
               mfi_ret r2 r' spm (Z_to_bv 64 0x50ef4) (Z_to_bv 64 RIz) stats (Z_to_bv 64 (SPB + c * 2 ^ 32)) (Z_to_bv 64 (2 ^ 18)) (Z_to_bv 64 slot) res ->
               regs_agree (fun i : reg => In i pf_clob) regs r').
    { intros r' res (_ & _ & _ & _ & _ & _ & _ & _ & AGL) x Hx.
      rewrite (AGL x) by (intros Hin; apply Hx; exact (SUB x Hin)).
      rewrite (AG2 x Hx). exact (AG1 x Hx). }
    (* [comment removed for export] *)
    apply (rarmap_katsD_h Hd HOFFSEG WX A r2 M0 rom mdlm spm (Z_to_bv 64 0x50ef4) (Z_to_bv 64 RIz) stats (Z_to_bv 64 (SPB + c * 2 ^ 32))
             (Z_to_bv 64 (2 ^ 18)) (Z_to_bv 64 slot) (Z_to_bv 64 (csize c)) (Z_to_bv 64 slot) (Z_to_bv 64 (2 ^ 18)) (Z_to_bv 64 0x17990)
             PGP CF Qok Qf MOK MKP B1 P2 B11 B12 B13 P8 B9 P18 B19 B20 P21).
    - rewrite Uspm. lia.
    - apply ret_ok_lit; [lia | reflexivity].
    - rewrite u_Z2bv by ((lazymatch goal with |- ?G => let G' := eval unfold slot in G in change_no_check G' end); lia). (lazymatch goal with |- ?G => let G' := eval unfold slot in G in change_no_check G' end). replace (c * 2 ^ 32) with (c * 1048576 * 4096) by lia.
      rewrite Z.add_mod, (Z.add_mod SPB), Z.mod_mul, S3, Hmu4k by lia. reflexivity.
    - rewrite u_Z2bv by lia. split; [reflexivity | lia].
    - rewrite u_Z2bv by lia. lia.
    - lia.
    - lia.
    - replace (at_ spm (-400)) with (at_ sp (-464)) by ((lazymatch goal with |- ?G => let G' := eval unfold spm in G in change_no_check G' end); rewrite at_at; reflexivity).
      eapply store_ok_mono; [(lazymatch goal with |- ?G => let G' := eval unfold M0 in G in change_no_check G' end); apply pf_m0_grows |].
      eapply (store_ok_sub ASEGS mem (at_ sp (-464)) _ 464); [first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | exact Hstk | first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite !at_u by lia; lia ] | first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite !at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ]].
    - apply CELL0; [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | exact Rgpg].
    - apply CELL0; [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | exact Rpg].
    - apply CELL0; [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | exact Rgcf].
    - apply CELL0; [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | exact Rdpm].
    - apply CELL0; [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | exact Rlim].
    - rewrite !u_Z2bv by ((lazymatch goal with |- ?G => let G' := eval unfold slot in G in change_no_check G' end); lia). rewrite Uspm. unfold slot in *. split; [lia | split; [lia | lia]].
    - exact HDgpg.
    - exact HDpg.
    - exact HDgcf.
    - exact HDdpm.
    - exact HDlim.
    - eapply hid_off_sub; [exact HDscr | rewrite Uspm; lia | rewrite Uspm; lia].
    - exact HALTm.
    - exact LCm.
    - exact AWF.
    - exact MIm.
    - intros mdlm0 rr SB0 MI0 HL0 G10 G11 G12 G13 G14 G15 Qok' Qf' K1.
      exact (NODE mdlm0 rr (same_but_materialized_trans _ _ _ SBMm SB0) MI0 HL0 G10 G11 G12 G13 G14 G15 Qok' Qf' K1).
    - intros mdlm0 SB0 MI0. exact (CHILD mdlm0 (same_but_materialized_trans _ _ _ SBMm SB0) MI0).
    - intros r' mdlm0 mdl4 SB0 MI0 SB4 MI4 RET.
      replace (at_ spm (-84)) with (at_ sp (-148)) by ((lazymatch goal with |- ?G => let G' := eval unfold spm in G in change_no_check G' end); rewrite at_at; reflexivity).
      replace (Z_to_bv 64 331508 : word) with (0x50ef4%bv : word) by (apply bv_eq; reflexivity).
      apply (CONTOK r' mdlm0 mdl4 (same_but_materialized_trans _ _ _ SBMm SB0) MI0 SB4 MI4); [apply (RETK r' _ RET) | apply (RETA r' _ RET)].
    - intros r' mdlm0 mdl4 SB0 MI0 SB4 MI4 RET.
      replace (at_ spm (-84)) with (at_ sp (-148)) by ((lazymatch goal with |- ?G => let G' := eval unfold spm in G in change_no_check G' end); rewrite at_at; reflexivity).
      replace (Z_to_bv 64 331508 : word) with (0x50ef4%bv : word) by (apply bv_eq; reflexivity).
      apply (CONTKP r' mdlm0 mdl4 (same_but_materialized_trans _ _ _ SBMm SB0) MI0 SB4 MI4); [apply (RETK r' _ RET) | apply (RETA r' _ RET)].
  Qed.

End USERMAPH.

Section FAMAPH.
  Variable Hd : word -> bool.
  Hypothesis HOFFSEG : H_off_segments ASEGS Hd.
  Hypothesis WX : wx_segs_nowrap ASEGS.

  Theorem efs_famap_katsD_h :
    forall (A : list (Z * Z)) regs (mem rom : word -> option byte) (model : Model)
           (sp ra s0v s1v s2v s3v s4v s5v : word) (RIz rbeg tot mfa PGP CF : Z) (Qok Qf : config -> Prop)
           (MOK MKP : Model -> Model),
    let slot := rbeg + 0xE0000000 + mfa in
    let M0 := efs_m0 mem sp ra s0v s1v s2v s3v in
    let M1 := mfi_m1 M0 (at_ sp (-48)) (Z_to_bv 64 0x4eb38) (Z_to_bv 64 (mfa + 2 ^ 18)) (Z_to_bv 64 slot) (Z_to_bv 64 (2 ^ 18)) (Z_to_bv 64 RIz)
                     s4v s5v (Z_to_bv 64 slot) (Z_to_bv 64 (2 ^ 18)) (Z_to_bv 64 0x19801) PGP in
    let ENOMEMw : word := Z_to_bv 64 (2 ^ 64 - 12) in
    let SCR := word_to_le_bytes 4 (Z_to_bv 64 0xffffffffaaaaaaaa) in
    getr regs 1 = ra -> getr regs 2 = sp -> getr regs 10 = Z_to_bv 64 0x103f18 -> getr regs 11 = Z_to_bv 64 RIz -> getr regs 12 = Z_to_bv 64 rbeg ->
    getr regs 13 = Z_to_bv 64 tot ->
    getr regs 8 = s0v -> getr regs 9 = s1v -> getr regs 18 = s2v -> getr regs 19 = s3v -> getr regs 20 = s4v -> getr regs 21 = s5v ->
    (2 ^ 24 + 48 <= U sp /\ U sp + 16 <= 2 ^ 47) ->
    (0 <= tot /\ 4 * tot <= 2 ^ 29) -> (0 <= mfa <= 2 ^ 29 /\ mfa mod 2 ^ 18 = 0) -> (mfa < 4 * tot <= mfa + 2 ^ 18) -> mfa + 2 ^ 18 <= 2 ^ 29 ->
    (AIMGHI <= rbeg /\ rbeg + 2 ^ 32 < 2 ^ 63 /\ rbeg mod 4096 = 0) ->
    (AIMGHI <= RIz /\ RIz + 128 <= U sp - 448) ->
    (AIMGLO <= PGP /\ PGP + 8 <= AIMGHI) -> (AIMGLO <= CF /\ CF + 264 <= AIMGHI) ->
    store_ok ASEGS mem (at_ sp (-448)) 448 = true ->
    rdn ASEGS mem (Z_to_bv 64 (RIz + 24)) 8 = Some (LE8 (Z_to_bv 64 mfa)) ->
    rdn ASEGS mem (Z_to_bv 64 (0x103f18 + 56)) 1 = Some [Z_to_bv 8 0] ->
    rdn ASEGS mem (Z_to_bv 64 0xff250) 8 = Some (LE8 (Z_to_bv 64 PGP)) ->
    rdn ASEGS mem (Z_to_bv 64 PGP) 8 = Some (LE8 (Z_to_bv 64 4096)) ->
    rdn ASEGS mem (Z_to_bv 64 0xff260) 8 = Some (LE8 (Z_to_bv 64 CF)) ->
    rdn ASEGS mem (Z_to_bv 64 (CF + 260)) 1 = Some [Z_to_bv 8 0] ->
    rdn ASEGS mem (Z_to_bv 64 (CF + 144)) 8 = Some (LE8 (Z_to_bv 64 0)) ->
    (slot + 2 ^ 18 <= U sp - 448 \/ U sp <= slot) ->
    hid_off Hd (RIz + 24) 8 -> hid_off Hd (0x103f18 + 56) 1 ->
    hid_off Hd 0xff250 8 -> hid_off Hd PGP 8 -> hid_off Hd 0xff260 8 -> hid_off Hd (CF + 260) 1 -> hid_off Hd (CF + 144) 8 ->
    hid_off Hd (U sp - 448) 448 ->
    m_halted model = None -> lazy_cover Hd (m_vm_lazy model) A -> A_wf A -> MInv A model ->
    (forall mdlm (r1 : bvmap 5 word), same_but_materialized model mdlm -> MInv A mdlm -> m_halted mdlm = None ->
        getr r1 10 = Z_to_bv 64 slot -> getr r1 11 = Z_to_bv 64 (2 ^ 18) -> getr r1 12 = Z_to_bv 64 3 -> getr r1 13 = Z_to_bv 64 50 ->
        getr r1 14 = Z_to_bv 64 (2 ^ 64 - 1) -> getr r1 15 = Z_to_bv 64 0 ->
        forall Qok' Qf' : config -> Prop,
          katwD ASEGS (mkCfg (mkst (regupd r1 10 (Z_to_bv 64 slot)) (0x80740 : word) (zfill (Z_to_bv 64 slot) (Z_to_bv 64 (2 ^ 18)) M1) rom) (MOK mdlm)) Qok' Qf' ->
          katsD ASEGS (mkCfg (epend r1 (0x8073c : word) M1 rom (Z_to_bv 64 222)) mdlm) Qok' Qf') ->
    (forall mdlm, same_but_materialized model mdlm -> MInv A mdlm ->
        (m_halted (MOK mdlm) = None /\ lazy_cover Hd (m_vm_lazy (MOK mdlm)) A /\ MInv A (MOK mdlm))
        /\ (m_halted (MKP mdlm) = None /\ lazy_cover Hd (m_vm_lazy (MKP mdlm)) A /\ MInv A (MKP mdlm))) ->
    (forall (r' : bvmap 5 word) mdlm mdl4,
        same_but_materialized model mdlm -> MInv A mdlm -> same_but_materialized (MOK mdlm) mdl4 -> MInv A mdl4 ->
        efs_at_ret sp s4v RIz slot mfa r' (Z_to_bv 64 slot) -> regs_agree (fun i : reg => In i efs_clob) regs r' ->
        katwD ASEGS (mkCfg (mkst r' (0x4eb38 : word) (wbytes (zfill (Z_to_bv 64 slot) (Z_to_bv 64 (2 ^ 18)) M1) (at_ sp (-132)) SCR) rom) mdl4) Qok Qf) ->
    (forall (r' : bvmap 5 word) mdlm mdl4,
        same_but_materialized model mdlm -> MInv A mdlm -> same_but_materialized (MKP mdlm) mdl4 -> MInv A mdl4 ->
        efs_at_ret sp s4v RIz slot mfa r' (Z_to_bv 64 0) -> regs_agree (fun i : reg => In i efs_clob) regs r' ->
        katD ASEGS (mkCfg (mkst r' (0x4eb38 : word) (wbytes (wbytes M1 (at_ sp (-132)) SCR) (at_ sp (-132)) (word_to_le_bytes 4 (Z_to_bv 64 12))) rom) mdl4) Qf) ->
    katsD ASEGS (mkCfg (mkst regs (0x4ea98 : word) mem rom) model) Qok Qf.
  Proof using WX HOFFSEG.
    intros A regs mem rom model sp ra s0v s1v s2v s3v s4v s5v RIz rbeg tot mfa PGP CF Qok Qf MOK MKP slot M0 M1 ENOMEMw SCR
           H1 H2 H10 H11 H12 H13 H8 H9 H18 H19 H20 H21 Hsp Htot Hmfa Hneed Hroom Hrbeg HRI HPGP HCF Hstk
           R_mfa C_pre Rgpg Rpg Rgcf Rdpm Rlim Hslot
           HDmfa HDpre HDgpg HDpg HDgcf HDdpm HDlim HDscr HALT LC AWF MI NODE CHILD CONTOK CONTKP.
    pose proof (u64_range sp) as Hspr. destruct Hsp as [SP1 SP2]. destruct Hrbeg as (RB1 & RB2 & RB3). destruct HRI as [RI1 RI2].
    destruct HPGP as [PG1 PG2]. destruct HCF as [CF1 CF2]. destruct Hmfa as [MF1 MF2].
    set (spm := at_ sp (-48)).
    assert (Uspm : U spm = U sp - 48) by ((lazymatch goal with |- ?G => let G' := eval unfold spm in G in change_no_check G' end); first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ]).
    assert (CELLR : forall (cc : Z) (k : nat) v, 0 <= cc -> cc + Z.of_nat k <= U sp - 448 -> hid_off Hd cc (Z.of_nat k) ->
               rdn ASEGS mem (Z_to_bv 64 cc) k = Some v -> rdn ASEGS (mrestrict Hd mem) (Z_to_bv 64 cc) k = Some v).
    { intros cc k v Hc0 Hc1 Hh Hr. rewrite rdn_mrestrict; [exact Hr | first [ solve [ wd_unorm1; wd_zofnat; lia ] | rewrite u_Z2bv by lia; lia ] | rewrite u_Z2bv by lia; exact Hh]. }
    assert (Hstk' : store_ok ASEGS (mrestrict Hd mem) (at_ sp (-48)) 48 = true).
    { rewrite store_ok_mrestrict; [| first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); intros x Hx; apply HDscr; lia].
      eapply (store_ok_sub ASEGS mem (at_ sp (-448)) _ 448); [first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | exact Hstk | first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite !at_u by lia; lia ] | first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite !at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ]]. }
    destruct (efs_map (mrestrict Hd mem) rom sp ra s0v s1v s2v s3v RIz rbeg tot mfa regs
                H1 H2 H10 H11 H12 H13 H8 H9 H18 H19 ltac:(lia) Htot (conj MF1 MF2) ltac:(lia) ltac:(lia) Hstk'
                (CELLR (RIz + 24) 8%nat _ ltac:(lia) ltac:((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia) HDmfa R_mfa)
                (CELLR (0x103f18 + 56) 1%nat _ ltac:(lia) ltac:((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia) HDpre C_pre) Hneed Hroom)
      as (r2 & RUN2 & B1 & B2 & B11 & B12 & B13 & B8 & B9 & B18 & B19 & AG2).
    rewrite efs_m0_mrestrict in RUN2 by (first [lia | intros x Hx; apply HDscr; lia]). fold M0 in RUN2.
    assert (M0out : forall x : word, (U x < U sp - 48 \/ U sp <= U x) -> M0 x = mem x) by (intros x Hx; (lazymatch goal with |- ?G => let G' := eval unfold M0 in G in change_no_check G' end); apply efs_m0_outside; [lia | exact Hx]).
    assert (CELL0 : forall (cc : Z) (k : nat) v, 0 <= cc -> cc + Z.of_nat k <= U sp - 448 ->
               rdn ASEGS mem (Z_to_bv 64 cc) k = Some v -> rdn ASEGS M0 (Z_to_bv 64 cc) k = Some v).
    { intros cc k v Hc0 Hc1 Hr. rewrite <- Hr. apply rdn_ext; [first [ solve [ wd_unorm1; wd_zofnat; lia ] | rewrite u_Z2bv by lia; lia ]|]. intros x Hx. rewrite u_Z2bv in Hx by lia. apply M0out. lia. }
    assert (M0hid : forall a : word, Hd a = true -> M0 a = mem a).
    { intros a Ha. apply M0out.
      destruct (Z_lt_le_dec (U a) (U sp - 48)) as [C1|C1]; [left; exact C1|].
      destruct (Z_lt_le_dec (U a) (U sp)) as [C2|C2]; [| right; exact C2].
      exfalso. rewrite (HDscr a) in Ha by lia. discriminate Ha. }
    apply (katsD_msteps_acct ASEGS Hd HOFFSEG WX A (mkst regs (0x4ea98 : word) mem rom)
             (mkst r2 (0x8a688 : word) (mrestrict Hd M0) rom) model Qok Qf LC AWF MI HALT).
    { rewrite mk_restrict_mkst. exact RUN2. }
    intros mdlm MIm SBMm HC1. rewrite mk_unrestrict_mkst.
    replace (RiscvSemantics.ms_mem (mkst regs (0x4ea98 : word) mem rom)) with mem by reflexivity.
    rewrite (mk_munrestrict_same Hd mem M0 M0hid).
    pose proof (same_but_materialized_frame model mdlm SBMm) as FRm.
    assert (HALTm : m_halted mdlm = None) by (destruct FRm as (_&_&_&_&_&_&_&_&_&_&_&_&Hh&_); rewrite Hh; exact HALT).
    assert (LCm : lazy_cover Hd (m_vm_lazy mdlm) A) by (destruct FRm as (_ & _ & Hl & _); rewrite Hl; exact LC).
    assert (A20 : getr r2 20 = s4v) by (rewrite (AG2 20%bv) by ((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); intros X; repeat (destruct X as [X|X]; [discriminate X|]); exact X); exact H20).
    assert (A21 : getr r2 21 = s5v) by (rewrite (AG2 21%bv) by ((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); intros X; repeat (destruct X as [X|X]; [discriminate X|]); exact X); exact H21).
    assert (SUB : forall x : reg, In x mfi_clob2 -> In x efs_clob).
    { intros x Hin. unfold mfi_clob2, mfi_clob in Hin. cbn [In] in Hin. (lazymatch goal with |- ?G => let G' := eval unfold efs_clob in G in change_no_check G' end).
      repeat (destruct Hin as [<-|Hin]; [solve [in_list]|]). destruct Hin. }
    assert (SUB2 : forall x : reg, In x [1%bv; 2%bv; 8%bv; 9%bv; 10%bv; 11%bv; 12%bv; 13%bv; 14%bv; 15%bv; 18%bv; 19%bv] -> In x efs_clob).
    { intros x Hin. cbn [In] in Hin. (lazymatch goal with |- ?G => let G' := eval unfold efs_clob in G in change_no_check G' end). repeat (destruct Hin as [<-|Hin]; [solve [in_list]|]). destruct Hin. }
    assert (RETK : forall (r' : bvmap 5 word) (res : word),
               mfi_ret r2 r' spm (Z_to_bv 64 0x4eb38) (Z_to_bv 64 (mfa + 2 ^ 18)) (Z_to_bv 64 slot) (Z_to_bv 64 (2 ^ 18)) (Z_to_bv 64 RIz) s4v res ->
               efs_at_ret sp s4v RIz slot mfa r' res).
    { intros r' res (C10 & C2 & C1 & C8 & C9 & C18 & C19 & C20 & AGL). (lazymatch goal with |- ?G => let G' := eval unfold efs_at_ret in G in change_no_check G' end). repeat split; assumption. }
    assert (RETA : forall (r' : bvmap 5 word) (res : word),
               mfi_ret r2 r' spm (Z_to_bv 64 0x4eb38) (Z_to_bv 64 (mfa + 2 ^ 18)) (Z_to_bv 64 slot) (Z_to_bv 64 (2 ^ 18)) (Z_to_bv 64 RIz) s4v res ->
               regs_agree (fun i : reg => In i efs_clob) regs r').
    { intros r' res (_ & _ & _ & _ & _ & _ & _ & _ & AGL) x Hx.
      rewrite (AGL x) by (intros Hin; apply Hx; exact (SUB x Hin)).
      apply AG2. intros Hin. apply Hx. exact (SUB2 x Hin). }
    apply (rarmap_katsD_h Hd HOFFSEG WX A r2 M0 rom mdlm spm (Z_to_bv 64 0x4eb38) (Z_to_bv 64 (mfa + 2 ^ 18)) (Z_to_bv 64 slot)
             (Z_to_bv 64 (2 ^ 18)) (Z_to_bv 64 RIz) s4v s5v (Z_to_bv 64 slot) (Z_to_bv 64 (2 ^ 18)) (Z_to_bv 64 0x19801)
             PGP CF Qok Qf MOK MKP B1 B2 B11 B12 B13 B8 B9 B18 B19 A20 A21).
    - rewrite Uspm. lia.
    - apply ret_ok_lit; [lia | reflexivity].
    - rewrite u_Z2bv by ((lazymatch goal with |- ?G => let G' := eval unfold slot in G in change_no_check G' end); lia). (lazymatch goal with |- ?G => let G' := eval unfold slot in G in change_no_check G' end). replace (rbeg + 0xE0000000 + mfa) with (rbeg + (917504 * 4096 + mfa)) by lia.
      rewrite Z.add_mod, RB3 by lia. rewrite (Z.add_mod (917504 * 4096)), Z.mod_mul by lia.
      assert (E : mfa mod 4096 = 0) by (clear - MF2; Z.div_mod_to_equations; lia). rewrite E. reflexivity.
    - rewrite u_Z2bv by lia. split; [reflexivity | lia].
    - rewrite u_Z2bv by lia. lia.
    - lia.
    - lia.
    - replace (at_ spm (-400)) with (at_ sp (-448)) by ((lazymatch goal with |- ?G => let G' := eval unfold spm in G in change_no_check G' end); rewrite at_at; reflexivity).
      eapply store_ok_mono; [(lazymatch goal with |- ?G => let G' := eval unfold M0 in G in change_no_check G' end); apply efs_m0_grows |].
      eapply (store_ok_sub ASEGS mem (at_ sp (-448)) _ 448); [first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | exact Hstk | first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite !at_u by lia; lia ] | first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite !at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ]].
    - apply CELL0; [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | exact Rgpg].
    - apply CELL0; [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | exact Rpg].
    - apply CELL0; [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | exact Rgcf].
    - apply CELL0; [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | exact Rdpm].
    - apply CELL0; [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | exact Rlim].
    - rewrite !u_Z2bv by ((lazymatch goal with |- ?G => let G' := eval unfold slot in G in change_no_check G' end); lia). rewrite Uspm. unfold slot in *. split; [lia | split; [lia | lia]].
    - exact HDgpg.
    - exact HDpg.
    - exact HDgcf.
    - exact HDdpm.
    - exact HDlim.
    - eapply hid_off_sub; [exact HDscr | rewrite Uspm; lia | rewrite Uspm; lia].
    - exact HALTm.
    - exact LCm.
    - exact AWF.
    - exact MIm.
    - intros mdlm0 rr SB0 MI0 HL0 G10 G11 G12 G13 G14 G15 Qok' Qf' K1.
      exact (NODE mdlm0 rr (same_but_materialized_trans _ _ _ SBMm SB0) MI0 HL0 G10 G11 G12 G13 G14 G15 Qok' Qf' K1).
    - intros mdlm0 SB0 MI0. exact (CHILD mdlm0 (same_but_materialized_trans _ _ _ SBMm SB0) MI0).
    - intros r' mdlm0 mdl4 SB0 MI0 SB4 MI4 RET.
      replace (at_ spm (-84)) with (at_ sp (-132)) by ((lazymatch goal with |- ?G => let G' := eval unfold spm in G in change_no_check G' end); rewrite at_at; reflexivity).
      replace (Z_to_bv 64 322360 : word) with (0x4eb38%bv : word) by (apply bv_eq; reflexivity).
      apply (CONTOK r' mdlm0 mdl4 (same_but_materialized_trans _ _ _ SBMm SB0) MI0 SB4 MI4); [apply (RETK r' _ RET) | apply (RETA r' _ RET)].
    - intros r' mdlm0 mdl4 SB0 MI0 SB4 MI4 RET.
      replace (at_ spm (-84)) with (at_ sp (-132)) by ((lazymatch goal with |- ?G => let G' := eval unfold spm in G in change_no_check G' end); rewrite at_at; reflexivity).
      replace (Z_to_bv 64 322360 : word) with (0x4eb38%bv : word) by (apply bv_eq; reflexivity).
      apply (CONTKP r' mdlm0 mdl4 (same_but_materialized_trans _ _ _ SBMm SB0) MI0 SB4 MI4); [apply (RETK r' _ RET) | apply (RETA r' _ RET)].
  Qed.

End FAMAPH.
End FPGenH.
End AsAllocM8rh.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtUnwind OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoison OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoisonI OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMMemA OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8Lc OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8s OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8u.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module AsAllocM8pah.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import Stdlib.Logic.FunctionalExtensionality.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.DivergeSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.SpinAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes.AgentNodes OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocSim OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys6.MhKSys OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsK OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys6.AsKSys OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsRtK OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtUnwind OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoison OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoisonI OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMMemA.AsAllocMI OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM9b.AsAllocM8m OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8k OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8e.AsAllocM8p OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8e OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMRunS2.AsAllocM8r AsAllocM8kh AsAllocM8rh OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8Lc.AsAllocM8pa OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8s OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8u.AsAllocM8t OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8u OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMRunS2.AsAllocM8w OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMRunS2.AsAllocM8x OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMRunS2.AsAllocM8xp.
Import OSSVerify.glaze.binary_reflection.images.Asan.
Import ListNotations.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Ltac wm_clear_disj_or T := lazymatch T with | _ \/ _ => idtac | ?A /\ ?B => first [wm_clear_disj_or A | wm_clear_disj_or B] | ?A <-> ?B => first [wm_clear_disj_or A | wm_clear_disj_or B] | ?A -> ?B => first [wm_clear_disj_or A | wm_clear_disj_or B] end.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AmLia.   (* [comment removed for export] *)
Ltac wm_clear_disj := am_wm_clear_disj.   (* [comment removed for export] *)
Ltac wm_lia0 := tryif noncert_goal_has_var then (Zify.zify; xlia zchecker)
                else first [ solve [noncert_clear_all; Zify.zify; xlia zchecker] | Zify.zify; xlia zchecker ].
#[local] Ltac lia ::= first [ solve [wm_clear_disj; wm_lia0] | wm_lia0 ].
Open Scope bv_scope.
Local Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation ASEGS := Asan.M.loaded_segments.
#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).
#[local] Abbreviation U := bv_unsigned.


Section FPGenPH.
Context {fx : FPState}.

Section PFARMH.
  Variable Hd : word -> bool.
  Hypothesis HOFFSEG : H_off_segments ASEGS Hd.
  Hypothesis WX : wx_segs_nowrap ASEGS.
  (* [comment removed for export] *)
  Variable Hd2 : word -> bool.
  Hypothesis HOFFSEG2 : H_off_segments ASEGS Hd2.
  Variable A2 : list (Z * Z).
  Hypothesis AWF2 : A_wf A2.
  Variables (A : list (Z * Z)) (regs : bvmap 5 word) (mem rom : word -> option byte) (model : Model)
            (sp ra s0v s1v s2v s3v s4v s5v s6v thr tp gp tsdp ctxw v72 v80 vst midend : word) (cpm : byte)
            (RIz SPB c req au mu nf PGP CF T thr0 : Z) (Qok Qf : config -> Prop) (MOK MKP : Model -> Model).
  #[local] Abbreviation stats := (at_ thr 2768).
  #[local] Abbreviation slot := (SPB + c * 2 ^ 32 + mu).
  #[local] Abbreviation SH := ((SPB + c * 2 ^ 32 + mu) / 8 + 0x7fff8000).
  #[local] Abbreviation M0 := (pf_m0 mem sp ra s0v s1v s2v s3v s4v s5v s6v).
  #[local] Abbreviation M1 := (mfi_m1 M0 (at_ sp (-64)) (Z_to_bv 64 0x50ef4) (Z_to_bv 64 RIz) stats (Z_to_bv 64 (SPB + c * 2 ^ 32)) (Z_to_bv 64 (2 ^ 18))
                     (Z_to_bv 64 slot) (Z_to_bv 64 (csize c)) (Z_to_bv 64 slot) (Z_to_bv 64 (2 ^ 18)) (Z_to_bv 64 0x17990) PGP).
  #[local] Abbreviation ENOMEMw := (Z_to_bv 64 (2 ^ 64 - 12) : word).
  #[local] Abbreviation SCR := (word_to_le_bytes 4 (Z_to_bv 64 0xffffffffaaaaaaaa)).
  #[local] Abbreviation MR := (pf_mr mem sp ra s0v s1v s2v s3v s4v s5v s6v stats RIz SPB c mu PGP).
  (* [comment removed for export] *)
  Hypothesis H1 : getr regs 1 = ra.
  Hypothesis H2 : getr regs 2 = sp.
  Hypothesis H4 : getr regs 4 = tp.
  Hypothesis H3 : getr regs 3 = gp.
  Hypothesis H10 : getr regs 10 = Z_to_bv 64 0x103f18.
  Hypothesis H11 : getr regs 11 = stats.
  Hypothesis H12 : getr regs 12 = Z_to_bv 64 c.
  Hypothesis H13 : getr regs 13 = Z_to_bv 64 RIz.
  Hypothesis H14 : getr regs 14 = Z_to_bv 64 req.
  Hypothesis H8 : getr regs 8 = s0v.
  Hypothesis H9 : getr regs 9 = s1v.
  Hypothesis H18 : getr regs 18 = s2v.
  Hypothesis H19 : getr regs 19 = s3v.
  Hypothesis H20 : getr regs 20 = s4v.
  Hypothesis H21 : getr regs 21 = s5v.
  Hypothesis H22 : getr regs 22 = s6v.
  Hypothesis Hsp : 2 ^ 32 + 4096 <= U sp /\ U sp + 16 <= 2 ^ 47.
  Hypothesis Hret : ret_ok ra.
  Hypothesis Hc : 1 <= c <= 30.
  Hypothesis Hreq : 1 <= req /\ csize c * req <= 2 ^ 18.
  Hypothesis Hau : 0 <= au <= mu /\ mu + 2 ^ 18 <= 0xE0000000.
  Hypothesis Hmap : mu < au + csize c * req.
  Hypothesis HSPB : 0 <= SPB /\ SPB + 2 ^ 37 < 2 ^ 63 /\ SPB mod 4096 = 0 /\ AIMGHI <= SPB.
  Hypothesis Hmu4k : mu mod 4096 = 0.
  Hypothesis Hnf : 0 <= nf <= 2 ^ 27.
  Hypothesis HRI : AIMGHI <= RIz /\ RIz + 128 <= U sp - 464.
  Hypothesis HPGP : AIMGLO <= PGP /\ PGP + 8 <= AIMGHI.
  Hypothesis HCF : AIMGLO <= CF /\ CF + 264 <= AIMGHI.
  Hypothesis Hstk : store_ok ASEGS mem (at_ sp (-464)) 464 = true.
  Hypothesis C_sbeg : rdn ASEGS mem (Z_to_bv 64 (0x103f18 + 32)) 8 = Some (LE8 (Z_to_bv 64 SPB)).
  Hypothesis R_au : rdn ASEGS mem (Z_to_bv 64 (RIz + 32)) 8 = Some (LE8 (Z_to_bv 64 au)).
  Hypothesis R_mu : rdn ASEGS mem (Z_to_bv 64 (RIz + 48)) 8 = Some (LE8 (Z_to_bv 64 mu)).
  Hypothesis R_mm : rdn ASEGS mem (Z_to_bv 64 (RIz + 56)) 8 = Some (LE8 (Z_to_bv 64 0)).
  Hypothesis R_nf : rdn ASEGS mem (Z_to_bv 64 (RIz + 16)) 8 = Some (LE8 (Z_to_bv 64 nf)).
  Hypothesis C_rel : rdn ASEGS mem (Z_to_bv 64 (0x103f18 + 40)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 0xffffffff)).
  Hypothesis C_pre : rdn ASEGS mem (Z_to_bv 64 (0x103f18 + 56)) 1 = Some [Z_to_bv 8 0].
  Hypothesis Rgpg : rdn ASEGS mem (Z_to_bv 64 0xff250) 8 = Some (LE8 (Z_to_bv 64 PGP)).
  Hypothesis Rpg : rdn ASEGS mem (Z_to_bv 64 PGP) 8 = Some (LE8 (Z_to_bv 64 4096)).
  Hypothesis Rgcf : rdn ASEGS mem (Z_to_bv 64 0xff260) 8 = Some (LE8 (Z_to_bv 64 CF)).
  Hypothesis Rdpm : rdn ASEGS mem (Z_to_bv 64 (CF + 260)) 1 = Some [Z_to_bv 8 0].
  Hypothesis Rlim : rdn ASEGS mem (Z_to_bv 64 (CF + 144)) 8 = Some (LE8 (Z_to_bv 64 0)).
  Hypothesis Hslot : slot + 2 ^ 18 <= U sp - 464 \/ U sp <= slot.
  Hypothesis HDsbeg : hid_off Hd (0x103f18 + 32) 8.
  Hypothesis HDrel : hid_off Hd (0x103f18 + 40) 4.
  Hypothesis HDpre : hid_off Hd (0x103f18 + 56) 1.
  Hypothesis HDgpg : hid_off Hd 0xff250 8.
  Hypothesis HDpg : hid_off Hd PGP 8.
  Hypothesis HDgcf : hid_off Hd 0xff260 8.
  Hypothesis HDdpm : hid_off Hd (CF + 260) 1.
  Hypothesis HDlim : hid_off Hd (CF + 144) 8.
  Hypothesis HDscr : hid_off Hd (U sp - 464) 464.
  Hypothesis HALT : m_halted model = None.
  Hypothesis LC : lazy_cover Hd (m_vm_lazy model) A.
  Hypothesis AWF : A_wf A.
  Hypothesis MI : MInv A model.
  Hypothesis NODE : forall mdlm (r1 : bvmap 5 word), same_but_materialized model mdlm -> MInv A mdlm -> m_halted mdlm = None ->
        getr r1 10 = Z_to_bv 64 slot -> getr r1 11 = Z_to_bv 64 (2 ^ 18) -> getr r1 12 = Z_to_bv 64 3 -> getr r1 13 = Z_to_bv 64 50 ->
        getr r1 14 = Z_to_bv 64 (2 ^ 64 - 1) -> getr r1 15 = Z_to_bv 64 0 ->
        forall Qok' Qf' : config -> Prop,
          katwD ASEGS (mkCfg (mkst (regupd r1 10 (Z_to_bv 64 slot)) (0x80740 : word) (zfill (Z_to_bv 64 slot) (Z_to_bv 64 (2 ^ 18)) M1) rom) (MOK mdlm)) Qok' Qf' ->
          katsD ASEGS (mkCfg (epend r1 (0x8073c : word) M1 rom (Z_to_bv 64 222)) mdlm) Qok' Qf'.
  Hypothesis CHILD : forall mdlm, same_but_materialized model mdlm -> MInv A mdlm ->
        (m_halted (MOK mdlm) = None /\ lazy_cover Hd (m_vm_lazy (MOK mdlm)) A /\ MInv A (MOK mdlm))
        /\ (m_halted (MKP mdlm) = None /\ lazy_cover Hd (m_vm_lazy (MKP mdlm)) A /\ MInv A (MKP mdlm)).
  Hypothesis OKSW : forall mdlm mdl4, same_but_materialized model mdlm -> MInv A mdlm -> same_but_materialized (MOK mdlm) mdl4 -> MInv A mdl4 ->
        lazy_cover Hd2 (m_vm_lazy mdl4) A2 /\ MInv A2 mdl4.
  (* [comment removed for export] *)
  Hypothesis HT : U thr = T /\ 4096 <= T /\ T + 4096 <= U sp - 464 /\ T mod 8 = 0.
  Hypothesis HTRI : T + 4096 <= RIz \/ RIz + 128 <= T.
  Hypothesis HTSH : T + 4096 <= SH \/ SH + 2 ^ 15 <= T.
  Hypothesis HRSH : RIz + 128 <= SH \/ SH + 2 ^ 15 <= RIz.
  Hypothesis HTsl : T + 4096 <= slot \/ slot + 2 ^ 18 <= T.
  Hypothesis HRsl : RIz + 128 <= slot \/ slot + 2 ^ 18 <= RIz.
  Hypothesis PH : poisonH ASEGS asan_poison_tab mem (Z_to_bv 64 slot) (Z_to_bv 64 (2 ^ 18)) (Z_to_bv 64 250) (Z_to_bv 64 0x50f10) (at_ sp (-64)) cpm midend thr0.
  Hypothesis GH : gctH ASEGS asan_gct_tab mem (at_ (at_ sp (-64)) (-16)) tp tsdp ctxw thr.
  Hypothesis GB : U (gt_tsd asan_gct_tab) + 8 <= U sp - 464 /\ U tp - 80 <= U sp - 464 /\ U tsdp + 8 <= U sp - 464 /\ U ctxw + 160 <= U sp - 464.
  Hypothesis GS : (U (gt_tsd asan_gct_tab) + 8 <= slot \/ slot + 2 ^ 18 <= U (gt_tsd asan_gct_tab)) /\ (U tp - 80 <= slot \/ slot + 2 ^ 18 <= U tp - 88)
                  /\ (U tsdp + 8 <= slot \/ slot + 2 ^ 18 <= U tsdp) /\ (U ctxw + 160 <= slot \/ slot + 2 ^ 18 <= U ctxw + 152).
  Hypothesis G1 : U (gt_tsd asan_gct_tab) + 8 <= SH \/ SH + 2 ^ 15 <= U (gt_tsd asan_gct_tab).
  Hypothesis G2 : U tp - 80 <= SH \/ SH + 2 ^ 15 <= U tp - 88.
  Hypothesis G3 : U tsdp + 8 <= SH \/ SH + 2 ^ 15 <= U tsdp.
  Hypothesis G4 : U ctxw + 160 <= SH \/ SH + 2 ^ 15 <= U ctxw + 152.
  Hypothesis R72 : rdn ASEGS mem (at_ thr 2872) 8 = Some (LE8 v72).
  Hypothesis R80 : rdn ASEGS mem (at_ thr 2880) 8 = Some (LE8 v80).
  Hypothesis Rst : rdn ASEGS mem (at_ thr 2792) 8 = Some (LE8 vst).
  Hypothesis SOKT : store_ok ASEGS mem thr 4096 = true.
  Hypothesis SOKRI : store_ok ASEGS mem (Z_to_bv 64 RIz) 128 = true.
  Hypothesis HDc : Forall (fun c => hid_off Hd2 c 8) (poison_cells asan_poison_tab).
  Hypothesis HDsh : hid_off Hd2 SH (2 ^ 15).
  Hypothesis HD1 : hid_off Hd2 (U (gt_tsd asan_gct_tab)) 8.
  Hypothesis HD2 : hid_off Hd2 (U tp - 88) 8.
  Hypothesis HD3 : hid_off Hd2 (U tsdp) 8.
  Hypothesis HD4 : hid_off Hd2 (U ctxw + 152) 8.
  Hypothesis HDT : hid_off Hd2 T 4096.
  Hypothesis HDRI : hid_off Hd2 RIz 128.
  Hypothesis HDscr2 : hid_off Hd2 (U sp - 464) 464.
  Hypothesis HDRIa : hid_off Hd RIz 128.
  (* [comment removed for export] *)
  Hypothesis CONT1 : forall (r : bvmap 5 word) mdlm mdl5,
      same_but_materialized model mdlm -> MInv A mdlm -> same_but_materialized (MOK mdlm) mdl5 -> MInv A2 mdl5 ->
      pf_regs sp RIz SPB c r -> getr r 1 = Z_to_bv 64 0x50f68 ->
      getr r 10 = Z_to_bv 64 0x103f18 -> getr r 11 = Z_to_bv 64 RIz -> getr r 12 = Z_to_bv 64 (SPB + c * 2 ^ 32) ->
      getr r 13 = Z_to_bv 64 (nf + (mu + 2 ^ 18 - au) / csize c) ->
      getr r 9 = Z_to_bv 64 (nf + (mu + 2 ^ 18 - au) / csize c) -> getr r 19 = Z_to_bv 64 ((mu + 2 ^ 18 - au) / csize c) ->
      getr r 20 = Z_to_bv 64 (mu + 2 ^ 18 - au) -> getr r 4 = tp -> getr r 3 = gp ->
      katwD ASEGS (mkCfg (mkst r (0x4ea98 : word) (pam_3 MR sp thr v72 v80 vst RIz SPB c slot mu) rom) mdl5) Qok Qf.
  Hypothesis CONT0K : forall (r' r : bvmap 5 word) mdlm mdl5,
      same_but_materialized model mdlm -> MInv A mdlm -> same_but_materialized (MKP mdlm) mdl5 -> MInv A mdl5 ->
      regs_agree (fun i : reg => In i pf_clob) regs r' -> pf_post0 sp ra s0v s1v s2v s3v s4v s5v s6v r' r ->
      katD ASEGS (mkCfg (mkst r ra (wbytes (wbytes M1 (at_ sp (-148)) SCR) (at_ sp (-148)) (word_to_le_bytes 4 (Z_to_bv 64 12))) rom) mdl5) Qf.


  Theorem pf_map_arm_katsD_h : katsD ASEGS (mkCfg (mkst regs (0x50dd4 : word) mem rom) model) Qok Qf.
  Proof using CONT0K CONT1 HDRIa HDscr2 HDRI HDT HD4 HD3 HD2 HD1 HDsh HDc SOKRI SOKT Rst R80 R72 G4 G3 G2 G1 GS GB GH PH HRsl HTsl HRSH HTSH HTRI HT OKSW CHILD NODE MI AWF LC HALT HDscr HDlim HDdpm HDgcf HDpg HDgpg HDpre HDrel HDsbeg Hslot Rlim Rdpm Rgcf Rpg Rgpg C_pre C_rel R_nf R_mm R_mu R_au C_sbeg Hstk HCF HPGP HRI Hnf Hmu4k HSPB Hmap Hau Hreq Hc Hret Hsp H22 H21 H20 H19 H18 H9 H8 H14 H13 H12 H11 H10 H3 H4 H2 H1 MKP MOK thr0 T CF PGP nf mu au req c SPB RIz cpm midend vst v80 v72 ctxw tsdp gp tp thr s6v s5v s4v s3v s2v s1v s0v ra sp A AWF2 A2 HOFFSEG2 Hd2 WX HOFFSEG Hd.
    pose proof (u64_range sp) as Hspr. destruct Hsp as [SP1 SP2]. destruct HRI as [RI1 RI2]. destruct HSPB as (S1 & S2 & S3 & S4).
    destruct Hau as [[AU0 AU1] AU2]. destruct HT as (UT & T1 & T2 & T3). pose proof (u64_range thr) as Hthr.
    assert (SL : 0 <= slot /\ slot + 2 ^ 18 < 2 ^ 63) by lia.
    assert (HDf64 : hid_off Hd (U sp - 64) 64) by (eapply hid_off_sub; [exact HDscr | lia | lia]).
    assert (HDf128 : hid_off Hd2 (U sp - 128) 64) by (eapply hid_off_sub; [exact HDscr2 | lia | lia]).
    assert (FRAMES : forall mdlx mdly, m_halted mdlx = None -> lazy_cover Hd (m_vm_lazy mdlx) A -> same_but_materialized mdlx mdly ->
               m_halted mdly = None /\ lazy_cover Hd (m_vm_lazy mdly) A).
    { intros mdlx mdly HX LX SB. pose proof (same_but_materialized_frame mdlx mdly SB) as FR. split.
      - destruct FR as (_&_&_&_&_&_&_&_&_&_&_&_&Hh&_). rewrite Hh. exact HX.
      - destruct FR as (_ & _ & Hl & _). rewrite Hl. exact LX. }
    apply (pf_usermap_katsD_h Hd HOFFSEG WX A regs mem rom model sp ra s0v s1v s2v s3v s4v s5v s6v stats RIz SPB c req au mu PGP CF Qok Qf MOK MKP
             H1 H2 H10 H11 H12 H13 H14 H8 H9 H18 H19 H20 H21 H22 ltac:(lia) Hc Hreq (conj (conj AU0 AU1) AU2) Hmap (conj S1 (conj S2 (conj S3 S4))) Hmu4k (conj RI1 RI2) HPGP HCF Hstk
             C_sbeg R_au R_mu R_mm C_rel C_pre Rgpg Rpg Rgcf Rdpm Rlim Hslot
             HDsbeg ltac:(eapply hid_off_sub; [exact HDRIa | lia | lia]) ltac:(eapply hid_off_sub; [exact HDRIa | lia | lia]) ltac:(eapply hid_off_sub; [exact HDRIa | lia | lia])
             HDrel HDpre HDgpg HDpg HDgcf HDdpm HDlim HDscr HALT LC AWF MI NODE CHILD).
    - (* [comment removed for export] *)
      intros r' mdlm mdl4 SBm MIm SB4 MI4 (PR & E9 & E19 & E20 & E22 & E10) AG.
      destruct (CHILD mdlm SBm MIm) as ((HOK & LOK & _) & _).
      destruct (FRAMES _ _ HOK LOK SB4) as [HALT4 LC4].
      destruct (OKSW mdlm mdl4 SBm MIm SB4 MI4) as [LC2 MI2].
      assert (OUT : forall x : word, (U x < U sp - 464 \/ U sp <= U x) -> (U x < slot \/ slot + 2 ^ 18 <= U x) -> MR x = mem x)
        by (intros x X1 X2; apply pf_mr_outside; [lia | exact SL | exact X1 | exact X2]).
      assert (GR : mem_grows mem MR) by apply pf_mr_grows.
      assert (RDZ : forall (z : Z) (k : nat) v, 0 <= z -> z + Z.of_nat k <= U sp - 464 -> (z + Z.of_nat k <= slot \/ slot + 2 ^ 18 <= z) ->
                 rdn ASEGS mem (Z_to_bv 64 z) k = Some v -> rdn ASEGS MR (Z_to_bv 64 z) k = Some v).
      { intros z k v Z0 Z1 Z2 Hr. rewrite <- Hr. apply rdn_ext; [first [ solve [ wd_unorm1; wd_zofnat; lia ] | rewrite u_Z2bv by lia; lia ]|]. intros x Hx. rewrite u_Z2bv in Hx by lia.
        apply OUT; clear - Hx Z1 Z2; lia. }
      assert (RDT : forall (k : Z) v, 0 <= k -> k + 8 <= 4096 -> rdn ASEGS mem (at_ thr k) 8 = Some v -> rdn ASEGS MR (at_ thr k) 8 = Some v).
      { intros k v K0 K1 Hr. rewrite <- Hr. apply rdn_ext; [first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ]|]. intros x Hx. rewrite at_u in Hx by lia. cbn in Hx.
        apply OUT; clear - Hx UT T2 HTsl K0 K1; lia. }
      change (wbytes (zfill (Z_to_bv 64 slot) (Z_to_bv 64 (2 ^ 18)) M1) (at_ sp (-148)) SCR) with MR.
      apply (pf_after_map_katwD Hd2 HOFFSEG2 WX A2 r' MR rom mdl4 sp thr tp gp tsdp ctxw v72 v80 vst midend cpm RIz SPB c au mu nf T thr0 Qok Qf
               PR ltac:(rewrite (AG 4%bv) by ((lazymatch goal with |- ?G => let G' := eval unfold pf_clob in G in change_no_check G' end); (lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); intros X; repeat (destruct X as [X|X]; [discriminate X|]); exact X); exact H4)
               ltac:(rewrite (AG 3%bv) by ((lazymatch goal with |- ?G => let G' := eval unfold pf_clob in G in change_no_check G' end); (lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); intros X; repeat (destruct X as [X|X]; [discriminate X|]); exact X); exact H3)
               E9 E10 E19 E20 E22 (conj SP1 SP2) Hc (conj (conj AU0 AU1) AU2) Hnf ltac:(lia) ltac:(lia) ltac:(lia) HTRI HTSH HRSH).
      + apply (poisonH_keep_P ASEGS asan_poison_tab mem MR _ _ _ _ _ cpm midend thr0
                 (fun z => (z < U sp - 464 \/ U sp <= z) /\ (z < slot \/ slot + 2 ^ 18 <= z)) PH); [intros x [X1 X2]; apply OUT; assumption | exact GR |].
        eapply Forall_impl; [|exact asan_poison_cells_img]. cbv beta. intros c0 Hc0 z Hz. lia.
      + destruct GB as (B1 & B2 & B3 & B4). destruct GS as (Q1 & Q2 & Q3 & Q4).
        apply (gctH_keep_P ASEGS asan_gct_tab mem MR _ tp tsdp ctxw thr
                 (fun z => (z < U sp - 464 \/ U sp <= z) /\ (z < slot \/ slot + 2 ^ 18 <= z)) GH);
          [intros x [X1 X2]; apply OUT; assumption | exact GR
          | intros z Hz; cbv beta; clear - Hz B1 Q1; lia | intros z Hz; cbv beta; clear - Hz B2 Q2; lia
          | intros z Hz; cbv beta; clear - Hz B3 Q3; lia | intros z Hz; cbv beta; clear - Hz B4 Q4; lia].
      + destruct GB as (B1 & B2 & B3 & B4). lia.
      + exact G1.
      + exact G2.
      + exact G3.
      + exact G4.
      + apply RDT; [lia | lia | exact R72].
      + apply RDT; [lia | lia | exact R80].
      + apply RDT; [lia | lia | exact Rst].
      + apply RDZ; [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear - HRsl; lia | exact R_au].
      + apply RDZ; [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear - HRsl; lia | exact R_mu].
      + apply RDZ; [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear - HRsl; lia | exact R_nf].
      + eapply store_ok_mono; [exact GR | exact SOKT].
      + eapply store_ok_mono; [exact GR | exact SOKRI].
      + exact HDc.
      + exact HDf128.
      + exact HDsh.
      + exact HD1.
      + exact HD2.
      + exact HD3.
      + exact HD4.
      + exact HDT.
      + exact HDRI.
      + exact HALT4.
      + exact LC2.
      + exact AWF2.
      + exact MI2.
      + intros r mdl5 SB5 MI5 D0 D1 D10 D11 D12 D13 D9 D19 D20 D4 D3.
        exact (CONT1 r mdlm mdl5 SBm MIm (same_but_materialized_trans _ _ _ SB4 SB5) MI5 D0 D1 D10 D11 D12 D13 D9 D19 D20 D4 D3).
    - (* [comment removed for export] *)
      intros r' mdlm mdl4 SBm MIm SB4 MI4 (PR & E9 & E19 & E20 & E22 & E10) AG.
      destruct (CHILD mdlm SBm MIm) as (_ & (HKP & LKP & _)).
      destruct (FRAMES _ _ HKP LKP SB4) as [HALT4 LC4].
      set (MK := wbytes (wbytes M1 (at_ sp (-148)) SCR) (at_ sp (-148)) (word_to_le_bytes 4 (Z_to_bv 64 12))).
      assert (AGR : forall x : word, U sp - 64 <= U x < U sp -> MK x = M0 x).
      { intros x Hx. (lazymatch goal with |- ?G => let G' := eval unfold MK in G in change_no_check G' end).
        repeat (rewrite MemsetLibF.MemSplit.wbytes_outside; [ | rewrite length_N_to_le_bytes, at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite length_N_to_le_bytes, at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia]).
        apply mfi_m1_outside; first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite ?at_u by lia; lia ]. }
      destruct PR as (P2 & _).
      apply (pf_fail_map_katD Hd HOFFSEG WX A r' MK rom mdl4 sp ra s0v s1v s2v s3v s4v s5v s6v Qf P2 E10 Hret ltac:(lia)
               (pf_slots_ext MK mem sp ra s0v s1v s2v s3v s4v s5v s6v (-8) ra ltac:(lia) ltac:(lia) AGR ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 10))
               (pf_slots_ext MK mem sp ra s0v s1v s2v s3v s4v s5v s6v (-16) s0v ltac:(lia) ltac:(lia) AGR ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 10))
               (pf_slots_ext MK mem sp ra s0v s1v s2v s3v s4v s5v s6v (-24) s1v ltac:(lia) ltac:(lia) AGR ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 10))
               (pf_slots_ext MK mem sp ra s0v s1v s2v s3v s4v s5v s6v (-32) s2v ltac:(lia) ltac:(lia) AGR ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 10))
               (pf_slots_ext MK mem sp ra s0v s1v s2v s3v s4v s5v s6v (-40) s3v ltac:(lia) ltac:(lia) AGR ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 10))
               (pf_slots_ext MK mem sp ra s0v s1v s2v s3v s4v s5v s6v (-48) s4v ltac:(lia) ltac:(lia) AGR ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 10))
               (pf_slots_ext MK mem sp ra s0v s1v s2v s3v s4v s5v s6v (-56) s5v ltac:(lia) ltac:(lia) AGR ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 10))
               (pf_slots_ext MK mem sp ra s0v s1v s2v s3v s4v s5v s6v (-64) s6v ltac:(lia) ltac:(lia) AGR ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 10))
               HDf64 HALT4 LC4 AWF MI4).
      intros r mdl5 SB5 MI5 POST.
      exact (CONT0K r' r mdlm mdl5 SBm MIm (same_but_materialized_trans _ _ _ SB4 SB5) MI5 AG POST).
  Qed.
End PFARMH.
End FPGenPH.
End AsAllocM8pah.
Module AsAllocM8yh.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import Stdlib.Logic.FunctionalExtensionality.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.DivergeSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.SpinAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes.AgentNodes OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocSim OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys6.MhKSys OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsK OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys6.AsKSys OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsRtK OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtUnwind OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoison OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoisonI OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMMemA.AsAllocMI OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM9b.AsAllocM8m OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8k OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8e OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMRunS2.AsAllocM8r OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8s OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8u.AsAllocM8t OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8u OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMRunS2.AsAllocM8w OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMRunS2.AsAllocM8x.
Import AsAllocM8kh AsAllocM8rh OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMRunS2.AsAllocM8y.
Import OSSVerify.glaze.binary_reflection.images.Asan.
Import ListNotations.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Ltac wm_clear_disj_or T := lazymatch T with | _ \/ _ => idtac | ?A /\ ?B => first [wm_clear_disj_or A | wm_clear_disj_or B] | ?A <-> ?B => first [wm_clear_disj_or A | wm_clear_disj_or B] | ?A -> ?B => first [wm_clear_disj_or A | wm_clear_disj_or B] end.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AmLia.   (* [comment removed for export] *)
Ltac wm_clear_disj := am_wm_clear_disj.   (* [comment removed for export] *)
Ltac wm_lia0 := tryif noncert_goal_has_var then (Zify.zify; xlia zchecker)
                else first [ solve [noncert_clear_all; Zify.zify; xlia zchecker] | Zify.zify; xlia zchecker ].
#[local] Ltac lia ::= first [ solve [wm_clear_disj; wm_lia0] | wm_lia0 ].
Open Scope bv_scope.
Local Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation ASEGS := Asan.M.loaded_segments.
#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).
#[local] Abbreviation U := bv_unsigned.

Section FPGenYH.
Context {fx : FPState}.

Section EFSARMH.
  Variable Hd : word -> bool.
  Hypothesis HOFFSEG : H_off_segments ASEGS Hd.
  Hypothesis WX : wx_segs_nowrap ASEGS.
  (* [comment removed for export] *)
  Variable Hd2 : word -> bool.
  Hypothesis HOFFSEG2 : H_off_segments ASEGS Hd2.
  Variable A2 : list (Z * Z).
  Hypothesis AWF2 : A_wf A2.
  Variables (A : list (Z * Z)) (regs : bvmap 5 word) (mem rom : word -> option byte) (model : Model)
            (sp ra s0v s1v s2v s3v s4v s5v thr tp gp tsdp ctxw v72 v80 midend : word) (cpm : byte)
            (RIz rbeg tot mfa PGP CF T thr0 : Z) (Qok Qf : config -> Prop) (MOK MKP : Model -> Model).
  #[local] Abbreviation slot := (rbeg + 0xE0000000 + mfa).
  #[local] Abbreviation SH := ((rbeg + 0xE0000000 + mfa) / 8 + 0x7fff8000).
  #[local] Abbreviation M0 := (efs_m0 mem sp ra s0v s1v s2v s3v).
  #[local] Abbreviation M1 := (mfi_m1 M0 (at_ sp (-48)) (Z_to_bv 64 0x4eb38) (Z_to_bv 64 (mfa + 2 ^ 18)) (Z_to_bv 64 slot) (Z_to_bv 64 (2 ^ 18)) (Z_to_bv 64 RIz)
                     s4v s5v (Z_to_bv 64 slot) (Z_to_bv 64 (2 ^ 18)) (Z_to_bv 64 0x19801) PGP).
  #[local] Abbreviation ENOMEMw := (Z_to_bv 64 (2 ^ 64 - 12) : word).
  #[local] Abbreviation SCR := (word_to_le_bytes 4 (Z_to_bv 64 0xffffffffaaaaaaaa)).
  #[local] Abbreviation MR := (efs_mr mem sp ra s0v s1v s2v s3v s4v s5v RIz slot mfa PGP).
  (* [comment removed for export] *)
  Hypothesis H1 : getr regs 1 = ra.
  Hypothesis H2 : getr regs 2 = sp.
  Hypothesis H4 : getr regs 4 = tp.
  Hypothesis H3 : getr regs 3 = gp.
  Hypothesis H10 : getr regs 10 = Z_to_bv 64 0x103f18.
  Hypothesis H11 : getr regs 11 = Z_to_bv 64 RIz.
  Hypothesis H12 : getr regs 12 = Z_to_bv 64 rbeg.
  Hypothesis H13 : getr regs 13 = Z_to_bv 64 tot.
  Hypothesis H8 : getr regs 8 = s0v.
  Hypothesis H9 : getr regs 9 = s1v.
  Hypothesis H18 : getr regs 18 = s2v.
  Hypothesis H19 : getr regs 19 = s3v.
  Hypothesis H20 : getr regs 20 = s4v.
  Hypothesis H21 : getr regs 21 = s5v.
  Hypothesis Hsp : 2 ^ 32 + 4096 <= U sp /\ U sp + 16 <= 2 ^ 47.
  Hypothesis Hret : ret_ok ra.
  Hypothesis Htot : 0 <= tot /\ 4 * tot <= 2 ^ 29.
  Hypothesis Hmfa : 0 <= mfa <= 2 ^ 29 /\ mfa mod 2 ^ 18 = 0.
  Hypothesis Hneed : mfa < 4 * tot <= mfa + 2 ^ 18.
  Hypothesis Hroom : mfa + 2 ^ 18 <= 2 ^ 29.
  Hypothesis Hrbeg : AIMGHI <= rbeg /\ rbeg + 2 ^ 32 < 2 ^ 63 /\ rbeg mod 4096 = 0.
  Hypothesis HRI : AIMGHI <= RIz /\ RIz + 128 <= U sp - 448.
  Hypothesis HPGP : AIMGLO <= PGP /\ PGP + 8 <= AIMGHI.
  Hypothesis HCF : AIMGLO <= CF /\ CF + 264 <= AIMGHI.
  Hypothesis Hstk : store_ok ASEGS mem (at_ sp (-448)) 448 = true.
  Hypothesis R_mfa : rdn ASEGS mem (Z_to_bv 64 (RIz + 24)) 8 = Some (LE8 (Z_to_bv 64 mfa)).
  Hypothesis C_pre : rdn ASEGS mem (Z_to_bv 64 (0x103f18 + 56)) 1 = Some [Z_to_bv 8 0].
  Hypothesis Rgpg : rdn ASEGS mem (Z_to_bv 64 0xff250) 8 = Some (LE8 (Z_to_bv 64 PGP)).
  Hypothesis Rpg : rdn ASEGS mem (Z_to_bv 64 PGP) 8 = Some (LE8 (Z_to_bv 64 4096)).
  Hypothesis Rgcf : rdn ASEGS mem (Z_to_bv 64 0xff260) 8 = Some (LE8 (Z_to_bv 64 CF)).
  Hypothesis Rdpm : rdn ASEGS mem (Z_to_bv 64 (CF + 260)) 1 = Some [Z_to_bv 8 0].
  Hypothesis Rlim : rdn ASEGS mem (Z_to_bv 64 (CF + 144)) 8 = Some (LE8 (Z_to_bv 64 0)).
  Hypothesis Hslot : slot + 2 ^ 18 <= U sp - 448 \/ U sp <= slot.
  Hypothesis HDmfa : hid_off Hd (RIz + 24) 8.
  Hypothesis HDpre : hid_off Hd (0x103f18 + 56) 1.
  Hypothesis HDgpg : hid_off Hd 0xff250 8.
  Hypothesis HDpg : hid_off Hd PGP 8.
  Hypothesis HDgcf : hid_off Hd 0xff260 8.
  Hypothesis HDdpm : hid_off Hd (CF + 260) 1.
  Hypothesis HDlim : hid_off Hd (CF + 144) 8.
  Hypothesis HDscr : hid_off Hd (U sp - 448) 448.
  Hypothesis HALT : m_halted model = None.
  Hypothesis LC : lazy_cover Hd (m_vm_lazy model) A.
  Hypothesis AWF : A_wf A.
  Hypothesis MI : MInv A model.
  Hypothesis NODE : forall mdlm (r1 : bvmap 5 word), same_but_materialized model mdlm -> MInv A mdlm -> m_halted mdlm = None ->
        getr r1 10 = Z_to_bv 64 slot -> getr r1 11 = Z_to_bv 64 (2 ^ 18) -> getr r1 12 = Z_to_bv 64 3 -> getr r1 13 = Z_to_bv 64 50 ->
        getr r1 14 = Z_to_bv 64 (2 ^ 64 - 1) -> getr r1 15 = Z_to_bv 64 0 ->
        forall Qok' Qf' : config -> Prop,
          katwD ASEGS (mkCfg (mkst (regupd r1 10 (Z_to_bv 64 slot)) (0x80740 : word) (zfill (Z_to_bv 64 slot) (Z_to_bv 64 (2 ^ 18)) M1) rom) (MOK mdlm)) Qok' Qf' ->
          katsD ASEGS (mkCfg (epend r1 (0x8073c : word) M1 rom (Z_to_bv 64 222)) mdlm) Qok' Qf'.
  Hypothesis CHILD : forall mdlm, same_but_materialized model mdlm -> MInv A mdlm ->
        (m_halted (MOK mdlm) = None /\ lazy_cover Hd (m_vm_lazy (MOK mdlm)) A /\ MInv A (MOK mdlm))
        /\ (m_halted (MKP mdlm) = None /\ lazy_cover Hd (m_vm_lazy (MKP mdlm)) A /\ MInv A (MKP mdlm)).
  Hypothesis OKSW : forall mdlm mdl4, same_but_materialized model mdlm -> MInv A mdlm -> same_but_materialized (MOK mdlm) mdl4 -> MInv A mdl4 ->
        lazy_cover Hd2 (m_vm_lazy mdl4) A2 /\ MInv A2 mdl4.
  (* [comment removed for export] *)
  Hypothesis HT : U thr = T /\ 4096 <= T /\ T + 4096 <= U sp - 448 /\ T mod 8 = 0.
  Hypothesis HTRI : T + 4096 <= RIz \/ RIz + 128 <= T.
  Hypothesis HTSH : T + 4096 <= SH \/ SH + 2 ^ 15 <= T.
  Hypothesis HRSH : RIz + 128 <= SH \/ SH + 2 ^ 15 <= RIz.
  Hypothesis HSSH : U sp <= SH \/ SH + 2 ^ 15 <= U sp - 448.
  Hypothesis HTsl : T + 4096 <= slot \/ slot + 2 ^ 18 <= T.
  Hypothesis PH : poisonH ASEGS asan_poison_tab mem (Z_to_bv 64 slot) (Z_to_bv 64 (2 ^ 18)) (Z_to_bv 64 250) (Z_to_bv 64 0x4eb54) (at_ sp (-48)) cpm midend thr0.
  Hypothesis PCB : Forall (fun c => c + 8 <= AIMGHI) (poison_cells asan_poison_tab).
  Hypothesis GH : gctH ASEGS asan_gct_tab mem (at_ (at_ sp (-48)) (-16)) tp tsdp ctxw thr.
  Hypothesis GB : U (gt_tsd asan_gct_tab) + 8 <= U sp - 448 /\ U tp - 80 <= U sp - 448 /\ U tsdp + 8 <= U sp - 448 /\ U ctxw + 160 <= U sp - 448.
  Hypothesis GS : (U (gt_tsd asan_gct_tab) + 8 <= slot \/ slot + 2 ^ 18 <= U (gt_tsd asan_gct_tab)) /\ (U tp - 80 <= slot \/ slot + 2 ^ 18 <= U tp - 88)
                  /\ (U tsdp + 8 <= slot \/ slot + 2 ^ 18 <= U tsdp) /\ (U ctxw + 160 <= slot \/ slot + 2 ^ 18 <= U ctxw + 152).
  Hypothesis G1 : U (gt_tsd asan_gct_tab) + 8 <= SH \/ SH + 2 ^ 15 <= U (gt_tsd asan_gct_tab).
  Hypothesis G2 : U tp - 80 <= SH \/ SH + 2 ^ 15 <= U tp - 88.
  Hypothesis G3 : U tsdp + 8 <= SH \/ SH + 2 ^ 15 <= U tsdp.
  Hypothesis G4 : U ctxw + 160 <= SH \/ SH + 2 ^ 15 <= U ctxw + 152.
  Hypothesis R72 : rdn ASEGS mem (at_ thr 2872) 8 = Some (LE8 v72).
  Hypothesis R80 : rdn ASEGS mem (at_ thr 2880) 8 = Some (LE8 v80).
  Hypothesis SOKT : store_ok ASEGS mem thr 4096 = true.
  Hypothesis SOKRI : store_ok ASEGS mem (Z_to_bv 64 RIz) 128 = true.
  Hypothesis HDc : Forall (fun c => hid_off Hd2 c 8) (poison_cells asan_poison_tab).
  Hypothesis HDsh : hid_off Hd2 SH (2 ^ 15).
  Hypothesis HD1 : hid_off Hd2 (U (gt_tsd asan_gct_tab)) 8.
  Hypothesis HD2 : hid_off Hd2 (U tp - 88) 8.
  Hypothesis HD3 : hid_off Hd2 (U tsdp) 8.
  Hypothesis HD4 : hid_off Hd2 (U ctxw + 152) 8.
  Hypothesis HDT : hid_off Hd2 T 4096.
  Hypothesis HDRI : hid_off Hd2 RIz 128.
  Hypothesis HDscr2 : hid_off Hd2 (U sp - 448) 448.
  (* [comment removed for export] *)
  Hypothesis CONT1 : forall (r : bvmap 5 word) mdlm mdl5,
      same_but_materialized model mdlm -> MInv A mdlm -> same_but_materialized (MOK mdlm) mdl5 -> MInv A2 mdl5 ->
      getr r 10 = Z_to_bv 64 1 -> getr r 2 = sp -> getr r 1 = ra ->
      getr r 8 = s0v -> getr r 9 = s1v -> getr r 18 = s2v -> getr r 19 = s3v -> getr r 20 = s4v -> getr r 21 = s5v -> getr r 4 = tp -> getr r 3 = gp ->
      katwD ASEGS (mkCfg (mkst r ra (eam_3 MR sp s4v s5v thr v72 v80 RIz slot mfa) rom) mdl5) Qok Qf.
  Hypothesis CONT0K : forall (r' r : bvmap 5 word) mdlm mdl5,
      same_but_materialized model mdlm -> MInv A mdlm -> same_but_materialized (MKP mdlm) mdl5 -> MInv A mdl5 ->
      regs_agree (fun i : reg => In i efs_clob) regs r' -> efs_post sp ra s0v s1v s2v s3v 0 r' r ->
      katD ASEGS (mkCfg (mkst r ra (wbytes (wbytes M1 (at_ sp (-132)) SCR) (at_ sp (-132)) (word_to_le_bytes 4 (Z_to_bv 64 12))) rom) mdl5) Qf.


  Theorem efs_map_arm_katwD_h : katwD ASEGS (mkCfg (mkst regs (0x4ea98 : word) mem rom) model) Qok Qf.
  Proof using CONT0K CONT1 HDscr2 HDRI HDT HD4 HD3 HD2 HD1 HDsh HDc SOKRI SOKT R80 R72 G4 G3 G2 G1 GS GB GH PCB PH HTsl HSSH HRSH HTSH HTRI HT OKSW CHILD NODE MI AWF LC HALT HDscr HDlim HDdpm HDgcf HDpg HDgpg HDpre HDmfa Hslot Rlim Rdpm Rgcf Rpg Rgpg C_pre R_mfa Hstk HCF HPGP HRI Hrbeg Hroom Hneed Hmfa Htot Hret Hsp H21 H20 H19 H18 H9 H8 H13 H12 H11 H10 H3 H4 H2 H1 MKP MOK thr0 T CF PGP mfa tot rbeg RIz cpm midend v80 v72 ctxw tsdp gp tp thr s5v s4v s3v s2v s1v s0v ra sp A AWF2 A2 HOFFSEG2 Hd2 WX HOFFSEG Hd.
    pose proof (u64_range sp) as Hspr. destruct Hsp as [SP1 SP2]. destruct HRI as [RI1 RI2]. destruct Hrbeg as (RB1 & RB2 & RB3).
    destruct Hmfa as [[MF1 MF2] MF3]. destruct HT as (UT & T1 & T2 & T3). pose proof (u64_range thr) as Hthr.
    assert (SL : 0 <= slot /\ slot + 2 ^ 18 < 2 ^ 63) by lia.
    assert (HDf48 : hid_off Hd (U sp - 48) 48) by (eapply hid_off_sub; [exact HDscr | lia | lia]).
    assert (HDf112 : hid_off Hd2 (U sp - 112) 112) by (eapply hid_off_sub; [exact HDscr2 | lia | lia]).
    assert (FRAMES : forall mdlx mdly, m_halted mdlx = None -> lazy_cover Hd (m_vm_lazy mdlx) A -> same_but_materialized mdlx mdly ->
               m_halted mdly = None /\ lazy_cover Hd (m_vm_lazy mdly) A).
    { intros mdlx mdly HX LX SB. pose proof (same_but_materialized_frame mdlx mdly SB) as FR. split.
      - destruct FR as (_&_&_&_&_&_&_&_&_&_&_&_&Hh&_). rewrite Hh. exact HX.
      - destruct FR as (_ & _ & Hl & _). rewrite Hl. exact LX. }
    apply katsD_katwD.
    apply (efs_famap_katsD_h Hd HOFFSEG WX A regs mem rom model sp ra s0v s1v s2v s3v s4v s5v RIz rbeg tot mfa PGP CF Qok Qf MOK MKP
             H1 H2 H10 H11 H12 H13 H8 H9 H18 H19 H20 H21 ltac:(lia) Htot (conj (conj MF1 MF2) MF3) Hneed Hroom (conj RB1 (conj RB2 RB3)) (conj RI1 RI2) HPGP HCF Hstk
             R_mfa C_pre Rgpg Rpg Rgcf Rdpm Rlim Hslot HDmfa HDpre HDgpg HDpg HDgcf HDdpm HDlim HDscr HALT LC AWF MI NODE CHILD).
    - (* [comment removed for export] *)
      intros r' mdlm mdl4 SBm MIm SB4 MI4 (E2 & E8 & E9 & E18 & E19 & E10 & E20) AG.
      destruct (CHILD mdlm SBm MIm) as ((HOK & LOK & _) & _).
      destruct (FRAMES _ _ HOK LOK SB4) as [HALT4 LC4].
      destruct (OKSW mdlm mdl4 SBm MIm SB4 MI4) as [LC2 MI2].
      assert (OUT : forall x : word, (U x < U sp - 448 \/ U sp <= U x) -> (U x < slot \/ slot + 2 ^ 18 <= U x) -> MR x = mem x)
        by (intros x X1 X2; apply efs_mr_outside; [lia | exact SL | exact X1 | exact X2]).
      assert (GR : mem_grows mem MR) by apply efs_mr_grows.
      change (wbytes (zfill (Z_to_bv 64 slot) (Z_to_bv 64 (2 ^ 18)) M1) (at_ sp (-132)) SCR) with MR.
      apply (efs_after_map_katwD Hd2 HOFFSEG2 WX A2 r' MR rom mdl4 sp ra s0v s1v s2v s3v s4v s5v thr tp gp tsdp ctxw v72 v80 midend cpm RIz slot mfa T thr0 Qok Qf
               E2 ltac:(rewrite (AG 4%bv) by ((lazymatch goal with |- ?G => let G' := eval unfold efs_clob in G in change_no_check G' end); (lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); intros X; repeat (destruct X as [X|X]; [discriminate X|]); exact X); exact H4)
               ltac:(rewrite (AG 3%bv) by ((lazymatch goal with |- ?G => let G' := eval unfold efs_clob in G in change_no_check G' end); (lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); intros X; repeat (destruct X as [X|X]; [discriminate X|]); exact X); exact H3)
               E8 E9 E10 E18 E19 E20
               ltac:(rewrite (AG 21%bv) by ((lazymatch goal with |- ?G => let G' := eval unfold efs_clob in G in change_no_check G' end); (lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); intros X; repeat (destruct X as [X|X]; [discriminate X|]); exact X); exact H21)
               (conj SP1 SP2) Hret ltac:(lia) (conj MF1 MF2) ltac:(lia) ltac:(lia) HTRI HTSH HRSH ltac:(clear - HSSH; lia)).
      + (* [comment removed for export] *)
        apply (poisonH_keep_P ASEGS asan_poison_tab mem MR _ _ _ _ _ cpm midend thr0
                 (fun z => (z < U sp - 448 \/ U sp <= z) /\ (z < slot \/ slot + 2 ^ 18 <= z)) PH); [intros x [X1 X2]; apply OUT; assumption | exact GR |].
        eapply Forall_impl; [|exact PCB]. cbv beta. intros c Hc z Hz. lia.
      + (* [comment removed for export] *)
        destruct GB as (B1 & B2 & B3 & B4). destruct GS as (S1 & S2 & S3 & S4).
        apply (gctH_keep_P ASEGS asan_gct_tab mem MR _ tp tsdp ctxw thr
                 (fun z => (z < U sp - 448 \/ U sp <= z) /\ (z < slot \/ slot + 2 ^ 18 <= z)) GH); [intros x [X1 X2]; apply OUT; assumption | exact GR
                 | intros z Hz; cbv beta; clear - Hz B1 S1; lia | intros z Hz; cbv beta; clear - Hz B2 S2; lia
                 | intros z Hz; cbv beta; clear - Hz B3 S3; lia | intros z Hz; cbv beta; clear - Hz B4 S4; lia].
      + destruct GB as (B1 & B2 & B3 & B4). lia.
      + exact G1.
      + exact G2.
      + exact G3.
      + exact G4.
      + rewrite <- R72. apply rdn_ext; [first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ]|]. intros x Hx. rewrite at_u in Hx by lia. cbn in Hx. apply OUT; clear - Hx UT T2 HTsl; lia.
      + rewrite <- R80. apply rdn_ext; [first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ]|]. intros x Hx. rewrite at_u in Hx by lia. cbn in Hx. apply OUT; clear - Hx UT T2 HTsl; lia.
      + eapply store_ok_mono; [exact GR | exact SOKT].
      + eapply store_ok_mono; [exact GR | exact SOKRI].
      + apply (efs_mr_slots mem sp ra s0v s1v s2v s3v s4v s5v RIz slot mfa PGP ltac:(lia) SL (-8) ra Hslot); (lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 8.
      + apply (efs_mr_slots mem sp ra s0v s1v s2v s3v s4v s5v RIz slot mfa PGP ltac:(lia) SL (-16) s0v Hslot); (lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 8.
      + apply (efs_mr_slots mem sp ra s0v s1v s2v s3v s4v s5v RIz slot mfa PGP ltac:(lia) SL (-24) s1v Hslot); (lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 8.
      + apply (efs_mr_slots mem sp ra s0v s1v s2v s3v s4v s5v RIz slot mfa PGP ltac:(lia) SL (-32) s2v Hslot); (lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 8.
      + apply (efs_mr_slots mem sp ra s0v s1v s2v s3v s4v s5v RIz slot mfa PGP ltac:(lia) SL (-40) s3v Hslot); (lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 8.
      + exact HDc.
      + exact HDf112.
      + exact HDsh.
      + exact HD1.
      + exact HD2.
      + exact HD3.
      + exact HD4.
      + exact HDT.
      + exact HDRI.
      + exact HALT4.
      + exact LC2.
      + exact AWF2.
      + exact MI2.
      + intros r mdl5 SB5 MI5 C10 C2 C1 C8 C9 C18 C19 C20 C21 C4 C3.
        exact (CONT1 r mdlm mdl5 SBm MIm (same_but_materialized_trans _ _ _ SB4 SB5) MI5 C10 C2 C1 C8 C9 C18 C19 C20 C21 C4 C3).
    - (* [comment removed for export] *)
      intros r' mdlm mdl4 SBm MIm SB4 MI4 (E2 & E8 & E9 & E18 & E19 & E10 & E20) AG.
      destruct (CHILD mdlm SBm MIm) as (_ & (HKP & LKP & _)).
      destruct (FRAMES _ _ HKP LKP SB4) as [HALT4 LC4].
      set (MK := wbytes (wbytes M1 (at_ sp (-132)) SCR) (at_ sp (-132)) (word_to_le_bytes 4 (Z_to_bv 64 12))).
      assert (AGR : forall x : word, U sp - 48 <= U x < U sp -> MK x = M0 x).
      { intros x Hx. (lazymatch goal with |- ?G => let G' := eval unfold MK in G in change_no_check G' end).
        repeat (rewrite MemsetLibF.MemSplit.wbytes_outside; [ | rewrite length_N_to_le_bytes, at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite length_N_to_le_bytes, at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia]).
        apply mfi_m1_outside; first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite ?at_u by lia; lia ]. }
      apply (efs_fail_katD Hd HOFFSEG WX A r' MK rom mdl4 sp ra s0v s1v s2v s3v Qf E2 Hret E10 ltac:(lia)
               (efs_slots_ext MK mem sp ra s0v s1v s2v s3v (-8) ra ltac:(lia) ltac:(lia) AGR ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 8))
               (efs_slots_ext MK mem sp ra s0v s1v s2v s3v (-16) s0v ltac:(lia) ltac:(lia) AGR ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 8))
               (efs_slots_ext MK mem sp ra s0v s1v s2v s3v (-24) s1v ltac:(lia) ltac:(lia) AGR ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 8))
               (efs_slots_ext MK mem sp ra s0v s1v s2v s3v (-32) s2v ltac:(lia) ltac:(lia) AGR ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 8))
               (efs_slots_ext MK mem sp ra s0v s1v s2v s3v (-40) s3v ltac:(lia) ltac:(lia) AGR ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 8))
               HDf48 HALT4 LC4 AWF MI4).
      intros r mdl5 SB5 MI5 POST.
      exact (CONT0K r' r mdlm mdl5 SBm MIm (same_but_materialized_trans _ _ _ SB4 SB5) MI5 AG POST).
  Qed.
End EFSARMH.
End FPGenYH.
End AsAllocM8yh.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8Lcq.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module AsAllocM8yhq.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import Stdlib.Logic.FunctionalExtensionality.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.DivergeSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.SpinAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes.AgentNodes OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocSim OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys6.MhKSys OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsK OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys6.AsKSys OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsRtK OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtUnwind OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoison OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoisonI OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMMemA.AsAllocMI OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM9b.AsAllocM8m OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8k OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8e OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMRunS2.AsAllocM8r OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8s OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8u.AsAllocM8t OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8u OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMRunS2.AsAllocM8w OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMRunS2.AsAllocM8x.
Import AsAllocM8kh AsAllocM8rh OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMRunS2.AsAllocM8y.
Import AsAllocM8yh OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8Lcq.AsAllocM8uq.
Import OSSVerify.glaze.binary_reflection.images.Asan.
Import ListNotations.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Ltac wm_clear_disj_or T := lazymatch T with | _ \/ _ => idtac | ?A /\ ?B => first [wm_clear_disj_or A | wm_clear_disj_or B] | ?A <-> ?B => first [wm_clear_disj_or A | wm_clear_disj_or B] | ?A -> ?B => first [wm_clear_disj_or A | wm_clear_disj_or B] end.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AmLia.   (* [comment removed for export] *)
Ltac wm_clear_disj := am_wm_clear_disj.   (* [comment removed for export] *)
Ltac wm_lia0 := tryif noncert_goal_has_var then (Zify.zify; xlia zchecker)
                else first [ solve [noncert_clear_all; Zify.zify; xlia zchecker] | Zify.zify; xlia zchecker ].
#[local] Ltac lia ::= first [ solve [wm_clear_disj; wm_lia0] | wm_lia0 ].
Open Scope bv_scope.
Local Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation ASEGS := Asan.M.loaded_segments.
#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).
#[local] Abbreviation U := bv_unsigned.

Section FPGenYH.
Context {fx : FPState}.

Section EFSARMH.
  Variable Hd : word -> bool.
  Hypothesis HOFFSEG : H_off_segments ASEGS Hd.
  Hypothesis WX : wx_segs_nowrap ASEGS.
  (* [comment removed for export] *)
  Variable Hd2 : word -> bool.
  Hypothesis HOFFSEG2 : H_off_segments ASEGS Hd2.
  Variable A2 : list (Z * Z).
  Hypothesis AWF2 : A_wf A2.
  Variables (A : list (Z * Z)) (regs : bvmap 5 word) (mem rom : word -> option byte) (model : Model)
            (sp ra s0v s1v s2v s3v s4v s5v thr tp gp tsdp ctxw v72 v80 midend : word) (cpm : byte)
            (RIz rbeg tot mfa PGP CF T thr0 : Z) (Qok Qf : config -> Prop) (MOK MKP : Model -> Model).
  #[local] Abbreviation slot := (rbeg + 0xE0000000 + mfa).
  #[local] Abbreviation SH := ((rbeg + 0xE0000000 + mfa) / 8 + 0x7fff8000).
  #[local] Abbreviation M0 := (efs_m0 mem sp ra s0v s1v s2v s3v).
  #[local] Abbreviation M1 := (mfi_m1 M0 (at_ sp (-48)) (Z_to_bv 64 0x4eb38) (Z_to_bv 64 (mfa + 2 ^ 18)) (Z_to_bv 64 slot) (Z_to_bv 64 (2 ^ 18)) (Z_to_bv 64 RIz)
                     s4v s5v (Z_to_bv 64 slot) (Z_to_bv 64 (2 ^ 18)) (Z_to_bv 64 0x19801) PGP).
  #[local] Abbreviation ENOMEMw := (Z_to_bv 64 (2 ^ 64 - 12) : word).
  #[local] Abbreviation SCR := (word_to_le_bytes 4 (Z_to_bv 64 0xffffffffaaaaaaaa)).
  #[local] Abbreviation MR := (efs_mr mem sp ra s0v s1v s2v s3v s4v s5v RIz slot mfa PGP).
  (* [comment removed for export] *)
  Hypothesis H1 : getr regs 1 = ra.
  Hypothesis H2 : getr regs 2 = sp.
  Hypothesis H4 : getr regs 4 = tp.
  Hypothesis H3 : getr regs 3 = gp.
  Hypothesis H10 : getr regs 10 = Z_to_bv 64 0x103f18.
  Hypothesis H11 : getr regs 11 = Z_to_bv 64 RIz.
  Hypothesis H12 : getr regs 12 = Z_to_bv 64 rbeg.
  Hypothesis H13 : getr regs 13 = Z_to_bv 64 tot.
  Hypothesis H8 : getr regs 8 = s0v.
  Hypothesis H9 : getr regs 9 = s1v.
  Hypothesis H18 : getr regs 18 = s2v.
  Hypothesis H19 : getr regs 19 = s3v.
  Hypothesis H20 : getr regs 20 = s4v.
  Hypothesis H21 : getr regs 21 = s5v.
  Hypothesis Hsp : 2 ^ 32 + 4096 <= U sp /\ U sp + 16 <= 2 ^ 47.
  Hypothesis Hret : ret_ok ra.
  Hypothesis Htot : 0 <= tot /\ 4 * tot <= 2 ^ 29.
  Hypothesis Hmfa : 0 <= mfa <= 2 ^ 29 /\ mfa mod 2 ^ 18 = 0.
  Hypothesis Hneed : mfa < 4 * tot <= mfa + 2 ^ 18.
  Hypothesis Hroom : mfa + 2 ^ 18 <= 2 ^ 29.
  Hypothesis Hrbeg : AIMGHI <= rbeg /\ rbeg + 2 ^ 32 < 2 ^ 63 /\ rbeg mod 4096 = 0.
  Hypothesis HRI : AIMGHI <= RIz /\ RIz + 128 <= U sp - 448.
  Hypothesis HPGP : AIMGLO <= PGP /\ PGP + 8 <= AIMGHI.
  Hypothesis HCF : AIMGLO <= CF /\ CF + 264 <= AIMGHI.
  Hypothesis Hstk : store_ok ASEGS mem (at_ sp (-448)) 448 = true.
  Hypothesis R_mfa : rdn ASEGS mem (Z_to_bv 64 (RIz + 24)) 8 = Some (LE8 (Z_to_bv 64 mfa)).
  Hypothesis C_pre : rdn ASEGS mem (Z_to_bv 64 (0x103f18 + 56)) 1 = Some [Z_to_bv 8 0].
  Hypothesis Rgpg : rdn ASEGS mem (Z_to_bv 64 0xff250) 8 = Some (LE8 (Z_to_bv 64 PGP)).
  Hypothesis Rpg : rdn ASEGS mem (Z_to_bv 64 PGP) 8 = Some (LE8 (Z_to_bv 64 4096)).
  Hypothesis Rgcf : rdn ASEGS mem (Z_to_bv 64 0xff260) 8 = Some (LE8 (Z_to_bv 64 CF)).
  Hypothesis Rdpm : rdn ASEGS mem (Z_to_bv 64 (CF + 260)) 1 = Some [Z_to_bv 8 0].
  Hypothesis Rlim : rdn ASEGS mem (Z_to_bv 64 (CF + 144)) 8 = Some (LE8 (Z_to_bv 64 0)).
  Hypothesis Hslot : slot + 2 ^ 18 <= U sp - 448 \/ U sp <= slot.
  Hypothesis HDmfa : hid_off Hd (RIz + 24) 8.
  Hypothesis HDpre : hid_off Hd (0x103f18 + 56) 1.
  Hypothesis HDgpg : hid_off Hd 0xff250 8.
  Hypothesis HDpg : hid_off Hd PGP 8.
  Hypothesis HDgcf : hid_off Hd 0xff260 8.
  Hypothesis HDdpm : hid_off Hd (CF + 260) 1.
  Hypothesis HDlim : hid_off Hd (CF + 144) 8.
  Hypothesis HDscr : hid_off Hd (U sp - 448) 448.
  Hypothesis HALT : m_halted model = None.
  Hypothesis LC : lazy_cover Hd (m_vm_lazy model) A.
  Hypothesis AWF : A_wf A.
  Hypothesis MI : MInv A model.
  Hypothesis NODE : forall mdlm (r1 : bvmap 5 word), same_but_materialized model mdlm -> MInv A mdlm -> m_halted mdlm = None ->
        getr r1 10 = Z_to_bv 64 slot -> getr r1 11 = Z_to_bv 64 (2 ^ 18) -> getr r1 12 = Z_to_bv 64 3 -> getr r1 13 = Z_to_bv 64 50 ->
        getr r1 14 = Z_to_bv 64 (2 ^ 64 - 1) -> getr r1 15 = Z_to_bv 64 0 ->
        forall Qok' Qf' : config -> Prop,
          katwD ASEGS (mkCfg (mkst (regupd r1 10 (Z_to_bv 64 slot)) (0x80740 : word) (zfill (Z_to_bv 64 slot) (Z_to_bv 64 (2 ^ 18)) M1) rom) (MOK mdlm)) Qok' Qf' ->
          katsD ASEGS (mkCfg (epend r1 (0x8073c : word) M1 rom (Z_to_bv 64 222)) mdlm) Qok' Qf'.
  Hypothesis CHILD : forall mdlm, same_but_materialized model mdlm -> MInv A mdlm ->
        (m_halted (MOK mdlm) = None /\ lazy_cover Hd (m_vm_lazy (MOK mdlm)) A /\ MInv A (MOK mdlm))
        /\ (m_halted (MKP mdlm) = None /\ lazy_cover Hd (m_vm_lazy (MKP mdlm)) A /\ MInv A (MKP mdlm)).
  Hypothesis OKSW : forall mdlm mdl4, same_but_materialized model mdlm -> MInv A mdlm -> same_but_materialized (MOK mdlm) mdl4 -> MInv A mdl4 ->
        lazy_cover Hd2 (m_vm_lazy mdl4) A2 /\ MInv A2 mdl4.
  (* [comment removed for export] *)
  Hypothesis HT : U thr = T /\ 4096 <= T /\ T + 4096 <= U sp - 448 /\ T mod 8 = 0.
  Hypothesis HTRI : T + 4096 <= RIz \/ RIz + 128 <= T.
  Hypothesis HTSH : T + 4096 <= SH \/ SH + 2 ^ 15 <= T.
  Hypothesis HRSH : RIz + 128 <= SH \/ SH + 2 ^ 15 <= RIz.
  Hypothesis HSSH : U sp <= SH \/ SH + 2 ^ 15 <= U sp - 448.
  Hypothesis HTsl : T + 4096 <= slot \/ slot + 2 ^ 18 <= T.
  Hypothesis PH : poisonH ASEGS asan_poison_tab mem (Z_to_bv 64 slot) (Z_to_bv 64 (2 ^ 18)) (Z_to_bv 64 250) (Z_to_bv 64 0x4eb54) (at_ sp (-48)) cpm midend thr0.
  Hypothesis PCB : Forall (fun c => c + 8 <= AIMGHI) (poison_cells asan_poison_tab).
  Hypothesis GH : gctH ASEGS asan_gct_tab mem (at_ (at_ sp (-48)) (-16)) tp tsdp ctxw thr.
  Hypothesis GB : U (gt_tsd asan_gct_tab) + 8 <= U sp - 448 /\ U tp - 80 <= U sp - 448 /\ U tsdp + 8 <= U sp - 448 /\ U ctxw + 160 <= U sp - 448.
  Hypothesis GS : (U (gt_tsd asan_gct_tab) + 8 <= slot \/ slot + 2 ^ 18 <= U (gt_tsd asan_gct_tab)) /\ (U tp - 80 <= slot \/ slot + 2 ^ 18 <= U tp - 88)
                  /\ (U tsdp + 8 <= slot \/ slot + 2 ^ 18 <= U tsdp) /\ (U ctxw + 160 <= slot \/ slot + 2 ^ 18 <= U ctxw + 152).
  Hypothesis G1 : U (gt_tsd asan_gct_tab) + 8 <= SH \/ SH + 2 ^ 15 <= U (gt_tsd asan_gct_tab).
  Hypothesis G2 : U tp - 80 <= SH \/ SH + 2 ^ 15 <= U tp - 88.
  Hypothesis G3 : U tsdp + 8 <= SH \/ SH + 2 ^ 15 <= U tsdp.
  Hypothesis G4 : U ctxw + 160 <= SH \/ SH + 2 ^ 15 <= U ctxw + 152.
  Hypothesis R72 : rdn ASEGS mem (at_ thr 2872) 8 = Some (LE8 v72).
  Hypothesis R80 : rdn ASEGS mem (at_ thr 2880) 8 = Some (LE8 v80).
  Hypothesis SOKT : store_ok ASEGS mem thr 4096 = true.
  Hypothesis SOKRI : store_ok ASEGS mem (Z_to_bv 64 RIz) 128 = true.
  Hypothesis HDc : Forall (fun c => hid_off Hd2 c 8) (poison_cells asan_poison_tab).
  Hypothesis HDsh : hid_off Hd2 SH (2 ^ 15).
  Hypothesis HD1 : hid_off Hd2 (U (gt_tsd asan_gct_tab)) 8.
  Hypothesis HD2 : hid_off Hd2 (U tp - 88) 8.
  Hypothesis HD3 : hid_off Hd2 (U tsdp) 8.
  Hypothesis HD4 : hid_off Hd2 (U ctxw + 152) 8.
  Hypothesis HDT : hid_off Hd2 T 4096.
  Hypothesis HDRI : hid_off Hd2 RIz 128.
  Hypothesis HDscr2 : hid_off Hd2 (U sp - 448) 448.
  (* [comment removed for export] *)
  Hypothesis CONT1 : forall (r : bvmap 5 word) mdlm mdl5,
      same_but_materialized model mdlm -> MInv A mdlm -> same_but_materialized (MOK mdlm) mdl5 -> MInv A2 mdl5 ->
      getr r 10 = Z_to_bv 64 1 -> getr r 2 = sp -> getr r 1 = ra ->
      getr r 8 = s0v -> getr r 9 = s1v -> getr r 18 = s2v -> getr r 19 = s3v -> getr r 20 = s4v -> getr r 21 = s5v -> getr r 4 = tp -> getr r 3 = gp ->
      (forall i : reg, In i [22%bv; 23%bv; 24%bv; 25%bv; 26%bv; 27%bv] -> getr r i = getr regs i) ->
      katwD ASEGS (mkCfg (mkst r ra (eam_3 MR sp s4v s5v thr v72 v80 RIz slot mfa) rom) mdl5) Qok Qf.
  Hypothesis CONT0K : forall (r' r : bvmap 5 word) mdlm mdl5,
      same_but_materialized model mdlm -> MInv A mdlm -> same_but_materialized (MKP mdlm) mdl5 -> MInv A mdl5 ->
      regs_agree (fun i : reg => In i efs_clob) regs r' -> efs_post sp ra s0v s1v s2v s3v 0 r' r ->
      katD ASEGS (mkCfg (mkst r ra (wbytes (wbytes M1 (at_ sp (-132)) SCR) (at_ sp (-132)) (word_to_le_bytes 4 (Z_to_bv 64 12))) rom) mdl5) Qf.


  Theorem efs_map_arm_katwD_h_x : katwD ASEGS (mkCfg (mkst regs (0x4ea98 : word) mem rom) model) Qok Qf.
  Proof using CONT0K CONT1 HDscr2 HDRI HDT HD4 HD3 HD2 HD1 HDsh HDc SOKRI SOKT R80 R72 G4 G3 G2 G1 GS GB GH PCB PH HTsl HSSH HRSH HTSH HTRI HT OKSW CHILD NODE MI AWF LC HALT HDscr HDlim HDdpm HDgcf HDpg HDgpg HDpre HDmfa Hslot Rlim Rdpm Rgcf Rpg Rgpg C_pre R_mfa Hstk HCF HPGP HRI Hrbeg Hroom Hneed Hmfa Htot Hret Hsp H21 H20 H19 H18 H9 H8 H13 H12 H11 H10 H3 H4 H2 H1 MKP MOK thr0 T CF PGP mfa tot rbeg RIz cpm midend v80 v72 ctxw tsdp gp tp thr s5v s4v s3v s2v s1v s0v ra sp A AWF2 A2 HOFFSEG2 Hd2 WX HOFFSEG Hd.
    pose proof (u64_range sp) as Hspr. destruct Hsp as [SP1 SP2]. destruct HRI as [RI1 RI2]. destruct Hrbeg as (RB1 & RB2 & RB3).
    destruct Hmfa as [[MF1 MF2] MF3]. destruct HT as (UT & T1 & T2 & T3). pose proof (u64_range thr) as Hthr.
    assert (SL : 0 <= slot /\ slot + 2 ^ 18 < 2 ^ 63) by lia.
    assert (HDf48 : hid_off Hd (U sp - 48) 48) by (eapply hid_off_sub; [exact HDscr | lia | lia]).
    assert (HDf112 : hid_off Hd2 (U sp - 112) 112) by (eapply hid_off_sub; [exact HDscr2 | lia | lia]).
    assert (FRAMES : forall mdlx mdly, m_halted mdlx = None -> lazy_cover Hd (m_vm_lazy mdlx) A -> same_but_materialized mdlx mdly ->
               m_halted mdly = None /\ lazy_cover Hd (m_vm_lazy mdly) A).
    { intros mdlx mdly HX LX SB. pose proof (same_but_materialized_frame mdlx mdly SB) as FR. split.
      - destruct FR as (_&_&_&_&_&_&_&_&_&_&_&_&Hh&_). rewrite Hh. exact HX.
      - destruct FR as (_ & _ & Hl & _). rewrite Hl. exact LX. }
    apply katsD_katwD.
    apply (efs_famap_katsD_h Hd HOFFSEG WX A regs mem rom model sp ra s0v s1v s2v s3v s4v s5v RIz rbeg tot mfa PGP CF Qok Qf MOK MKP
             H1 H2 H10 H11 H12 H13 H8 H9 H18 H19 H20 H21 ltac:(lia) Htot (conj (conj MF1 MF2) MF3) Hneed Hroom (conj RB1 (conj RB2 RB3)) (conj RI1 RI2) HPGP HCF Hstk
             R_mfa C_pre Rgpg Rpg Rgcf Rdpm Rlim Hslot HDmfa HDpre HDgpg HDpg HDgcf HDdpm HDlim HDscr HALT LC AWF MI NODE CHILD).
    - (* [comment removed for export] *)
      intros r' mdlm mdl4 SBm MIm SB4 MI4 (E2 & E8 & E9 & E18 & E19 & E10 & E20) AG.
      destruct (CHILD mdlm SBm MIm) as ((HOK & LOK & _) & _).
      destruct (FRAMES _ _ HOK LOK SB4) as [HALT4 LC4].
      destruct (OKSW mdlm mdl4 SBm MIm SB4 MI4) as [LC2 MI2].
      assert (OUT : forall x : word, (U x < U sp - 448 \/ U sp <= U x) -> (U x < slot \/ slot + 2 ^ 18 <= U x) -> MR x = mem x)
        by (intros x X1 X2; apply efs_mr_outside; [lia | exact SL | exact X1 | exact X2]).
      assert (GR : mem_grows mem MR) by apply efs_mr_grows.
      change (wbytes (zfill (Z_to_bv 64 slot) (Z_to_bv 64 (2 ^ 18)) M1) (at_ sp (-132)) SCR) with MR.
      apply (efs_after_map_katwD_x Hd2 HOFFSEG2 WX A2 r' MR rom mdl4 sp ra s0v s1v s2v s3v s4v s5v thr tp gp tsdp ctxw v72 v80 midend cpm RIz slot mfa T thr0 Qok Qf
               E2 ltac:(rewrite (AG 4%bv) by ((lazymatch goal with |- ?G => let G' := eval unfold efs_clob in G in change_no_check G' end); (lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); intros X; repeat (destruct X as [X|X]; [discriminate X|]); exact X); exact H4)
               ltac:(rewrite (AG 3%bv) by ((lazymatch goal with |- ?G => let G' := eval unfold efs_clob in G in change_no_check G' end); (lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); intros X; repeat (destruct X as [X|X]; [discriminate X|]); exact X); exact H3)
               E8 E9 E10 E18 E19 E20
               ltac:(rewrite (AG 21%bv) by ((lazymatch goal with |- ?G => let G' := eval unfold efs_clob in G in change_no_check G' end); (lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); intros X; repeat (destruct X as [X|X]; [discriminate X|]); exact X); exact H21)
               (conj SP1 SP2) Hret ltac:(lia) (conj MF1 MF2) ltac:(lia) ltac:(lia) HTRI HTSH HRSH ltac:(clear - HSSH; lia)).
      + (* [comment removed for export] *)
        apply (poisonH_keep_P ASEGS asan_poison_tab mem MR _ _ _ _ _ cpm midend thr0
                 (fun z => (z < U sp - 448 \/ U sp <= z) /\ (z < slot \/ slot + 2 ^ 18 <= z)) PH); [intros x [X1 X2]; apply OUT; assumption | exact GR |].
        eapply Forall_impl; [|exact PCB]. cbv beta. intros c Hc z Hz. lia.
      + (* [comment removed for export] *)
        destruct GB as (B1 & B2 & B3 & B4). destruct GS as (S1 & S2 & S3 & S4).
        apply (gctH_keep_P ASEGS asan_gct_tab mem MR _ tp tsdp ctxw thr
                 (fun z => (z < U sp - 448 \/ U sp <= z) /\ (z < slot \/ slot + 2 ^ 18 <= z)) GH); [intros x [X1 X2]; apply OUT; assumption | exact GR
                 | intros z Hz; cbv beta; clear - Hz B1 S1; lia | intros z Hz; cbv beta; clear - Hz B2 S2; lia
                 | intros z Hz; cbv beta; clear - Hz B3 S3; lia | intros z Hz; cbv beta; clear - Hz B4 S4; lia].
      + destruct GB as (B1 & B2 & B3 & B4). lia.
      + exact G1.
      + exact G2.
      + exact G3.
      + exact G4.
      + rewrite <- R72. apply rdn_ext; [first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ]|]. intros x Hx. rewrite at_u in Hx by lia. cbn in Hx. apply OUT; clear - Hx UT T2 HTsl; lia.
      + rewrite <- R80. apply rdn_ext; [first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ]|]. intros x Hx. rewrite at_u in Hx by lia. cbn in Hx. apply OUT; clear - Hx UT T2 HTsl; lia.
      + eapply store_ok_mono; [exact GR | exact SOKT].
      + eapply store_ok_mono; [exact GR | exact SOKRI].
      + apply (efs_mr_slots mem sp ra s0v s1v s2v s3v s4v s5v RIz slot mfa PGP ltac:(lia) SL (-8) ra Hslot); (lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 8.
      + apply (efs_mr_slots mem sp ra s0v s1v s2v s3v s4v s5v RIz slot mfa PGP ltac:(lia) SL (-16) s0v Hslot); (lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 8.
      + apply (efs_mr_slots mem sp ra s0v s1v s2v s3v s4v s5v RIz slot mfa PGP ltac:(lia) SL (-24) s1v Hslot); (lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 8.
      + apply (efs_mr_slots mem sp ra s0v s1v s2v s3v s4v s5v RIz slot mfa PGP ltac:(lia) SL (-32) s2v Hslot); (lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 8.
      + apply (efs_mr_slots mem sp ra s0v s1v s2v s3v s4v s5v RIz slot mfa PGP ltac:(lia) SL (-40) s3v Hslot); (lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 8.
      + exact HDc.
      + exact HDf112.
      + exact HDsh.
      + exact HD1.
      + exact HD2.
      + exact HD3.
      + exact HD4.
      + exact HDT.
      + exact HDRI.
      + exact HALT4.
      + exact LC2.
      + exact AWF2.
      + exact MI2.
      + intros r mdl5 SB5 MI5 C10 C2 C1 C8 C9 C18 C19 C20 C21 C4 C3 CX.
        refine (CONT1 r mdlm mdl5 SBm MIm (same_but_materialized_trans _ _ _ SB4 SB5) MI5 C10 C2 C1 C8 C9 C18 C19 C20 C21 C4 C3 _).
        intros i Hi. rewrite (CX i Hi). apply AG. (lazymatch goal with |- ?G => let G' := eval unfold efs_clob in G in change_no_check G' end). cbn [In] in Hi |- *.
        repeat (destruct Hi as [<-|Hi]; [intros X; repeat (destruct X as [X|X]; [discriminate X|]); exact X|]). destruct Hi.
    - (* [comment removed for export] *)
      intros r' mdlm mdl4 SBm MIm SB4 MI4 (E2 & E8 & E9 & E18 & E19 & E10 & E20) AG.
      destruct (CHILD mdlm SBm MIm) as (_ & (HKP & LKP & _)).
      destruct (FRAMES _ _ HKP LKP SB4) as [HALT4 LC4].
      set (MK := wbytes (wbytes M1 (at_ sp (-132)) SCR) (at_ sp (-132)) (word_to_le_bytes 4 (Z_to_bv 64 12))).
      assert (AGR : forall x : word, U sp - 48 <= U x < U sp -> MK x = M0 x).
      { intros x Hx. (lazymatch goal with |- ?G => let G' := eval unfold MK in G in change_no_check G' end).
        repeat (rewrite MemsetLibF.MemSplit.wbytes_outside; [ | rewrite length_N_to_le_bytes, at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite length_N_to_le_bytes, at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia]).
        apply mfi_m1_outside; first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite ?at_u by lia; lia ]. }
      apply (efs_fail_katD Hd HOFFSEG WX A r' MK rom mdl4 sp ra s0v s1v s2v s3v Qf E2 Hret E10 ltac:(lia)
               (efs_slots_ext MK mem sp ra s0v s1v s2v s3v (-8) ra ltac:(lia) ltac:(lia) AGR ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 8))
               (efs_slots_ext MK mem sp ra s0v s1v s2v s3v (-16) s0v ltac:(lia) ltac:(lia) AGR ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 8))
               (efs_slots_ext MK mem sp ra s0v s1v s2v s3v (-24) s1v ltac:(lia) ltac:(lia) AGR ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 8))
               (efs_slots_ext MK mem sp ra s0v s1v s2v s3v (-32) s2v ltac:(lia) ltac:(lia) AGR ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 8))
               (efs_slots_ext MK mem sp ra s0v s1v s2v s3v (-40) s3v ltac:(lia) ltac:(lia) AGR ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 8))
               HDf48 HALT4 LC4 AWF MI4).
      intros r mdl5 SB5 MI5 POST.
      exact (CONT0K r' r mdlm mdl5 SBm MIm (same_but_materialized_trans _ _ _ SB4 SB5) MI5 AG POST).
  Qed.
End EFSARMH.
End FPGenYH.
End AsAllocM8yhq.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap Mprotect.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocSim. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.MemSplit OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4.AgentLib OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocSim.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys6 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.BackingAlgebra. Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsK OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys6.AsKSys OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys6.AsKSys2 OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsRtK OSSVerify.Proofs.glaze.binary_reflection.lib.Common.BackingAlgebra OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys6.AsanNodesLibE.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFree3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsP3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsP23 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsP33 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvHoleU3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvHoleP3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsRc73. Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinv3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinvGeom3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOps3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOpsPf3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d.AsAinvOpsPf3c OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d.AsAinvFreeS OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFree3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsP3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsP23 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsP33 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvHole3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvHoleU3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvHoleP3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsRc73.AsAinvRepX3.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFHyp OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtUnwind OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoison OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoisonI OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8Lc OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM9b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8k OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8e OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM9c OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMRunS2 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8s OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8u. Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFHyp OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtUnwind OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoison OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoisonI OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8Lc.AsAllocMHyp OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM9b.AsAllocM8m OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8k OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8e.AsAllocM8p OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM9c.AsAllocM8q OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8e OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMRunS2.AsAllocM8r OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8s OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8u.AsAllocM8t OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8u OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8Lc.AsAllocM8v OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMRunS2.AsAllocM8w OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMRunS2.AsAllocM8x OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMRunS2.AsAllocM8y OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8Lc.AsAllocM8z OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8Lc.AsAllocM8pa OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8Lc.AsAllocM8La OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8Lc.AsAllocM8Lk.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys7b OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys10 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8Lc. Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys7b OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys10.AsKSys7c AsAllocM8kh AsAllocM8rh AsAllocM8yh OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8Lc.
From OSSVerify.glaze.binary_reflection.images Require Import Asan.
Import ListNotations.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Import AmLia.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac wm_clear_disj_or T := lazymatch T with | _ \/ _ => idtac | ?A /\ ?B => first [wm_clear_disj_or A | wm_clear_disj_or B] | ?A <-> ?B => first [wm_clear_disj_or A | wm_clear_disj_or B] | ?A -> ?B => first [wm_clear_disj_or A | wm_clear_disj_or B] end.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AmLia.   (* [comment removed for export] *)
Ltac wm_clear_disj := am_wm_clear_disj.   (* [comment removed for export] *)
Ltac wm_lia0 := tryif noncert_goal_has_var then (Zify.zify; xlia zchecker)
                else first [ solve [noncert_clear_all; Zify.zify; xlia zchecker] | Zify.zify; xlia zchecker ].
#[local] Ltac am_inner ::= first [ solve [wm_clear_disj; wm_lia0] | wm_lia0 ].
#[local] Ltac lia ::= am_lia.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation U := bv_unsigned.
#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).
#[local] Abbreviation LE4 z := (word_to_le_bytes 4 (Z_to_bv 64 z)).


Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).



Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section WithCeil.
Context {RC : run_ceil}.
Context {fx : FPState}.

Section L3h.
  Variable bt : as_boot.
  Hypothesis BT_segs : bt_segs bt = ASEGS.
  Hypothesis BT_ia : bt_ia bt = asan_addrs.
  Variables (TP TSDP PGP FL MIDEND : Z).
  Hypothesis CELLS : malloc_cells bt TP TSDP PGP FL MIDEND.
  Hypothesis PCELLS : pop_cells bt.
  Variable X : Z -> Prop.
  #[local] Abbreviation T := (bt_thread bt).
  #[local] Abbreviation CTX := (bt_tctx bt).
  #[local] Abbreviation SBEG := (bt_spacebeg bt).
  #[local] Abbreviation XL := (XL bt X).
  #[local] Abbreviation IA := (bt_ia bt).

  (* [comment removed for export] *)
  Hypothesis N3FH : AsKSys10.AsKSys7c.N3FH_stmt bt.

  Theorem popBf_katwD_h :
    forall (c : Z) st Lc FF (M : mem) (rom : mem) mdl (regs : bvmap 5 word) (sp ra s0v s1v s2v s3v s4v s5v tp gp : word) (tot : Z) (Qok Qf : config -> Prop),
    1 <= c <= 30 -> WF bt st Lc FF -> RepX bt (XL c) st Lc FF M mdl -> m_halted mdl = None -> BackingAlgebra.model_ivs_wf mdl ->
    r_fhole (a_reg st c) = true -> r_mapped_fa (a_reg st c) + KFAMAP <= 2 ^ 29 ->
    r_mapped_fa (a_reg st c) <= 4 * (r_mapped_user (a_reg st c) / csize c) -> a_kact st <= KCAP ->       (* [comment removed for export] *)
    let r := a_reg st c in let mfa := r_mapped_fa r in let lo := fa_beg SBEG c + mfa in
    (forall z, X z -> ~ (reginfo bt c <= z < reginfo bt c + 128) /\ ~ (AIMGLO <= z < AIMGHI) /\ ~ (CTX + 152 <= z < CTX + 160)
                      /\ ~ (lo <= z < lo + KFAMAP) /\ ~ (sh_lo lo <= z < sh_lo lo + KFAMAP / 8)) ->
    getr regs 1 = ra -> getr regs 2 = sp -> getr regs 4 = tp -> getr regs 3 = gp -> U tp = TP -> getr regs 10 = Z_to_bv 64 0x103f18 ->
    getr regs 11 = Z_to_bv 64 (reginfo bt c) -> getr regs 12 = Z_to_bv 64 (region_beg SBEG c) -> getr regs 13 = Z_to_bv 64 tot ->
    getr regs 8 = s0v -> getr regs 9 = s1v -> getr regs 18 = s2v -> getr regs 19 = s3v -> getr regs 20 = s4v -> getr regs 21 = s5v ->
    (CEIL + 448 <= U sp /\ U sp + 16 <= 2 ^ 47) -> ret_ok ra -> (0 <= tot /\ 4 * tot <= 2 ^ 29) -> (mfa < 4 * tot <= mfa + 2 ^ 18) ->
    writableZ ASEGS M (U sp - 448) (U sp) ->
    (* [comment removed for export] *)
    (forall (r' : bvmap 5 word) (M' : mem) mdl',
        let st' := add_meter (op_famap st c) 0 [(sh_lo lo, sh_lo lo + KFAMAP / 8)] 0 in
        WF bt st' Lc FF -> RepX bt (XL c) st' Lc FF M' mdl' ->
        same_except_vm mdl mdl' -> lazy_kept IA Lc FF mdl mdl' -> BackingAlgebra.model_ivs_wf mdl' -> m_halted mdl' = None ->
        (forall a : word, M' a <> M a ->
            ((U sp - 448 <= U a < U sp) \/ (lo <= U a < lo + KFAMAP) \/ (sh_lo lo <= U a < sh_lo lo + KFAMAP / 8)
             \/ (T + 2872 <= U a < T + 2888) \/ (reginfo bt c + 24 <= U a < reginfo bt c + 32)) /\ M' a <> None) ->
        getr r' 10 = Z_to_bv 64 1 -> getr r' 2 = sp -> getr r' 1 = ra ->
        getr r' 8 = s0v -> getr r' 9 = s1v -> getr r' 18 = s2v -> getr r' 19 = s3v -> getr r' 20 = s4v -> getr r' 21 = s5v -> getr r' 4 = tp -> getr r' 3 = gp ->
        katwD ASEGS (mkCfg (mkst r' ra M' rom) mdl') Qok Qf) ->
    (* [comment removed for export] *)
    (forall (r0 r' : bvmap 5 word) (M' : mem) mdl' st',
        (st' = st \/ st' = op_fhole st c) ->
        WF bt st' Lc FF -> RepX bt (XL c) st' Lc FF M' mdl' ->
        same_except_vm mdl mdl' -> lazy_kept IA Lc FF mdl mdl' -> BackingAlgebra.model_ivs_wf mdl' -> m_halted mdl' = None ->
        (forall a : word, M' a <> M a -> ((U sp - 448 <= U a < U sp) /\ M' a <> None) \/ (lo <= U a < lo + KFAMAP)) ->
        regs_agree (fun i : reg => In i efs_clob) regs r0 -> efs_post sp ra s0v s1v s2v s3v 0 r0 r' ->
        katD ASEGS (mkCfg (mkst r' ra M' rom) mdl') Qf) ->
    katwD ASEGS (mkCfg (mkst regs (0x4ea98%bv : word) M rom) mdl) Qok Qf.
  Proof using N3FH PCELLS CELLS MIDEND FL PGP TSDP BT_ia BT_segs.
    intros c st Lc FF M rom mdl regs sp ra s0v s1v s2v s3v s4v s5v tp gp tot Qok Qf Hc W RX HALT MW FH ROOM FAQ KC r mfa lo XOFF
           H1 H2 H4 H3 Etp H10 H11 H12 H13 H8 H9 H18 H19 H20 H21 Hsp Hret Htot Hneed WSTK CONT1 CONT0.
    pose proof ceil_rng as CR. destruct Hsp as [SP1 SP2]. pose proof (u64_range sp) as Hspr.
    pose proof RX as (M0 & RP & D).
    pose proof (region_facts bt st Lc FF W c Hc) as RF. cbn zeta in RF. fold r in RF.
    destruct RF as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11 & E12 & E13 & E14). fold mfa in E6, E7, E14.
    pose proof W as ((WR1 & _) & _). destruct (WR1 c Hc) as (_ & _ & _ & _ & Y5 & Y6 & _). fold r mfa in Y5, Y6.
    pose proof CELLS as (CELL_mcs & CELL_gcf & CELL_fum & CELL_inited & CELL_pg & CELL_P & CREST).
    assert (G_consts : 0x10000 <= TSDP /\ TSDP + 8 <= 0x65d000 /\ 0x10000 <= PGP /\ PGP + 8 <= 0x65d000 /\ 0x10000 + 88 <= TP /\ TP + 0x40 <= 0x65d000).
    { do 32 (destruct CREST as (_ & CREST)). destruct CREST as (A1 & A2 & A3 & A4 & _ & _ & _ & A8 & A9). repeat split; assumption. }
    destruct G_consts as (Gs1 & Gs2 & Gp1 & Gp2 & Gt1 & Gt2).
    pose proof PCELLS as (PC_rel & PC_rib & PC_pre & PC_dpm & PC_lim).
    set (RIz := reginfo bt c) in *. set (rbeg := region_beg SBEG c) in *.
    assert (ERI : RIz = SBEG + KSPACE + 128 * c) by reflexivity.
    assert (ERB : rbeg = SBEG + c * 2 ^ 32) by ((lazymatch goal with |- ?G => let G' := eval unfold rbeg, region_beg, KREGION in G in change_no_check G' end); reflexivity).
    assert (ELO : lo = rbeg + 0xE0000000 + mfa) by ((lazymatch goal with |- ?G => let G' := eval unfold lo, fa_beg, KFAOFF in G in change_no_check G' end); fold rbeg; reflexivity).
    assert (ESH : sh_lo lo = (rbeg + 0xE0000000 + mfa) / 8 + 0x7fff8000) by (rewrite ELO; (lazymatch goal with |- ?G => let G' := eval unfold sh_lo, SB in G in change_no_check G' end); lia).
    (* [comment removed for export] *)
    pose proof RP as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10 & R11 & R12 & R13 & R14 & R15).
    destruct (R4 c Hc) as [(G0 & G8 & G16 & G24 & G32 & G40 & G48 & G56 & G68 & GW) (F1 & F2 & F3)]. fold r RIz mfa in G24, GW.
    rewrite BT_segs in *. destruct R14 as (Bw1 & Bw2 & _).
    (* [comment removed for export] *)
    pose proof (pk_thread_geom bt BT_ia st Lc FF W) as (T1 & T2 & C1 & C2 & T4k & TIMG & CIMG).
    pose proof (pk_thread_geom2 bt st Lc FF W) as (TBAND & CBAND & TSP & CSP & S1 & S2 & S3).
    unfold KSPACE, PG, KFAMAP, KFAOFF, AS_HEAPLO, AS_LO in *.
    assert (SLOT : SBEG <= lo /\ lo + 2 ^ 18 <= SBEG + 2 ^ 37 /\ lo mod 8 = 0).
    { split; [rewrite ELO, ERB; lia|]. split; [rewrite ELO; fold rbeg in E5; unfold fa_beg in E5; lia|].
      (lazymatch goal with |- ?G => let G' := eval unfold lo in G in change_no_check G' end). apply mod8_of_4096_sum; [exact E12 | exact E14]. }
    destruct SLOT as (SL0 & SL1 & SL8).
    assert (SLa : 17594333495296 <= lo) by lia.
    assert (SLb : lo + 2 ^ 18 <= CEIL) by lia.
    destruct (sh_band lo (2 ^ 18) SLa ltac:(lia) SLb ltac:(reflexivity)) as (SHB0 & SHB1 & SHB2).
    unfold AS_GAPHI, AS_HEAPLO in SHB0, SHB1. replace (2 ^ 18 / 8) with (2 ^ 15) in SHB1, SHB2 by reflexivity.
    set (SH := sh_lo lo) in *. assert (ESH' : SH = SB + lo / 8) by reflexivity. rewrite <- ESH' in SHB0, SHB1, SHB2.
    (* [comment removed for export] *)
    assert (YIMG : forall z, XL c z -> ~ (AIMGLO <= z < AIMGHI)).
    { intros z [Hx | Hl]; [exact (proj1 (proj2 (XOFF z Hx))) | fold RIz in Hl; lia]. }
    assert (YCTX : forall z, XL c z -> ~ (CTX + 152 <= z < CTX + 160)).
    { intros z [Hx | Hl]; [exact (proj1 (proj2 (proj2 (XOFF z Hx)))) | fold RIz in Hl; clear - Hl CSP ERI E9 E10 C1; lia]. }
    assert (XRI : forall i, RIz + 8 <= i < RIz + 128 -> ~ XL c i).
    { intros i Hi [Hx | Hl]; [exact (proj1 (XOFF i Hx) ltac:(fold RIz; lia)) | fold RIz in Hl; lia]. }
    assert (XSL : forall i, lo <= i < lo + 2 ^ 18 -> ~ XL c i).
    { intros i Hi [Hx | Hl]; [exact (proj1 (proj2 (proj2 (proj2 (XOFF i Hx)))) Hi) | fold RIz in Hl; lia]. }
    assert (XSH : forall i, SH <= i < SH + 2 ^ 15 -> ~ XL c i).
    { intros i Hi [Hx | Hl]; [apply (proj2 (proj2 (proj2 (proj2 (XOFF i Hx))))); fold SH; replace (2 ^ 18 / 8) with (2 ^ 15) by reflexivity; exact Hi | fold RIz in Hl; lia]. }
    (* [comment removed for export] *)
    destruct (N3FH st Lc FF M0 mdl c W RP Hc FH MW HALT KC) as (AWF2 & NODEF & BUD & LEDOK).
    cbv zeta in AWF2, NODEF, BUD, LEDOK. fold r mfa lo SH in AWF2, NODEF, BUD, LEDOK. unfold KUSERMAP, KFAMAP in AWF2, NODEF, BUD, LEDOK.
    set (addr := Z_to_bv 64 lo : word) in *. set (size := Z_to_bv 64 (2 ^ 18) : word) in *.
    set (A2 := a_aa st ++ [(SH, SH + 2 ^ 18 / 8)]) in *.
    set (OKm := OKh addr size) in *.
    (* [comment removed for export] *)
    set (Hd := HID st mdl). set (Hd2 := mkH (m_vm_lazy mdl) A2).
    assert (NHs : forall z, 0 <= z < 2 ^ 64 -> (CEIL <= z \/ AIMGLO <= z < AIMGHI) -> Hd (Z_to_bv 64 z) = false).
    { intros z Hz Hr. apply (HID_off_zone bt st mdl z R13 Hz). rewrite BT_ia. (lazymatch goal with |- ?G => let G' := eval cbn [ia_img_lo ia_img_hi asan_addrs] in G in change_no_check G' end). clear - Hr. lia. }
    assert (NHri : forall z, RIz <= z < RIz + 128 -> Hd (Z_to_bv 64 z) = false).
    { intros z Hz. apply HID_notlazy; [lia|]. apply (rep_nolazy_reginfo bt st Lc FF M0 mdl W RP). (lazymatch goal with |- ?G => let G' := eval unfold KSPACE, PG in G in change_no_check G' end). lia. }
    assert (NH2s : forall z, 0 <= z < 2 ^ 64 -> (CEIL <= z \/ AIMGLO <= z < AIMGHI) -> Hd2 (Z_to_bv 64 z) = false).
    { intros z Hz Hr. exact (mkH_off_zone bt BT_ia st mdl A2 z R13 Hz Hr). }
    assert (NH2ri : forall z, RIz <= z < RIz + 128 -> Hd2 (Z_to_bv 64 z) = false).
    { intros z Hz. apply mkH_notlazy; [lia|]. apply (rep_nolazy_reginfo bt st Lc FF M0 mdl W RP). (lazymatch goal with |- ?G => let G' := eval unfold KSPACE, PG in G in change_no_check G' end). lia. }
    assert (NH2rt : forall z, (T <= z < T + 4096) \/ (CTX <= z < CTX + 0x10000) -> Hd2 (Z_to_bv 64 z) = false).
    { intros z Hz. apply mkH_notlazy; [clear - Hz T1 T2 C1 C2 CR; lia|]. exact (pk_nolazy_rt bt st Lc FF M0 mdl W RP z Hz). }
    assert (NH2sh : forall z, SH <= z < SH + 2 ^ 15 -> Hd2 (Z_to_bv 64 z) = false).
    { intros z Hz. apply mkH_allowed. (lazymatch goal with |- ?G => let G' := eval unfold A2 in G in change_no_check G' end). apply (range_allowed_last (a_aa st) SH (SH + 2 ^ 18 / 8)); [ | | lia | replace (2 ^ 18 / 8) with (2 ^ 15) by reflexivity; lia | replace (2 ^ 18 / 8) with (2 ^ 15) by reflexivity; exact Hz].
      - pose proof AWF2 as AW. unfold A2, A_wf in AW. apply Forall_app in AW as [_ AW]. apply Forall_cons_iff in AW as [(_ & AW1 & _) _]. cbn [fst] in AW1. (lazymatch goal with |- ?G => let G' := eval unfold PG in G in change_no_check G' end). exact AW1.
      - pose proof AWF2 as AW. unfold A2, A_wf in AW. apply Forall_app in AW as [_ AW]. apply Forall_cons_iff in AW as [(_ & _ & AW2) _]. cbn [snd] in AW2. (lazymatch goal with |- ?G => let G' := eval unfold PG in G in change_no_check G' end). exact AW2. }
    assert (HOFF : forall (H : word -> bool) lo0 n, (forall z, lo0 <= z < lo0 + n -> H (Z_to_bv 64 z) = false) -> hid_off H lo0 n).
    { intros H lo0 n Hz x Hx. rewrite <- (Z_to_bv_bv_unsigned _ x). apply Hz. exact Hx. }
    (* [comment removed for export] *)
    pose proof (pk_T_writable bt BT_segs BT_ia (XL c) st Lc FF M M0 mdl W RP D) as TWR.
    destruct (pk_junk8 M T (T + 4096) (T + 2872) TWR ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as (v72 & R72).
    destruct (pk_junk8 M T (T + 4096) (T + 2880) TWR ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as (v80 & R80).
    set (thr := Z_to_bv 64 T : word).
    assert (UT : U thr = T) by ((lazymatch goal with |- ?G => let G' := eval unfold thr in G in change_no_check G' end); rewrite u_Z2bv by lia; reflexivity).
    apply (efs_map_arm_katwD_h Hd (HID_off_segments bt st Lc FF M0 mdl BT_ia RP) asanF_segs_wx Hd2 (mkH_off_segments bt BT_ia st mdl A2 R13) A2 AWF2 (a_aa st)
             regs M rom mdl sp ra s0v s1v s2v s3v s4v s5v thr tp gp (Z_to_bv 64 TSDP) (Z_to_bv 64 CTX) v72 v80 (Z_to_bv 64 MIDEND) (Z_to_bv 8 1)
             RIz rbeg tot mfa PGP 0x1990a8 T 0 Qok Qf OKm (fun m => m)).
    all: try (first [exact H1 | exact H2 | exact H4 | exact H3 | exact H10 | exact H11 | exact H12 | exact H13 | exact H8 | exact H9 | exact H18 | exact H19 | exact H20 | exact H21
                    | exact Hret | exact Htot | exact HALT | exact Bw1 | exact Bw2 | exact Hneed]).
    - (* [comment removed for export] *) lia.
    - split; [lia | exact Y6].
    - exact ROOM.
    - split; [lia|]. split; [lia | exact E11].
    - lia.
    - lia.
    - lia.
    - apply (writableZ_sok M (U sp - 448) (U sp)); [exact WSTK | rewrite at_u by lia; lia | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | lia].
    - apply (repx_rd (XL c) M M0 D (RIz + 24) 8 _); [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | intros i Hi; apply XRI; cbn in Hi; lia | exact G24].
    - change (1064728 + 56) with 0x103f50. rewrite <- (w2b1 0) by lia. exact (pk_const bt BT_segs (XL c) st Lc FF M M0 mdl RP D YIMG _ _ _ PC_pre ltac:(lia) ltac:((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia)).
    - exact (pk_const bt BT_segs (XL c) st Lc FF M M0 mdl RP D YIMG _ _ _ CELL_pg ltac:(lia) ltac:((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia)).
    - exact (pk_const bt BT_segs (XL c) st Lc FF M M0 mdl RP D YIMG _ _ _ CELL_P ltac:(lia) ltac:((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia)).
    - exact (pk_const bt BT_segs (XL c) st Lc FF M M0 mdl RP D YIMG _ _ _ CELL_gcf ltac:(lia) ltac:((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia)).
    - change (1674984 + 260) with 0x1991ac. rewrite <- (w2b1 0) by lia. exact (pk_const bt BT_segs (XL c) st Lc FF M M0 mdl RP D YIMG _ _ _ PC_dpm ltac:(lia) ltac:((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia)).
    - change (1674984 + 144) with 0x199138. exact (pk_const bt BT_segs (XL c) st Lc FF M M0 mdl RP D YIMG _ _ _ PC_lim ltac:(lia) ltac:((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia)).
    - left. rewrite <- ELO. lia.
    - apply HOFF. intros z Hz. apply NHri. lia.
    - apply HOFF. intros z Hz. apply NHs; lia.
    - apply HOFF. intros z Hz. apply NHs; lia.
    - apply HOFF. intros z Hz. apply NHs; lia.
    - apply HOFF. intros z Hz. apply NHs; lia.
    - apply HOFF. intros z Hz. apply NHs; lia.
    - apply HOFF. intros z Hz. apply NHs; lia.
    - apply HOFF. intros z Hz. apply NHs; lia.
    - apply lazy_cover_HID.
    - (* [comment removed for export] *)
      intros mdlm r1 SBm MIm HLm G10 G11 G12 G13 G14 G15 Qok' Qf' K1.
      destruct (NODEF mdlm SBm MIm) as (N1 & N2 & N3 & N4 & _).
      apply (node1_of_fixfree2_s r1 _ rom mdlm addr size Qok' Qf' HLm G10 G11 G12 G13 G14 G15); [ | | | | exact N1 | exact N2 | exact N3 | | exact K1].
      + (lazymatch goal with |- ?G => let G' := eval unfold addr in G in change_no_check G' end). rewrite u_Z2bv by lia. (lazymatch goal with |- ?G => let G' := eval unfold lo in G in change_no_check G' end). apply mod4096_sum; [exact E12 | exact E14].
      + (lazymatch goal with |- ?G => let G' := eval unfold addr in G in change_no_check G' end). rewrite u_Z2bv by lia. lia.
      + (lazymatch goal with |- ?G => let G' := eval unfold size in G in change_no_check G' end). rewrite u_Z2bv by lia. lia.
      + (lazymatch goal with |- ?G => let G' := eval unfold size in G in change_no_check G' end). rewrite u_Z2bv by lia. reflexivity.
      + (lazymatch goal with |- ?G => let G' := eval unfold size in G in change_no_check G' end). rewrite u_Z2bv by lia. exact N4.
    - (* [comment removed for export] *)
      intros mdlm SBm MIm. destruct (NODEF mdlm SBm MIm) as (_ & _ & _ & _ & HOK & MOKI & LZOK).
      split.
      + split; [exact HOK|]. split; [| exact MOKI]. exact (lazy_cover_sub Hd _ _ _ (lazy_cover_HID st mdl) LZOK).
      + split; [exact (halted_sbm mdl mdlm SBm HALT)|]. split; [| exact MIm].
        pose proof (same_but_materialized_frame mdl mdlm SBm) as (_ & _ & EL & _). rewrite EL. apply lazy_cover_HID.
    - (* [comment removed for export] *)
      intros mdlm mdl4 SBm MIm SB4 MI4. split; [| exact (BUD mdlm mdl4 SBm SB4 MI4)].
      destruct (NODEF mdlm SBm MIm) as (_ & _ & _ & _ & _ & _ & LZOK).
      pose proof (same_but_materialized_frame _ _ SB4) as (_ & _ & EL & _). rewrite EL.
      exact (lazy_cover_sub Hd2 _ _ _ (lazy_cover_mkH (m_vm_lazy mdl) A2 (m_vm_lazy mdl) (incl_refl _)) LZOK).
    - destruct (pos_mod4096 T T1 T4k) as [T4 T8]. split; [exact UT|]. split; [exact T4|]. split; [lia | exact T8].
    - clear - TSP ERI E9 E10. lia.
    - rewrite <- ESH. clear - TBAND SHB0 SHB1. lia.
    - rewrite <- ESH. right. lia.
    - rewrite <- ESH. right. lia.
    - rewrite <- ELO. clear - TSP SL0 SL1. lia.
    - rewrite <- ELO.
      apply (pk_poisonH bt BT_segs BT_ia TP TSDP PGP FL MIDEND CELLS (XL c) st Lc FF M M0 mdl RP D YIMG lo (Z_to_bv 64 322388) (at_ sp (-48)));
        [(lazymatch goal with |- ?G => let G' := eval unfold AS_HEAPLO in G in change_no_check G' end); lia | lia | exact SL8 | rewrite at_u by lia; lia | rewrite at_u by lia; lia | | apply ret_ok_lit; [lia | reflexivity]].
      intros i Hi. rewrite at_u in Hi by lia. apply WSTK. lia.
    - eapply Forall_impl; [| exact asan_poison_cells_img]. cbv beta. intros c0 [_ Hc0]. exact Hc0.
    - apply (pk_gctH bt BT_segs BT_ia TP TSDP PGP FL MIDEND CELLS (XL c) st Lc FF M M0 mdl W RP D YIMG YCTX (at_ (at_ sp (-48)) (-16)) tp Etp);
        [rewrite !at_u by (rewrite ?at_u by lia; lia); lia | rewrite !at_u by (rewrite ?at_u by lia; lia); lia |].
      intros i Hi. rewrite !at_u in Hi by (rewrite ?at_u by lia; lia). apply WSTK. lia.
    - (lazymatch goal with |- ?G => let G' := eval cbn [gt_tsd asan_gct_tab] in G in change_no_check G' end). rewrite !u_Z2bv by lia. rewrite Etp. lia.
    - (lazymatch goal with |- ?G => let G' := eval cbn [gt_tsd asan_gct_tab] in G in change_no_check G' end). rewrite !u_Z2bv by lia. rewrite Etp. rewrite <- ELO.
      split; [left; lia|]. split; [left; lia|]. split; [left; lia|]. clear - CSP SL0 SL1. lia.
    - (lazymatch goal with |- ?G => let G' := eval cbn [gt_tsd asan_gct_tab] in G in change_no_check G' end). rewrite !u_Z2bv by lia. rewrite <- ESH. left. lia.
    - rewrite Etp. rewrite <- ESH. left. lia.
    - rewrite !u_Z2bv by lia. rewrite <- ESH. left. lia.
    - rewrite !u_Z2bv by lia. rewrite <- ESH. clear - CBAND SHB0 SHB1. lia.
    - replace (at_ thr 2872) with (Z_to_bv 64 (T + 2872)) by (apply bv_eq; rewrite at_u by lia; rewrite u_Z2bv by lia; lia). exact R72.
    - replace (at_ thr 2880) with (Z_to_bv 64 (T + 2880)) by (apply bv_eq; rewrite at_u by lia; rewrite u_Z2bv by lia; lia). exact R80.
    - apply (writableZ_sok M T (T + 4096)); [exact TWR | lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | lia].
    - apply (writableZ_sok M RIz (RIz + 128)); [apply (repx_wr (XL c) M M0 D); [lia | lia | exact GW] | rewrite u_Z2bv by lia; lia | rewrite u_Z2bv by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | lia].
    - (lazymatch goal with |- ?G => let G' := eval unfold poison_cells, asan_poison_tab in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [pt_g_shoff pt_p_shoff pt_g_midbeg pt_p_midbeg pt_g_midend pt_p_midend pt_g_hiend pt_p_hiend pt_g_rms pt_p_rms pt_g_cfl pt_p_cfl pt_c_cpm] in G in change_no_check G' end).
      repeat (constructor; [apply HOFF; intros z Hz; apply NH2s; lia|]). constructor.
    - rewrite <- ESH. apply HOFF. exact NH2sh.
    - (lazymatch goal with |- ?G => let G' := eval cbn [gt_tsd asan_gct_tab] in G in change_no_check G' end). rewrite u_Z2bv by lia. apply HOFF. intros z Hz. apply NH2s; lia.
    - rewrite Etp. apply HOFF. intros z Hz. apply NH2s; lia.
    - rewrite u_Z2bv by lia. apply HOFF. intros z Hz. apply NH2s; lia.
    - rewrite u_Z2bv by lia. apply HOFF. intros z Hz. apply NH2rt. right. lia.
    - apply HOFF. intros z Hz. apply NH2rt. left. lia.
    - apply HOFF. exact NH2ri.
    - apply HOFF. intros z Hz. apply NH2s; lia.
    - (* [comment removed for export] *)
      intros r' mdlm mdl5 SBm MIm SB5 MI5 Q10 Q2 Q1 Q8 Q9 Q18 Q19 Q20 Q21 Q4 Q3.
      rewrite <- ELO.
      destruct (LEDOK mdlm mdl5 SBm SB5) as (LED & SEV & LK & MW5 & HL5).
      set (MR := efs_mr M sp ra s0v s1v s2v s3v s4v s5v RIz lo mfa PGP).
      set (M' := eam_3 MR sp s4v s5v thr v72 v80 RIz lo mfa).
      assert (ESH2 : SH = lo / 8 + 2147450880) by (rewrite ESH'; (lazymatch goal with |- ?G => let G' := eval unfold SB in G in change_no_check G' end); lia).
      assert (OUTM : forall a : word, (U a < U sp - 448 \/ U sp <= U a) -> (U a < lo \/ lo + 2 ^ 18 <= U a) -> (U a < SH \/ SH + 2 ^ 15 <= U a) ->
                 (U a < T + 2872 \/ T + 2888 <= U a) -> (U a < RIz + 24 \/ RIz + 32 <= U a) -> M' a = M a).
      { intros a X1 X2 X3 X4 X5. (lazymatch goal with |- ?G => let G' := eval unfold M' in G in change_no_check G' end).
        rewrite (eam_3_outside MR sp s4v s5v thr v72 v80 RIz lo mfa ltac:(lia) ltac:(lia) a
                   ltac:(lia) ltac:(lia) ltac:(lia) ltac:(clear - X1; lia)
                   ltac:(rewrite <- ESH2; exact X3) ltac:(rewrite UT; exact X4) X5).
        (lazymatch goal with |- ?G => let G' := eval unfold MR in G in change_no_check G' end). apply efs_mr_outside; [lia | lia | exact X1 | exact X2]. }
      assert (GRM : mem_grows M M').
      { (lazymatch goal with |- ?G => let G' := eval unfold M' in G in change_no_check G' end). eapply mem_grows_trans; [| apply eam_3_grows]. (lazymatch goal with |- ?G => let G' := eval unfold MR in G in change_no_check G' end). apply efs_mr_grows. }
      assert (DEFSL : forall a : word, lo <= U a < lo + 2 ^ 18 -> M' a <> None).
      { intros a Ha. (lazymatch goal with |- ?G => let G' := eval unfold M' in G in change_no_check G' end). apply eam_3_grows. (lazymatch goal with |- ?G => let G' := eval unfold MR, efs_mr in G in change_no_check G' end). apply wbytes_grows. (lazymatch goal with |- ?G => let G' := eval unfold zfill, zmem in G in change_no_check G' end). rewrite !u_Z2bv by lia.
        rewrite (proj2 (Z.leb_le _ _)) by lia. rewrite (proj2 (Z.ltb_lt _ _)) by lia. discriminate. }
      assert (WRIM : writableZ ASEGS M RIz (RIz + 128)) by (apply (repx_wr (XL c) M M0 D); [lia | lia | exact GW]).
      assert (FOOTM : forall a : word, M' a <> M a ->
                ((U sp - 448 <= U a < U sp) \/ (lo <= U a < lo + 2 ^ 18) \/ (SH <= U a < SH + 2 ^ 15)
                 \/ (T + 2872 <= U a < T + 2888) \/ (RIz + 24 <= U a < RIz + 32)) /\ M' a <> None).
      { intros a Ha.
        assert (IN : ((U sp - 448 <= U a < U sp) \/ (lo <= U a < lo + 2 ^ 18) \/ (SH <= U a < SH + 2 ^ 15)
                      \/ (T + 2872 <= U a < T + 2888) \/ (RIz + 24 <= U a < RIz + 32))
                     \/ ((U a < U sp - 448 \/ U sp <= U a) /\ (U a < lo \/ lo + 2 ^ 18 <= U a) /\ (U a < SH \/ SH + 2 ^ 15 <= U a)
                         /\ (U a < T + 2872 \/ T + 2888 <= U a) /\ (U a < RIz + 24 \/ RIz + 32 <= U a))) by (clear; lia).
        destruct IN as [IN | (O1 & O2 & O3 & O4 & O5)]; [| exfalso; exact (Ha (OUTM a O1 O2 O3 O4 O5))].
        split; [exact IN|].
        destruct IN as [I1 | [I2 | [I3 | [I4 | I5]]]].
        - apply GRM. destruct (WSTK (U a) I1) as [Dd _]. rewrite Z_to_bv_bv_unsigned in Dd. exact Dd.
        - exact (DEFSL a I2).
        - apply GRM. rewrite <- (Z_to_bv_bv_unsigned _ a). apply (pk_shadow_def bt (XL c) st Lc FF M M0 mdl RP D). (lazymatch goal with |- ?G => let G' := eval unfold shmaps, AS_GAPHI, AS_HEAPLO in G in change_no_check G' end). right. clear - I3 SHB0 SHB1. lia.
        - apply GRM. destruct (TWR (U a) ltac:(clear - I4; lia)) as [Dd _]. rewrite Z_to_bv_bv_unsigned in Dd. exact Dd.
        - apply GRM. destruct (WRIM (U a) ltac:(clear - I5; lia)) as [Dd _]. rewrite Z_to_bv_bv_unsigned in Dd. exact Dd. }
      assert (W' : WF bt (add_meter (op_famap st c) 0 [(SH, SH + 2 ^ 18 / 8)] 0) Lc FF).
      { apply (WF_meter bt (op_famap st c) Lc FF 0 [(SH, SH + 2 ^ 18 / 8)] 0 (OPS_WF_famap_pf bt st Lc FF c W Hc ROOM FAQ)); lia. }
      assert (RX' : RepX bt (XL c) (add_meter (op_famap st c) 0 [(SH, SH + 2 ^ 18 / 8)] 0) Lc FF M' mdl5).
      { apply (AsAinvOpsRc73.AsAinvRepX3.RepX_mono bt (fun z => XL c z /\ ~ False) (XL c)); [intros z [Hz _]; exact Hz|].
        apply (repx_step bt (XL c) (fun _ => False)
                 (fun z => (U sp - 448 <= z < U sp) \/ (lo <= z < lo + 2 ^ 18) \/ (SH <= z < SH + 2 ^ 15) \/ (T + 2872 <= z < T + 2888) \/ (RIz + 24 <= z < RIz + 32))
                 Xdec_false st _ Lc Lc FF FF M M' mdl mdl5 RX FOOTM ltac:(intros a F; destruct F)).
        intros N0 N0' RPn Dn DIFF _ SAME.
        assert (EQF : forall a : word, ~ XL c (U a) -> N0' a = M' a) by (intros a Ha; apply SAME; exact (repx_off (XL c) M N0 Dn a Ha)).
        pose proof RPn as (_ & _ & _ & R4n & _). destruct (R4n c Hc) as [(_ & _ & _ & _ & _ & _ & _ & _ & _ & GWn) _]. rewrite BT_segs in GWn. fold RIz in GWn.
        destruct LED as (L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8 & L9 & L10 & L11 & L12 & L13).
        apply (OPS_REP_famap_pf bt st Lc FF N0 N0' mdl mdl5 c W RPn Hc ROOM); rewrite ?BT_segs.
        - intros a Ha. destruct (DIFF a Ha) as [[F | []] Dd]. split; [|exact Dd]. (lazymatch goal with |- ?G => let G' := eval unfold foot_famap, fslot in G in change_no_check G' end). fold r mfa lo RIz SH. (lazymatch goal with |- ?G => let G' := eval unfold KFAMAP, T_UNW in G in change_no_check G' end).
          replace (2 ^ 18 / 8) with (2 ^ 15) by reflexivity. clear - F SP1 CR. lia.
        - (lazymatch goal with |- ?G => let G' := eval unfold cellZ, cellN in G in change_no_check G' end). fold r mfa RIz. rewrite (rdn_ext ASEGS 8 N0' M' (Z_to_bv 64 (RIz + 24))); [ | rewrite u_Z2bv by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | ].
          + (lazymatch goal with |- ?G => let G' := eval unfold KFAMAP in G in change_no_check G' end). exact (eam_3_mfa ASEGS MR sp s4v s5v thr v72 v80 RIz lo mfa ltac:(lia)).
          + intros x Hx. rewrite u_Z2bv in Hx by lia. cbn in Hx. apply EQF. apply XRI. lia.
        - fold RIz. apply (repx_wr (fun _ => True) N0' N0 (fun a Ha => conj I (proj2 (DIFF a Ha)))); [lia | lia | exact GWn].
        - fold r mfa lo. (lazymatch goal with |- ?G => let G' := eval unfold KFAMAP in G in change_no_check G' end). apply writableZ_of_def; [lia | lia |]. intros i Hi.
          rewrite (EQF (Z_to_bv 64 i)) by (rewrite u_Z2bv by lia; apply XSL; exact Hi). apply DEFSL. rewrite u_Z2bv by lia. exact Hi.
        - fold r mfa lo SH. (lazymatch goal with |- ?G => let G' := eval unfold KFAMAP, fillZ, byteZ, cellN in G in change_no_check G' end). replace (2 ^ 18 / 8) with (2 ^ 15) by reflexivity. intros i Hi.
          rewrite w2b1 by ((lazymatch goal with |- ?G => let G' := eval unfold FA in G in change_no_check G' end); lia).
          rewrite (rdn_ext ASEGS 1 N0' M' (Z_to_bv 64 i)); [ | rewrite u_Z2bv by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | intros x Hx; rewrite u_Z2bv in Hx by lia; cbn in Hx; apply EQF, XSH; lia].
          replace i with (lo / 8 + 2147450880 + (i - SH)) by lia.
          exact (eam_3_fill ASEGS MR sp thr v72 v80 RIz lo ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(rewrite <- ESH2; right; lia)
                   ltac:(rewrite <- ESH2, UT; clear - TBAND SHB0 SHB1; lia) ltac:(rewrite <- ESH2; right; lia) ltac:(rewrite <- ESH2; right; lia) s4v s5v mfa (i - SH) ltac:(lia)).
        - exact L1. - exact L2. - exact L3. - exact L4. - exact L5. - exact L6. - exact L7. - exact L8. - exact L9. - exact L10. - exact L11. - exact L12.
        - exact MI5.
        - exact L13. }
      apply (CONT1 r' M' mdl5 W' RX' SEV LK MW5 HL5); [| exact Q10 | exact Q2 | exact Q1 | exact Q8 | exact Q9 | exact Q18 | exact Q19 | exact Q20 | exact Q21 | exact Q4 | exact Q3].
      intros a Ha. destruct (FOOTM a Ha) as [F Dd]. split; [| exact Dd]. replace (2 ^ 18 / 8) with (2 ^ 15) by reflexivity. fold RIz. clear - F. lia.
    - (* [comment removed for export] *)
      intros r0 r' mdlm mdl5 SBm MIm SB5 MI5 AG POST. cbv beta in SB5.
      match goal with |- katD _ (mkCfg (mkst _ _ ?MKK _) _) _ => set (MK := MKK) end.
      pose proof (same_but_materialized_trans _ _ _ SBm SB5) as SBK.
      assert (OUTK : forall a : word, (U a < U sp - 448 \/ U sp <= U a) -> MK a = M a).
      { intros a Ha. (lazymatch goal with |- ?G => let G' := eval unfold MK in G in change_no_check G' end).
        repeat (rewrite MemsetLibF.MemSplit.wbytes_outside; [ | rewrite length_N_to_le_bytes, at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite length_N_to_le_bytes, at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia]).
        rewrite mfi_m1_outside by (rewrite ?at_u by lia; lia). apply efs_m0_outside; lia. }
      assert (GRK : mem_grows M MK).
      { (lazymatch goal with |- ?G => let G' := eval unfold MK in G in change_no_check G' end). do 2 (eapply mem_grows_trans; [| apply wbytes_grows]). eapply mem_grows_trans; [apply efs_m0_grows | apply mfi_m1_grows]. }
      assert (FOOTK : forall a : word, MK a <> M a -> (U sp - 448 <= U a < U sp) /\ MK a <> None).
      { intros a Ha. assert (IN : (U sp - 448 <= U a < U sp) \/ (U a < U sp - 448 \/ U sp <= U a)) by (clear; lia).
        destruct IN as [IN | O1]; [| exfalso; exact (Ha (OUTK a O1))]. split; [exact IN|].
        apply GRK. destruct (WSTK (U a) IN) as [Dd _]. rewrite Z_to_bv_bv_unsigned in Dd. exact Dd. }
      apply (CONT0 r0 r' MK mdl5 st (or_introl eq_refl) W); [ | exact (same_but_materialized_except_vm _ _ SBK) | exact (lazy_kept_sbm bt Lc FF mdl mdl5 SBK)
                                                              | exact (model_ivs_wf_sbm mdl mdl5 SBK MW) | exact (halted_sbm mdl mdl5 SBK HALT) | | exact AG | exact POST].
      + apply (repx_frame_step bt (XL c) st Lc FF M MK mdl mdl5 W RX); [| exact MI5 | exact SBK].
        intros a Ha. destruct (FOOTK a Ha) as [IN Dd]. split; [|exact Dd].
        intros RCa. pose proof (rep_cells_lt_ceil bt BT_ia st Lc FF (U a) W RCa). lia.
      + intros a Ha. left. exact (FOOTK a Ha).
  Qed.


End L3h.
End WithCeil.
