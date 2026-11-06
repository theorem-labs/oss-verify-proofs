(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
Require Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Logic.FunctionalExtensionality LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocSim OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys6 OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFRcA OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8m OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM9i OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8e OSSVerify.glaze.binary_reflection.images.AsanUbsan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module BoAllocM8r.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import Stdlib.Logic.FunctionalExtensionality.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.DivergeSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.SpinAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes.AgentNodes OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocSim OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys6.MhKSys OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsK OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys6.AsKSys OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsRtK OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFRcA OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8m OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM9i.BoAllocM8k OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8e.BoAllocM8p OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8e.
Import OSSVerify.glaze.binary_reflection.images.AsanUbsan.
Import ListNotations.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation BSEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).
#[local] Abbreviation U := bv_unsigned.

Section FPGen1.
Context {fx : FPState}.

(* [comment removed for export] *)
Lemma pf_m0_outside : forall mem (sp ra s0v s1v s2v s3v s4v s5v s6v x : word), 64 <= U sp ->
  (U x < U sp - 64 \/ U sp <= U x) -> pf_m0 mem sp ra s0v s1v s2v s3v s4v s5v s6v x = mem x.
Proof using.
  intros mem sp ra s0v s1v s2v s3v s4v s5v s6v x Hsp Hx. pose proof (u64_range sp) as Hspr. (lazymatch goal with |- ?G => let G' := eval unfold pf_m0 in G in change_no_check G' end).
  repeat (rewrite MemsetLibF.MemSplit.wbytes_outside; [ | rewrite length_N_to_le_bytes, at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite length_N_to_le_bytes, at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia]).
  reflexivity.
Qed.
Lemma pf_m0_grows : forall mem (sp ra s0v s1v s2v s3v s4v s5v s6v : word), mem_grows mem (pf_m0 mem sp ra s0v s1v s2v s3v s4v s5v s6v).
Proof using. intros. (lazymatch goal with |- ?G => let G' := eval unfold pf_m0 in G in change_no_check G' end). repeat (eapply mem_grows_trans; [|apply wbytes_grows]). apply mem_grows_refl. Qed.
Lemma pf_m0_mrestrict : forall (Hd : word -> bool) mem (sp ra s0v s1v s2v s3v s4v s5v s6v : word), 64 <= U sp ->
  hid_off Hd (U sp - 64) 64 ->
  pf_m0 (mrestrict Hd mem) sp ra s0v s1v s2v s3v s4v s5v s6v = mrestrict Hd (pf_m0 mem sp ra s0v s1v s2v s3v s4v s5v s6v).
Proof using.
  intros Hd mem sp ra s0v s1v s2v s3v s4v s5v s6v Hsp HOFF. pose proof (u64_range sp). (lazymatch goal with |- ?G => let G' := eval unfold pf_m0 in G in change_no_check G' end).
  rewrite !wbytes_mrestrict; [reflexivity | | | | | | | | | | | | | | | |];
    wd_lenlit; rewrite ?length_N_to_le_bytes, ?at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn [length Z.of_nat Pos.of_succ_nat Pos.succ Pos.to_nat] in G in change_no_check G' end); first [lia | intros x Hx; apply HOFF; lia].
Qed.

(* [comment removed for export] *)
Definition pf_at_ret (sp stats : word) (RIz SPB c mu : Z) (r : bvmap 5 word) (res : word) : Prop :=
  pf_regs sp RIz SPB c r /\ getr r 9 = stats /\ getr r 19 = Z_to_bv 64 (2 ^ 18)
  /\ getr r 20 = Z_to_bv 64 (SPB + c * 2 ^ 32 + mu) /\ getr r 22 = Z_to_bv 64 0x10ab58 /\ getr r 10 = res.

Section USERMAP.
  Variable Hd : word -> bool.
  Hypothesis HOFFSEG : H_off_segments BSEGS Hd.
  Hypothesis WX : wx_segs_nowrap BSEGS.

  Theorem pf_usermap_katsD :
    forall (A : list (Z * Z)) regs (mem rom : word -> option byte) (model : Model)
           (sp ra s0v s1v s2v s3v s4v s5v s6v stats : word) (RIz SPB c req au mu PGP CF : Z) (Qok Qf : config -> Prop)
           (MOK MKP MDS : Model -> Model),
    let slot := SPB + c * 2 ^ 32 + mu in
    let M0 := pf_m0 mem sp ra s0v s1v s2v s3v s4v s5v s6v in
    let M1 := mfi_m1 M0 (at_ sp (-64)) (Z_to_bv 64 0x51964) (Z_to_bv 64 RIz) stats (Z_to_bv 64 (SPB + c * 2 ^ 32)) (Z_to_bv 64 (2 ^ 18))
                     (Z_to_bv 64 slot) (Z_to_bv 64 (csize c)) (Z_to_bv 64 slot) (Z_to_bv 64 (2 ^ 18)) (Z_to_bv 64 0x178e4) PGP in
    let ENOMEMw : word := Z_to_bv 64 (2 ^ 64 - 12) in
    let SCR := word_to_le_bytes 4 (Z_to_bv 64 0xffffffffaaaaaaaa) in
    (* [comment removed for export] *)
    getr regs 1 = ra -> getr regs 2 = sp -> getr regs 10 = Z_to_bv 64 0x10ab58 -> getr regs 11 = stats -> getr regs 12 = Z_to_bv 64 c ->
    getr regs 13 = Z_to_bv 64 RIz -> getr regs 14 = Z_to_bv 64 req ->
    getr regs 8 = s0v -> getr regs 9 = s1v -> getr regs 18 = s2v -> getr regs 19 = s3v -> getr regs 20 = s4v -> getr regs 21 = s5v -> getr regs 22 = s6v ->
    (2 ^ 24 + 64 <= U sp /\ U sp + 16 <= 2 ^ 47) -> 1 <= c <= 30 -> (1 <= req /\ csize c * req <= 2 ^ 18) ->
    (0 <= au <= mu /\ mu + 2 ^ 18 <= 0xE0000000) -> mu < au + csize c * req ->
    (0 <= SPB /\ SPB + 2 ^ 37 < 2 ^ 63 /\ SPB mod 4096 = 0 /\ AIMGHI <= SPB) -> mu mod 4096 = 0 ->
    (AIMGHI <= RIz /\ RIz + 128 <= U sp - 464) ->
    (AIMGLO <= PGP /\ PGP + 8 <= AIMGHI) -> (AIMGLO <= CF /\ CF + 264 <= AIMGHI) ->
    store_ok BSEGS mem (at_ sp (-464)) 464 = true ->
    (* [comment removed for export] *)
    rdn BSEGS mem (Z_to_bv 64 (0x10ab58 + 32)) 8 = Some (LE8 (Z_to_bv 64 SPB)) ->
    rdn BSEGS mem (Z_to_bv 64 (RIz + 32)) 8 = Some (LE8 (Z_to_bv 64 au)) ->
    rdn BSEGS mem (Z_to_bv 64 (RIz + 48)) 8 = Some (LE8 (Z_to_bv 64 mu)) ->
    rdn BSEGS mem (Z_to_bv 64 (RIz + 56)) 8 = Some (LE8 (Z_to_bv 64 0)) ->
    rdn BSEGS mem (Z_to_bv 64 (0x10ab58 + 40)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 0xffffffff)) ->
    rdn BSEGS mem (Z_to_bv 64 (0x10ab58 + 56)) 1 = Some [Z_to_bv 8 0] ->
    rdn BSEGS mem (Z_to_bv 64 0x105ef8) 8 = Some (LE8 (Z_to_bv 64 PGP)) ->
    rdn BSEGS mem (Z_to_bv 64 PGP) 8 = Some (LE8 (Z_to_bv 64 4096)) ->
    rdn BSEGS mem (Z_to_bv 64 0x105f08) 8 = Some (LE8 (Z_to_bv 64 CF)) ->
    rdn BSEGS mem (Z_to_bv 64 (CF + 260)) 1 = Some [Z_to_bv 8 0] ->
    rdn BSEGS mem (Z_to_bv 64 (CF + 144)) 8 = Some (LE8 (Z_to_bv 64 0)) ->
    (* [comment removed for export] *)
    (slot + 2 ^ 18 <= U sp - 464 \/ U sp <= slot) ->
    (* [comment removed for export] *)
    hid_off Hd (0x10ab58 + 32) 8 -> hid_off Hd (RIz + 32) 8 -> hid_off Hd (RIz + 48) 8 -> hid_off Hd (RIz + 56) 8 ->
    hid_off Hd (0x10ab58 + 40) 4 -> hid_off Hd (0x10ab58 + 56) 1 ->
    hid_off Hd 0x105ef8 8 -> hid_off Hd PGP 8 -> hid_off Hd 0x105f08 8 -> hid_off Hd (CF + 260) 1 -> hid_off Hd (CF + 144) 8 ->
    hid_off Hd (U sp - 464) 464 ->
    (* [comment removed for export] *)
    m_halted model = None -> lazy_cover Hd (m_vm_lazy model) A -> A_wf A -> MInv A model ->
    (* [comment removed for export] *)
    (forall mdlm (r1 : bvmap 5 word), same_but_materialized model mdlm -> MInv A mdlm -> m_halted mdlm = None ->
        getr r1 10 = Z_to_bv 64 slot -> getr r1 11 = Z_to_bv 64 (2 ^ 18) -> getr r1 12 = Z_to_bv 64 3 -> getr r1 13 = Z_to_bv 64 50 ->
        getr r1 14 = Z_to_bv 64 (2 ^ 64 - 1) -> getr r1 15 = Z_to_bv 64 0 ->
        forall Qok' Qf' : config -> Prop,
          katwD BSEGS (mkCfg (mkst (regupd r1 10 (Z_to_bv 64 slot)) (0x811b0 : word) (zfill (Z_to_bv 64 slot) (Z_to_bv 64 (2 ^ 18)) M1) rom) (MOK mdlm)) Qok' Qf' ->
          katsD BSEGS (mkCfg (epend r1 (0x811ac : word) M1 rom (Z_to_bv 64 222)) mdlm) Qok' Qf') ->
    (forall mdlm, same_but_materialized model mdlm -> MInv A mdlm ->
        (m_halted (MOK mdlm) = None /\ lazy_cover Hd (m_vm_lazy (MOK mdlm)) A /\ MInv A (MOK mdlm))
        /\ (m_halted (MKP mdlm) = None /\ lazy_cover Hd (m_vm_lazy (MKP mdlm)) A /\ MInv A (MKP mdlm))
        /\ (m_halted (MDS mdlm) = None /\ lazy_cover Hd (m_vm_lazy (MDS mdlm)) A /\ MInv A (MDS mdlm))) ->
    (* [comment removed for export] *)
    (forall (r' : bvmap 5 word) mdlm mdl4,
        same_but_materialized model mdlm -> MInv A mdlm -> same_but_materialized (MOK mdlm) mdl4 -> MInv A mdl4 ->
        pf_at_ret sp stats RIz SPB c mu r' (Z_to_bv 64 slot) -> regs_agree (fun i : reg => In i pf_clob) regs r' ->
        katwD BSEGS (mkCfg (mkst r' (0x51964 : word) (wbytes (zfill (Z_to_bv 64 slot) (Z_to_bv 64 (2 ^ 18)) M1) (at_ sp (-148)) SCR) rom) mdl4) Qok Qf) ->
    (forall (r' : bvmap 5 word) mdlm mdl4,
        same_but_materialized model mdlm -> MInv A mdlm -> same_but_materialized (MKP mdlm) mdl4 -> MInv A mdl4 ->
        pf_at_ret sp stats RIz SPB c mu r' (Z_to_bv 64 0) -> regs_agree (fun i : reg => In i pf_clob) regs r' ->
        katD BSEGS (mkCfg (mkst r' (0x51964 : word) (wbytes (wbytes M1 (at_ sp (-148)) SCR) (at_ sp (-148)) (word_to_le_bytes 4 (Z_to_bv 64 12))) rom) mdl4) Qf) ->
    (forall (r' : bvmap 5 word) mdlm mdl4,
        same_but_materialized model mdlm -> MInv A mdlm -> same_but_materialized (MDS mdlm) mdl4 -> MInv A mdl4 ->
        pf_at_ret sp stats RIz SPB c mu r' (Z_to_bv 64 0) -> regs_agree (fun i : reg => In i pf_clob) regs r' ->
        katD BSEGS (mkCfg (mkst r' (0x51964 : word) (wbytes (wbytes (unfill (Z_to_bv 64 slot) (Z_to_bv 64 (2 ^ 18)) M1) (at_ sp (-148)) SCR) (at_ sp (-148)) (word_to_le_bytes 4 (Z_to_bv 64 12))) rom) mdl4) Qf) ->
    katsD BSEGS (mkCfg (mkst regs (0x51844 : word) mem rom) model) Qok Qf.
  Proof using WX HOFFSEG.
    intros A regs mem rom model sp ra s0v s1v s2v s3v s4v s5v s6v stats RIz SPB c req au mu PGP CF Qok Qf MOK MKP MDS slot M0 M1 ENOMEMw SCR
           H1 H2 H10 H11 H12 H13 H14 H8 H9 H18 H19 H20 H21 H22 Hsp Hc Hreq Hau Hmap HSPB Hmu4k HRI HPGP HCF Hstk
           C_sbeg R_au R_mu R_mm C_rel C_pre Rgpg Rpg Rgcf Rdpm Rlim Hslot
           HDsbeg HDau HDmu HDmm HDrel HDpre HDgpg HDpg HDgcf HDdpm HDlim HDscr HALT LC AWF MI NODE CHILD CONTOK CONTKP CONTDS.
    pose proof (u64_range sp) as Hspr. destruct Hsp as [SP1 SP2]. destruct HSPB as (S1 & S2 & S3 & S4). destruct HRI as [RI1 RI2].
    destruct HPGP as [PG1 PG2]. destruct HCF as [CF1 CF2]. destruct Hau as [AU1 AU2]. destruct Hreq as [RQ1 RQ2].
    pose proof (csize_pos c Hc) as [CS1 CS2].
    set (spm := at_ sp (-64)).
    assert (Uspm : U spm = U sp - 64) by ((lazymatch goal with |- ?G => let G' := eval unfold spm in G in change_no_check G' end); first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ]).
    (* [comment removed for export] *)
    assert (CELLR : forall (cc : Z) (k : nat) v, 0 <= cc -> cc + Z.of_nat k <= U sp - 464 -> hid_off Hd cc (Z.of_nat k) ->
               rdn BSEGS mem (Z_to_bv 64 cc) k = Some v -> rdn BSEGS (mrestrict Hd mem) (Z_to_bv 64 cc) k = Some v).
    { intros cc k v Hc0 Hc1 Hh Hr. rewrite rdn_mrestrict; [exact Hr | first [ solve [ wd_unorm1; wd_zofnat; lia ] | rewrite u_Z2bv by lia; lia ] | rewrite u_Z2bv by lia; exact Hh]. }
    assert (Hstk' : store_ok BSEGS (mrestrict Hd mem) (at_ sp (-64)) 64 = true).
    { rewrite store_ok_mrestrict; [| first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); intros x Hx; apply HDscr; lia].
      eapply (store_ok_sub BSEGS mem (at_ sp (-464)) _ 464); [first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | exact Hstk | first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite !at_u by lia; lia ] | first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite !at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ]]. }
    destruct (pf_head_map (mrestrict Hd mem) rom sp ra s0v s1v s2v s3v s4v s5v s6v stats RIz SPB c req au mu regs
                H1 H2 H10 H11 H12 H13 H14 H8 H9 H18 H19 H20 H21 H22 ltac:(lia) Hc (conj RQ1 RQ2) (conj AU1 AU2) ltac:(lia) ltac:(lia) Hstk'
                (CELLR (0x10ab58 + 32) 8%nat _ ltac:(lia) ltac:((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia) HDsbeg C_sbeg)
                (CELLR (RIz + 32) 8%nat _ ltac:(lia) ltac:((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia) HDau R_au)
                (CELLR (RIz + 48) 8%nat _ ltac:(lia) ltac:((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia) HDmu R_mu) Hmap)
      as (r1 & RUN1 & PR1 & A9 & A10 & A12 & A19 & A20 & AG1).
    rewrite pf_m0_mrestrict in RUN1 by (first [lia | intros x Hx; apply HDscr; lia]). fold M0 in RUN1.
    assert (M0out : forall x : word, (U x < U sp - 64 \/ U sp <= U x) -> M0 x = mem x) by (intros x Hx; (lazymatch goal with |- ?G => let G' := eval unfold M0 in G in change_no_check G' end); apply pf_m0_outside; [lia | exact Hx]).
    assert (CELL0 : forall (cc : Z) (k : nat) v, 0 <= cc -> cc + Z.of_nat k <= U sp - 464 ->
               rdn BSEGS mem (Z_to_bv 64 cc) k = Some v -> rdn BSEGS M0 (Z_to_bv 64 cc) k = Some v).
    { intros cc k v Hc0 Hc1 Hr. rewrite <- Hr. apply rdn_ext; [first [ solve [ wd_unorm1; wd_zofnat; lia ] | rewrite u_Z2bv by lia; lia ]|]. intros x Hx. rewrite u_Z2bv in Hx by lia. apply M0out. lia. }
    assert (CELLR0 : forall (cc : Z) (k : nat) v, 0 <= cc -> cc + Z.of_nat k <= U sp - 464 -> hid_off Hd cc (Z.of_nat k) ->
               rdn BSEGS mem (Z_to_bv 64 cc) k = Some v -> rdn BSEGS (mrestrict Hd M0) (Z_to_bv 64 cc) k = Some v).
    { intros cc k v Hc0 Hc1 Hh Hr. rewrite rdn_mrestrict; [apply CELL0; assumption | first [ solve [ wd_unorm1; wd_zofnat; lia ] | rewrite u_Z2bv by lia; lia ] | rewrite u_Z2bv by lia; exact Hh]. }
    destruct (pf_map (mrestrict Hd M0) rom sp stats RIz SPB c (au + csize c * req) mu r1 PR1 A9 A10 A19 A20 ltac:(lia) Hc ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
                (CELLR0 (0x10ab58 + 40) 4%nat _ ltac:(lia) ltac:((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia) HDrel C_rel)
                (CELLR0 (0x10ab58 + 56) 1%nat _ ltac:(lia) ltac:((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia) HDpre C_pre)
                (CELLR0 (RIz + 56) 8%nat _ ltac:(lia) ltac:((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia) HDmm R_mm))
      as (r2 & RUN2 & PR2 & B9 & B1 & B11 & B12 & B13 & B19 & B20 & B22 & AG2).
    assert (M0hid : forall a : word, Hd a = true -> M0 a = mem a).
    { intros a Ha. apply M0out.
      destruct (Z_lt_le_dec (U a) (U sp - 64)) as [C1|C1]; [left; exact C1|].
      destruct (Z_lt_le_dec (U a) (U sp)) as [C2|C2]; [| right; exact C2].
      exfalso. rewrite (HDscr a) in Ha by lia. discriminate Ha. }
    apply (katsD_msteps_acct BSEGS Hd HOFFSEG WX A (mkst regs (0x51844 : word) mem rom)
             (mkst r2 (0x8b0f8 : word) (mrestrict Hd M0) rom) model Qok Qf LC AWF MI HALT).
    { rewrite mk_restrict_mkst. eapply msteps_trans; [exact RUN1 | exact RUN2]. }
    intros mdlm MIm SBMm HC1. rewrite mk_unrestrict_mkst.
    replace (RiscvSemantics.ms_mem (mkst regs (0x51844 : word) mem rom)) with mem by reflexivity.
    rewrite (mk_munrestrict_same Hd mem M0 M0hid).
    pose proof (same_but_materialized_frame model mdlm SBMm) as FRm.
    assert (HALTm : m_halted mdlm = None) by (destruct FRm as (_&_&_&_&_&_&_&_&_&_&_&_&Hh&_); rewrite Hh; exact HALT).
    assert (LCm : lazy_cover Hd (m_vm_lazy mdlm) A) by (destruct FRm as (_ & _ & Hl & _); rewrite Hl; exact LC).
    destruct PR2 as (P2 & P8 & P18 & P21).
    assert (SUB : forall x : reg, In x mfi_clob2 -> In x pf_clob).
    { intros x Hin. unfold mfi_clob2, mfi_clob in Hin. cbn [In] in Hin. (lazymatch goal with |- ?G => let G' := eval unfold pf_clob in G in change_no_check G' end).
      repeat (destruct Hin as [<-|Hin]; [solve [in_list]|]). destruct Hin. }
    assert (RETK : forall (r' : bvmap 5 word) (res : word),
               mfi_ret r2 r' spm (Z_to_bv 64 0x51964) (Z_to_bv 64 RIz) stats (Z_to_bv 64 (SPB + c * 2 ^ 32)) (Z_to_bv 64 (2 ^ 18)) (Z_to_bv 64 slot) res ->
               pf_at_ret sp stats RIz SPB c mu r' res).
    { intros r' res (C10 & C2 & C1 & C8 & C9 & C18 & C19 & C20 & AGL). (lazymatch goal with |- ?G => let G' := eval unfold pf_at_ret, pf_regs in G in change_no_check G' end).
      assert (N21 : ~ In (21%bv : reg) mfi_clob2) by ((lazymatch goal with |- ?G => let G' := eval unfold mfi_clob2, mfi_clob in G in change_no_check G' end); (lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); intros X; repeat (destruct X as [X|X]; [discriminate X|]); exact X).
      assert (N22 : ~ In (22%bv : reg) mfi_clob2) by ((lazymatch goal with |- ?G => let G' := eval unfold mfi_clob2, mfi_clob in G in change_no_check G' end); (lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); intros X; repeat (destruct X as [X|X]; [discriminate X|]); exact X).
      rewrite (AGL 21%bv N21), (AGL 22%bv N22).
      repeat split; assumption. }
    assert (RETA : forall (r' : bvmap 5 word) (res : word),
               mfi_ret r2 r' spm (Z_to_bv 64 0x51964) (Z_to_bv 64 RIz) stats (Z_to_bv 64 (SPB + c * 2 ^ 32)) (Z_to_bv 64 (2 ^ 18)) (Z_to_bv 64 slot) res ->
               regs_agree (fun i : reg => In i pf_clob) regs r').
    { intros r' res (_ & _ & _ & _ & _ & _ & _ & _ & AGL) x Hx.
      rewrite (AGL x) by (intros Hin; apply Hx; exact (SUB x Hin)).
      rewrite (AG2 x Hx). exact (AG1 x Hx). }
    (* [comment removed for export] *)
    apply (rarmap_katsD Hd HOFFSEG WX A r2 M0 rom mdlm spm (Z_to_bv 64 0x51964) (Z_to_bv 64 RIz) stats (Z_to_bv 64 (SPB + c * 2 ^ 32))
             (Z_to_bv 64 (2 ^ 18)) (Z_to_bv 64 slot) (Z_to_bv 64 (csize c)) (Z_to_bv 64 slot) (Z_to_bv 64 (2 ^ 18)) (Z_to_bv 64 0x178e4)
             PGP CF Qok Qf MOK MKP MDS B1 P2 B11 B12 B13 P8 B9 P18 B19 B20 P21).
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
      eapply (store_ok_sub BSEGS mem (at_ sp (-464)) _ 464); [first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | exact Hstk | first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite !at_u by lia; lia ] | first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite !at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ]].
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
      replace (Z_to_bv 64 334180 : word) with (0x51964%bv : word) by (apply bv_eq; reflexivity).
      apply (CONTOK r' mdlm0 mdl4 (same_but_materialized_trans _ _ _ SBMm SB0) MI0 SB4 MI4); [apply (RETK r' _ RET) | apply (RETA r' _ RET)].
    - intros r' mdlm0 mdl4 SB0 MI0 SB4 MI4 RET.
      replace (at_ spm (-84)) with (at_ sp (-148)) by ((lazymatch goal with |- ?G => let G' := eval unfold spm in G in change_no_check G' end); rewrite at_at; reflexivity).
      replace (Z_to_bv 64 334180 : word) with (0x51964%bv : word) by (apply bv_eq; reflexivity).
      apply (CONTKP r' mdlm0 mdl4 (same_but_materialized_trans _ _ _ SBMm SB0) MI0 SB4 MI4); [apply (RETK r' _ RET) | apply (RETA r' _ RET)].
    - intros r' mdlm0 mdl4 SB0 MI0 SB4 MI4 RET.
      replace (at_ spm (-84)) with (at_ sp (-148)) by ((lazymatch goal with |- ?G => let G' := eval unfold spm in G in change_no_check G' end); rewrite at_at; reflexivity).
      replace (Z_to_bv 64 334180 : word) with (0x51964%bv : word) by (apply bv_eq; reflexivity).
      apply (CONTDS r' mdlm0 mdl4 (same_but_materialized_trans _ _ _ SBMm SB0) MI0 SB4 MI4); [apply (RETK r' _ RET) | apply (RETA r' _ RET)].
  Qed.

End USERMAP.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma efs_m0_outside : forall mem (sp ra s0v s1v s2v s3v x : word), 48 <= U sp ->
  (U x < U sp - 48 \/ U sp <= U x) -> efs_m0 mem sp ra s0v s1v s2v s3v x = mem x.
Proof using.
  intros mem sp ra s0v s1v s2v s3v x Hsp Hx. pose proof (u64_range sp) as Hspr. (lazymatch goal with |- ?G => let G' := eval unfold efs_m0 in G in change_no_check G' end).
  repeat (rewrite MemsetLibF.MemSplit.wbytes_outside; [ | rewrite length_N_to_le_bytes, at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite length_N_to_le_bytes, at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia]).
  reflexivity.
Qed.
Lemma efs_m0_grows : forall mem (sp ra s0v s1v s2v s3v : word), mem_grows mem (efs_m0 mem sp ra s0v s1v s2v s3v).
Proof using. intros. (lazymatch goal with |- ?G => let G' := eval unfold efs_m0 in G in change_no_check G' end). repeat (eapply mem_grows_trans; [|apply wbytes_grows]). apply mem_grows_refl. Qed.
Lemma efs_m0_mrestrict : forall (Hd : word -> bool) mem (sp ra s0v s1v s2v s3v : word), 48 <= U sp ->
  hid_off Hd (U sp - 48) 48 ->
  efs_m0 (mrestrict Hd mem) sp ra s0v s1v s2v s3v = mrestrict Hd (efs_m0 mem sp ra s0v s1v s2v s3v).
Proof using.
  intros Hd mem sp ra s0v s1v s2v s3v Hsp HOFF. pose proof (u64_range sp). (lazymatch goal with |- ?G => let G' := eval unfold efs_m0 in G in change_no_check G' end).
  rewrite !wbytes_mrestrict; [reflexivity | | | | | | | | | |];
    wd_lenlit; rewrite ?length_N_to_le_bytes, ?at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn [length Z.of_nat Pos.of_succ_nat Pos.succ Pos.to_nat] in G in change_no_check G' end); first [lia | intros x Hx; apply HOFF; lia].
Qed.

(* [comment removed for export] *)
Definition efs_at_ret (sp s4v : word) (RIz slot mfa : Z) (r : bvmap 5 word) (res : word) : Prop :=
  getr r 2 = at_ sp (-48) /\ getr r 8 = Z_to_bv 64 (mfa + 2 ^ 18) /\ getr r 9 = Z_to_bv 64 slot /\ getr r 18 = Z_to_bv 64 (2 ^ 18)
  /\ getr r 19 = Z_to_bv 64 RIz /\ getr r 10 = res /\ getr r 20 = s4v.
Definition efs_clob : list reg := [1; 2; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20; 28; 29; 30; 31]%bv.

Section FAMAP.
  Variable Hd : word -> bool.
  Hypothesis HOFFSEG : H_off_segments BSEGS Hd.
  Hypothesis WX : wx_segs_nowrap BSEGS.

  Theorem efs_famap_katsD :
    forall (A : list (Z * Z)) regs (mem rom : word -> option byte) (model : Model)
           (sp ra s0v s1v s2v s3v s4v s5v : word) (RIz rbeg tot mfa PGP CF : Z) (Qok Qf : config -> Prop)
           (MOK MKP MDS : Model -> Model),
    let slot := rbeg + 0xE0000000 + mfa in
    let M0 := efs_m0 mem sp ra s0v s1v s2v s3v in
    let M1 := mfi_m1 M0 (at_ sp (-48)) (Z_to_bv 64 0x4f5a8) (Z_to_bv 64 (mfa + 2 ^ 18)) (Z_to_bv 64 slot) (Z_to_bv 64 (2 ^ 18)) (Z_to_bv 64 RIz)
                     s4v s5v (Z_to_bv 64 slot) (Z_to_bv 64 (2 ^ 18)) (Z_to_bv 64 0x19778) PGP in
    let ENOMEMw : word := Z_to_bv 64 (2 ^ 64 - 12) in
    let SCR := word_to_le_bytes 4 (Z_to_bv 64 0xffffffffaaaaaaaa) in
    getr regs 1 = ra -> getr regs 2 = sp -> getr regs 10 = Z_to_bv 64 0x10ab58 -> getr regs 11 = Z_to_bv 64 RIz -> getr regs 12 = Z_to_bv 64 rbeg ->
    getr regs 13 = Z_to_bv 64 tot ->
    getr regs 8 = s0v -> getr regs 9 = s1v -> getr regs 18 = s2v -> getr regs 19 = s3v -> getr regs 20 = s4v -> getr regs 21 = s5v ->
    (2 ^ 24 + 48 <= U sp /\ U sp + 16 <= 2 ^ 47) ->
    (0 <= tot /\ 4 * tot <= 2 ^ 29) -> (0 <= mfa <= 2 ^ 29 /\ mfa mod 2 ^ 18 = 0) -> (mfa < 4 * tot <= mfa + 2 ^ 18) -> mfa + 2 ^ 18 <= 2 ^ 29 ->
    (AIMGHI <= rbeg /\ rbeg + 2 ^ 32 < 2 ^ 63 /\ rbeg mod 4096 = 0) ->
    (AIMGHI <= RIz /\ RIz + 128 <= U sp - 448) ->
    (AIMGLO <= PGP /\ PGP + 8 <= AIMGHI) -> (AIMGLO <= CF /\ CF + 264 <= AIMGHI) ->
    store_ok BSEGS mem (at_ sp (-448)) 448 = true ->
    rdn BSEGS mem (Z_to_bv 64 (RIz + 24)) 8 = Some (LE8 (Z_to_bv 64 mfa)) ->
    rdn BSEGS mem (Z_to_bv 64 (0x10ab58 + 56)) 1 = Some [Z_to_bv 8 0] ->
    rdn BSEGS mem (Z_to_bv 64 0x105ef8) 8 = Some (LE8 (Z_to_bv 64 PGP)) ->
    rdn BSEGS mem (Z_to_bv 64 PGP) 8 = Some (LE8 (Z_to_bv 64 4096)) ->
    rdn BSEGS mem (Z_to_bv 64 0x105f08) 8 = Some (LE8 (Z_to_bv 64 CF)) ->
    rdn BSEGS mem (Z_to_bv 64 (CF + 260)) 1 = Some [Z_to_bv 8 0] ->
    rdn BSEGS mem (Z_to_bv 64 (CF + 144)) 8 = Some (LE8 (Z_to_bv 64 0)) ->
    (slot + 2 ^ 18 <= U sp - 448 \/ U sp <= slot) ->
    hid_off Hd (RIz + 24) 8 -> hid_off Hd (0x10ab58 + 56) 1 ->
    hid_off Hd 0x105ef8 8 -> hid_off Hd PGP 8 -> hid_off Hd 0x105f08 8 -> hid_off Hd (CF + 260) 1 -> hid_off Hd (CF + 144) 8 ->
    hid_off Hd (U sp - 448) 448 ->
    m_halted model = None -> lazy_cover Hd (m_vm_lazy model) A -> A_wf A -> MInv A model ->
    (forall mdlm (r1 : bvmap 5 word), same_but_materialized model mdlm -> MInv A mdlm -> m_halted mdlm = None ->
        getr r1 10 = Z_to_bv 64 slot -> getr r1 11 = Z_to_bv 64 (2 ^ 18) -> getr r1 12 = Z_to_bv 64 3 -> getr r1 13 = Z_to_bv 64 50 ->
        getr r1 14 = Z_to_bv 64 (2 ^ 64 - 1) -> getr r1 15 = Z_to_bv 64 0 ->
        forall Qok' Qf' : config -> Prop,
          katwD BSEGS (mkCfg (mkst (regupd r1 10 (Z_to_bv 64 slot)) (0x811b0 : word) (zfill (Z_to_bv 64 slot) (Z_to_bv 64 (2 ^ 18)) M1) rom) (MOK mdlm)) Qok' Qf' ->
          katsD BSEGS (mkCfg (epend r1 (0x811ac : word) M1 rom (Z_to_bv 64 222)) mdlm) Qok' Qf') ->
    (forall mdlm, same_but_materialized model mdlm -> MInv A mdlm ->
        (m_halted (MOK mdlm) = None /\ lazy_cover Hd (m_vm_lazy (MOK mdlm)) A /\ MInv A (MOK mdlm))
        /\ (m_halted (MKP mdlm) = None /\ lazy_cover Hd (m_vm_lazy (MKP mdlm)) A /\ MInv A (MKP mdlm))
        /\ (m_halted (MDS mdlm) = None /\ lazy_cover Hd (m_vm_lazy (MDS mdlm)) A /\ MInv A (MDS mdlm))) ->
    (forall (r' : bvmap 5 word) mdlm mdl4,
        same_but_materialized model mdlm -> MInv A mdlm -> same_but_materialized (MOK mdlm) mdl4 -> MInv A mdl4 ->
        efs_at_ret sp s4v RIz slot mfa r' (Z_to_bv 64 slot) -> regs_agree (fun i : reg => In i efs_clob) regs r' ->
        katwD BSEGS (mkCfg (mkst r' (0x4f5a8 : word) (wbytes (zfill (Z_to_bv 64 slot) (Z_to_bv 64 (2 ^ 18)) M1) (at_ sp (-132)) SCR) rom) mdl4) Qok Qf) ->
    (forall (r' : bvmap 5 word) mdlm mdl4,
        same_but_materialized model mdlm -> MInv A mdlm -> same_but_materialized (MKP mdlm) mdl4 -> MInv A mdl4 ->
        efs_at_ret sp s4v RIz slot mfa r' (Z_to_bv 64 0) -> regs_agree (fun i : reg => In i efs_clob) regs r' ->
        katD BSEGS (mkCfg (mkst r' (0x4f5a8 : word) (wbytes (wbytes M1 (at_ sp (-132)) SCR) (at_ sp (-132)) (word_to_le_bytes 4 (Z_to_bv 64 12))) rom) mdl4) Qf) ->
    (forall (r' : bvmap 5 word) mdlm mdl4,
        same_but_materialized model mdlm -> MInv A mdlm -> same_but_materialized (MDS mdlm) mdl4 -> MInv A mdl4 ->
        efs_at_ret sp s4v RIz slot mfa r' (Z_to_bv 64 0) -> regs_agree (fun i : reg => In i efs_clob) regs r' ->
        katD BSEGS (mkCfg (mkst r' (0x4f5a8 : word) (wbytes (wbytes (unfill (Z_to_bv 64 slot) (Z_to_bv 64 (2 ^ 18)) M1) (at_ sp (-132)) SCR) (at_ sp (-132)) (word_to_le_bytes 4 (Z_to_bv 64 12))) rom) mdl4) Qf) ->
    katsD BSEGS (mkCfg (mkst regs (0x4f508 : word) mem rom) model) Qok Qf.
  Proof using WX HOFFSEG.
    intros A regs mem rom model sp ra s0v s1v s2v s3v s4v s5v RIz rbeg tot mfa PGP CF Qok Qf MOK MKP MDS slot M0 M1 ENOMEMw SCR
           H1 H2 H10 H11 H12 H13 H8 H9 H18 H19 H20 H21 Hsp Htot Hmfa Hneed Hroom Hrbeg HRI HPGP HCF Hstk
           R_mfa C_pre Rgpg Rpg Rgcf Rdpm Rlim Hslot
           HDmfa HDpre HDgpg HDpg HDgcf HDdpm HDlim HDscr HALT LC AWF MI NODE CHILD CONTOK CONTKP CONTDS.
    pose proof (u64_range sp) as Hspr. destruct Hsp as [SP1 SP2]. destruct Hrbeg as (RB1 & RB2 & RB3). destruct HRI as [RI1 RI2].
    destruct HPGP as [PG1 PG2]. destruct HCF as [CF1 CF2]. destruct Hmfa as [MF1 MF2].
    set (spm := at_ sp (-48)).
    assert (Uspm : U spm = U sp - 48) by ((lazymatch goal with |- ?G => let G' := eval unfold spm in G in change_no_check G' end); first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ]).
    assert (CELLR : forall (cc : Z) (k : nat) v, 0 <= cc -> cc + Z.of_nat k <= U sp - 448 -> hid_off Hd cc (Z.of_nat k) ->
               rdn BSEGS mem (Z_to_bv 64 cc) k = Some v -> rdn BSEGS (mrestrict Hd mem) (Z_to_bv 64 cc) k = Some v).
    { intros cc k v Hc0 Hc1 Hh Hr. rewrite rdn_mrestrict; [exact Hr | first [ solve [ wd_unorm1; wd_zofnat; lia ] | rewrite u_Z2bv by lia; lia ] | rewrite u_Z2bv by lia; exact Hh]. }
    assert (Hstk' : store_ok BSEGS (mrestrict Hd mem) (at_ sp (-48)) 48 = true).
    { rewrite store_ok_mrestrict; [| first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); intros x Hx; apply HDscr; lia].
      eapply (store_ok_sub BSEGS mem (at_ sp (-448)) _ 448); [first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | exact Hstk | first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite !at_u by lia; lia ] | first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite !at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ]]. }
    destruct (efs_map (mrestrict Hd mem) rom sp ra s0v s1v s2v s3v RIz rbeg tot mfa regs
                H1 H2 H10 H11 H12 H13 H8 H9 H18 H19 ltac:(lia) Htot (conj MF1 MF2) ltac:(lia) ltac:(lia) Hstk'
                (CELLR (RIz + 24) 8%nat _ ltac:(lia) ltac:((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia) HDmfa R_mfa)
                (CELLR (0x10ab58 + 56) 1%nat _ ltac:(lia) ltac:((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia) HDpre C_pre) Hneed Hroom)
      as (r2 & RUN2 & B1 & B2 & B11 & B12 & B13 & B8 & B9 & B18 & B19 & AG2).
    rewrite efs_m0_mrestrict in RUN2 by (first [lia | intros x Hx; apply HDscr; lia]). fold M0 in RUN2.
    assert (M0out : forall x : word, (U x < U sp - 48 \/ U sp <= U x) -> M0 x = mem x) by (intros x Hx; (lazymatch goal with |- ?G => let G' := eval unfold M0 in G in change_no_check G' end); apply efs_m0_outside; [lia | exact Hx]).
    assert (CELL0 : forall (cc : Z) (k : nat) v, 0 <= cc -> cc + Z.of_nat k <= U sp - 448 ->
               rdn BSEGS mem (Z_to_bv 64 cc) k = Some v -> rdn BSEGS M0 (Z_to_bv 64 cc) k = Some v).
    { intros cc k v Hc0 Hc1 Hr. rewrite <- Hr. apply rdn_ext; [first [ solve [ wd_unorm1; wd_zofnat; lia ] | rewrite u_Z2bv by lia; lia ]|]. intros x Hx. rewrite u_Z2bv in Hx by lia. apply M0out. lia. }
    assert (M0hid : forall a : word, Hd a = true -> M0 a = mem a).
    { intros a Ha. apply M0out.
      destruct (Z_lt_le_dec (U a) (U sp - 48)) as [C1|C1]; [left; exact C1|].
      destruct (Z_lt_le_dec (U a) (U sp)) as [C2|C2]; [| right; exact C2].
      exfalso. rewrite (HDscr a) in Ha by lia. discriminate Ha. }
    apply (katsD_msteps_acct BSEGS Hd HOFFSEG WX A (mkst regs (0x4f508 : word) mem rom)
             (mkst r2 (0x8b0f8 : word) (mrestrict Hd M0) rom) model Qok Qf LC AWF MI HALT).
    { rewrite mk_restrict_mkst. exact RUN2. }
    intros mdlm MIm SBMm HC1. rewrite mk_unrestrict_mkst.
    replace (RiscvSemantics.ms_mem (mkst regs (0x4f508 : word) mem rom)) with mem by reflexivity.
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
               mfi_ret r2 r' spm (Z_to_bv 64 0x4f5a8) (Z_to_bv 64 (mfa + 2 ^ 18)) (Z_to_bv 64 slot) (Z_to_bv 64 (2 ^ 18)) (Z_to_bv 64 RIz) s4v res ->
               efs_at_ret sp s4v RIz slot mfa r' res).
    { intros r' res (C10 & C2 & C1 & C8 & C9 & C18 & C19 & C20 & AGL). (lazymatch goal with |- ?G => let G' := eval unfold efs_at_ret in G in change_no_check G' end). repeat split; assumption. }
    assert (RETA : forall (r' : bvmap 5 word) (res : word),
               mfi_ret r2 r' spm (Z_to_bv 64 0x4f5a8) (Z_to_bv 64 (mfa + 2 ^ 18)) (Z_to_bv 64 slot) (Z_to_bv 64 (2 ^ 18)) (Z_to_bv 64 RIz) s4v res ->
               regs_agree (fun i : reg => In i efs_clob) regs r').
    { intros r' res (_ & _ & _ & _ & _ & _ & _ & _ & AGL) x Hx.
      rewrite (AGL x) by (intros Hin; apply Hx; exact (SUB x Hin)).
      apply AG2. intros Hin. apply Hx. exact (SUB2 x Hin). }
    apply (rarmap_katsD Hd HOFFSEG WX A r2 M0 rom mdlm spm (Z_to_bv 64 0x4f5a8) (Z_to_bv 64 (mfa + 2 ^ 18)) (Z_to_bv 64 slot)
             (Z_to_bv 64 (2 ^ 18)) (Z_to_bv 64 RIz) s4v s5v (Z_to_bv 64 slot) (Z_to_bv 64 (2 ^ 18)) (Z_to_bv 64 0x19778)
             PGP CF Qok Qf MOK MKP MDS B1 B2 B11 B12 B13 B8 B9 B18 B19 A20 A21).
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
      eapply (store_ok_sub BSEGS mem (at_ sp (-448)) _ 448); [first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | exact Hstk | first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite !at_u by lia; lia ] | first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite !at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ]].
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
      replace (Z_to_bv 64 325032 : word) with (0x4f5a8%bv : word) by (apply bv_eq; reflexivity).
      apply (CONTOK r' mdlm0 mdl4 (same_but_materialized_trans _ _ _ SBMm SB0) MI0 SB4 MI4); [apply (RETK r' _ RET) | apply (RETA r' _ RET)].
    - intros r' mdlm0 mdl4 SB0 MI0 SB4 MI4 RET.
      replace (at_ spm (-84)) with (at_ sp (-132)) by ((lazymatch goal with |- ?G => let G' := eval unfold spm in G in change_no_check G' end); rewrite at_at; reflexivity).
      replace (Z_to_bv 64 325032 : word) with (0x4f5a8%bv : word) by (apply bv_eq; reflexivity).
      apply (CONTKP r' mdlm0 mdl4 (same_but_materialized_trans _ _ _ SBMm SB0) MI0 SB4 MI4); [apply (RETK r' _ RET) | apply (RETA r' _ RET)].
    - intros r' mdlm0 mdl4 SB0 MI0 SB4 MI4 RET.
      replace (at_ spm (-84)) with (at_ sp (-132)) by ((lazymatch goal with |- ?G => let G' := eval unfold spm in G in change_no_check G' end); rewrite at_at; reflexivity).
      replace (Z_to_bv 64 325032 : word) with (0x4f5a8%bv : word) by (apply bv_eq; reflexivity).
      apply (CONTDS r' mdlm0 mdl4 (same_but_materialized_trans _ _ _ SBMm SB0) MI0 SB4 MI4); [apply (RETK r' _ RET) | apply (RETA r' _ RET)].
  Qed.

End FAMAP.
End FPGen1.
End BoAllocM8r.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtUnwindT OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoison OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtPoisonI OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM0 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMMemA OSSVerify.Proofs.glaze.binary_reflection.lib.Bo_code_50a9c_51a9c OSSVerify.Proofs.glaze.binary_reflection.lib.BoCodeM1 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8s OSSVerify.Proofs.glaze.binary_reflection.lib.AmLia.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module BoAllocM8sq.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtUnwindT OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoison OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtPoisonI OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM0 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMMemA.BoAllocMI OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8e.BoAllocM8p OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8e OSSVerify.Proofs.glaze.binary_reflection.lib.Bo_code_50a9c_51a9c OSSVerify.Proofs.glaze.binary_reflection.lib.BoCodeM1 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8s.
Import OSSVerify.glaze.binary_reflection.images.AsanUbsan.
Import ListNotations.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AmLia.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac am_inner ::= tryif noncert_goal_has_var then (Zify.zify; xlia zchecker) else first [ solve [noncert_clear_all; Zify.zify; xlia zchecker] | Zify.zify; xlia zchecker ].
#[local] Ltac lia ::= am_lia.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation BSEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).
#[local] Abbreviation U := bv_unsigned.

Section FPGen.
Context {fx : FPState}.

Section EFSAFTERMAPX.
  Variables (M rom : word -> option byte) (sp ra s0v s1v s2v s3v s4x s5x thr tp gp tsdp ctxw v72 v80 midend : word) (cpm : byte)
            (RIz slot mfa T thr0 : Z).
  Variable regs : bvmap 5 word.
  Hypothesis H2 : getr regs 2 = at_ sp (-48).
  Hypothesis H4 : getr regs 4 = tp.
  Hypothesis H3 : getr regs 3 = gp.
  Hypothesis H8 : getr regs 8 = Z_to_bv 64 (mfa + 2 ^ 18).
  Hypothesis H9 : getr regs 9 = Z_to_bv 64 slot.
  Hypothesis H10 : getr regs 10 = Z_to_bv 64 slot.
  Hypothesis H18 : getr regs 18 = Z_to_bv 64 (2 ^ 18).
  Hypothesis H19 : getr regs 19 = Z_to_bv 64 RIz.
  Hypothesis H20 : getr regs 20 = s4x.
  Hypothesis H21 : getr regs 21 = s5x.
  Hypothesis Hsp : (2 ^ 32 + 4096 <= U sp /\ U sp + 16 <= 2 ^ 47)%Z.
  Hypothesis Hret : ret_ok ra.
  Hypothesis Hslot : (0 < slot < 2 ^ 64)%Z.
  Hypothesis Hmfa : (0 <= mfa <= 2 ^ 29)%Z.
  Hypothesis HRI : (AIMGHI <= RIz /\ RIz + 128 <= U sp - 48)%Z.
  Hypothesis HT : (U thr = T /\ 4096 <= T /\ T + 4096 <= U sp - 48 /\ T mod 8 = 0)%Z.
  Hypothesis HTRI : (T + 4096 <= RIz \/ RIz + 128 <= T)%Z.
  Hypothesis PH : poisonH BSEGS both_poison_tab M (Z_to_bv 64 slot) (Z_to_bv 64 (2 ^ 18)) (Z_to_bv 64 250) (Z_to_bv 64 0x4f5c4) (at_ sp (-48)) cpm midend thr0.
  #[local] Abbreviation E1 := (eam_1 M sp s4x s5x RIz slot mfa).
  #[local] Abbreviation E2 := (eam_2 M sp s4x s5x RIz slot mfa).
  #[local] Abbreviation E3 := (eam_3 M sp s4x s5x thr v72 v80 RIz slot mfa).
  Hypothesis GH : gctH BSEGS both_gct_tab E1 (at_ (at_ sp (-48)) (-16)) tp tsdp ctxw thr.
  Hypothesis SOK_g : store_ok BSEGS E1 (at_ (at_ sp (-48)) (-8)) 8 = true.
  Hypothesis R_72 : rdn BSEGS E2 (at_ thr 2872) 8 = Some (LE8 v72).
  Hypothesis R_80 : rdn BSEGS E2 (at_ thr 2880) 8 = Some (LE8 v80).
  Hypothesis SOK_T : store_ok BSEGS E2 thr 4096 = true.
  Hypothesis SOK_RI : store_ok BSEGS E2 (Z_to_bv 64 RIz) 128 = true.
  Hypothesis S_ra : rdn BSEGS E2 (at_ sp (-8)) 8 = Some (LE8 ra).
  Hypothesis S_s0 : rdn BSEGS E2 (at_ sp (-16)) 8 = Some (LE8 s0v).
  Hypothesis S_s1 : rdn BSEGS E2 (at_ sp (-24)) 8 = Some (LE8 s1v).
  Hypothesis S_s2 : rdn BSEGS E2 (at_ sp (-32)) 8 = Some (LE8 s2v).
  Hypothesis S_s3 : rdn BSEGS E2 (at_ sp (-40)) 8 = Some (LE8 s3v).

  Theorem efs_after_map_x :
    exists r, msteps BSEGS (mkst regs (0x4f5a8 : word) M rom) (mkst r ra E3 rom)
      /\ getr r 10 = Z_to_bv 64 1 /\ getr r 2 = sp /\ getr r 1 = ra
      /\ getr r 8 = s0v /\ getr r 9 = s1v /\ getr r 18 = s2v /\ getr r 19 = s3v /\ getr r 20 = s4x /\ getr r 21 = s5x /\ getr r 4 = tp /\ getr r 3 = gp
      /\ (forall i : reg, In i [22; 23; 24; 25; 26; 27] -> getr r i = getr regs i).
  Proof using S_s3 S_s2 S_s1 S_s0 S_ra SOK_RI SOK_T R_80 R_72 SOK_g GH PH HTRI HT HRI Hmfa Hslot Hret Hsp H21 H20 H19 H18 H10 H9 H8 H3 H4 H2 thr0 T cpm midend ctxw tsdp.
    pose proof (u64_range sp) as Hspr. destruct Hsp as [SP1 SP2]. destruct HT as (UT & T1 & T2 & T3).
    destruct (efs_mapped M rom sp slot regs H10 H9 H18 Hslot) as (r1 & RUN1 & A1 & A10 & A11 & A12 & AG1).
    assert (K1 : forall i : reg, ~ In i [1%bv; 10%bv; 11%bv; 12%bv; 14%bv] -> getr r1 i = getr regs i) by (intros i Hi; apply AG1; exact Hi).
    destruct (both_poison_shadow M rom (Z_to_bv 64 slot) (Z_to_bv 64 (2 ^ 18)) (Z_to_bv 64 250) (Z_to_bv 64 0x4f5c4) (at_ sp (-48)) cpm midend thr0 r1
                PH A1 ltac:(rewrite K1 by ((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); intros X; repeat (destruct X as [X|X]; [discriminate X|]); exact X); exact H2) A10 A11 A12)
      as (r2 & RUN2 & AG2).
    assert (K2 : forall i : reg, In i [2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 18%bv; 19%bv; 20%bv; 21%bv; 22%bv; 23%bv; 24%bv; 25%bv; 26%bv; 27%bv] -> getr r2 i = getr regs i).
    { intros i Hi. rewrite (AG2 i), K1; [reflexivity | |];
        cbn [In] in Hi; repeat (destruct Hi as [<-|Hi]; [(lazymatch goal with |- ?G => let G' := eval unfold poison_clob in G in change_no_check G' end); (lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); intros X; repeat (destruct X as [X|X]; [discriminate X|]); exact X|]); destruct Hi. }
    rewrite !K1 in RUN2 by ((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); intros X; repeat (destruct X as [X|X]; [discriminate X|]); exact X).
    rewrite H8, H9, H18, H19, H20, H21 in RUN2.
    change (wbytes (ps_frame M _ _ _ _ _ _ _ _) _ _) with E1 in RUN2.
    replace (Z_to_bv 64 0x4f5c4 : word) with (0x4f5c4%bv : word) in RUN2 by (apply bv_eq; reflexivity).
    pose proof (jal_4f5c4 r2 E1 rom) as RUNJ.
    assert (RETg : ret_ok (at_ ARB 0x4f5c8)) by (rewrite ARB_lit8 by lia; apply ret_ok_lit; [lia | reflexivity]).
    destruct (gts_run BSEGS ARB both_HGTS ARB_ok both_gct_tab E1 rom (regupd r2 1 (at_ ARB 0x4f5c8)) (at_ ARB 0x4f5c8) (at_ sp (-48)) tp tsdp ctxw thr
                both_gct_tab_ok both_GTRB GH SOK_g ltac:(first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ]) ltac:(lia) ltac:(lia) RETg
                ltac:(rewrite getr_same by (intros E; discriminate E); reflexivity)
                ltac:(rewrite getr_other by (intros E; discriminate E); rewrite (K2 2%bv) by ((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); am_tauto); exact H2)
                ltac:(rewrite getr_other by (intros E; discriminate E); rewrite (K2 4%bv) by ((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); am_tauto); exact H4))
      as (r3 & RUN3 & D10 & AG3).
    change (wbytes (wbytes E1 _ _) _ _) with E2 in RUN3.
    assert (K3 : forall i : reg, In i [2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 18%bv; 19%bv; 20%bv; 21%bv; 22%bv; 23%bv; 24%bv; 25%bv; 26%bv; 27%bv] -> getr r3 i = getr regs i).
    { intros i Hi. rewrite (AG3 i); [rewrite getr_other; [exact (K2 i Hi)|] |];
        cbn [In] in Hi; repeat (destruct Hi as [<-|Hi]; [first [intros X; discriminate X | (lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); intros X; repeat (destruct X as [X|X]; [discriminate X|]); exact X]|]); destruct Hi. }
    rewrite (ARB_lit8 0x4f5c8) in RUN3, RUNJ by lia.
    replace (Z_to_bv 64 0x4f5c8 : word) with (0x4f5c8%bv : word) in RUN3, RUNJ by (apply bv_eq; reflexivity).
    destruct (efs_stats E2 rom sp ra s0v s1v s2v s3v thr v72 v80 RIz mfa T r3
                ltac:(rewrite K3 by ((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); am_tauto); exact H2) ltac:(lia) Hret S_ra S_s0 S_s1 S_s2 S_s3 HRI (conj UT (conj T1 (conj T2 T3)))
                R_72 R_80 SOK_T SOK_RI D10
                ltac:(rewrite K3 by ((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); am_tauto); exact H8) ltac:(rewrite K3 by ((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); am_tauto); exact H18)
                ltac:(rewrite K3 by ((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); am_tauto); exact H19))
      as (r4 & RUN4 & P4).
    change (efs_ms E2 thr RIz mfa v72 v80) with E3 in RUN4.
    destruct P4 as (B10 & B2 & B1 & B8 & B9 & B18 & B19 & AG4).
    exists r4. split.
    - eapply msteps_trans; [exact RUN1|]. eapply msteps_trans; [exact RUN2|]. eapply msteps_trans; [exact RUNJ|].
      eapply msteps_trans; [exact RUN3|]. exact RUN4.
    - repeat (split; [assumption|]).
      split; [rewrite (AG4 20%bv) by ((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); intros X; repeat (destruct X as [X|X]; [discriminate X|]); exact X); rewrite (K3 20%bv) by ((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); am_tauto); exact H20|].
      split; [rewrite (AG4 21%bv) by ((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); intros X; repeat (destruct X as [X|X]; [discriminate X|]); exact X); rewrite (K3 21%bv) by ((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); am_tauto); exact H21|].
      split.
      + rewrite (AG4 4%bv) by ((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); intros X; repeat (destruct X as [X|X]; [discriminate X|]); exact X). rewrite (K3 4%bv) by ((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); am_tauto). exact H4.
      + split; [rewrite (AG4 3%bv) by ((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); intros X; repeat (destruct X as [X|X]; [discriminate X|]); exact X); rewrite (K3 3%bv) by ((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); am_tauto); exact H3|].
        intros i Hi. rewrite (AG4 i); [apply K3; cbn [In] in Hi |- *; am_tauto|].
        cbn [In] in Hi. repeat (destruct Hi as [<-|Hi]; [(lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); intros X; repeat (destruct X as [X|X]; [discriminate X|]); exact X|]). destruct Hi.
  Qed.
End EFSAFTERMAPX.
End FPGen.
End BoAllocM8sq.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtMemcpyBase OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8u OSSVerify.Proofs.glaze.binary_reflection.lib.HsAtom.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module BoAllocM8uq.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import Stdlib.Logic.FunctionalExtensionality.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.DivergeSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.SpinAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes.AgentNodes OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocSim OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys6.MhKSys OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsK OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys6.AsKSys OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsRtK OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtMemcpyBase OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtUnwindT OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoison OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtPoisonI OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM0 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMMemA.BoAllocMI OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM9i.BoAllocM8k OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8e.BoAllocM8p OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8e OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8s OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8u.BoAllocM8t OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8u BoAllocM8sq.
Import OSSVerify.glaze.binary_reflection.images.AsanUbsan.
Import ListNotations.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AmLia.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.HsAtom.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac am_inner ::= tryif noncert_goal_has_var then (Zify.zify; xlia zchecker) else first [ solve [noncert_clear_all; Zify.zify; xlia zchecker] | Zify.zify; xlia zchecker ].
#[local] Ltac lia ::= ha_first_lia.   (* [comment removed for export] *)
Open Scope bv_scope.
Local Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation BSEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).
#[local] Abbreviation U := bv_unsigned.

Section FPGen.
Context {fx : FPState}.

Section LIFTS.
  Variable Hd : word -> bool.
  Hypothesis HOFFSEG : H_off_segments BSEGS Hd.
  Hypothesis WX : wx_segs_nowrap BSEGS.

  Theorem efs_after_map_katwD_x :
    forall (A : list (Z * Z)) (regs : bvmap 5 word) (M rom : word -> option byte) (model : Model)
           (sp ra s0v s1v s2v s3v s4x s5x thr tp gp tsdp ctxw v72 v80 midend : word) (cpm : byte) (RIz slot mfa T thr0 : Z) (Qok Qf : config -> Prop),
    let SH := slot / 8 + 0x7fff8000 in
    getr regs 2 = at_ sp (-48) -> getr regs 4 = tp -> getr regs 3 = gp -> getr regs 8 = Z_to_bv 64 (mfa + 2 ^ 18) -> getr regs 9 = Z_to_bv 64 slot ->
    getr regs 10 = Z_to_bv 64 slot -> getr regs 18 = Z_to_bv 64 (2 ^ 18) -> getr regs 19 = Z_to_bv 64 RIz -> getr regs 20 = s4x -> getr regs 21 = s5x ->
    (2 ^ 32 + 4096 <= U sp /\ U sp + 16 <= 2 ^ 47) -> ret_ok ra -> 0 < slot < 2 ^ 63 -> 0 <= mfa <= 2 ^ 29 ->
    (AIMGHI <= RIz /\ RIz + 128 <= U sp - 112) ->
    (U thr = T /\ 4096 <= T /\ T + 4096 <= U sp - 112 /\ T mod 8 = 0) -> (T + 4096 <= RIz \/ RIz + 128 <= T) ->
    (T + 4096 <= SH \/ SH + 2 ^ 15 <= T) -> (RIz + 128 <= SH \/ SH + 2 ^ 15 <= RIz) -> (U sp <= SH \/ SH + 2 ^ 15 <= U sp - 112) ->
    poisonH BSEGS both_poison_tab M (Z_to_bv 64 slot) (Z_to_bv 64 (2 ^ 18)) (Z_to_bv 64 250) (Z_to_bv 64 0x4f5c4) (at_ sp (-48)) cpm midend thr0 ->
    gctH BSEGS both_gct_tab M (at_ (at_ sp (-48)) (-16)) tp tsdp ctxw thr ->
    (U (gt_tsd both_gct_tab) + 8 <= U sp - 112 /\ U tp - 80 <= U sp - 112 /\ U tsdp + 8 <= U sp - 112 /\ U ctxw + 160 <= U sp - 112) ->
    (U (gt_tsd both_gct_tab) + 8 <= SH \/ SH + 2 ^ 15 <= U (gt_tsd both_gct_tab)) ->
    (U tp - 80 <= SH \/ SH + 2 ^ 15 <= U tp - 88) -> (U tsdp + 8 <= SH \/ SH + 2 ^ 15 <= U tsdp) ->
    (U ctxw + 160 <= SH \/ SH + 2 ^ 15 <= U ctxw + 152) ->
    rdn BSEGS M (at_ thr 2872) 8 = Some (LE8 v72) -> rdn BSEGS M (at_ thr 2880) 8 = Some (LE8 v80) ->
    store_ok BSEGS M thr 4096 = true -> store_ok BSEGS M (Z_to_bv 64 RIz) 128 = true ->
    rdn BSEGS M (at_ sp (-8)) 8 = Some (LE8 ra) -> rdn BSEGS M (at_ sp (-16)) 8 = Some (LE8 s0v) -> rdn BSEGS M (at_ sp (-24)) 8 = Some (LE8 s1v) ->
    rdn BSEGS M (at_ sp (-32)) 8 = Some (LE8 s2v) -> rdn BSEGS M (at_ sp (-40)) 8 = Some (LE8 s3v) ->
    Forall (fun c => hid_off Hd c 8) (poison_cells both_poison_tab) ->
    hid_off Hd (U sp - 112) 112 -> hid_off Hd SH (2 ^ 15) ->
    hid_off Hd (U (gt_tsd both_gct_tab)) 8 -> hid_off Hd (U tp - 88) 8 -> hid_off Hd (U tsdp) 8 -> hid_off Hd (U ctxw + 152) 8 ->
    hid_off Hd T 4096 -> hid_off Hd RIz 128 ->
    m_halted model = None -> lazy_cover Hd (m_vm_lazy model) A -> A_wf A -> MInv A model ->
    (forall (r : bvmap 5 word) mdlm, same_but_materialized model mdlm -> MInv A mdlm ->
        getr r 10 = Z_to_bv 64 1 -> getr r 2 = sp -> getr r 1 = ra ->
        getr r 8 = s0v -> getr r 9 = s1v -> getr r 18 = s2v -> getr r 19 = s3v -> getr r 20 = s4x -> getr r 21 = s5x -> getr r 4 = tp -> getr r 3 = gp ->
        (forall i : reg, In i [22%bv; 23%bv; 24%bv; 25%bv; 26%bv; 27%bv] -> getr r i = getr regs i) ->
        katwD BSEGS (mkCfg (mkst r ra (eam_3 M sp s4x s5x thr v72 v80 RIz slot mfa) rom) mdlm) Qok Qf) ->
    katwD BSEGS (mkCfg (mkst regs (0x4f5a8 : word) M rom) model) Qok Qf.
  Proof using WX HOFFSEG.
    intros A regs M rom model sp ra s0v s1v s2v s3v s4x s5x thr tp gp tsdp ctxw v72 v80 midend cpm RIz slot mfa T thr0 Qok Qf SH
           H2 H4 H3 H8 H9 H10 H18 H19 H20 H21 Hsp Hret Hslot Hmfa HRI HT HTRI HTSH HRSH HSSH PH GH GB G1 G2 G3 G4 R72 R80 SOKT SOKRI
           Sra Ss0 Ss1 Ss2 Ss3 HDc HDf HDsh HD1 HD2 HD3 HD4 HDT HDRI HALT LC AWF MI CONT.
    pose proof (u64_range sp) as Hspr. destruct Hsp as [SP1 SP2].
    destruct HT as (UT & T1 & T2 & T3). destruct HRI as [RI1 RI2]. pose proof (u64_range thr) as Hthr.
    assert (SL : 0 <= slot < 2 ^ 63) by lia.
    subst SH.
    set (Mr := mrestrict Hd M).
    assert (Ufsp : U (at_ sp (-48)) = U sp - 48) by (first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ]).
    assert (HDf1 : hid_off Hd (U sp - 112) 64) by (eapply hid_off_sub; [exact HDf | lia | lia]).
    assert (PHr : poisonH BSEGS both_poison_tab Mr (Z_to_bv 64 slot) (Z_to_bv 64 (2 ^ 18)) (Z_to_bv 64 250) (Z_to_bv 64 0x4f5c4) (at_ sp (-48)) cpm midend thr0).
    { apply poisonH_mrestrict; [exact PH | exact HDc | rewrite Ufsp; replace (U sp - 48 - 64) with (U sp - 112) by lia; exact HDf1 |].
      destruct (psfill_shad slot SL) as (E1 & E2 & _). rewrite E1, E2. exact HDsh. }
    assert (GHr0 : gctH BSEGS both_gct_tab Mr (at_ (at_ sp (-48)) (-16)) tp tsdp ctxw thr).
    { apply gctH_mrestrict; [exact GH | exact HD1 | exact HD2 | exact HD3 | exact HD4 |].
      rewrite at_u by (rewrite Ufsp; lia). rewrite Ufsp. eapply hid_off_sub; [exact HDf | lia | lia]. }
    assert (GHr : gctH BSEGS both_gct_tab (eam_1 Mr sp s4x s5x RIz slot mfa) (at_ (at_ sp (-48)) (-16)) tp tsdp ctxw thr).
    { apply eam_1_gctH; [lia | exact SL | exact GHr0 | exact GB | exact G1 | exact G2 | exact G3 | exact G4]. }
    assert (OUT2 : forall (a : word) (k : nat), (U a + Z.of_nat k <= U sp - 112 \/ U sp - 48 <= U a) -> U a + Z.of_nat k <= 2 ^ 64 ->
               (U a + Z.of_nat k <= slot / 8 + 0x7fff8000 \/ slot / 8 + 0x7fff8000 + 2 ^ 15 <= U a) -> hid_off Hd (U a) (Z.of_nat k) ->
               rdn BSEGS (eam_2 Mr sp s4x s5x RIz slot mfa) a k = rdn BSEGS M a k).
    { intros a k B1 B0 B2 Hh. pose proof (u64_range a). rewrite <- (rdn_mrestrict BSEGS Hd M a k) by (first [lia | exact Hh]).
      apply rdn_ext; [lia|]. intros x Hx. apply eam_2_outside; [lia | exact SL | lia | lia]. }
    assert (SOKr : forall (a : word) (k : nat), U a + Z.of_nat k <= 2 ^ 64 -> hid_off Hd (U a) (Z.of_nat k) -> store_ok BSEGS M a k = true ->
               store_ok BSEGS (eam_2 Mr sp s4x s5x RIz slot mfa) a k = true).
    { intros a k B1 Hh SOK. eapply store_ok_mono; [apply eam_2_grows|]. (lazymatch goal with |- ?G => let G' := eval unfold Mr in G in change_no_check G' end). rewrite store_ok_mrestrict by (first [lia | exact Hh]). exact SOK. }
    assert (Ut : forall k, 0 <= k < 4096 -> U (at_ thr k) = T + k) by (intros k Hk; first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ]).
    assert (Us : forall k, -48 <= k < 0 -> U (at_ sp k) = U sp + k) by (intros k Hk; first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ]).
    destruct (efs_after_map_x Mr rom sp ra s0v s1v s2v s3v s4x s5x thr tp gp tsdp ctxw v72 v80 midend cpm RIz slot mfa T thr0 regs
                H2 H4 H3 H8 H9 H10 H18 H19 H20 H21 (conj SP1 SP2) Hret ltac:(lia) Hmfa ltac:(lia) ltac:(lia) HTRI PHr GHr)
      as (r & RUN & C10 & C2 & C1 & C8 & C9 & C18 & C19 & C20 & C21 & C4 & C3 & CX).
    - (* [comment removed for export] *)
      eapply store_ok_mono; [apply eam_1_grows|]. (lazymatch goal with |- ?G => let G' := eval unfold Mr in G in change_no_check G' end).
      rewrite store_ok_mrestrict; [ | rewrite at_u by (rewrite Ufsp; lia); rewrite Ufsp; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia
                                    | rewrite at_u by (rewrite Ufsp; lia); rewrite Ufsp; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); eapply hid_off_sub; [exact HDf | lia | lia]].
      destruct PH as [_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ P22 _ _].
      eapply (store_ok_sub BSEGS M (at_ (at_ sp (-48)) (-64)) _ 64); [rewrite at_u by (rewrite Ufsp; lia); rewrite Ufsp; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | exact P22 | rewrite !at_u by (rewrite ?Ufsp; lia); lia | rewrite !at_u by (rewrite ?Ufsp; lia); (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia].
    - rewrite OUT2; [exact R72 | rewrite Ut by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite Ut by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite Ut by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite Ut by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); eapply hid_off_sub; [exact HDT | lia | lia]].
    - rewrite OUT2; [exact R80 | rewrite Ut by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite Ut by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite Ut by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite Ut by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); eapply hid_off_sub; [exact HDT | lia | lia]].
    - apply SOKr; [lia | rewrite UT; exact HDT | exact SOKT].
    - apply SOKr; [first [ solve [ wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite u_Z2bv by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | rewrite u_Z2bv by lia; exact HDRI | exact SOKRI].
    - rewrite OUT2; [exact Sra | rewrite Us by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite Us by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite Us by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite Us by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); eapply hid_off_sub; [exact HDf | lia | lia]].
    - rewrite OUT2; [exact Ss0 | rewrite Us by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite Us by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite Us by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite Us by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); eapply hid_off_sub; [exact HDf | lia | lia]].
    - rewrite OUT2; [exact Ss1 | rewrite Us by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite Us by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite Us by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite Us by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); eapply hid_off_sub; [exact HDf | lia | lia]].
    - rewrite OUT2; [exact Ss2 | rewrite Us by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite Us by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite Us by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite Us by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); eapply hid_off_sub; [exact HDf | lia | lia]].
    - rewrite OUT2; [exact Ss3 | rewrite Us by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite Us by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite Us by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite Us by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); eapply hid_off_sub; [exact HDf | lia | lia]].
    - assert (HIDSAME : forall a : word, Hd a = true -> eam_3 M sp s4x s5x thr v72 v80 RIz slot mfa a = M a).
      { intros a Ha.
        pose proof (hid_true_off Hd a _ _ Ha HDf1) as Z1. pose proof (hid_true_off Hd a _ _ Ha HDsh) as Z2.
        pose proof (hid_true_off Hd a _ _ Ha HDT) as Z3. pose proof (hid_true_off Hd a _ _ Ha HDRI) as Z4.
        apply eam_3_outside; [clear - SP1; lia | exact SL | clear - UT T2 SP2 Hspr; lia | clear - RI1; lia | clear - RI2 SP2 Hspr; lia
                             | clear - Z1; lia | exact Z2 | clear - Z3 UT; lia | clear - Z4; lia]. }
      apply (katwD_msteps_acct BSEGS Hd HOFFSEG WX A (mkst regs (0x4f5a8 : word) M rom)
               (mkst r ra (mrestrict Hd (eam_3 M sp s4x s5x thr v72 v80 RIz slot mfa)) rom) model Qok Qf LC AWF MI HALT).
      { rewrite mk_restrict_mkst. fold Mr.
        rewrite <- (eam_3_mrestrict M sp s4x s5x thr v72 v80 RIz slot mfa ltac:(lia) SL Hd ltac:(lia) ltac:(lia) ltac:(lia) HDf1 HDsh ltac:(rewrite UT; exact HDT) HDRI).
        exact RUN. }
      intros mdlm MIm SBMm HC1. rewrite mk_unrestrict_mkst.
      replace (RiscvSemantics.ms_mem (mkst regs (0x4f5a8 : word) M rom)) with M by reflexivity.
      rewrite (mk_munrestrict_same Hd M _ HIDSAME).
      apply (CONT r mdlm SBMm MIm C10 C2 C1 C8 C9 C18 C19 C20 C21 C4 C3 CX).
  Qed.
End LIFTS.
End FPGen.
End BoAllocM8uq.
Module BoAllocM8w.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import Stdlib.Logic.FunctionalExtensionality.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.DivergeSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.SpinAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes.AgentNodes OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocSim OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys6.MhKSys OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsK OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys6.AsKSys OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsRtK OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM9i.BoAllocM8k OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8e.BoAllocM8p OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8e BoAllocM8r OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8u.
Import OSSVerify.glaze.binary_reflection.images.AsanUbsan.
Import ListNotations.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation BSEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).
#[local] Abbreviation U := bv_unsigned.

Section FPGen.
Context {fx : FPState}.

Section LIFTS.
  Variable Hd : word -> bool.
  Hypothesis HOFFSEG : H_off_segments BSEGS Hd.
  Hypothesis WX : wx_segs_nowrap BSEGS.

  (* [comment removed for export] *)
  Lemma lift_katD_mem : forall (A : list (Z * Z)) regs (pc : word) r (pc' : word) (M M' rom : word -> option byte) (model : Model) (Q : config -> Prop),
    msteps BSEGS (mkst regs pc (mrestrict Hd M) rom) (mkst r pc' (mrestrict Hd M') rom) ->
    (forall a : word, Hd a = true -> M' a = M a) ->
    m_halted model = None -> lazy_cover Hd (m_vm_lazy model) A -> A_wf A -> MInv A model ->
    (forall mdlm, same_but_materialized model mdlm -> MInv A mdlm -> katD BSEGS (mkCfg (mkst r pc' M' rom) mdlm) Q) ->
    katD BSEGS (mkCfg (mkst regs pc M rom) model) Q.
  Proof using WX HOFFSEG.
    intros A regs pc r pc' M M' rom model Q RUN SAME HALT LC AWF MI CONT.
    apply (katD_msteps_acct BSEGS Hd HOFFSEG WX A (mkst regs pc M rom) (mkst r pc' (mrestrict Hd M') rom) model Q LC AWF MI HALT).
    { rewrite mk_restrict_mkst. exact RUN. }
    intros mdlm MIm SBMm HC1. rewrite mk_unrestrict_mkst.
    replace (RiscvSemantics.ms_mem (mkst regs pc M rom)) with M by reflexivity.
    rewrite (mk_munrestrict_same Hd M M' SAME). exact (CONT mdlm SBMm MIm).
  Qed.

  Lemma lift_katwD_mem : forall (A : list (Z * Z)) regs (pc : word) r (pc' : word) (M M' rom : word -> option byte) (model : Model) (Qok Qf : config -> Prop),
    msteps BSEGS (mkst regs pc (mrestrict Hd M) rom) (mkst r pc' (mrestrict Hd M') rom) ->
    (forall a : word, Hd a = true -> M' a = M a) ->
    m_halted model = None -> lazy_cover Hd (m_vm_lazy model) A -> A_wf A -> MInv A model ->
    (forall mdlm, same_but_materialized model mdlm -> MInv A mdlm -> katwD BSEGS (mkCfg (mkst r pc' M' rom) mdlm) Qok Qf) ->
    katwD BSEGS (mkCfg (mkst regs pc M rom) model) Qok Qf.
  Proof using WX HOFFSEG.
    intros A regs pc r pc' M M' rom model Qok Qf RUN SAME HALT LC AWF MI CONT.
    apply (katwD_msteps_acct BSEGS Hd HOFFSEG WX A (mkst regs pc M rom) (mkst r pc' (mrestrict Hd M') rom) model Qok Qf LC AWF MI HALT).
    { rewrite mk_restrict_mkst. exact RUN. }
    intros mdlm MIm SBMm HC1. rewrite mk_unrestrict_mkst.
    replace (RiscvSemantics.ms_mem (mkst regs pc M rom)) with M by reflexivity.
    rewrite (mk_munrestrict_same Hd M M' SAME). exact (CONT mdlm SBMm MIm).
  Qed.

  (* [comment removed for export] *)
  Lemma sp_rd_mrestrict : forall (M : word -> option byte) (sp : word) (fr k : Z) v,
    fr <= U sp -> U sp <= 2 ^ 64 - 16 -> hid_off Hd (U sp - fr) fr -> - fr <= k -> k + 8 <= 0 ->
    rdn BSEGS M (at_ sp k) 8 = Some v -> rdn BSEGS (mrestrict Hd M) (at_ sp k) 8 = Some v.
  Proof using.
    intros M sp fr k v F1 F2 Hh K0 K1 Hr.
    rewrite rdn_mrestrict; [exact Hr | first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); eapply hid_off_sub; [exact Hh | lia | lia]].
  Qed.

  Theorem efs_fail_katD :
    forall (A : list (Z * Z)) (regs : bvmap 5 word) (M rom : word -> option byte) (model : Model) (sp ra s0v s1v s2v s3v : word) (Q : config -> Prop),
    getr regs 2 = at_ sp (-48) -> ret_ok ra -> getr regs 10 = Z_to_bv 64 0 ->
    (48 <= U sp /\ U sp <= 2 ^ 64 - 16) ->
    rdn BSEGS M (at_ sp (-8)) 8 = Some (LE8 ra) -> rdn BSEGS M (at_ sp (-16)) 8 = Some (LE8 s0v) -> rdn BSEGS M (at_ sp (-24)) 8 = Some (LE8 s1v) ->
    rdn BSEGS M (at_ sp (-32)) 8 = Some (LE8 s2v) -> rdn BSEGS M (at_ sp (-40)) 8 = Some (LE8 s3v) ->
    hid_off Hd (U sp - 48) 48 ->
    m_halted model = None -> lazy_cover Hd (m_vm_lazy model) A -> A_wf A -> MInv A model ->
    (forall (r : bvmap 5 word) mdlm, same_but_materialized model mdlm -> MInv A mdlm -> efs_post sp ra s0v s1v s2v s3v 0 regs r ->
        katD BSEGS (mkCfg (mkst r ra M rom) mdlm) Q) ->
    katD BSEGS (mkCfg (mkst regs (0x4f5a8 : word) M rom) model) Q.
  Proof using WX HOFFSEG.
    intros A regs M rom model sp ra s0v s1v s2v s3v Q H2 Hret H10 [SP1 SP2] Sra Ss0 Ss1 Ss2 Ss3 HDf HALT LC AWF MI CONT.
    destruct (efs_fail (mrestrict Hd M) rom sp ra s0v s1v s2v s3v regs H2 Hret
                (sp_rd_mrestrict M sp 48 (-8) _ SP1 SP2 HDf ltac:(lia) ltac:(lia) Sra) (sp_rd_mrestrict M sp 48 (-16) _ SP1 SP2 HDf ltac:(lia) ltac:(lia) Ss0)
                (sp_rd_mrestrict M sp 48 (-24) _ SP1 SP2 HDf ltac:(lia) ltac:(lia) Ss1) (sp_rd_mrestrict M sp 48 (-32) _ SP1 SP2 HDf ltac:(lia) ltac:(lia) Ss2)
                (sp_rd_mrestrict M sp 48 (-40) _ SP1 SP2 HDf ltac:(lia) ltac:(lia) Ss3) H10) as (r & RUN & POST).
    apply (lift_katD_mem A regs (0x4f5a8 : word) r ra M M rom model Q RUN (fun _ _ => eq_refl) HALT LC AWF MI).
    intros mdlm SBM MIm. exact (CONT r mdlm SBM MIm POST).
  Qed.

  Theorem pf_fail_efs_katD :
    forall (A : list (Z * Z)) (regs : bvmap 5 word) (M rom : word -> option byte) (model : Model) (sp ra s0v s1v s2v s3v s4v s5v s6v : word) (Q : config -> Prop),
    getr regs 2 = at_ sp (-64) -> getr regs 10 = Z_to_bv 64 0 -> ret_ok ra ->
    (64 <= U sp /\ U sp <= 2 ^ 64 - 16) ->
    rdn BSEGS M (at_ sp (-8)) 8 = Some (LE8 ra) -> rdn BSEGS M (at_ sp (-16)) 8 = Some (LE8 s0v) -> rdn BSEGS M (at_ sp (-24)) 8 = Some (LE8 s1v) ->
    rdn BSEGS M (at_ sp (-32)) 8 = Some (LE8 s2v) -> rdn BSEGS M (at_ sp (-40)) 8 = Some (LE8 s3v) -> rdn BSEGS M (at_ sp (-48)) 8 = Some (LE8 s4v) ->
    rdn BSEGS M (at_ sp (-56)) 8 = Some (LE8 s5v) -> rdn BSEGS M (at_ sp (-64)) 8 = Some (LE8 s6v) ->
    hid_off Hd (U sp - 64) 64 ->
    m_halted model = None -> lazy_cover Hd (m_vm_lazy model) A -> A_wf A -> MInv A model ->
    (forall (r : bvmap 5 word) mdlm, same_but_materialized model mdlm -> MInv A mdlm -> pf_post0 sp ra s0v s1v s2v s3v s4v s5v s6v regs r ->
        katD BSEGS (mkCfg (mkst r ra M rom) mdlm) Q) ->
    katD BSEGS (mkCfg (mkst regs (0x519d8 : word) M rom) model) Q.
  Proof using WX HOFFSEG.
    intros A regs M rom model sp ra s0v s1v s2v s3v s4v s5v s6v Q H2 H10 Hret [SP1 SP2] Sra Ss0 Ss1 Ss2 Ss3 Ss4 Ss5 Ss6 HDf HALT LC AWF MI CONT.
    destruct (pf_fail_efs (mrestrict Hd M) rom sp ra s0v s1v s2v s3v s4v s5v s6v regs H2 H10 Hret
                (sp_rd_mrestrict M sp 64 (-8) _ SP1 SP2 HDf ltac:(lia) ltac:(lia) Sra) (sp_rd_mrestrict M sp 64 (-16) _ SP1 SP2 HDf ltac:(lia) ltac:(lia) Ss0)
                (sp_rd_mrestrict M sp 64 (-24) _ SP1 SP2 HDf ltac:(lia) ltac:(lia) Ss1) (sp_rd_mrestrict M sp 64 (-32) _ SP1 SP2 HDf ltac:(lia) ltac:(lia) Ss2)
                (sp_rd_mrestrict M sp 64 (-40) _ SP1 SP2 HDf ltac:(lia) ltac:(lia) Ss3) (sp_rd_mrestrict M sp 64 (-48) _ SP1 SP2 HDf ltac:(lia) ltac:(lia) Ss4)
                (sp_rd_mrestrict M sp 64 (-56) _ SP1 SP2 HDf ltac:(lia) ltac:(lia) Ss5) (sp_rd_mrestrict M sp 64 (-64) _ SP1 SP2 HDf ltac:(lia) ltac:(lia) Ss6))
      as (r & RUN & POST).
    apply (lift_katD_mem A regs (0x519d8 : word) r ra M M rom model Q RUN (fun _ _ => eq_refl) HALT LC AWF MI).
    intros mdlm SBM MIm. exact (CONT r mdlm SBM MIm POST).
  Qed.

  Theorem pf_fail_map_katD :
    forall (A : list (Z * Z)) (regs : bvmap 5 word) (M rom : word -> option byte) (model : Model) (sp ra s0v s1v s2v s3v s4v s5v s6v : word) (Q : config -> Prop),
    getr regs 2 = at_ sp (-64) -> getr regs 10 = Z_to_bv 64 0 -> ret_ok ra ->
    (64 <= U sp /\ U sp <= 2 ^ 64 - 16) ->
    rdn BSEGS M (at_ sp (-8)) 8 = Some (LE8 ra) -> rdn BSEGS M (at_ sp (-16)) 8 = Some (LE8 s0v) -> rdn BSEGS M (at_ sp (-24)) 8 = Some (LE8 s1v) ->
    rdn BSEGS M (at_ sp (-32)) 8 = Some (LE8 s2v) -> rdn BSEGS M (at_ sp (-40)) 8 = Some (LE8 s3v) -> rdn BSEGS M (at_ sp (-48)) 8 = Some (LE8 s4v) ->
    rdn BSEGS M (at_ sp (-56)) 8 = Some (LE8 s5v) -> rdn BSEGS M (at_ sp (-64)) 8 = Some (LE8 s6v) ->
    hid_off Hd (U sp - 64) 64 ->
    m_halted model = None -> lazy_cover Hd (m_vm_lazy model) A -> A_wf A -> MInv A model ->
    (forall (r : bvmap 5 word) mdlm, same_but_materialized model mdlm -> MInv A mdlm -> pf_post0 sp ra s0v s1v s2v s3v s4v s5v s6v regs r ->
        katD BSEGS (mkCfg (mkst r ra M rom) mdlm) Q) ->
    katD BSEGS (mkCfg (mkst regs (0x51964 : word) M rom) model) Q.
  Proof using WX HOFFSEG.
    intros A regs M rom model sp ra s0v s1v s2v s3v s4v s5v s6v Q H2 H10 Hret [SP1 SP2] Sra Ss0 Ss1 Ss2 Ss3 Ss4 Ss5 Ss6 HDf HALT LC AWF MI CONT.
    destruct (pf_fail_map (mrestrict Hd M) rom sp ra s0v s1v s2v s3v s4v s5v s6v regs H2 H10 Hret
                (sp_rd_mrestrict M sp 64 (-8) _ SP1 SP2 HDf ltac:(lia) ltac:(lia) Sra) (sp_rd_mrestrict M sp 64 (-16) _ SP1 SP2 HDf ltac:(lia) ltac:(lia) Ss0)
                (sp_rd_mrestrict M sp 64 (-24) _ SP1 SP2 HDf ltac:(lia) ltac:(lia) Ss1) (sp_rd_mrestrict M sp 64 (-32) _ SP1 SP2 HDf ltac:(lia) ltac:(lia) Ss2)
                (sp_rd_mrestrict M sp 64 (-40) _ SP1 SP2 HDf ltac:(lia) ltac:(lia) Ss3) (sp_rd_mrestrict M sp 64 (-48) _ SP1 SP2 HDf ltac:(lia) ltac:(lia) Ss4)
                (sp_rd_mrestrict M sp 64 (-56) _ SP1 SP2 HDf ltac:(lia) ltac:(lia) Ss5) (sp_rd_mrestrict M sp 64 (-64) _ SP1 SP2 HDf ltac:(lia) ltac:(lia) Ss6))
      as (r & RUN & POST).
    apply (lift_katD_mem A regs (0x51964 : word) r ra M M rom model Q RUN (fun _ _ => eq_refl) HALT LC AWF MI).
    intros mdlm SBM MIm. exact (CONT r mdlm SBM MIm POST).
  Qed.

  Theorem efs_enough_katwD :
    forall (A : list (Z * Z)) (regs : bvmap 5 word) (mem rom : word -> option byte) (model : Model) (sp ra s0v s1v s2v s3v : word) (RIz tot mfa : Z)
           (Qok Qf : config -> Prop),
    getr regs 1 = ra -> getr regs 2 = sp -> getr regs 11 = Z_to_bv 64 RIz -> getr regs 13 = Z_to_bv 64 tot ->
    getr regs 8 = s0v -> getr regs 9 = s1v -> getr regs 18 = s2v -> getr regs 19 = s3v ->
    (2 ^ 24 <= U sp /\ U sp + 16 <= 2 ^ 47) -> ret_ok ra -> (0 <= tot /\ 4 * tot <= 2 ^ 29) -> (0 <= mfa <= 2 ^ 29 /\ mfa mod 2 ^ 18 = 0) ->
    (AIMGHI <= RIz /\ RIz + 128 <= U sp - 48) ->
    store_ok BSEGS mem (at_ sp (-48)) 48 = true ->
    rdn BSEGS mem (Z_to_bv 64 (RIz + 24)) 8 = Some (LE8 (Z_to_bv 64 mfa)) -> 4 * tot <= mfa ->
    hid_off Hd (U sp - 48) 48 -> hid_off Hd (RIz + 24) 8 ->
    m_halted model = None -> lazy_cover Hd (m_vm_lazy model) A -> A_wf A -> MInv A model ->
    (forall (r : bvmap 5 word) mdlm, same_but_materialized model mdlm -> MInv A mdlm -> efs_post sp ra s0v s1v s2v s3v 1 regs r ->
        katwD BSEGS (mkCfg (mkst r ra (efs_m0 mem sp ra s0v s1v s2v s3v) rom) mdlm) Qok Qf) ->
    katwD BSEGS (mkCfg (mkst regs (0x4f508 : word) mem rom) model) Qok Qf.
  Proof using WX HOFFSEG.
    intros A regs mem rom model sp ra s0v s1v s2v s3v RIz tot mfa Qok Qf H1 H2 H11 H13 H8 H9 H18 H19 Hsp Hret Htot Hmfa HRI Hstk Rmfa Hen HDf HDm
           HALT LC AWF MI CONT.
    pose proof (u64_range sp) as Hspr. destruct Hsp as [SP1 SP2]. destruct HRI as [RI1 RI2].
    destruct (efs_enough (mrestrict Hd mem) rom sp ra s0v s1v s2v s3v RIz tot mfa regs H1 H2 H11 H13 H8 H9 H18 H19 (conj SP1 SP2) Hret Htot Hmfa (conj RI1 RI2))
      as (r & RUN & POST).
    - rewrite store_ok_mrestrict; [exact Hstk | first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); eapply hid_off_sub; [exact HDf | lia | lia]].
    - rewrite rdn_mrestrict; [exact Rmfa | first [ solve [ wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite u_Z2bv by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | rewrite u_Z2bv by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); exact HDm].
    - exact Hen.
    - rewrite efs_m0_mrestrict in RUN by (first [lia | exact HDf]).
      apply (lift_katwD_mem A regs (0x4f508 : word) r ra mem (efs_m0 mem sp ra s0v s1v s2v s3v) rom model Qok Qf RUN); [ | exact HALT | exact LC | exact AWF | exact MI |].
      + intros a Ha. pose proof (hid_true_off Hd a _ _ Ha HDf) as Z1. apply efs_m0_outside; lia.
      + intros mdlm SBM MIm. exact (CONT r mdlm SBM MIm POST).
  Qed.
End LIFTS.
End FPGen.
End BoAllocM8w.
Module BoAllocM8x.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocSim.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtUnwindT OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoison OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtPoisonI OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8m OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8e BoAllocM8r OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8u.BoAllocM8t OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8u.
Import OSSVerify.glaze.binary_reflection.images.AsanUbsan.
Import ListNotations.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation BSEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).
#[local] Abbreviation U := bv_unsigned.


(* [comment removed for export] *)
Lemma poisonH_keep_P : forall segs t (mem M' : word -> option byte) (addr size value ra sp : word) cpm midend thr (P : Z -> Prop),
  poisonH segs t mem addr size value ra sp cpm midend thr ->
  (forall x : word, P (U x) -> M' x = mem x) -> mem_grows mem M' ->
  Forall (fun c => forall z, c <= z < c + 8 -> P z) (poison_cells t) ->
  poisonH segs t M' addr size value ra sp cpm midend thr.
Proof.
  intros segs t mem M' addr size value ra sp cpm midend thr P PH HM GR Hc.
  destruct PH as [P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 P11 P12 P13 P14 P15 P16 P17 P18 P21 P22 P23 P24].
  pose proof (u64_range sp) as Hsp.
  pose proof P15 as CB. unfold poison_cells in Hc, CB.
  fc Hc h1. fc Hc h2. fc Hc h3. fc Hc h4. fc Hc h5. fc Hc h6. fc Hc h7. fc Hc h8. fc Hc h9. fc Hc h10. fc Hc h11. fc Hc h12. fc Hc h13. fc Hc h14.
  fc CB b1. fc CB b2. fc CB b3. fc CB b4. fc CB b5. fc CB b6. fc CB b7. fc CB b8. fc CB b9. fc CB b10. fc CB b11. fc CB b12. fc CB b13. fc CB b14.
  cbv beta in *.
  assert (KP : forall (c : Z) (k : nat) v, 0 <= c -> c + 8 <= U sp - 64 -> Z.of_nat k <= 8 -> (forall z, c <= z < c + 8 -> P z) ->
             rdn segs mem (Z_to_bv 64 c) k = Some v -> rdn segs M' (Z_to_bv 64 c) k = Some v).
  { intros c k v C0 C1 K8 HP Hr. rewrite <- Hr. apply rdn_ext; [first [ solve [ wd_unorm1; wd_zofnat; lia ] | rewrite u_Z2bv by lia; lia ]|].
    intros x Hx. rewrite u_Z2bv in Hx by lia. apply HM, HP. lia. }
  split; try assumption.
  - apply KP; [lia | lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | assumption | assumption].
  - apply KP; [lia | lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | assumption | assumption].
  - apply KP; [lia | lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | assumption | assumption].
  - apply KP; [lia | lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | assumption | assumption].
  - apply KP; [lia | lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | assumption | assumption].
  - apply KP; [lia | lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | assumption | assumption].
  - apply KP; [lia | lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | assumption | assumption].
  - apply KP; [lia | lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | assumption | assumption].
  - apply KP; [lia | lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | assumption | assumption].
  - apply KP; [lia | lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | assumption | assumption].
  - intros Hv. destruct (P13 Hv) as [R C]. split; [|exact C]. apply KP; [lia | lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | assumption | assumption].
  - intros Hv. destruct (P14 Hv) as (R1 & R2 & L & T1 & T2). repeat split; try assumption.
    + apply KP; [lia | lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | assumption | assumption].
    + apply KP; [lia | lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | assumption | assumption].
  - eapply store_ok_mono; [exact GR | exact P22].
  - eapply store_ok_mono; [exact GR | exact P23].
Qed.

Lemma zfill_grows' : forall (a n : word) (Mb : word -> option byte), mem_grows Mb (zfill a n Mb).
Proof. intros a n Mb x Hx. (lazymatch goal with |- ?G => let G' := eval unfold zfill, zmem in G in change_no_check G' end). destruct (_ && _)%bool; [discriminate | exact Hx]. Qed.

(* [comment removed for export] *)
Definition efs_mr (mem : word -> option byte) (sp ra s0v s1v s2v s3v s4v s5v : word) (RIz slot mfa PGP : Z) : word -> option byte :=
  wbytes (zfill (Z_to_bv 64 slot) (Z_to_bv 64 (2 ^ 18))
            (mfi_m1 (efs_m0 mem sp ra s0v s1v s2v s3v) (at_ sp (-48)) (Z_to_bv 64 0x4f5a8) (Z_to_bv 64 (mfa + 2 ^ 18)) (Z_to_bv 64 slot) (Z_to_bv 64 (2 ^ 18))
                    (Z_to_bv 64 RIz) s4v s5v (Z_to_bv 64 slot) (Z_to_bv 64 (2 ^ 18)) (Z_to_bv 64 0x19778) PGP))
         (at_ sp (-132)) (word_to_le_bytes 4 (Z_to_bv 64 0xffffffffaaaaaaaa)).

Section EFSMR.
  Variables (mem : word -> option byte) (sp ra s0v s1v s2v s3v s4v s5v : word) (RIz slot mfa PGP : Z).
  Hypothesis Hsp : 2 ^ 24 + 48 <= U sp /\ U sp + 16 <= 2 ^ 47.
  Hypothesis Hslot : 0 <= slot /\ slot + 2 ^ 18 < 2 ^ 63.
  #[local] Abbreviation MR := (efs_mr mem sp ra s0v s1v s2v s3v s4v s5v RIz slot mfa PGP).
  #[local] Abbreviation M0 := (efs_m0 mem sp ra s0v s1v s2v s3v).

  Lemma efs_mr_outside0 : forall x : word, (U x < U sp - 448 \/ U sp - 48 <= U x) -> (U x < slot \/ slot + 2 ^ 18 <= U x) -> MR x = M0 x.
  Proof using Hslot Hsp.
    intros x X1 X2. pose proof (u64_range sp) as Hspr. destruct Hsp as [SP1 SP2]. destruct Hslot as [SL1 SL2]. (lazymatch goal with |- ?G => let G' := eval unfold efs_mr in G in change_no_check G' end).
    rewrite MemsetLibF.MemSplit.wbytes_outside; [ | rewrite length_N_to_le_bytes, at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite length_N_to_le_bytes, at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia].
    rewrite zfill_out by (first [ solve [ wd_unorm1; wd_zofnat; lia ] | rewrite !u_Z2bv by lia; lia ]).
    apply mfi_m1_outside; first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite ?at_u by lia; lia ].
  Qed.
  Lemma efs_mr_outside : forall x : word, (U x < U sp - 448 \/ U sp <= U x) -> (U x < slot \/ slot + 2 ^ 18 <= U x) -> MR x = mem x.
  Proof using Hslot Hsp.
    intros x X1 X2. destruct Hsp as [SP1 SP2]. rewrite efs_mr_outside0 by lia. apply efs_m0_outside; lia.
  Qed.
  Lemma efs_mr_grows : mem_grows mem MR.
  Proof using.
    (lazymatch goal with |- ?G => let G' := eval unfold efs_mr in G in change_no_check G' end). eapply mem_grows_trans; [|apply wbytes_grows]. eapply mem_grows_trans; [|apply zfill_grows'].
    eapply mem_grows_trans; [apply efs_m0_grows | apply mfi_m1_grows].
  Qed.
  (* [comment removed for export] *)
  Lemma efs_mr_slots : forall (k : Z) (v : word), (slot + 2 ^ 18 <= U sp - 448 \/ U sp <= slot) ->
    In (k, v) [(-8, ra); (-16, s0v); (-24, s1v); (-32, s2v); (-40, s3v)] -> rdn BSEGS MR (at_ sp k) 8 = Some (LE8 v).
  Proof using Hslot Hsp.
    intros k v HS Hin. pose proof (u64_range sp) as Hspr. destruct Hsp as [SP1 SP2].
    assert (K : -40 <= k <= -8) by (cbn [In] in Hin; repeat (destruct Hin as [E|Hin]; [injection E as <- <-; lia|]); destruct Hin).
    rewrite (rdn_ext BSEGS 8 MR M0 (at_ sp k)); [ | first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | intros x Hx; rewrite at_u in Hx by lia; cbn in Hx; apply efs_mr_outside0; lia].
    (lazymatch goal with |- ?G => let G' := eval unfold efs_m0 in G in change_no_check G' end). cbn [In] in Hin.
    repeat (destruct Hin as [E|Hin]; [injection E as <- <-; rd8_chain|]). destruct Hin.
  Qed.
End EFSMR.
End BoAllocM8x.
Module BoAllocM8xp.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocSim.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8m OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8e.BoAllocM8p BoAllocM8r BoAllocM8x.
Import OSSVerify.glaze.binary_reflection.images.AsanUbsan.
Import ListNotations.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation BSEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).
#[local] Abbreviation U := bv_unsigned.

Lemma pf_slots_ext : forall (MM mem : word -> option byte) (sp ra s0v s1v s2v s3v s4v s5v s6v : word) (k : Z) (v : word),
  64 <= U sp -> U sp + 16 <= 2 ^ 64 ->
  (forall x : word, U sp - 64 <= U x < U sp -> MM x = pf_m0 mem sp ra s0v s1v s2v s3v s4v s5v s6v x) ->
  In (k, v) [(-8, ra); (-16, s0v); (-24, s1v); (-32, s2v); (-40, s3v); (-48, s4v); (-56, s5v); (-64, s6v)] ->
  rdn BSEGS MM (at_ sp k) 8 = Some (LE8 v).
Proof.
  intros MM mem sp ra s0v s1v s2v s3v s4v s5v s6v k v SP1 SP2 HM Hin. pose proof (u64_range sp) as Hspr.
  assert (K : -64 <= k <= -8) by (cbn [In] in Hin; repeat (destruct Hin as [E|Hin]; [injection E as <- <-; lia|]); destruct Hin).
  rewrite (rdn_ext BSEGS 8 MM (pf_m0 mem sp ra s0v s1v s2v s3v s4v s5v s6v) (at_ sp k));
    [ | first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | intros x Hx; rewrite at_u in Hx by lia; cbn in Hx; apply HM; lia].
  (lazymatch goal with |- ?G => let G' := eval unfold pf_m0 in G in change_no_check G' end). cbn [In] in Hin.
  repeat (destruct Hin as [E|Hin]; [injection E as <- <-; rd8_chain|]). destruct Hin.
Qed.

Definition pf_mr (mem : word -> option byte) (sp ra s0v s1v s2v s3v s4v s5v s6v stats : word) (RIz SPB c mu PGP : Z) : word -> option byte :=
  wbytes (zfill (Z_to_bv 64 (SPB + c * 2 ^ 32 + mu)) (Z_to_bv 64 (2 ^ 18))
            (mfi_m1 (pf_m0 mem sp ra s0v s1v s2v s3v s4v s5v s6v) (at_ sp (-64)) (Z_to_bv 64 0x51964) (Z_to_bv 64 RIz) stats (Z_to_bv 64 (SPB + c * 2 ^ 32))
                    (Z_to_bv 64 (2 ^ 18)) (Z_to_bv 64 (SPB + c * 2 ^ 32 + mu)) (Z_to_bv 64 (csize c)) (Z_to_bv 64 (SPB + c * 2 ^ 32 + mu)) (Z_to_bv 64 (2 ^ 18))
                    (Z_to_bv 64 0x178e4) PGP))
         (at_ sp (-148)) (word_to_le_bytes 4 (Z_to_bv 64 0xffffffffaaaaaaaa)).

Section PFMR.
  Variables (mem : word -> option byte) (sp ra s0v s1v s2v s3v s4v s5v s6v stats : word) (RIz SPB c mu PGP : Z).
  Hypothesis Hsp : 2 ^ 24 + 64 <= U sp /\ U sp + 16 <= 2 ^ 47.
  #[local] Abbreviation slot := (SPB + c * 2 ^ 32 + mu).
  Hypothesis Hslot : 0 <= slot /\ slot + 2 ^ 18 < 2 ^ 63.
  #[local] Abbreviation MR := (pf_mr mem sp ra s0v s1v s2v s3v s4v s5v s6v stats RIz SPB c mu PGP).
  #[local] Abbreviation M0 := (pf_m0 mem sp ra s0v s1v s2v s3v s4v s5v s6v).

  Lemma pf_mr_outside0 : forall x : word, (U x < U sp - 464 \/ U sp - 64 <= U x) -> (U x < slot \/ slot + 2 ^ 18 <= U x) -> MR x = M0 x.
  Proof using Hslot Hsp.
    intros x X1 X2. pose proof (u64_range sp) as Hspr. destruct Hsp as [SP1 SP2]. destruct Hslot as [SL1 SL2]. (lazymatch goal with |- ?G => let G' := eval unfold pf_mr in G in change_no_check G' end).
    rewrite MemsetLibF.MemSplit.wbytes_outside; [ | rewrite length_N_to_le_bytes, at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite length_N_to_le_bytes, at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia].
    rewrite zfill_out by (first [ solve [ wd_unorm1; wd_zofnat; lia ] | rewrite !u_Z2bv by lia; lia ]).
    apply mfi_m1_outside; first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite ?at_u by lia; lia ].
  Qed.
  Lemma pf_mr_outside : forall x : word, (U x < U sp - 464 \/ U sp <= U x) -> (U x < slot \/ slot + 2 ^ 18 <= U x) -> MR x = mem x.
  Proof using Hslot Hsp.
    intros x X1 X2. destruct Hsp as [SP1 SP2]. rewrite pf_mr_outside0 by lia. apply pf_m0_outside; lia.
  Qed.
  Lemma pf_mr_grows : mem_grows mem MR.
  Proof using.
    (lazymatch goal with |- ?G => let G' := eval unfold pf_mr in G in change_no_check G' end). eapply mem_grows_trans; [|apply wbytes_grows]. eapply mem_grows_trans; [|apply zfill_grows'].
    eapply mem_grows_trans; [apply pf_m0_grows | apply mfi_m1_grows].
  Qed.
  Lemma pf_mr_slots : forall (k : Z) (v : word), (slot + 2 ^ 18 <= U sp - 464 \/ U sp <= slot) ->
    In (k, v) [(-8, ra); (-16, s0v); (-24, s1v); (-32, s2v); (-40, s3v); (-48, s4v); (-56, s5v); (-64, s6v)] -> rdn BSEGS MR (at_ sp k) 8 = Some (LE8 v).
  Proof using Hslot Hsp.
    intros k v HS Hin. destruct Hsp as [SP1 SP2].
    apply (pf_slots_ext MR mem sp ra s0v s1v s2v s3v s4v s5v s6v k v ltac:(lia) ltac:(lia)); [|exact Hin].
    intros x Hx. apply pf_mr_outside0; lia.
  Qed.
End PFMR.
End BoAllocM8xp.
Module BoAllocM8y.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import Stdlib.Logic.FunctionalExtensionality.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.DivergeSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.SpinAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes.AgentNodes OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocSim OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys6.MhKSys OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsK OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys6.AsKSys OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsRtK OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtUnwindT OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoison OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtPoisonI OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMMemA.BoAllocMI OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8m OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM9i.BoAllocM8k OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8e BoAllocM8r OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8s OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8u.BoAllocM8t OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8u BoAllocM8w BoAllocM8x.
Import OSSVerify.glaze.binary_reflection.images.AsanUbsan.
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

#[local] Abbreviation BSEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).
#[local] Abbreviation U := bv_unsigned.

Section FPGen.
Context {fx : FPState}.

(* [comment removed for export] *)
Lemma efs_slots_ext : forall (MM mem : word -> option byte) (sp ra s0v s1v s2v s3v : word) (k : Z) (v : word),
  48 <= U sp -> U sp + 16 <= 2 ^ 64 ->
  (forall x : word, U sp - 48 <= U x < U sp -> MM x = efs_m0 mem sp ra s0v s1v s2v s3v x) ->
  In (k, v) [(-8, ra); (-16, s0v); (-24, s1v); (-32, s2v); (-40, s3v)] -> rdn BSEGS MM (at_ sp k) 8 = Some (LE8 v).
Proof using.
  intros MM mem sp ra s0v s1v s2v s3v k v SP1 SP2 HM Hin. pose proof (u64_range sp) as Hspr.
  assert (K : -40 <= k <= -8) by (cbn [In] in Hin; repeat (destruct Hin as [E|Hin]; [injection E as <- <-; lia|]); destruct Hin).
  rewrite (rdn_ext BSEGS 8 MM (efs_m0 mem sp ra s0v s1v s2v s3v) (at_ sp k)); [ | first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | intros x Hx; rewrite at_u in Hx by lia; cbn in Hx; apply HM; lia].
  (lazymatch goal with |- ?G => let G' := eval unfold efs_m0 in G in change_no_check G' end). cbn [In] in Hin.
  repeat (destruct Hin as [E|Hin]; [injection E as <- <-; rd8_chain|]). destruct Hin.
Qed.

Section EFSARM.
  Variable Hd : word -> bool.
  Hypothesis HOFFSEG : H_off_segments BSEGS Hd.
  Hypothesis WX : wx_segs_nowrap BSEGS.
  (* [comment removed for export] *)
  Variable Hd2 : word -> bool.
  Hypothesis HOFFSEG2 : H_off_segments BSEGS Hd2.
  Variable A2 : list (Z * Z).
  Hypothesis AWF2 : A_wf A2.
  Variables (A : list (Z * Z)) (regs : bvmap 5 word) (mem rom : word -> option byte) (model : Model)
            (sp ra s0v s1v s2v s3v s4v s5v thr tp gp tsdp ctxw v72 v80 midend : word) (cpm : byte)
            (RIz rbeg tot mfa PGP CF T thr0 : Z) (Qok Qf : config -> Prop) (MOK MKP MDS : Model -> Model).
  #[local] Abbreviation slot := (rbeg + 0xE0000000 + mfa).
  #[local] Abbreviation SH := ((rbeg + 0xE0000000 + mfa) / 8 + 0x7fff8000).
  #[local] Abbreviation M0 := (efs_m0 mem sp ra s0v s1v s2v s3v).
  #[local] Abbreviation M1 := (mfi_m1 M0 (at_ sp (-48)) (Z_to_bv 64 0x4f5a8) (Z_to_bv 64 (mfa + 2 ^ 18)) (Z_to_bv 64 slot) (Z_to_bv 64 (2 ^ 18)) (Z_to_bv 64 RIz)
                     s4v s5v (Z_to_bv 64 slot) (Z_to_bv 64 (2 ^ 18)) (Z_to_bv 64 0x19778) PGP).
  #[local] Abbreviation ENOMEMw := (Z_to_bv 64 (2 ^ 64 - 12) : word).
  #[local] Abbreviation SCR := (word_to_le_bytes 4 (Z_to_bv 64 0xffffffffaaaaaaaa)).
  #[local] Abbreviation MR := (efs_mr mem sp ra s0v s1v s2v s3v s4v s5v RIz slot mfa PGP).
  (* [comment removed for export] *)
  Hypothesis H1 : getr regs 1 = ra.
  Hypothesis H2 : getr regs 2 = sp.
  Hypothesis H4 : getr regs 4 = tp.
  Hypothesis H3 : getr regs 3 = gp.
  Hypothesis H10 : getr regs 10 = Z_to_bv 64 0x10ab58.
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
  Hypothesis Hstk : store_ok BSEGS mem (at_ sp (-448)) 448 = true.
  Hypothesis R_mfa : rdn BSEGS mem (Z_to_bv 64 (RIz + 24)) 8 = Some (LE8 (Z_to_bv 64 mfa)).
  Hypothesis C_pre : rdn BSEGS mem (Z_to_bv 64 (0x10ab58 + 56)) 1 = Some [Z_to_bv 8 0].
  Hypothesis Rgpg : rdn BSEGS mem (Z_to_bv 64 0x105ef8) 8 = Some (LE8 (Z_to_bv 64 PGP)).
  Hypothesis Rpg : rdn BSEGS mem (Z_to_bv 64 PGP) 8 = Some (LE8 (Z_to_bv 64 4096)).
  Hypothesis Rgcf : rdn BSEGS mem (Z_to_bv 64 0x105f08) 8 = Some (LE8 (Z_to_bv 64 CF)).
  Hypothesis Rdpm : rdn BSEGS mem (Z_to_bv 64 (CF + 260)) 1 = Some [Z_to_bv 8 0].
  Hypothesis Rlim : rdn BSEGS mem (Z_to_bv 64 (CF + 144)) 8 = Some (LE8 (Z_to_bv 64 0)).
  Hypothesis Hslot : slot + 2 ^ 18 <= U sp - 448 \/ U sp <= slot.
  Hypothesis HDmfa : hid_off Hd (RIz + 24) 8.
  Hypothesis HDpre : hid_off Hd (0x10ab58 + 56) 1.
  Hypothesis HDgpg : hid_off Hd 0x105ef8 8.
  Hypothesis HDpg : hid_off Hd PGP 8.
  Hypothesis HDgcf : hid_off Hd 0x105f08 8.
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
          katwD BSEGS (mkCfg (mkst (regupd r1 10 (Z_to_bv 64 slot)) (0x811b0 : word) (zfill (Z_to_bv 64 slot) (Z_to_bv 64 (2 ^ 18)) M1) rom) (MOK mdlm)) Qok' Qf' ->
          katsD BSEGS (mkCfg (epend r1 (0x811ac : word) M1 rom (Z_to_bv 64 222)) mdlm) Qok' Qf'.
  Hypothesis CHILD : forall mdlm, same_but_materialized model mdlm -> MInv A mdlm ->
        (m_halted (MOK mdlm) = None /\ lazy_cover Hd (m_vm_lazy (MOK mdlm)) A /\ MInv A (MOK mdlm))
        /\ (m_halted (MKP mdlm) = None /\ lazy_cover Hd (m_vm_lazy (MKP mdlm)) A /\ MInv A (MKP mdlm))
        /\ (m_halted (MDS mdlm) = None /\ lazy_cover Hd (m_vm_lazy (MDS mdlm)) A /\ MInv A (MDS mdlm)).
  Hypothesis OKSW : forall mdlm mdl4, same_but_materialized model mdlm -> MInv A mdlm -> same_but_materialized (MOK mdlm) mdl4 -> MInv A mdl4 ->
        lazy_cover Hd2 (m_vm_lazy mdl4) A2 /\ MInv A2 mdl4.
  (* [comment removed for export] *)
  Hypothesis HT : U thr = T /\ 4096 <= T /\ T + 4096 <= U sp - 448 /\ T mod 8 = 0.
  Hypothesis HTRI : T + 4096 <= RIz \/ RIz + 128 <= T.
  Hypothesis HTSH : T + 4096 <= SH \/ SH + 2 ^ 15 <= T.
  Hypothesis HRSH : RIz + 128 <= SH \/ SH + 2 ^ 15 <= RIz.
  Hypothesis HSSH : U sp <= SH \/ SH + 2 ^ 15 <= U sp - 448.
  Hypothesis HTsl : T + 4096 <= slot \/ slot + 2 ^ 18 <= T.
  Hypothesis PH : poisonH BSEGS both_poison_tab mem (Z_to_bv 64 slot) (Z_to_bv 64 (2 ^ 18)) (Z_to_bv 64 250) (Z_to_bv 64 0x4f5c4) (at_ sp (-48)) cpm midend thr0.
  Hypothesis PCB : Forall (fun c => c + 8 <= AIMGHI) (poison_cells both_poison_tab).
  Hypothesis GH : gctH BSEGS both_gct_tab mem (at_ (at_ sp (-48)) (-16)) tp tsdp ctxw thr.
  Hypothesis GB : U (gt_tsd both_gct_tab) + 8 <= U sp - 448 /\ U tp - 80 <= U sp - 448 /\ U tsdp + 8 <= U sp - 448 /\ U ctxw + 160 <= U sp - 448.
  Hypothesis GS : (U (gt_tsd both_gct_tab) + 8 <= slot \/ slot + 2 ^ 18 <= U (gt_tsd both_gct_tab)) /\ (U tp - 80 <= slot \/ slot + 2 ^ 18 <= U tp - 88)
                  /\ (U tsdp + 8 <= slot \/ slot + 2 ^ 18 <= U tsdp) /\ (U ctxw + 160 <= slot \/ slot + 2 ^ 18 <= U ctxw + 152).
  Hypothesis G1 : U (gt_tsd both_gct_tab) + 8 <= SH \/ SH + 2 ^ 15 <= U (gt_tsd both_gct_tab).
  Hypothesis G2 : U tp - 80 <= SH \/ SH + 2 ^ 15 <= U tp - 88.
  Hypothesis G3 : U tsdp + 8 <= SH \/ SH + 2 ^ 15 <= U tsdp.
  Hypothesis G4 : U ctxw + 160 <= SH \/ SH + 2 ^ 15 <= U ctxw + 152.
  Hypothesis R72 : rdn BSEGS mem (at_ thr 2872) 8 = Some (LE8 v72).
  Hypothesis R80 : rdn BSEGS mem (at_ thr 2880) 8 = Some (LE8 v80).
  Hypothesis SOKT : store_ok BSEGS mem thr 4096 = true.
  Hypothesis SOKRI : store_ok BSEGS mem (Z_to_bv 64 RIz) 128 = true.
  Hypothesis HDc : Forall (fun c => hid_off Hd2 c 8) (poison_cells both_poison_tab).
  Hypothesis HDsh : hid_off Hd2 SH (2 ^ 15).
  Hypothesis HD1 : hid_off Hd2 (U (gt_tsd both_gct_tab)) 8.
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
      katwD BSEGS (mkCfg (mkst r ra (eam_3 MR sp s4v s5v thr v72 v80 RIz slot mfa) rom) mdl5) Qok Qf.
  Hypothesis CONT0K : forall (r' r : bvmap 5 word) mdlm mdl5,
      same_but_materialized model mdlm -> MInv A mdlm -> same_but_materialized (MKP mdlm) mdl5 -> MInv A mdl5 ->
      regs_agree (fun i : reg => In i efs_clob) regs r' -> efs_post sp ra s0v s1v s2v s3v 0 r' r ->
      katD BSEGS (mkCfg (mkst r ra (wbytes (wbytes M1 (at_ sp (-132)) SCR) (at_ sp (-132)) (word_to_le_bytes 4 (Z_to_bv 64 12))) rom) mdl5) Qf.
  Hypothesis CONT0D : forall (r' r : bvmap 5 word) mdlm mdl5,
      same_but_materialized model mdlm -> MInv A mdlm -> same_but_materialized (MDS mdlm) mdl5 -> MInv A mdl5 ->
      regs_agree (fun i : reg => In i efs_clob) regs r' -> efs_post sp ra s0v s1v s2v s3v 0 r' r ->
      katD BSEGS (mkCfg (mkst r ra (wbytes (wbytes (unfill (Z_to_bv 64 slot) (Z_to_bv 64 (2 ^ 18)) M1) (at_ sp (-132)) SCR) (at_ sp (-132)) (word_to_le_bytes 4 (Z_to_bv 64 12))) rom) mdl5) Qf.

  Theorem efs_map_arm_katwD : katwD BSEGS (mkCfg (mkst regs (0x4f508 : word) mem rom) model) Qok Qf.
  Proof using CONT0D CONT0K CONT1 HDscr2 HDRI HDT HD4 HD3 HD2 HD1 HDsh HDc SOKRI SOKT R80 R72 G4 G3 G2 G1 GS GB GH PCB PH HTsl HSSH HRSH HTSH HTRI HT OKSW CHILD NODE MI AWF LC HALT HDscr HDlim HDdpm HDgcf HDpg HDgpg HDpre HDmfa Hslot Rlim Rdpm Rgcf Rpg Rgpg C_pre R_mfa Hstk HCF HPGP HRI Hrbeg Hroom Hneed Hmfa Htot Hret Hsp H21 H20 H19 H18 H9 H8 H13 H12 H11 H10 H3 H4 H2 H1 MDS MKP MOK thr0 T CF PGP mfa tot rbeg RIz cpm midend v80 v72 ctxw tsdp gp tp thr s5v s4v s3v s2v s1v s0v ra sp A AWF2 A2 HOFFSEG2 Hd2 WX HOFFSEG Hd.
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
    apply (efs_famap_katsD Hd HOFFSEG WX A regs mem rom model sp ra s0v s1v s2v s3v s4v s5v RIz rbeg tot mfa PGP CF Qok Qf MOK MKP MDS
             H1 H2 H10 H11 H12 H13 H8 H9 H18 H19 H20 H21 ltac:(lia) Htot (conj (conj MF1 MF2) MF3) Hneed Hroom (conj RB1 (conj RB2 RB3)) (conj RI1 RI2) HPGP HCF Hstk
             R_mfa C_pre Rgpg Rpg Rgcf Rdpm Rlim Hslot HDmfa HDpre HDgpg HDpg HDgcf HDdpm HDlim HDscr HALT LC AWF MI NODE CHILD).
    - (* [comment removed for export] *)
      intros r' mdlm mdl4 SBm MIm SB4 MI4 (E2 & E8 & E9 & E18 & E19 & E10 & E20) AG.
      destruct (CHILD mdlm SBm MIm) as ((HOK & LOK & _) & _ & _).
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
        apply (poisonH_keep_P BSEGS both_poison_tab mem MR _ _ _ _ _ cpm midend thr0
                 (fun z => (z < U sp - 448 \/ U sp <= z) /\ (z < slot \/ slot + 2 ^ 18 <= z)) PH); [intros x [X1 X2]; apply OUT; assumption | exact GR |].
        eapply Forall_impl; [|exact PCB]. cbv beta. intros c Hc z Hz. lia.
      + (* [comment removed for export] *)
        destruct GB as (B1 & B2 & B3 & B4). destruct GS as (S1 & S2 & S3 & S4).
        apply (gctH_keep_P BSEGS both_gct_tab mem MR _ tp tsdp ctxw thr
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
      destruct (CHILD mdlm SBm MIm) as (_ & (HKP & LKP & _) & _).
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
    - (* [comment removed for export] *)
      intros r' mdlm mdl4 SBm MIm SB4 MI4 (E2 & E8 & E9 & E18 & E19 & E10 & E20) AG.
      destruct (CHILD mdlm SBm MIm) as (_ & _ & (HDS & LDS & _)).
      destruct (FRAMES _ _ HDS LDS SB4) as [HALT4 LC4].
      set (MK := wbytes (wbytes (unfill (Z_to_bv 64 slot) (Z_to_bv 64 (2 ^ 18)) M1) (at_ sp (-132)) SCR) (at_ sp (-132)) (word_to_le_bytes 4 (Z_to_bv 64 12))).
      assert (AGR : forall x : word, U sp - 48 <= U x < U sp -> MK x = M0 x).
      { intros x Hx. (lazymatch goal with |- ?G => let G' := eval unfold MK in G in change_no_check G' end).
        repeat (rewrite MemsetLibF.MemSplit.wbytes_outside; [ | rewrite length_N_to_le_bytes, at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite length_N_to_le_bytes, at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia]).
        rewrite unfill_out by (rewrite !u_Z2bv by (clear - SL; lia); clear - Hx Hslot; lia).
        apply mfi_m1_outside; first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite ?at_u by lia; lia ]. }
      apply (efs_fail_katD Hd HOFFSEG WX A r' MK rom mdl4 sp ra s0v s1v s2v s3v Qf E2 Hret E10 ltac:(lia)
               (efs_slots_ext MK mem sp ra s0v s1v s2v s3v (-8) ra ltac:(lia) ltac:(lia) AGR ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 8))
               (efs_slots_ext MK mem sp ra s0v s1v s2v s3v (-16) s0v ltac:(lia) ltac:(lia) AGR ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 8))
               (efs_slots_ext MK mem sp ra s0v s1v s2v s3v (-24) s1v ltac:(lia) ltac:(lia) AGR ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 8))
               (efs_slots_ext MK mem sp ra s0v s1v s2v s3v (-32) s2v ltac:(lia) ltac:(lia) AGR ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 8))
               (efs_slots_ext MK mem sp ra s0v s1v s2v s3v (-40) s3v ltac:(lia) ltac:(lia) AGR ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 8))
               HDf48 HALT4 LC4 AWF MI4).
      intros r mdl5 SB5 MI5 POST.
      exact (CONT0D r' r mdlm mdl5 SBm MIm (same_but_materialized_trans _ _ _ SB4 SB5) MI5 AG POST).
  Qed.
End EFSARM.
End FPGen.
End BoAllocM8y.
Module BoAllocM8yq.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import Stdlib.Logic.FunctionalExtensionality.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.DivergeSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.SpinAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes.AgentNodes OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocSim OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys6.MhKSys OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsK OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys6.AsKSys OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsRtK OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtUnwindT OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoison OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtPoisonI OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMMemA.BoAllocMI OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8m OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM9i.BoAllocM8k OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8e BoAllocM8r OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8s OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8u.BoAllocM8t OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8u BoAllocM8w BoAllocM8x.
Import BoAllocM8y BoAllocM8uq.
Import OSSVerify.glaze.binary_reflection.images.AsanUbsan.
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

#[local] Abbreviation BSEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).
#[local] Abbreviation U := bv_unsigned.

Section FPGen.
Context {fx : FPState}.


Section EFSARM.
  Variable Hd : word -> bool.
  Hypothesis HOFFSEG : H_off_segments BSEGS Hd.
  Hypothesis WX : wx_segs_nowrap BSEGS.
  (* [comment removed for export] *)
  Variable Hd2 : word -> bool.
  Hypothesis HOFFSEG2 : H_off_segments BSEGS Hd2.
  Variable A2 : list (Z * Z).
  Hypothesis AWF2 : A_wf A2.
  Variables (A : list (Z * Z)) (regs : bvmap 5 word) (mem rom : word -> option byte) (model : Model)
            (sp ra s0v s1v s2v s3v s4v s5v thr tp gp tsdp ctxw v72 v80 midend : word) (cpm : byte)
            (RIz rbeg tot mfa PGP CF T thr0 : Z) (Qok Qf : config -> Prop) (MOK MKP MDS : Model -> Model).
  #[local] Abbreviation slot := (rbeg + 0xE0000000 + mfa).
  #[local] Abbreviation SH := ((rbeg + 0xE0000000 + mfa) / 8 + 0x7fff8000).
  #[local] Abbreviation M0 := (efs_m0 mem sp ra s0v s1v s2v s3v).
  #[local] Abbreviation M1 := (mfi_m1 M0 (at_ sp (-48)) (Z_to_bv 64 0x4f5a8) (Z_to_bv 64 (mfa + 2 ^ 18)) (Z_to_bv 64 slot) (Z_to_bv 64 (2 ^ 18)) (Z_to_bv 64 RIz)
                     s4v s5v (Z_to_bv 64 slot) (Z_to_bv 64 (2 ^ 18)) (Z_to_bv 64 0x19778) PGP).
  #[local] Abbreviation ENOMEMw := (Z_to_bv 64 (2 ^ 64 - 12) : word).
  #[local] Abbreviation SCR := (word_to_le_bytes 4 (Z_to_bv 64 0xffffffffaaaaaaaa)).
  #[local] Abbreviation MR := (efs_mr mem sp ra s0v s1v s2v s3v s4v s5v RIz slot mfa PGP).
  (* [comment removed for export] *)
  Hypothesis H1 : getr regs 1 = ra.
  Hypothesis H2 : getr regs 2 = sp.
  Hypothesis H4 : getr regs 4 = tp.
  Hypothesis H3 : getr regs 3 = gp.
  Hypothesis H10 : getr regs 10 = Z_to_bv 64 0x10ab58.
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
  Hypothesis Hstk : store_ok BSEGS mem (at_ sp (-448)) 448 = true.
  Hypothesis R_mfa : rdn BSEGS mem (Z_to_bv 64 (RIz + 24)) 8 = Some (LE8 (Z_to_bv 64 mfa)).
  Hypothesis C_pre : rdn BSEGS mem (Z_to_bv 64 (0x10ab58 + 56)) 1 = Some [Z_to_bv 8 0].
  Hypothesis Rgpg : rdn BSEGS mem (Z_to_bv 64 0x105ef8) 8 = Some (LE8 (Z_to_bv 64 PGP)).
  Hypothesis Rpg : rdn BSEGS mem (Z_to_bv 64 PGP) 8 = Some (LE8 (Z_to_bv 64 4096)).
  Hypothesis Rgcf : rdn BSEGS mem (Z_to_bv 64 0x105f08) 8 = Some (LE8 (Z_to_bv 64 CF)).
  Hypothesis Rdpm : rdn BSEGS mem (Z_to_bv 64 (CF + 260)) 1 = Some [Z_to_bv 8 0].
  Hypothesis Rlim : rdn BSEGS mem (Z_to_bv 64 (CF + 144)) 8 = Some (LE8 (Z_to_bv 64 0)).
  Hypothesis Hslot : slot + 2 ^ 18 <= U sp - 448 \/ U sp <= slot.
  Hypothesis HDmfa : hid_off Hd (RIz + 24) 8.
  Hypothesis HDpre : hid_off Hd (0x10ab58 + 56) 1.
  Hypothesis HDgpg : hid_off Hd 0x105ef8 8.
  Hypothesis HDpg : hid_off Hd PGP 8.
  Hypothesis HDgcf : hid_off Hd 0x105f08 8.
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
          katwD BSEGS (mkCfg (mkst (regupd r1 10 (Z_to_bv 64 slot)) (0x811b0 : word) (zfill (Z_to_bv 64 slot) (Z_to_bv 64 (2 ^ 18)) M1) rom) (MOK mdlm)) Qok' Qf' ->
          katsD BSEGS (mkCfg (epend r1 (0x811ac : word) M1 rom (Z_to_bv 64 222)) mdlm) Qok' Qf'.
  Hypothesis CHILD : forall mdlm, same_but_materialized model mdlm -> MInv A mdlm ->
        (m_halted (MOK mdlm) = None /\ lazy_cover Hd (m_vm_lazy (MOK mdlm)) A /\ MInv A (MOK mdlm))
        /\ (m_halted (MKP mdlm) = None /\ lazy_cover Hd (m_vm_lazy (MKP mdlm)) A /\ MInv A (MKP mdlm))
        /\ (m_halted (MDS mdlm) = None /\ lazy_cover Hd (m_vm_lazy (MDS mdlm)) A /\ MInv A (MDS mdlm)).
  Hypothesis OKSW : forall mdlm mdl4, same_but_materialized model mdlm -> MInv A mdlm -> same_but_materialized (MOK mdlm) mdl4 -> MInv A mdl4 ->
        lazy_cover Hd2 (m_vm_lazy mdl4) A2 /\ MInv A2 mdl4.
  (* [comment removed for export] *)
  Hypothesis HT : U thr = T /\ 4096 <= T /\ T + 4096 <= U sp - 448 /\ T mod 8 = 0.
  Hypothesis HTRI : T + 4096 <= RIz \/ RIz + 128 <= T.
  Hypothesis HTSH : T + 4096 <= SH \/ SH + 2 ^ 15 <= T.
  Hypothesis HRSH : RIz + 128 <= SH \/ SH + 2 ^ 15 <= RIz.
  Hypothesis HSSH : U sp <= SH \/ SH + 2 ^ 15 <= U sp - 448.
  Hypothesis HTsl : T + 4096 <= slot \/ slot + 2 ^ 18 <= T.
  Hypothesis PH : poisonH BSEGS both_poison_tab mem (Z_to_bv 64 slot) (Z_to_bv 64 (2 ^ 18)) (Z_to_bv 64 250) (Z_to_bv 64 0x4f5c4) (at_ sp (-48)) cpm midend thr0.
  Hypothesis PCB : Forall (fun c => c + 8 <= AIMGHI) (poison_cells both_poison_tab).
  Hypothesis GH : gctH BSEGS both_gct_tab mem (at_ (at_ sp (-48)) (-16)) tp tsdp ctxw thr.
  Hypothesis GB : U (gt_tsd both_gct_tab) + 8 <= U sp - 448 /\ U tp - 80 <= U sp - 448 /\ U tsdp + 8 <= U sp - 448 /\ U ctxw + 160 <= U sp - 448.
  Hypothesis GS : (U (gt_tsd both_gct_tab) + 8 <= slot \/ slot + 2 ^ 18 <= U (gt_tsd both_gct_tab)) /\ (U tp - 80 <= slot \/ slot + 2 ^ 18 <= U tp - 88)
                  /\ (U tsdp + 8 <= slot \/ slot + 2 ^ 18 <= U tsdp) /\ (U ctxw + 160 <= slot \/ slot + 2 ^ 18 <= U ctxw + 152).
  Hypothesis G1 : U (gt_tsd both_gct_tab) + 8 <= SH \/ SH + 2 ^ 15 <= U (gt_tsd both_gct_tab).
  Hypothesis G2 : U tp - 80 <= SH \/ SH + 2 ^ 15 <= U tp - 88.
  Hypothesis G3 : U tsdp + 8 <= SH \/ SH + 2 ^ 15 <= U tsdp.
  Hypothesis G4 : U ctxw + 160 <= SH \/ SH + 2 ^ 15 <= U ctxw + 152.
  Hypothesis R72 : rdn BSEGS mem (at_ thr 2872) 8 = Some (LE8 v72).
  Hypothesis R80 : rdn BSEGS mem (at_ thr 2880) 8 = Some (LE8 v80).
  Hypothesis SOKT : store_ok BSEGS mem thr 4096 = true.
  Hypothesis SOKRI : store_ok BSEGS mem (Z_to_bv 64 RIz) 128 = true.
  Hypothesis HDc : Forall (fun c => hid_off Hd2 c 8) (poison_cells both_poison_tab).
  Hypothesis HDsh : hid_off Hd2 SH (2 ^ 15).
  Hypothesis HD1 : hid_off Hd2 (U (gt_tsd both_gct_tab)) 8.
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
      katwD BSEGS (mkCfg (mkst r ra (eam_3 MR sp s4v s5v thr v72 v80 RIz slot mfa) rom) mdl5) Qok Qf.
  Hypothesis CONT0K : forall (r' r : bvmap 5 word) mdlm mdl5,
      same_but_materialized model mdlm -> MInv A mdlm -> same_but_materialized (MKP mdlm) mdl5 -> MInv A mdl5 ->
      regs_agree (fun i : reg => In i efs_clob) regs r' -> efs_post sp ra s0v s1v s2v s3v 0 r' r ->
      katD BSEGS (mkCfg (mkst r ra (wbytes (wbytes M1 (at_ sp (-132)) SCR) (at_ sp (-132)) (word_to_le_bytes 4 (Z_to_bv 64 12))) rom) mdl5) Qf.
  Hypothesis CONT0D : forall (r' r : bvmap 5 word) mdlm mdl5,
      same_but_materialized model mdlm -> MInv A mdlm -> same_but_materialized (MDS mdlm) mdl5 -> MInv A mdl5 ->
      regs_agree (fun i : reg => In i efs_clob) regs r' -> efs_post sp ra s0v s1v s2v s3v 0 r' r ->
      katD BSEGS (mkCfg (mkst r ra (wbytes (wbytes (unfill (Z_to_bv 64 slot) (Z_to_bv 64 (2 ^ 18)) M1) (at_ sp (-132)) SCR) (at_ sp (-132)) (word_to_le_bytes 4 (Z_to_bv 64 12))) rom) mdl5) Qf.

  Theorem efs_map_arm_katwD_x : katwD BSEGS (mkCfg (mkst regs (0x4f508 : word) mem rom) model) Qok Qf.
  Proof using CONT0D CONT0K CONT1 HDscr2 HDRI HDT HD4 HD3 HD2 HD1 HDsh HDc SOKRI SOKT R80 R72 G4 G3 G2 G1 GS GB GH PCB PH HTsl HSSH HRSH HTSH HTRI HT OKSW CHILD NODE MI AWF LC HALT HDscr HDlim HDdpm HDgcf HDpg HDgpg HDpre HDmfa Hslot Rlim Rdpm Rgcf Rpg Rgpg C_pre R_mfa Hstk HCF HPGP HRI Hrbeg Hroom Hneed Hmfa Htot Hret Hsp H21 H20 H19 H18 H9 H8 H13 H12 H11 H10 H3 H4 H2 H1 MDS MKP MOK thr0 T CF PGP mfa tot rbeg RIz cpm midend v80 v72 ctxw tsdp gp tp thr s5v s4v s3v s2v s1v s0v ra sp A AWF2 A2 HOFFSEG2 Hd2 WX HOFFSEG Hd.
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
    apply (efs_famap_katsD Hd HOFFSEG WX A regs mem rom model sp ra s0v s1v s2v s3v s4v s5v RIz rbeg tot mfa PGP CF Qok Qf MOK MKP MDS
             H1 H2 H10 H11 H12 H13 H8 H9 H18 H19 H20 H21 ltac:(lia) Htot (conj (conj MF1 MF2) MF3) Hneed Hroom (conj RB1 (conj RB2 RB3)) (conj RI1 RI2) HPGP HCF Hstk
             R_mfa C_pre Rgpg Rpg Rgcf Rdpm Rlim Hslot HDmfa HDpre HDgpg HDpg HDgcf HDdpm HDlim HDscr HALT LC AWF MI NODE CHILD).
    - (* [comment removed for export] *)
      intros r' mdlm mdl4 SBm MIm SB4 MI4 (E2 & E8 & E9 & E18 & E19 & E10 & E20) AG.
      destruct (CHILD mdlm SBm MIm) as ((HOK & LOK & _) & _ & _).
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
        apply (poisonH_keep_P BSEGS both_poison_tab mem MR _ _ _ _ _ cpm midend thr0
                 (fun z => (z < U sp - 448 \/ U sp <= z) /\ (z < slot \/ slot + 2 ^ 18 <= z)) PH); [intros x [X1 X2]; apply OUT; assumption | exact GR |].
        eapply Forall_impl; [|exact PCB]. cbv beta. intros c Hc z Hz. lia.
      + (* [comment removed for export] *)
        destruct GB as (B1 & B2 & B3 & B4). destruct GS as (S1 & S2 & S3 & S4).
        apply (gctH_keep_P BSEGS both_gct_tab mem MR _ tp tsdp ctxw thr
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
      destruct (CHILD mdlm SBm MIm) as (_ & (HKP & LKP & _) & _).
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
    - (* [comment removed for export] *)
      intros r' mdlm mdl4 SBm MIm SB4 MI4 (E2 & E8 & E9 & E18 & E19 & E10 & E20) AG.
      destruct (CHILD mdlm SBm MIm) as (_ & _ & (HDS & LDS & _)).
      destruct (FRAMES _ _ HDS LDS SB4) as [HALT4 LC4].
      set (MK := wbytes (wbytes (unfill (Z_to_bv 64 slot) (Z_to_bv 64 (2 ^ 18)) M1) (at_ sp (-132)) SCR) (at_ sp (-132)) (word_to_le_bytes 4 (Z_to_bv 64 12))).
      assert (AGR : forall x : word, U sp - 48 <= U x < U sp -> MK x = M0 x).
      { intros x Hx. (lazymatch goal with |- ?G => let G' := eval unfold MK in G in change_no_check G' end).
        repeat (rewrite MemsetLibF.MemSplit.wbytes_outside; [ | rewrite length_N_to_le_bytes, at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite length_N_to_le_bytes, at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia]).
        rewrite unfill_out by (rewrite !u_Z2bv by (clear - SL; lia); clear - Hx Hslot; lia).
        apply mfi_m1_outside; first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite ?at_u by lia; lia ]. }
      apply (efs_fail_katD Hd HOFFSEG WX A r' MK rom mdl4 sp ra s0v s1v s2v s3v Qf E2 Hret E10 ltac:(lia)
               (efs_slots_ext MK mem sp ra s0v s1v s2v s3v (-8) ra ltac:(lia) ltac:(lia) AGR ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 8))
               (efs_slots_ext MK mem sp ra s0v s1v s2v s3v (-16) s0v ltac:(lia) ltac:(lia) AGR ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 8))
               (efs_slots_ext MK mem sp ra s0v s1v s2v s3v (-24) s1v ltac:(lia) ltac:(lia) AGR ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 8))
               (efs_slots_ext MK mem sp ra s0v s1v s2v s3v (-32) s2v ltac:(lia) ltac:(lia) AGR ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 8))
               (efs_slots_ext MK mem sp ra s0v s1v s2v s3v (-40) s3v ltac:(lia) ltac:(lia) AGR ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 8))
               HDf48 HALT4 LC4 AWF MI4).
      intros r mdl5 SB5 MI5 POST.
      exact (CONT0D r' r mdlm mdl5 SBm MIm (same_but_materialized_trans _ _ _ SB4 SB5) MI5 AG POST).
  Qed.
End EFSARM.
End FPGen.
End BoAllocM8yq.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM9c.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module BoAllocM9f.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtUnwindT OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoison OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtPoisonI OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM0 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMMemA.BoAllocMI OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8s OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM9c.BoAllocM9a OSSVerify.Proofs.glaze.binary_reflection.lib.Bo_code_50a9c_51a9c.
Import OSSVerify.glaze.binary_reflection.images.AsanUbsan.
Import ListNotations.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation BSEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).
#[local] Abbreviation U := bv_unsigned.

Section FPGen.
Context {fx : FPState}.

(* [comment removed for export] *)
Lemma jal_510e8 : forall regs mem rom,
  msteps BSEGS (mkst regs (0x510e8 : word) mem rom) (mkst (regupd regs 1 (at_ ARB 0x510ec)) (at_ ARB 0x77ff8) mem rom).
Proof using.
  intros regs mem rom. rewrite !ARB_lit8 by lia.
  an F_510e8 D_510e8. close_eq.
Qed.

(* [comment removed for export] *)
Definition la_tb (size mb : Z) : Z := (mb + 4096 + size - (mb + 4096 + size) mod 8)%Z.

(* [comment removed for export] *)
Definition lam_1 (M : word -> option byte) (sp stats : word) (size mb : Z) : word -> option byte :=
  wbytes (ps_frame M (at_ sp (-96)) (Z_to_bv 64 0x510d8) stats (Z_to_bv 64 (0x10ab58 + 64)) (Z_to_bv 64 (la_msz size)) (Z_to_bv 64 size)
                   (Z_to_bv 64 mb) (Z_to_bv 64 (mb + 4096 + size)))
         (Z_to_bv 64 (shad (Z_to_bv 64 mb))) (repeat (cbyte (Z_to_bv 64 250)) (Z.to_nat (shlen (Z_to_bv 64 4096)))).
Definition lam_2 (M : word -> option byte) (sp stats : word) (size mb : Z) : word -> option byte :=
  wbytes (ps_frame (lam_1 M sp stats size mb) (at_ sp (-96)) (Z_to_bv 64 0x510e8) stats (Z_to_bv 64 (0x10ab58 + 64)) (Z_to_bv 64 (la_msz size))
                   (Z_to_bv 64 size) (Z_to_bv 64 mb) (Z_to_bv 64 (mb + 4096 + size)))
         (Z_to_bv 64 (shad (Z_to_bv 64 (la_tb size mb))))
         (repeat (cbyte (Z_to_bv 64 250)) (Z.to_nat (shlen (Z_to_bv 64 (mb + la_msz size - la_tb size mb))))).
Definition lam_3 (M : word -> option byte) (sp stats : word) (size mb : Z) : word -> option byte :=
  wbytes (wbytes (lam_2 M sp stats size mb) (at_ (at_ sp (-96)) (-8)) (LE8 (at_ ARB 0x510ec)))
         (at_ (at_ sp (-96)) (-24)) (LE8 (at_ ARB 0x78004)).

Section AFTERGRANT.
  Variables (M rom : word -> option byte) (sp stats thr tp gp tsdp ctxw midend : word) (cpm : byte) (size mb thr0 : Z).
  Variable regs : bvmap 5 word.
  Hypothesis HR : la_regs sp stats size regs.
  Hypothesis H10 : getr regs 10 = Z_to_bv 64 mb.
  Hypothesis H21 : getr regs 21 = Z_to_bv 64 8.
  Hypothesis H4 : getr regs 4 = tp.
  Hypothesis H3 : getr regs 3 = gp.
  Hypothesis Hsp : (2 ^ 32 + 4096 <= U sp /\ U sp + 16 <= 2 ^ 47)%Z.
  Hypothesis Hsize : (1 <= size <= 2 ^ 41)%Z.
  Hypothesis Hmb : (4096 <= mb /\ mb + la_msz size < 2 ^ 63 /\ mb mod 4096 = 0)%Z.
  Hypothesis C_pg : rdn BSEGS M (Z_to_bv 64 (0x10ab58 + 64)) 8 = Some (LE8 (Z_to_bv 64 4096)).
  Hypothesis HT : (4096 <= U thr /\ U thr + 4096 <= 2 ^ 63)%Z.
  #[local] Abbreviation L1 := (lam_1 M sp stats size mb).
  #[local] Abbreviation L2 := (lam_2 M sp stats size mb).
  #[local] Abbreviation L3 := (lam_3 M sp stats size mb).
  (* [comment removed for export] *)
  Hypothesis PH1 : poisonH BSEGS both_poison_tab M (Z_to_bv 64 mb) (Z_to_bv 64 4096) (Z_to_bv 64 250) (Z_to_bv 64 0x510d8) (at_ sp (-96)) cpm midend thr0.
  Hypothesis PH2 : poisonH BSEGS both_poison_tab L1 (Z_to_bv 64 (la_tb size mb)) (Z_to_bv 64 (mb + la_msz size - la_tb size mb)) (Z_to_bv 64 250)
                           (Z_to_bv 64 0x510e8) (at_ sp (-96)) cpm midend thr0.
  (* [comment removed for export] *)
  Hypothesis GH : gctH BSEGS both_gct_tab L2 (at_ (at_ sp (-96)) (-16)) tp tsdp ctxw thr.
  Hypothesis SOK_g : store_ok BSEGS L2 (at_ (at_ sp (-96)) (-8)) 8 = true.

  Theorem la_after_grant :
    exists r, msteps BSEGS (mkst regs (0x51080 : word) M rom) (mkst r (0x510ec : word) L3 rom)
      /\ la_regs2 sp stats size mb r /\ getr r 10 = at_ thr 2800 /\ getr r 4 = tp /\ getr r 3 = gp
      /\ getr r 26 = getr regs 26 /\ getr r 27 = getr regs 27.
  Proof using SOK_g GH PH2 PH1 HT C_pg Hmb Hsize Hsp H3 H4 H21 H10 HR thr0 cpm midend ctxw tsdp.
    pose proof (u64_range sp) as Hspr. destruct Hsp as [SP1 SP2].
    (* [comment removed for export] *)
    destruct (la_mid1 M rom sp stats size mb regs HR Hsize Hmb C_pg H10 H21) as (r1 & RUN1 & PR1 & A1 & A10 & A11 & A12 & AG1).
    assert (K1 : forall i : reg, ~ In i [1%bv; 10%bv; 11%bv; 12%bv; 20%bv; 21%bv; 22%bv; 23%bv; 25%bv] -> getr r1 i = getr regs i) by (intros i Hi; apply AG1; exact Hi).
    pose proof PR1 as ((P2 & P8 & P9 & P18 & P19 & P24) & P20 & P22 & P23 & P25 & P21).
    Ltac nclob := (lazymatch goal with |- ?G => let G' := eval unfold poison_clob in G in change_no_check G' end); (lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); intros X; repeat (destruct X as [X|X]; [discriminate X|]); exact X.
    (* [comment removed for export] *)
    destruct (both_poison_shadow M rom (Z_to_bv 64 mb) (Z_to_bv 64 4096) (Z_to_bv 64 250) (Z_to_bv 64 0x510d8) (at_ sp (-96)) cpm midend thr0 r1
                PH1 A1 P2 A10 A11 A12) as (r2 & RUN2 & AG2).
    rewrite P8, P9, P18, P19, P20, P21 in RUN2.
    change (wbytes (ps_frame M _ _ _ _ _ _ _ _) _ _) with L1 in RUN2.
    replace (Z_to_bv 64 0x510d8 : word) with (0x510d8%bv : word) in RUN2 by (apply bv_eq; reflexivity).
    assert (PR2 : la_regs2 sp stats size mb r2).
    { (lazymatch goal with |- ?G => let G' := eval unfold la_regs2, la_regs in G in change_no_check G' end). rewrite !(AG2 _) by nclob. exact PR1. }
    (* [comment removed for export] *)
    destruct (la_mid2 L1 rom sp stats size mb r2 PR2 Hsize Hmb) as (r3 & RUN3 & PR3 & B1 & B10 & B11 & B12 & AG3).
    pose proof PR3 as ((Q2 & Q8 & Q9 & Q18 & Q19 & Q24) & Q20 & Q22 & Q23 & Q25 & Q21).
    (* [comment removed for export] *)
    destruct (both_poison_shadow L1 rom (Z_to_bv 64 (la_tb size mb)) (Z_to_bv 64 (mb + la_msz size - la_tb size mb)) (Z_to_bv 64 250) (Z_to_bv 64 0x510e8)
                (at_ sp (-96)) cpm midend thr0 r3 PH2 B1 Q2 B10 B11 B12) as (r4 & RUN4 & AG4).
    rewrite Q8, Q9, Q18, Q19, Q20, Q21 in RUN4.
    change (wbytes (ps_frame L1 _ _ _ _ _ _ _ _) _ _) with L2 in RUN4.
    replace (Z_to_bv 64 0x510e8 : word) with (0x510e8%bv : word) in RUN4 by (apply bv_eq; reflexivity).
    assert (PR4 : la_regs2 sp stats size mb r4).
    { (lazymatch goal with |- ?G => let G' := eval unfold la_regs2, la_regs in G in change_no_check G' end). rewrite !(AG4 _) by nclob. exact PR3. }
    (* [comment removed for export] *)
    pose proof (jal_510e8 r4 L2 rom) as RUNJ.
    assert (RETg : ret_ok (at_ ARB 0x510ec)) by (rewrite ARB_lit8 by lia; apply ret_ok_lit; [lia | reflexivity]).
    pose proof PR4 as ((S2 & S8 & S9 & S18 & S19 & S24) & S20 & S22 & S23 & S25 & S21).
    assert (T4 : getr r4 4 = tp).
    { rewrite (AG4 4%bv) by nclob. rewrite (AG3 4%bv) by ((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); intros X; repeat (destruct X as [X|X]; [discriminate X|]); exact X).
      rewrite (AG2 4%bv) by nclob. rewrite K1 by ((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); intros X; repeat (destruct X as [X|X]; [discriminate X|]); exact X). exact H4. }
    assert (T3 : getr r4 3 = gp).
    { rewrite (AG4 3%bv) by nclob. rewrite (AG3 3%bv) by ((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); intros X; repeat (destruct X as [X|X]; [discriminate X|]); exact X).
      rewrite (AG2 3%bv) by nclob. rewrite K1 by ((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); intros X; repeat (destruct X as [X|X]; [discriminate X|]); exact X). exact H3. }
    assert (T26 : getr r4 26 = getr regs 26).
    { rewrite (AG4 26%bv) by nclob. rewrite (AG3 26%bv) by ((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); intros X; repeat (destruct X as [X|X]; [discriminate X|]); exact X).
      rewrite (AG2 26%bv) by nclob. rewrite K1 by ((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); intros X; repeat (destruct X as [X|X]; [discriminate X|]); exact X). reflexivity. }
    assert (T27 : getr r4 27 = getr regs 27).
    { rewrite (AG4 27%bv) by nclob. rewrite (AG3 27%bv) by ((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); intros X; repeat (destruct X as [X|X]; [discriminate X|]); exact X).
      rewrite (AG2 27%bv) by nclob. rewrite K1 by ((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); intros X; repeat (destruct X as [X|X]; [discriminate X|]); exact X). reflexivity. }
    destruct (gts_run BSEGS ARB both_HGTS ARB_ok both_gct_tab L2 rom (regupd r4 1 (at_ ARB 0x510ec)) (at_ ARB 0x510ec) (at_ sp (-96)) tp tsdp ctxw thr
                both_gct_tab_ok both_GTRB GH SOK_g ltac:(first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ]) ltac:(lia) ltac:(lia) RETg
                ltac:(rewrite getr_same by (intros E; discriminate E); reflexivity)
                ltac:(rewrite getr_other by (intros E; discriminate E); exact S2)
                ltac:(rewrite getr_other by (intros E; discriminate E); exact T4))
      as (r5 & RUN5 & D10 & AG5).
    change (wbytes (wbytes L2 _ _) _ _) with L3 in RUN5.
    rewrite (ARB_lit8 0x510ec) in RUN5, RUNJ by lia.
    replace (Z_to_bv 64 0x510ec : word) with (0x510ec%bv : word) in RUN5, RUNJ by (apply bv_eq; reflexivity).
    assert (K5 : forall i : reg, i <> 1%bv -> i <> 10%bv -> i <> 11%bv -> getr r5 i = getr r4 i).
    { intros i N1 N10 N11. rewrite (AG5 i) by ((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); intros [X|[X|[]]]; [apply N10 | apply N11]; symmetry; exact X).
      rewrite getr_other by (intros E; apply N1; first [exact E | symmetry; exact E]). reflexivity. }
    exists r5. split.
    - eapply msteps_trans; [exact RUN1|]. eapply msteps_trans; [exact RUN2|]. eapply msteps_trans; [exact RUN3|].
      eapply msteps_trans; [exact RUN4|]. eapply msteps_trans; [exact RUNJ|]. exact RUN5.
    - split.
      + (lazymatch goal with |- ?G => let G' := eval unfold la_regs2, la_regs in G in change_no_check G' end). rewrite !K5 by (intros E; discriminate E). exact PR4.
      + split; [exact D10|]. split; [rewrite K5 by (intros E; discriminate E); exact T4|]. split; [rewrite K5 by (intros E; discriminate E); exact T3|].
        split; [rewrite K5 by (intros E; discriminate E); exact T26 | rewrite K5 by (intros E; discriminate E); exact T27].
  Qed.
End AFTERGRANT.
End FPGen.
End BoAllocM9f.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtIMemmove OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM4 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMSbM4 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM9g.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module BoAllocMSumS.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoison OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtIMemmove.AsDepotSum OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM4 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMSbM4.BoAllocM4s OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM9c.BoAllocM9a OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM9c.BoAllocM9b OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM9c BoAllocM9f OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM9g.
Import ListNotations.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).
#[local] Abbreviation U := bv_unsigned.

Lemma msum_wbytes_in : forall (W : Z -> Prop) M M1 (a : word) bs, msum W M M1 -> U a + Z.of_nat (length bs) <= 2 ^ 64 ->
  (forall z, U a <= z < U a + Z.of_nat (length bs) -> W z) -> msum W M (wbytes M1 a bs).
Proof.
  intros W M M1 a bs S Hnw HW.
  apply (msum_weaken (wun W (ivl (U a) (Z.of_nat (length bs))))); [intros z [H|H]; [exact H | apply HW; unfold ivl in H; lia]|].
  eapply msum_trans; [exact S | apply msum_wbytes; exact Hnw].
Qed.

(* [comment removed for export] *)
Ltac msum_nest := repeat (apply msum_wbytes_in; [| |]); [apply msum_refl | ..].

Lemma length_repeat_Z : forall {A} (b : A) k, 0 <= k -> Z.of_nat (length (repeat b (Z.to_nat k))) = k.
Proof. intros A b k Hk. rewrite repeat_length. lia. Qed.
End BoAllocMSumS.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.MemSplit.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtUnwindT OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoison OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtPoisonI OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM0 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMMemA OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM4 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMSbM4 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8s OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8u OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM9c OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM9g OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM9z OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtIMemmove. Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtUnwindT OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoison OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtPoisonI OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM0 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMMemA.BoAllocMI OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM4 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMSbM4.BoAllocM4s OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8s BoAllocM8x OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8u.BoAllocM8t OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM9c.BoAllocM9a OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM9c.BoAllocM9b OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM9c OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM9c.BoAllocM9d BoAllocM9f OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM9g OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM9z OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtIMemmove.AsDepotSum BoAllocMSumS.
From OSSVerify.glaze.binary_reflection.images Require Import AsanUbsan.
Import ListNotations.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
(* [comment removed for export] *)
Ltac wm_clear_disj_or T := lazymatch T with | _ \/ _ => idtac | ?A /\ ?B => first [wm_clear_disj_or A | wm_clear_disj_or B] | ?A <-> ?B => first [wm_clear_disj_or A | wm_clear_disj_or B] | ?A -> ?B => first [wm_clear_disj_or A | wm_clear_disj_or B] end.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AmLia.   (* [comment removed for export] *)
Ltac wm_clear_disj := am_wm_clear_disj.   (* [comment removed for export] *)
Ltac wm_lia0 := tryif noncert_goal_has_var then (Zify.zify; xlia zchecker)
                else first [ solve [noncert_clear_all; Zify.zify; xlia zchecker] | Zify.zify; xlia zchecker ].
#[local] Ltac lia ::= first [ solve [wm_clear_disj; wm_lia0] | wm_lia0 ].

#[local] Abbreviation U := bv_unsigned.
#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).
#[local] Abbreviation LE4 z := (word_to_le_bytes 4 (Z_to_bv 64 z)).
#[local] Abbreviation LE2 z := (word_to_le_bytes 2 (Z_to_bv 64 z)).

Section FPGen.
Context {fx : FPState}.

Lemma at0_litS : forall c : Z, 0 <= c < 2 ^ 64 -> at_ (Z_to_bv 64 0) c = Z_to_bv 64 c.
Proof using. intros c Hc. apply bv_eq. rewrite at_u by (first [ solve [ wd_unorm1; wd_zofnat; lia ] | rewrite u_Z2bv by lia; lia ]). rewrite !u_Z2bv by lia. reflexivity. Qed.
Lemma ARB_litS : forall c : Z, 0 <= c < 2 ^ 64 -> at_ ARB c = Z_to_bv 64 c.
Proof using. intros c Hc. (lazymatch goal with |- ?G => let G' := eval unfold ARB in G in change_no_check G' end). apply at0_litS. exact Hc. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section TAIL.
  Variables (M rom : word -> option byte) (regs : bvmap 5 word).
  Variables (S thr ctxw tr szw naw curw mxw blw w16 w24 : word) (bsz : list byte) (b1 : byte) (n mb nch PA cz tid : Z).
  #[local] Abbreviation size := (sec_needed n).
  #[local] Abbreviation msz := (la_msz (sec_needed n)).
  #[local] Abbreviation spL := (at_ S (-2320)).
  #[local] Abbreviation sp2 := (at_ S (-2272)).
  #[local] Abbreviation m := (Z_to_bv 64 (mb + 4096)).
  #[local] Abbreviation idx := (63 - cz).
  Hypothesis H2 : getr regs 2 = at_ spL (-96).
  Hypothesis H8 : getr regs 8 = Z_to_bv 64 0x10ae08.
  Hypothesis H9 : getr regs 9 = Z_to_bv 64 (0x10ab58 + 64).
  Hypothesis H18 : getr regs 18 = Z_to_bv 64 msz.
  Hypothesis H19 : getr regs 19 = Z_to_bv 64 cz.
  Hypothesis H21 : getr regs 21 = Z_to_bv 64 mb.
  Hypothesis H13 : getr regs 13 = Z_to_bv 64 nch.
  Hypothesis H10 : getr regs 10 = m.
  Hypothesis H26 : getr regs 26 = thr.
  Hypothesis H27 : getr regs 27 = Z_to_bv 64 1.
  (* [comment removed for export] *)
  Hypothesis GS : 2 ^ 32 + 4096 <= U S /\ U S + 16 <= 2 ^ 47.
  Hypothesis Gn : 64513 <= n <= 2 ^ 34.
  Hypothesis Hnch : 0 <= nch < 2 ^ 20.
  Hypothesis Hcz : 0 <= cz <= 63.
  Hypothesis Htid : 0 <= tid < 2 ^ 31.
  Hypothesis Hmb : AIMGHI <= mb /\ mb + msz <= 2 ^ 47 /\ mb mod 4096 = 0.
  Hypothesis Hmbsp : mb + msz <= U S - 3584 \/ U S <= mb.
  Hypothesis HPA : AIMGHI <= PA /\ PA + 2 ^ 23 < 2 ^ 63.
  Hypothesis HPAmb : PA + 2 ^ 23 <= mb \/ mb + msz <= PA.
  Hypothesis HPAsp : PA + 2 ^ 23 <= U S - 3584 \/ U S <= PA.
  Hypothesis GT : (4096 <= U thr /\ hideW (U thr + 4096 <= AIMGLO \/ AIMGHI <= U thr)) /\ U thr + 4096 <= U S - 3584.
  Hypothesis GTmb : U thr + 4096 <= mb \/ mb + msz <= U thr.
  Hypothesis GTPA : U thr + 4096 <= PA \/ PA + 2 ^ 23 <= U thr.
  Hypothesis Gctx : 1 <= U ctxw /\ U ctxw + 4096 <= U S - 3584 /\ (U ctxw + 4096 <= AIMGLO \/ AIMGHI <= U ctxw).
  Hypothesis Gctxmb : U ctxw + 4096 <= mb \/ mb + msz <= U ctxw.
  Hypothesis GctxPA : U ctxw + 4096 <= PA \/ PA + 2 ^ 23 <= U ctxw.
  (* [comment removed for export] *)
  Hypothesis R_pa : rdn BSEGS M (Z_to_bv 64 (0x10ab58 + 72)) 8 = Some (LE8 (Z_to_bv 64 PA)).
  Hypothesis R_na : rdn BSEGS M (Z_to_bv 64 0x10abe0) 8 = Some (LE8 naw).
  Hypothesis R_cur : rdn BSEGS M (Z_to_bv 64 0x10abf0) 8 = Some (LE8 curw).
  Hypothesis R_mx : rdn BSEGS M (Z_to_bv 64 0x10abf8) 8 = Some (LE8 mxw).
  Hypothesis R_bl : rdn BSEGS M (Z_to_bv 64 (0x10ac00 + 8 * idx)) 8 = Some (LE8 blw).
  Hypothesis R_16 : rdn BSEGS M (Z_to_bv 64 0x10ae18) 8 = Some (LE8 w16).
  Hypothesis R_24 : rdn BSEGS M (Z_to_bv 64 0x10ae20) 8 = Some (LE8 w24).
  Hypothesis SOK_h : store_ok BSEGS M (Z_to_bv 64 mb) 32 = true.
  Hypothesis SOK_pa : store_ok BSEGS M (Z_to_bv 64 (PA + 8 * nch)) 8 = true.
  Hypothesis SOK_inst : store_ok BSEGS M (Z_to_bv 64 0x10ab98) 728 = true.
  Hypothesis FLA : forall (o : Z) (v : word),
    In (o, v) [(-8, Z_to_bv 64 0x50d94); (-16, Z_to_bv 64 8); (-24, Z_to_bv 64 n); (-32, Z_to_bv 64 8); (-40, Z_to_bv 64 size); (-48, Z_to_bv 64 2048);
               (-56, Z_to_bv 64 n); (-64, Z_to_bv 64 0x10ab58); (-72, at_ S (-2128)); (-80, Z_to_bv 64 18446744073709551608); (-88, Z_to_bv 64 7)] ->
    rdn BSEGS M (at_ spL o) 8 = Some (LE8 v).
  Hypothesis FC : forall (o : Z) (v : word),
    In (o, v) [(-8, Z_to_bv 64 0x4c834); (-16, Z_to_bv 64 0); (-24, Z_to_bv 64 n); (-32, Z_to_bv 64 8); (-40, Z_to_bv 64 size); (-48, Z_to_bv 64 2048)] ->
    rdn BSEGS M (at_ sp2 o) 8 = Some (LE8 v).
  Hypothesis Rb1 : rdn BSEGS M (at_ m (rz n - 15)) 1 = Some [b1].
  Hypothesis SOKh : store_ok BSEGS M (at_ m (rz n - 16)) 16 = true.
  Hypothesis R16 : rdn BSEGS M (at_ sp2 16) 8 = Some (LE8 (Z_to_bv 64 16)).
  Hypothesis RT0 : rdn BSEGS M thr 8 = Some (LE8 ctxw).
  Hypothesis Rtid : rdn BSEGS M (at_ ctxw 8) 4 = Some (LE4 tid).
  Hypothesis Rtr : rdn BSEGS M (at_ S (-2128)) 8 = Some (LE8 tr).
  Hypothesis Rsz : rdn BSEGS M (at_ (at_ S (-2128)) 8) 8 = Some bsz.
  Hypothesis Hsz : bytes_le_to_Z bsz = U szw /\ length bsz = 8%nat.

  #[local] Abbreviation sumw := (v_add curw (Z_to_bv 64 msz)).
  Definition st_mx : word := if U sumw <? U mxw then mxw else sumw.
  Definition st_m2 : word -> option byte := la_m2 M mb nch PA idx msz naw sumw st_mx blw w16 w24.
  Definition st_mem : word -> option byte := amCs_mem st_m2 m b1 n.

  (* [comment removed for export] *)
  Definition W_sect2 (z : Z) : Prop :=
    (mb + 24 <= z < mb + 32) \/ (PA + 8 * nch <= z < PA + 8 * nch + 8) \/ (0x10abd0 <= z < 0x10ae28).
  Definition W_sect (z : Z) : Prop := W_sect2 z \/ (mb + 4096 + 2032 <= z < mb + 4096 + 2048).

  Lemma st_m2_sum : msum W_sect2 M st_m2.
  Proof using Hsz HPA Hmb Htid Hcz Hnch Gn tid bsz szw rom.
    destruct Hmb as (MB1 & MB2 & MB3). destruct HPA as [PA1 PA2].
    assert (LF0 : 0 <= msz) by (pose proof (sec_needed_bnd n ltac:(lia)); (lazymatch goal with |- ?G => let G' := eval unfold la_msz in G in change_no_check G' end); Z.div_mod_to_equations; lia).
    (lazymatch goal with |- ?G => let G' := eval unfold st_m2, la_m2 in G in change_no_check G' end). msum_nest;
      wd_lenlit; rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; (lazymatch goal with |- ?G => let G' := eval cbn [length Z.of_nat Pos.of_succ_nat Pos.succ Pos.to_nat] in G in change_no_check G' end);
      first [lia | intros z Hz; (lazymatch goal with |- ?G => let G' := eval unfold W_sect2 in G in change_no_check G' end); lia].
  Qed.
  Lemma st_mem_sum : msum W_sect M st_mem.
  Proof using Hsz HPA Hmb Htid Hcz Hnch Gn tid bsz szw rom.
    destruct Hmb as (MB1 & MB2 & MB3). pose proof (rz_sec n ltac:(lia)) as Erz.
    assert (LF0 : 0 <= msz) by (pose proof (sec_needed_bnd n ltac:(lia)); (lazymatch goal with |- ?G => let G' := eval unfold la_msz in G in change_no_check G' end); Z.div_mod_to_equations; lia).
    assert (Um : U m = mb + 4096) by (rewrite u_Z2bv by lia; reflexivity).
    (lazymatch goal with |- ?G => let G' := eval unfold st_mem, amCs_mem in G in change_no_check G' end).
    apply (msum_weaken (wun W_sect2 (fun z => mb + 4096 + 2032 <= z < mb + 4096 + 2048))); [intros z [H|H]; [left; exact H | right; exact H]|].
    eapply msum_trans; [exact st_m2_sum|].
    do 4 (apply msum_wbytes_in;
            [| solve [wd_lenlit; rewrite ?length_N_to_le_bytes, ?at_u by (rewrite Um; lia); (lazymatch goal with |- ?G => let G' := eval cbn [length Z.of_nat Pos.of_succ_nat Pos.succ Pos.to_nat] in G in change_no_check G' end); rewrite Um; lia]
             | solve [wd_lenlit; rewrite ?length_N_to_le_bytes, ?at_u by (rewrite Um; lia); (lazymatch goal with |- ?G => let G' := eval cbn [length Z.of_nat Pos.of_succ_nat Pos.succ Pos.to_nat] in G in change_no_check G' end);
                      intros z Hz; rewrite Um, Erz in Hz; lia]]).
    apply msum_refl.
  Qed.

  Theorem sec_run_tail :
    exists r : bvmap 5 word,
      msteps BSEGS (mkst regs (0x51228 : word) M rom) (mkst r (Z_to_bv 64 0x8f4f0) st_mem rom)
      /\ getr r 1 = Z_to_bv 64 0x4c940 /\ getr r 2 = sp2 /\ getr r 10 = tr /\ getr r 11 = szw
      /\ getr r 8 = Z_to_bv 64 0 /\ getr r 9 = Z_to_bv 64 n /\ getr r 18 = m /\ getr r 19 = Z_to_bv 64 size
      /\ getr r 20 = at_ m (rz n) /\ getr r 21 = at_ m (rz n - 16) /\ getr r 22 = Z_to_bv 64 0x10ab58 /\ getr r 23 = at_ S (-2128)
      /\ getr r 24 = Z_to_bv 64 (tid * 2 ^ 32) /\ getr r 25 = at_ m (rz n + n)
      /\ (forall i : reg, In i [3; 4; 26; 27]%bv -> getr r i = getr regs i).
  Proof using Hsz Rsz Rtr Rtid RT0 R16 SOKh Rb1 FC FLA SOK_inst SOK_pa SOK_h R_24 R_16 R_bl R_mx R_cur R_na R_pa GctxPA Gctxmb Gctx GTPA GTmb GT HPAsp HPAmb HPA Hmbsp Hmb Htid Hcz Hnch Gn GS H27 H26 H10 H13 H21 H19 H18 H9 H8 H2 bsz ctxw thr.
    destruct GS as [S1 S2]. destruct Hmb as (MB1 & MB2 & MB3). destruct HPA as [PA1 PA2]. destruct GT as ((T1 & T1b) & T2). destruct Gctx as (C1 & C2 & C3).
    pose proof (u64_range S) as HSr. pose proof (u64_range thr) as Hthr. pose proof (u64_range ctxw) as Hcr.
    pose proof (rz_sec n ltac:(lia)) as Erz. pose proof (sec_needed_bnd n ltac:(lia)) as Hsnb.
    assert (LF : msz mod 4096 = 0 /\ size + 4096 <= msz <= size + 8191) by ((lazymatch goal with |- ?G => let G' := eval unfold la_msz in G in change_no_check G' end); Z.div_mod_to_equations; lia).
    destruct LF as [LF1 LF2].
    assert (Um : U m = mb + 4096) by (rewrite u_Z2bv by lia; reflexivity).
    assert (UspL : U spL = U S - 2320) by (first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ]).
    assert (Usp2 : U sp2 = U S - 2272) by (first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ]).
    assert (RETL : ret_ok (Z_to_bv 64 0x50d94)) by (apply ret_ok_lit; [lia | reflexivity]).
    assert (RETC : ret_ok (Z_to_bv 64 0x4c834)) by (apply ret_ok_lit; [lia | reflexivity]).
    (* [comment removed for export] *)
    destruct (la_t2bg M rom spL (Z_to_bv 64 0x50d94) (Z_to_bv 64 8) (Z_to_bv 64 n) (Z_to_bv 64 8) (Z_to_bv 64 size) (Z_to_bv 64 2048)
                (Z_to_bv 64 n) (Z_to_bv 64 0x10ab58) (at_ S (-2128)) (Z_to_bv 64 18446744073709551608) (Z_to_bv 64 7) naw curw mxw blw w16 w24
                size mb nch PA cz regs H2 H8 H9 H18 H19 H21 H13 ltac:(rewrite UspL; lia) RETL ltac:(lia) Hnch Hcz ltac:(lia) ltac:(lia)
                ltac:(clear - HPAmb LF1 LF2 Hsnb Gn; lia) ltac:(rewrite UspL; clear - Hmbsp LF1 LF2 Hsnb Gn S1; lia) ltac:(rewrite UspL; clear - HPAsp S1; lia)
                R_pa R_na R_cur R_mx R_bl R_16 R_24 SOK_h SOK_pa SOK_inst
                (FLA (-8) _ ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 20)) (FLA (-16) _ ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 20)) (FLA (-24) _ ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 20))
                (FLA (-32) _ ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 20)) (FLA (-40) _ ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 20)) (FLA (-48) _ ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 20))
                (FLA (-56) _ ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 20)) (FLA (-64) _ ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 20)) (FLA (-72) _ ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 20))
                (FLA (-80) _ ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 20)) (FLA (-88) _ ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 20)))
      as (r1 & RUN1 & (A2 & A1 & A8 & A9 & A18 & A19 & A20 & A21 & A22 & A23 & A24 & A25 & AG1)).
    change (la_m2 M mb nch PA (63 - cz) (la_msz (sec_needed n)) naw (v_add curw (Z_to_bv 64 (la_msz (sec_needed n)))) _ blw w16 w24) with st_m2 in RUN1.
    pose proof st_m2_sum as SUM2.
    assert (K1 : forall i : reg, In i [3; 4; 10; 26; 27]%bv -> getr r1 i = getr regs i).
    { intros i Hi. apply AG1. cbn [In] in Hi |- *. intros Hx. repeat (destruct Hi as [<-|Hi]; [repeat (destruct Hx as [Hx|Hx]; [discriminate Hx|]); exact Hx|]). exact Hi. }
    (* [comment removed for export] *)
    assert (XF : forall (a : word) (k : nat) v, U a + Z.of_nat k <= 2 ^ 64 -> (forall z, U a <= z < U a + Z.of_nat k -> ~ W_sect2 z) ->
              rdn BSEGS M a k = Some v -> rdn BSEGS st_m2 a k = Some v).
    { intros a k v Hnw Hd Hr. exact (msum_rdn_eq BSEGS W_sect2 M st_m2 a k v SUM2 Hnw Hd Hr). }
    assert (XFS : forall (k : Z) (w : nat) v, -3584 <= k -> k + Z.of_nat w <= 0 -> rdn BSEGS M (at_ S k) w = Some v -> rdn BSEGS st_m2 (at_ S k) w = Some v).
    { intros k w v Kl Kh Hr. apply XF; [first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ] | | exact Hr].
      intros z Hz. rewrite at_u in Hz by lia. (lazymatch goal with |- ?G => let G' := eval unfold W_sect2 in G in change_no_check G' end). clear - Hz Kl Kh S1 S2 MB1 LF1 LF2 Hsnb Gn Hmbsp PA1 HPAsp Hnch. lia. }
    (* [comment removed for export] *)
    assert (FC2 : forall (o : Z) (v : word),
              In (o, v) [(-8, Z_to_bv 64 0x4c834); (-16, Z_to_bv 64 0); (-24, Z_to_bv 64 n); (-32, Z_to_bv 64 8); (-40, Z_to_bv 64 size); (-48, Z_to_bv 64 2048)] ->
              rdn BSEGS st_m2 (at_ sp2 o) 8 = Some (LE8 v)).
    { intros o v Hin.
      assert (Ho : -48 <= o <= -8) by (clear - Hin; cbn [In] in Hin; repeat (destruct Hin as [E|Hin]; [injection E as <- <-; lia|]); destruct Hin).
      rewrite at_at. apply XFS; [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia |]. rewrite <- at_at. exact (FC o v Hin). }
    destruct (cbs_ret st_m2 rom sp2 (Z_to_bv 64 0x4c834) (Z_to_bv 64 0) (Z_to_bv 64 n) (Z_to_bv 64 8) (Z_to_bv 64 size) (Z_to_bv 64 2048) m r1
                ltac:(rewrite A2; rewrite !at_at; reflexivity) A8 ltac:(rewrite K1 by ((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 10); exact H10) RETC
                (FC2 (-8) _ ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 10)) (FC2 (-16) _ ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 10)) (FC2 (-24) _ ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 10))
                (FC2 (-32) _ ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 10)) (FC2 (-40) _ ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 10)) (FC2 (-48) _ ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 10)))
      as (r2 & RUN2 & B10 & B2 & B1 & B8 & B9 & B18 & B19 & B20 & AG2).
    assert (K2 : forall i : reg, In i [3; 4; 21; 22; 23; 24; 25; 26; 27]%bv -> getr r2 i = getr r1 i).
    { intros i Hi. apply AG2. cbn [In] in Hi |- *. intros Hx. repeat (destruct Hi as [<-|Hi]; [repeat (destruct Hx as [Hx|Hx]; [discriminate Hx|]); exact Hx|]). exact Hi. }
    (* [comment removed for export] *)
    destruct (amCs_run BSEGS ARB both_HAL2 r2 st_m2 rom sp2 m (at_ S (-2128)) thr ctxw tr szw bsz b1 n tid)
      as (r4 & RUN4 & E1 & E10 & E11 & E18 & E20 & E21 & E24 & E25 & AG4).
    { exact B2. }
    { exact B9. }
    { exact B10. }
    { exact B19. }
    { rewrite Erz. exact B20. }
    { rewrite K2 by ((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 10). exact A21. }
    { rewrite K2 by ((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 10). exact A23. }
    { rewrite K2 by ((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 10). exact A25. }
    { rewrite K2, K1 by ((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 10). exact H26. }
    { rewrite K2, K1 by ((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 10). exact H27. }
    { exact Gn. }
    { exact Htid. }
    { rewrite Um. split; [clear - MB3; Z.div_mod_to_equations; lia | lia]. }
    { rewrite Usp2. lia. }
    { split; [split; [exact T1 | exact T1b] | lia]. }
    { lia. }
    { rewrite at_u by lia. lia. }
    { apply XF; [rewrite at_u by (rewrite Um; lia); rewrite Um; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | | exact Rb1].
      intros z Hz. rewrite at_u in Hz by (rewrite Um; lia). rewrite Um, Erz in Hz. cbn in Hz. (lazymatch goal with |- ?G => let G' := eval unfold W_sect2 in G in change_no_check G' end). clear - Hz MB1 HPAmb PA1 Hnch LF1 LF2 Hsnb Gn. lia. }
    { exact (msum_store_ok BSEGS W_sect2 M st_m2 _ _ SUM2 SOKh). }
    { rewrite at_at. apply XFS; [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia |]. rewrite <- at_at. exact R16. }
    { apply XF; [(lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | | exact RT0]. intros z Hz. cbn in Hz. (lazymatch goal with |- ?G => let G' := eval unfold W_sect2 in G in change_no_check G' end). unfold hideW in T1b. clear - Hz T1 T1b T2 GTmb GTPA MB1 PA1 Hnch LF1 LF2 Hsnb Gn. lia. }
    { apply XF; [first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | | exact Rtid]. intros z Hz. rewrite at_u in Hz by lia. cbn in Hz. (lazymatch goal with |- ?G => let G' := eval unfold W_sect2 in G in change_no_check G' end).
      clear - Hz C1 C2 C3 Gctxmb GctxPA MB1 PA1 Hnch LF1 LF2 Hsnb Gn. lia. }
    { apply XFS; [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | exact Rtr]. }
    { rewrite at_at. apply XFS; [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia |]. rewrite <- at_at. exact Rsz. }
    { exact Hsz. }
    { rewrite Um, Usp2, Erz. clear - Hmbsp LF1 LF2 Hsnb Gn S1. lia. }
    { rewrite Um, Erz. clear - GTmb LF1 LF2 Hsnb Gn T1. lia. }
    { rewrite Um, Erz. clear - Gctxmb LF1 LF2 Hsnb Gn C1. lia. }
    { rewrite Um, Erz, at_u by lia. clear - Hmbsp LF1 LF2 Hsnb Gn S1 S2. lia. }
    change (amCs_mem st_m2 m b1 n) with st_mem in RUN4.
    rewrite (ARB_litS 0x4c834) in RUN4 by lia. rewrite (ARB_litS 0x8f4f0) in RUN4 by lia.
    exists r4. split.
    { eapply msteps_trans; [exact RUN1|]. eapply msteps_trans; [| exact RUN4].
      replace (0x50d94%bv : word) with (Z_to_bv 64 0x50d94 : word) in RUN2 by (apply bv_eq; reflexivity). exact RUN2. }
    split; [rewrite E1; apply ARB_litS; lia|].
    split; [rewrite (AG4 2%bv) by notin; exact B2|].
    split; [exact E10|]. split; [exact E11|].
    split; [rewrite (AG4 8%bv) by notin; exact B8|].
    split; [rewrite (AG4 9%bv) by notin; exact B9|].
    split; [exact E18|].
    split; [rewrite (AG4 19%bv) by notin; exact B19|].
    split; [exact E20|]. split; [exact E21|].
    split; [rewrite (AG4 22%bv) by notin; rewrite K2 by ((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 12); exact A22|].
    split; [rewrite (AG4 23%bv) by notin; rewrite K2 by ((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 12); exact A23|].
    split; [exact E24|]. split; [exact E25|].
    intros i Hi. cbn [In] in Hi.
    repeat (destruct Hi as [<-|Hi]; [rewrite (AG4 _) by notin; rewrite K2 by ((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 10); apply K1; (lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 10|]).
    destruct Hi.
  Qed.
End TAIL.

End FPGen.
