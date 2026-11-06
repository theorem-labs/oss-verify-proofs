(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap Mprotect.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocSim OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys6 OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.BackingAlgebra OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM9b OSSVerify.Proofs.glaze.binary_reflection.lib.AsCodeM5. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.DivergeSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.SpinAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes.AgentNodes OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocSim OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys6.MhKSys OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsK OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys6.AsKSys OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys6.AsKSys2 OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsRtK OSSVerify.Proofs.glaze.binary_reflection.lib.Common.BackingAlgebra OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys6.AsanNodesLibE OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM9b.AsAllocM8m OSSVerify.Proofs.glaze.binary_reflection.lib.AsCodeM5.
From OSSVerify.glaze.binary_reflection.images Require Import Asan.
Import ListNotations.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation ASEGS := Asan.M.loaded_segments.
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
  Hypothesis HOFFSEG : H_off_segments ASEGS Hd.
  Hypothesis WX : wx_segs_nowrap ASEGS.



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
        /\ (m_halted (MKP mdlm) = None /\ lazy_cover Hd (m_vm_lazy (MKP mdlm)) A /\ MInv A (MKP mdlm))
        /\ (m_halted (MDS mdlm) = None /\ lazy_cover Hd (m_vm_lazy (MDS mdlm)) A /\ MInv A (MDS mdlm))) ->
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
    (* [comment removed for export] *)
    (forall (r' : bvmap 5 word) mdlm mdl4,
        same_but_materialized model mdlm -> MInv A mdlm -> same_but_materialized (MDS mdlm) mdl4 -> MInv A mdl4 ->
        mfi_ret regs r' sp ra s0v s1v s2v s3v s4v (Z_to_bv 64 0) ->
        katD ASEGS (mkCfg (mkst r' ra (wbytes (wbytes (unfill addr size M1) (at_ sp (-84)) SCR) (at_ sp (-84)) (LE4 12)) rom) mdl4) Qf) ->
    katsD ASEGS (mkCfg (mkst regs (0x8a688 : word) mem rom) model) Qok Qf.
  Proof using WX HOFFSEG.
    intros A regs mem rom model sp ra s0v s1v s2v s3v s4v s5v addr size name PGP CF Qok Qf MOK MKP MDS M1 ENOMEMw SCR
           H1 H2 H11 H12 H13 H8 H9 H18 H19 H20 H21 Hsp Hret Haddr Hsize Hname HPGP HCF Hstk Rgpg Rpg Rgcf Rdpm Rlim
           Hslot HDgpg HDpg HDgcf HDdpm HDlim HDscr HALT LC AWF MI NODE CHILD CONTOK CONTKP CONTDS.
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
    destruct (CHILD mdlm SBMm MIm) as ((HOK1 & HOK2 & HOK3) & _ & _).
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
    katD ASEGS (mkCfg (mkst (regupd r1 10 addr) (0x80740 : word) (zfill addr size M1) rom)
                      (fixedin_ok_model 3 (Z_to_bv 64 50) addr size mdlm)) Q' ->
    doomed ASEGS (mkCfg (mkst (regupd r1 10 (Z_to_bv 64 (2 ^ 64 - 12))) (0x80740 : word) M1 rom) mdlm) ->
    doomed ASEGS (mkCfg (mkst (regupd r1 10 (Z_to_bv 64 (2 ^ 64 - 12))) (0x80740 : word) (unfill addr size M1) rom)
                      (fixedin_destroyed_model addr size mdlm)) ->
    katD ASEGS (mkCfg (epend r1 (0x8073c : word) M1 rom (Z_to_bv 64 222)) mdlm) Q'.
  Proof using.
    intros r1 M1 rom mdlm addr size Q' HALT B10 B11 B12 B13 B14 B15 Hal Hpos Hsz Hszal Htop Htop64 Hrf Hmc Hbud KOK KKP KDS.
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
    apply (katD_mmap_fixedin3_dm ASEGS ms mdlm (Z_to_bv 64 222) 3 (Z_to_bv 64 50) addr (U size) HALT eq_refl
             ltac:(rewrite u_Z2bv by lia; reflexivity) ltac:(right; reflexivity) ltac:(vm_compute; reflexivity)
             E0 ltac:((lazymatch goal with |- ?G => let G' := eval unfold page_size in G in change_no_check G' end); exact Hal) Hpos E1 Hsz E2 E3 E4 E5 ltac:(rewrite PRU; exact Htop) Htop64
             ltac:(rewrite EN; exact Hrf) ltac:(rewrite EN; exact Hmc) ltac:(intros _; rewrite EN; exact Hbud) Q').
    - (* [comment removed for export] *)
      (lazymatch goal with |- ?G => let G' := eval unfold fxin_nx, fxin_effs, fxin_ms' in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval unfold ms in G in change_no_check G' end). rewrite AsKSys6.MhKSys.adv_retU_epend.
      replace (errno_ret ENOMEM) with (Z_to_bv 64 (2 ^ 64 - 12) : word) by (apply bv_eq; vm_compute; reflexivity).
      replace (v_addi (0x8073c%bv : word) 4) with (0x80740%bv : word) by (apply bv_eq; vm_compute; reflexivity).
      exact KKP.
    - (* [comment removed for export] *)
      (lazymatch goal with |- ?G => let G' := eval unfold fxin_nx, fxin_effs, fxin_ms' in G in change_no_check G' end). rewrite EN. (lazymatch goal with |- ?G => let G' := eval unfold fixedin_ok_eff in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [Z.eqb] in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval unfold ms in G in change_no_check G' end).
      rewrite (AsKSys6.MhKSys.adv_zerosr_epend r1 (0x8073c%bv : word) M1 rom (Z_to_bv 64 222) addr addr size).
      replace (v_addi (0x8073c%bv : word) 4) with (0x80740%bv : word) by (apply bv_eq; vm_compute; reflexivity).
      exact KOK.
    - (* [comment removed for export] *)
      (lazymatch goal with |- ?G => let G' := eval unfold fxin_nx, fxin_effs, fxin_ms' in G in change_no_check G' end). rewrite EN. (lazymatch goal with |- ?G => let G' := eval unfold ms in G in change_no_check G' end). rewrite AsKSys6.MhKSys.adv_unmaps1_epend.
      replace (errno_ret ENOMEM) with (Z_to_bv 64 (2 ^ 64 - 12) : word) by (apply bv_eq; vm_compute; reflexivity).
      replace (v_addi (0x8073c%bv : word) 4) with (0x80740%bv : word) by (apply bv_eq; vm_compute; reflexivity).
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
    katwD ASEGS (mkCfg (mkst (regupd r1 10 addr) (0x80740 : word) (zfill addr size M1) rom)
                      (fixedin_ok_model 3 (Z_to_bv 64 50) addr size mdlm)) Qok' Qf' ->
    katsD ASEGS (mkCfg (epend r1 (0x8073c : word) M1 rom (Z_to_bv 64 222)) mdlm) Qok' Qf'.
  Proof using.
    intros r1 M1 rom mdlm addr size Qok' Qf' HALT B10 B11 B12 B13 B14 B15 Hal Hpos Hsz Hszal Htop Htop64 Hrf Hmc Hbud KOK.
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
             (node_mmap_fixedin1 ASEGS ms mdlm (Z_to_bv 64 222) 3 (Z_to_bv 64 50) addr (U size) HALT eq_refl
                ltac:(rewrite u_Z2bv by lia; reflexivity) ltac:(right; reflexivity) ltac:(vm_compute; reflexivity)
                E0 ltac:((lazymatch goal with |- ?G => let G' := eval unfold page_size in G in change_no_check G' end); exact Hal) Hpos E1 Hsz E2 E3 E4 E5 ltac:(rewrite PRU; exact Htop) Htop64
                ltac:(rewrite EN; exact Hrf) ltac:(rewrite EN; exact Hmc) ltac:(intros _; rewrite EN; exact Hbud))).
    intros [].
    (lazymatch goal with |- ?G => let G' := eval unfold fxin_nx, fxin_effs, fxin_ms' in G in change_no_check G' end). rewrite EN. (lazymatch goal with |- ?G => let G' := eval unfold fixedin_ok_eff in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [Z.eqb] in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval unfold ms in G in change_no_check G' end).
    rewrite (AsKSys6.MhKSys.adv_zerosr_epend r1 (0x8073c%bv : word) M1 rom (Z_to_bv 64 222) addr addr size).
    replace (v_addi (0x8073c%bv : word) 4) with (0x80740%bv : word) by (apply bv_eq; vm_compute; reflexivity).
    exact KOK.
  Qed.
End NODE3.
End FPGen1.
