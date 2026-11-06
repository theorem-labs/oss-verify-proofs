(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AmLia.   (* [comment removed for export] *)
(* [comment removed for export] *)
Require Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFHyp OSSVerify.Proofs.glaze.binary_reflection.lib.BoDepotHit OSSVerify.Proofs.glaze.binary_reflection.lib.BoDepotTop3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys10 OSSVerify.glaze.binary_reflection.images.AsanUbsan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module BoDepotHyp9w.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.MemSplit OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsRtK.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinv3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinvGeom3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOps3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d.AsAinvFreeS.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFHyp OSSVerify.Proofs.glaze.binary_reflection.lib.BoDepotHit OSSVerify.Proofs.glaze.binary_reflection.lib.BoDepotTop3.BoDepotHyp9 OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys10.AsDepotTop0.
Import OSSVerify.glaze.binary_reflection.images.AsanUbsan.
Import ListNotations.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

#[local] Abbreviation U := bv_unsigned.
#[local] Abbreviation BSEGS := AsanUbsan.M.loaded_segments.

Section WithCeil.
Context {RC : run_ceil}.

Definition depot_foot_w (bt : as_boot) (KD : Z) (st' : ast) (sp : Z) (a : Z) : Prop :=
  depot_foot bt KD st' sp a \/ (SSOBJ bt + 8 <= a < SSOBJ bt + 16) \/ (DEPOT_NIDS bt + 8 <= a < DEPOT_NIDS bt + 12).

Definition depot_post_w (bt : as_boot) (FXOK : FPState -> Prop) (KD : Z) (X : Z -> Prop) (st : ast) (Lc FF : list (Z * Z))
           (M : mem) (mdl : Model) (R : bvmap 5 word) (sp ret : word) (c' : config) : Prop :=
  exists fx' st' (M' : mem) mdl' (R' : bvmap 5 word) (id : Z),
    c' = mkCfg (@mkst fx' R' ret M' (seg_rom BSEGS)) mdl'
    /\ FXOK fx' /\ (exists d' naa, st' = depot_st st d' naa)
    /\ WF bt st' Lc FF /\ RepX bt X st' Lc FF M' mdl'
    /\ (forall a : word, X (U a) -> (U sp <= U a \/ U a < U sp - KD) -> M' a = M a)
    /\ (forall a : word, M' a <> M a -> depot_foot_w bt KD st' (U sp) (U a) /\ M' a <> None)
    /\ (forall a : word, M' a <> M a -> (U sp - KD <= U a < U sp) \/ rt_priv (bt_ia bt) Lc FF (U a) \/ in_wins (ia_priv (bt_ia bt)) (U a))
    /\ regs_kept R R' /\ getr R' 10 = Z_to_bv 64 id /\ 0 <= id < 2 ^ 32
    /\ same_except_vm mdl mdl'
    /\ (forall a, 0 <= a < 2 ^ 64 -> lzb mdl' a = lzb mdl a                                 (* [comment removed for export] *)
               \/ (exists b, In b (dp_storeblocks (a_dep st')) /\ ~ In b (dp_storeblocks (a_dep st)) /\ b <= a < b + 2 ^ 23))
    /\ m_halted mdl' = None
    /\ BackingAlgebra.model_ivs_wf mdl'.


(* [comment removed for export] *)
Definition miss_case_w (bt : as_boot) (FXOK : FPState -> Prop) (KD : Z) (C : ast -> Z -> Prop) : Prop :=
  forall fx (X : Z -> Prop) st Lc FF (M M0 : mem) mdl (R r : bvmap 5 word) (sp buf ret : word) (sz tag : Z) (ws : list word),
    FXOK fx -> m_halted mdl = None -> BackingAlgebra.model_ivs_wf mdl ->
    WF bt st Lc FF -> Rep bt st Lc FF M0 mdl -> (forall a : word, M a <> M0 a -> X (U a) /\ M a <> None) ->
    (forall a, X a -> ~ (ia_img_lo (bt_ia bt) <= a < ia_img_hi (bt_ia bt))) -> PX bt st X -> (exists h : option Z, holes_le h st) ->
    depot_room bt st -> a_kact st <= KCAP ->
    getr R 1 = ret -> getr R 2 = sp ->
    CEIL + KD <= U sp -> U sp + 2192 <= 2 ^ 47 -> ret_ok ret ->
    (forall a : word, U sp - KD <= U a < U sp -> M a <> None /\ store_ok BSEGS M a 1%nat = true) ->
    1 <= sz <= 8 -> 0 <= tag < 256 -> U sp <= U buf -> U buf + 8 * sz < 2 ^ 64 ->
    (forall i, U buf <= i < U buf + 8 * sz -> M (Z_to_bv 64 i) <> None) ->
    C st sz ->
    let Hd := HID st mdl in let Mr := mrestrict Hd M in let h := sd_hashN ws tag in
    msteps BSEGS (@mkst fx R (Z_to_bv 64 0x8f4f0) Mr (seg_rom BSEGS))
                 (@mkst fx r (Z_to_bv 64 0x8f688) (sd_frame Mr sp R ret buf (Z_to_bv 64 (sz + tag * 2 ^ 32))) (seg_rom BSEGS)) ->
    getr r 2 = at_ sp (-112) /\ getr r 8 = Z_to_bv 64 0 /\ getr r 9 = Z_to_bv 64 0x1f0098
    /\ getr r 18 = Z_to_bv 64 (0x1f0098 + 4 * sd_bix h) /\ getr r 19 = h /\ getr r 20 = Z_to_bv 64 (0x1f0098 + 4194312)
    /\ getr r 22 = Z_to_bv 64 65535 /\ getr r 24 = Z_to_bv 64 (0x1f0098 + 4194320) /\ getr r 25 = Z_to_bv 64 (dp_tab (a_dep st) (sd_bix h))
    /\ regs_agree (fun i : reg => In i sd_clobx) R r ->
    katD BSEGS (mkCfg (@mkst fx R (Z_to_bv 64 0x8f4f0) M (seg_rom BSEGS)) mdl)
         (depot_post_w bt FXOK KD X st Lc FF M mdl R sp ret).
End WithCeil.
End BoDepotHyp9w.
Require LinuxProcessSemantics.Riscv.Sem OSSVerify.Proofs.glaze.binary_reflection.lib.Common.SumsLib OSSVerify.Proofs.glaze.binary_reflection.lib.BoDepotRunI OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRc4c OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtIMemmove.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module BoDepotRunF.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.Common.SumsLib.StartupAux.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib.AsRtAtomic OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.BoDepotHit OSSVerify.Proofs.glaze.binary_reflection.lib.BoDepotRunI.BoDepotLock OSSVerify.Proofs.glaze.binary_reflection.lib.BoDepotRunI.BoDepotIns OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRc4c.BoDepotStore OSSVerify.Proofs.glaze.binary_reflection.lib.BoDepotRunI.BoDepotStoreR OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtIMemmove.AsDepotSum OSSVerify.Proofs.glaze.binary_reflection.lib.BoDepotRunI.BoDepotRunT OSSVerify.Proofs.glaze.binary_reflection.lib.BoDepotRunI.BoDepotRunH OSSVerify.Proofs.glaze.binary_reflection.lib.BoDepotRunI.BoDepotRunS OSSVerify.Proofs.glaze.binary_reflection.lib.BoDepotRunI.
Import OSSVerify.glaze.binary_reflection.images.AsanUbsan.
Import ListNotations.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation BSEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).
#[local] Abbreviation LE4 v := (word_to_le_bytes 4 v).
#[local] Abbreviation U := bv_unsigned.

Section FPGen.
Context {fx : FPState}.

Definition fstore_W (P nd b : word) (cellz dstz n : Z) : Z -> Prop :=
  wun (ivl (U P - 224) 96) (wun (ivl (U nd + 8) 8) (wun (ivl (U b) 4) (wun (ivl 1966216 8) (wun (ivl cellz 4) (ivl dstz n))))).

Section FS.
  Variables (M1 rom : word -> option byte) (P ra nd b hsh tr blkd CF : word) (hd idz sz tag tot sov : Z) (bs : list byte).
  Variables (s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v : word).
  Variable r1 : bvmap 5 word.
  #[local] Abbreviation Q := (at_ P (-112)).
  #[local] Abbreviation spS := (at_ Q (-32)).
  #[local] Abbreviation packp := (at_ Q (-24)).
  #[local] Abbreviation args := (at_ P (-104)).
  #[local] Abbreviation cellz := (1966216 + 16 * (tot / 2 ^ 20) + 24)%Z.
  #[local] Abbreviation dstz := (U blkd + 8 * (tot mod 2 ^ 20))%Z.
  Hypothesis AT : at_store P nd b hsh hd idz r1 M1.
  Hypothesis HP : (2 ^ 32 + 224 <= U P /\ U P + 16 <= 2 ^ 47)%Z.
  Hypothesis Hret : ret_ok ra.
  Hypothesis HCF : (U CF + 244 <= 1966216)%Z.
  Hypothesis Hnd : (1966216 + 65552 <= U nd /\ U nd + 16 <= U P - 224)%Z.
  Hypothesis Hb : (1966216 + 65552 <= U b /\ U b + 4 <= U P - 224 /\ (U b + 4 <= U nd \/ U nd + 16 <= U b))%Z.
  Hypothesis Hblkd : (1966216 + 2 ^ 20 <= U blkd /\ U blkd + 2 ^ 23 <= U P - 224 /\ (U nd + 16 <= U blkd \/ U blkd + 2 ^ 23 <= U nd)
                      /\ (U b + 4 <= U blkd \/ U blkd + 2 ^ 23 <= U b))%Z.
  Hypothesis HtrP : (U P <= U tr /\ U tr + 8 * sz < 2 ^ 64)%Z.
  Hypothesis Hsz : (1 <= sz < 255)%Z.
  Hypothesis Htag : (0 <= tag < 256)%Z.
  Hypothesis Hhd : (0 <= hd < 2 ^ 31)%Z.
  Hypothesis Htot : (0 <= tot /\ tot + sz + 1 <= 2 ^ 32)%Z.
  Hypothesis Hsame : (tot / 2 ^ 20 = (tot + sz) / 2 ^ 20)%Z.
  Hypothesis Hsov : (0 <= sov < 2 ^ 32)%Z.
  Hypothesis Hbs : length bs = Z.to_nat (8 * sz).
  Hypothesis Rsz : rdn BSEGS M1 (at_ args 8) 4 = Some (LE4 (Z_to_bv 64 sz)).
  Hypothesis Rtag : rdn BSEGS M1 (at_ args 12) 4 = Some (LE4 (Z_to_bv 64 tag)).
  Hypothesis Rtr : rdn BSEGS M1 args 8 = Some (LE8 tr).
  Hypothesis Rws : rdn BSEGS M1 tr (length bs) = Some bs.
  Hypothesis Rtot : rdn BSEGS M1 SSW 8 = Some (LE8 (Z_to_bv 64 tot)).
  Hypothesis Rblk : rdn BSEGS M1 (Z_to_bv 64 (U SSW + 16 * (tot / 2 ^ 20) + 16)) 8 = Some (LE8 blkd).
  Hypothesis Rso : rdn BSEGS M1 (st_cell SSW tot) 4 = Some (LE4 (Z_to_bv 64 sov)).
  Hypothesis Rcfp : rdn BSEGS M1 (Z_to_bv 64 1072904) 8 = Some (LE8 CF).
  Hypothesis Rflag : rdn BSEGS M1 (at_ CF 240) 4 = Some (LE4 (Z_to_bv 64 0)).
  Hypothesis SL : forall (k : Z) (v : word),
    In (k, v) [(-8, ra); (-16, s0v); (-24, s1v); (-32, s2v); (-40, s3v); (-48, s4v); (-56, s5v); (-64, s6v); (-72, s7v); (-80, s8v); (-88, s9v)]%Z ->
    rdn BSEGS M1 (at_ P k) 8 = Some (LE8 v).
  Hypothesis SOKb : store_ok BSEGS M1 b 4 = true.
  Hypothesis SOKn : store_ok BSEGS M1 nd 16 = true.
  Hypothesis Hstk : store_ok BSEGS M1 (at_ P (-224)) 112 = true.
  Hypothesis SOKS : store_ok BSEGS M1 SSW 8 = true.
  Hypothesis SOKso : store_ok BSEGS M1 (st_cell SSW tot) 4 = true.
  Hypothesis SOKd : store_ok BSEGS M1 (st_dst blkd tot) (8 + length bs) = true.

  Lemma put_from_store :
    exists r M', msteps BSEGS (mkst r1 (0x8cef4 : word) M1 rom) (mkst r ra M' rom)
      /\ msum (fstore_W P nd b cellz dstz (8 + 8 * sz)) M1 M'
      /\ getr r 10 = Z_to_bv 64 idz /\ getr r 2 = P /\ getr r 1 = ra
      /\ getr r 8 = s0v /\ getr r 9 = s1v /\ getr r 18 = s2v /\ getr r 19 = s3v /\ getr r 20 = s4v /\ getr r 21 = s5v
      /\ getr r 22 = s6v /\ getr r 23 = s7v /\ getr r 24 = s8v /\ getr r 25 = s9v
      /\ rdn BSEGS M' b 4 = Some (LE4 (Z_to_bv 64 idz))
      /\ rdn BSEGS M' (at_ nd 8) 4 = Some (LE4 (Z_to_bv 64 hd)) /\ rdn BSEGS M' (at_ nd 12) 4 = Some (LE4 (st_id tot))
      /\ rdn BSEGS M' SSW 8 = Some (LE8 (v_add (Z_to_bv 64 tot) (Z_to_bv 64 (sz + 1))))
      /\ rdn BSEGS M' (st_cell SSW tot) 4 = Some (LE4 (v_add (Z_to_bv 64 sov) (Z_to_bv 64 (sz + 1))))
      /\ regs_agree (fun i : reg => In i put_clob) r1 r.
  Proof using AT HCF HP Hb Hblkd Hbs Hhd Hnd Hret Hsame Hsov Hstk Hsz Htag Htot HtrP Rblk Rcfp Rflag Rso Rsz Rtag Rtot Rtr Rws SL SOKS SOKb SOKd SOKn SOKso.
    pose proof (u64_range P) as HPr. pose proof (u64_range nd) as Hndr. pose proof (u64_range b) as Hbr. pose proof (u64_range blkd) as Hbdr.
    pose proof (u64_range tr) as Htrr. pose proof (u64_range CF) as HCr.
    destruct HP as [P1 P2]. destruct Hnd as [ND1 ND2]. destruct Hb as (B1' & B2' & B3'). destruct Hblkd as (BD1 & BD2 & BD3 & BD4).
    destruct HtrP as [T1 T2]. destruct Htot as [T0 T32].
    assert (USS : U SSW = 1966216%Z) by reflexivity.
    assert (UQ : U Q = (U P - 112)%Z) by (first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ]).
    assert (UspS : U spS = (U P - 144)%Z) by (first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ]).
    assert (Upk : U packp = (U P - 136)%Z) by (first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ]).
    assert (Uargs : U args = (U P - 104)%Z) by (first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ]).
    assert (Un8 : U (at_ nd 8) = (U nd + 8)%Z) by (first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ]).
    assert (Un12 : U (at_ nd 12) = (U nd + 12)%Z) by (first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ]).
    assert (Q20 : (0 <= tot / 2 ^ 20 < 2 ^ 12)%Z) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
    assert (M20 : (0 <= tot mod 2 ^ 20 /\ tot mod 2 ^ 20 + sz < 2 ^ 20)%Z).
    { pose proof (Z.div_mod tot (2 ^ 20) ltac:(lia)) as E1. pose proof (Z.mod_pos_bound tot (2 ^ 20) ltac:(lia)) as B1.
      pose proof (Z.div_mod (tot + sz) (2 ^ 20) ltac:(lia)) as E2. pose proof (Z.mod_pos_bound (tot + sz) (2 ^ 20) ltac:(lia)) as B2.
      rewrite <- Hsame in E2. lia. }
    assert (Lbs : Z.of_nat (length bs) = (8 * sz)%Z) by (rewrite Hbs, Z2Nat.id by lia; reflexivity).
    assert (Ucell : U (st_cell SSW tot) = cellz) by ((lazymatch goal with |- ?G => let G' := eval unfold st_cell in G in change_no_check G' end); rewrite USS; rewrite u_Z2bv by lia; reflexivity).
    assert (Udst : U (st_dst blkd tot) = dstz) by ((lazymatch goal with |- ?G => let G' := eval unfold st_dst in G in change_no_check G' end); rewrite u_Z2bv by lia; reflexivity).
    destruct AT as (A1 & A2 & A8 & A10 & A11 & A12 & A9 & A18 & A21 & A23 & RhshH & RraH & Rs0H).
    (* [comment removed for export] *)
    destruct (st_run M1 rom spS (0x8f234 : word) SSW args packp tr blkd nd nd b (getr r1 19) (getr r1 20) (getr r1 21) sz tag tot sov bs r1
                A1 A2 A8 A9 A18 eq_refl eq_refl eq_refl A10 A11 A12
                ltac:(rewrite UspS; lia) ltac:((lazymatch goal with |- ?G => let G' := eval unfold ret_ok in G in change_no_check G' end); apply bv_eq; vm_compute; reflexivity)
                ltac:(rewrite UspS, Uargs; lia) ltac:(rewrite UspS, Upk, Uargs; lia) ltac:(rewrite UspS, Upk; lia)
                Hsz Htag (conj T0 T32) Hsame Hsov ltac:(rewrite USS; split; [reflexivity | lia]) ltac:(rewrite USS, UspS; lia) Hbs
                Rsz Rtag Rtr Rws Rtot Rblk Rso)
      as (r2 & RUN2 & B10 & B2 & B1 & B8 & B9 & B18 & B19 & B20 & B21 & AG2).
    { rewrite at_at. first [clear - UQ Hstk HP | idtac]; (eapply (store_ok_sub BSEGS M1 (at_ P (-224)) _ 112); [first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ] | exact Hstk | first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite !at_u by lia; lia ] | first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite !at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ]]). }
    { eapply (store_ok_sub BSEGS M1 (at_ P (-224)) _ 112); [first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ] | exact Hstk | rewrite Upk, at_u by lia; lia | rewrite Upk, at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia]. }
    { exact SOKS. } { exact SOKso. } { exact SOKd. }
    set (M2 := st_mem M1 spS (0x8f234 : word) nd nd b (getr r1 19) (getr r1 20) (getr r1 21) SSW packp blkd tot sz tag sov bs) in *.
    destruct (st_mem_sum M1 spS (0x8f234 : word) nd nd b (getr r1 19) (getr r1 20) (getr r1 21) SSW packp blkd tot sz tag sov bs
                ltac:(rewrite UspS; lia) ltac:(rewrite UspS, Upk; lia) Hsz (conj T0 T32) ltac:(rewrite USS; lia) ltac:(rewrite USS, UspS; lia) Hbs ltac:(lia))
      as (SS & RtotS & RsoS & RpkS).
    fold M2 in SS, RtotS, RsoS, RpkS.
    assert (THRU2 : forall (a : word) (n : nat) v, (U a + Z.of_nat n <= 2 ^ 64)%Z ->
              (U a + Z.of_nat n <= U P - 224 \/ U P - 128 <= U a)%Z -> (U a + Z.of_nat n <= 1966216 \/ 1966216 + 8 <= U a)%Z ->
              (U a + Z.of_nat n <= cellz \/ cellz + 4 <= U a)%Z -> (U a + Z.of_nat n <= dstz \/ dstz + 8 + 8 * sz <= U a)%Z ->
              rdn BSEGS M1 a n = Some v -> rdn BSEGS M2 a n = Some v).
    { intros a n v B0 X1 X2 X3 X4 Hr. apply (msum_rdn_eq BSEGS _ M1 M2 _ _ _ SS B0); [| exact Hr].
      intros z Hz. (lazymatch goal with |- ?G => let G' := eval unfold store_W, wun, ivl in G in change_no_check G' end). rewrite USS, UspS, Upk. first [clear - Hz X4 X3 X2 X1 | idtac]; (lia). }
    (* [comment removed for export] *)
    assert (NI2 : forall i : reg, In i [23] -> ~ In i [1; 2; 5; 6; 8; 9; 10; 11; 12; 13; 14; 15; 18; 19; 20; 21]).
    { intros i Hi Hx. cbn [In] in Hi, Hx. repeat (destruct Hi as [<-|Hi]; [repeat (destruct Hx as [Hx|Hx]; [discriminate Hx|]); exact Hx|]). exact Hi. }
    destruct (put_tail M2 rom P ra nd b (st_id tot) (Z_to_bv 64 hd) (Z_to_bv 64 idz) CF (0 + st_full sov (sz + 1))
                s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v r2 B2 B8 B9 B10 B18 ltac:(rewrite B21; exact A21)
                ltac:(rewrite (AG2 23%bv) by (apply NI2; (lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); (repeat match goal with H : _ |- _ => clear H end; tauto)); exact A23)
                ltac:((first [clear - HP | idtac]; lia)) Hret ltac:((first [clear - Hnd HCF | idtac]; lia)) ltac:((first [clear - Hb | idtac]; lia))
                ltac:((lazymatch goal with |- ?G => let G' := eval unfold st_full in G in change_no_check G' end); destruct (sz + 1 + sov =? 1048576)%Z; (repeat match goal with H : _ |- _ => clear H end; lia)) ltac:((first [clear - HCF | idtac]; lia)) RpkS)
      as (r3 & M3 & RUN3 & ST & C10 & C2 & C1 & C8 & C9 & C18 & C19 & C20 & C21 & C22 & C23 & C24 & C25 & Rlink & Rsid & Rbk & AG3).
    { first [clear - THRU2 RraH M20 Q20 UQ Hblkd HP | idtac]; (apply THRU2; [first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | exact RraH]). }
    { first [clear - THRU2 Rs0H M20 Q20 UQ Hblkd HP | idtac]; (apply THRU2; [first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | exact Rs0H]). }
    { apply THRU2; [first [ solve [ wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite u_Z2bv by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | first [ solve [ wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite u_Z2bv by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | first [ solve [ wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite u_Z2bv by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | first [ solve [ wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite u_Z2bv by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | first [ solve [ wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite u_Z2bv by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | exact Rcfp]. }
    { apply THRU2; [first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | exact Rflag]. }
    { apply (msum_store_ok BSEGS _ M1 M2 _ _ SS). eapply (store_ok_sub BSEGS M1 nd _ 16); [lia | exact SOKn | rewrite Un12; lia | rewrite Un12; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia]. }
    { apply (msum_store_ok BSEGS _ M1 M2 _ _ SS). eapply (store_ok_sub BSEGS M1 nd _ 16); [lia | exact SOKn | rewrite Un8; lia | rewrite Un8; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia]. }
    { exact (msum_store_ok BSEGS _ M1 M2 _ _ SS SOKb). }
    { apply (msum_store_ok BSEGS _ M1 M2 _ _ SS). rewrite at_at. eapply (store_ok_sub BSEGS M1 (at_ P (-224)) _ 112); [first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ] | exact Hstk | first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite !at_u by lia; lia ] | first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite !at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ]]. }
    { intros k v Hin.
      assert (K : (-88 <= k <= -8)%Z) by (cbn [In] in Hin; repeat (destruct Hin as [E|Hin]; [injection E as <- <-; lia|]); destruct Hin).
      first [clear - K Hin THRU2 M20 Q20 SL Hblkd HP | idtac]; (apply THRU2; [first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | exact (SL k v Hin)]). }
    assert (THRU3 : forall (a : word) (n : nat) v, (U a + Z.of_nat n <= 2 ^ 64)%Z ->
              (U a + Z.of_nat n <= U P - 160 \/ U P - 144 <= U a)%Z -> (U a + Z.of_nat n <= U nd + 8 \/ U nd + 16 <= U a)%Z ->
              (U a + Z.of_nat n <= U b \/ U b + 4 <= U a)%Z -> rdn BSEGS M2 a n = Some v -> rdn BSEGS M3 a n = Some v).
    { intros a n v B0 X1 X2 X3 Hr. apply (msum_rdn_eq BSEGS _ M2 M3 _ _ _ ST B0); [| exact Hr].
      intros z Hz. (lazymatch goal with |- ?G => let G' := eval unfold tail_W, wun, ivl in G in change_no_check G' end). first [clear - Hz X3 X2 X1 | idtac]; (lia). }
    exists r3, M3. split; [eapply msteps_trans; [exact RUN2 | exact RUN3]|].
    split.
    { eapply msum_weaken; [| exact (msum_trans _ _ _ _ _ SS ST)]. (lazymatch goal with |- ?G => let G' := eval unfold fstore_W, store_W, tail_W, wun, ivl in G in change_no_check G' end). rewrite USS, UspS, Upk. intros z Hz. first [clear - Hz | idtac]; (lia). }
    repeat (split; [assumption|]).
    split. { apply THRU3; [rewrite USS; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite USS; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite USS; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite USS; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | exact RtotS]. }
    split. { first [clear - THRU3 RsoS Ucell Q20 Hb Hnd | idtac]; (apply THRU3; [rewrite Ucell; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite Ucell; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite Ucell; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite Ucell; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | exact RsoS]). }
    apply (regs_agree_trans _ r1 r2 r3); [ra_pc AG2 | exact AG3].
  Qed.
End FS.
End FPGen.
End BoDepotRunF.
Module BoDepotRunN2.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.Common.SumsLib.StartupAux.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib.AsRtAtomic OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.BoDepotHit OSSVerify.Proofs.glaze.binary_reflection.lib.BoDepotRunI.BoDepotLock OSSVerify.Proofs.glaze.binary_reflection.lib.BoDepotRunI.BoDepotIns OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRc4c.BoDepotStore OSSVerify.Proofs.glaze.binary_reflection.lib.BoDepotRunI.BoDepotStoreR OSSVerify.Proofs.glaze.binary_reflection.lib.BoDepotRunI.BoDepotMap OSSVerify.Proofs.glaze.binary_reflection.lib.BoDepotRunI.BoDepotIns2 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtIMemmove.AsDepotSum OSSVerify.Proofs.glaze.binary_reflection.lib.BoDepotRunI.BoDepotRunT OSSVerify.Proofs.glaze.binary_reflection.lib.BoDepotRunI.BoDepotRunH OSSVerify.Proofs.glaze.binary_reflection.lib.BoDepotRunI.BoDepotRunS OSSVerify.Proofs.glaze.binary_reflection.lib.BoDepotRunI BoDepotRunF OSSVerify.Proofs.glaze.binary_reflection.lib.BoDepotRunI.BoDepotRunN.
Import OSSVerify.glaze.binary_reflection.images.AsanUbsan.
Import ListNotations.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation BSEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).
#[local] Abbreviation LE4 v := (word_to_le_bytes 4 v).
#[local] Abbreviation U := bv_unsigned.

Section FPGen.
Context {fx : FPState}.

Definition n1tail_W (P MU nd b : word) (idx cellz dstz n : Z) : Z -> Prop :=
  wun (n1post_W P MU nd idx) (fstore_W P nd b cellz dstz n).

Section N1TAIL.
  Variables (MB rom : word -> option byte) (P ra MU hsh newblk b tr blkd CF : word) (hd NIDS sz tag tot sov : Z) (bs : list byte).
  Variables (s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v : word).
  Variable regs : bvmap 5 word.
  #[local] Abbreviation Q := (at_ P (-112)).
  #[local] Abbreviation idx := ((NIDS + 1) / 2 ^ 16)%Z.
  #[local] Abbreviation nd := (di_node newblk NIDS).
  #[local] Abbreviation args := (at_ P (-104)).
  #[local] Abbreviation cellz := (1966216 + 16 * (tot / 2 ^ 20) + 24)%Z.
  #[local] Abbreviation dstz := (U blkd + 8 * (tot mod 2 ^ 20))%Z.
  Hypothesis H2 : getr regs 2 = at_ Q (-32).
  Hypothesis H8 : getr regs 8 = MU.
  Hypothesis H9 : getr regs 9 = Z_to_bv 64 (U MU + 8 * idx).
  Hypothesis H10 : getr regs 10 = newblk.
  Hypothesis H19 : getr regs 19 = hsh.
  Hypothesis H21 : getr regs 21 = Z_to_bv 64 hd.
  Hypothesis H22 : getr regs 22 = Z_to_bv 64 65535.
  Hypothesis H23 : getr regs 23 = Z_to_bv 64 (NIDS + 1).
  Hypothesis HP : (2 ^ 32 + 224 <= U P /\ U P + 16 <= 2 ^ 47)%Z.
  Hypothesis Hret : ret_ok ra.
  Hypothesis HMU : (1966216 + 65552 + 4 * 2 ^ 20 <= U MU /\ U MU + 8 + 8 * 2 ^ 15 <= 2 ^ 32)%Z.
  Hypothesis HCF : (U CF + 244 <= 1966216)%Z.
  Hypothesis Hn : (0 <= NIDS /\ NIDS + 1 < 2 ^ 31)%Z.
  Hypothesis Hblk : (U MU + 8 + 8 * 2 ^ 15 <= U newblk /\ U newblk + 2 ^ 20 <= U P - 224)%Z.
  Hypothesis Hb : (1966216 + 65552 <= U b /\ U b + 4 <= U MU)%Z.
  Hypothesis Hblkd : (U MU + 8 + 8 * 2 ^ 15 <= U blkd /\ U blkd + 2 ^ 23 <= U P - 224 /\ (U newblk + 2 ^ 20 <= U blkd \/ U blkd + 2 ^ 23 <= U newblk))%Z.
  Hypothesis HtrP : (U P <= U tr /\ U tr + 8 * sz < 2 ^ 64)%Z.
  Hypothesis Hsz : (1 <= sz < 255)%Z.
  Hypothesis Htag : (0 <= tag < 256)%Z.
  Hypothesis Hhd : (0 <= hd < 2 ^ 31)%Z.
  Hypothesis Htot : (0 <= tot /\ tot + sz + 1 <= 2 ^ 32)%Z.
  Hypothesis Hsame : (tot / 2 ^ 20 = (tot + sz) / 2 ^ 20)%Z.
  Hypothesis Hsov : (0 <= sov < 2 ^ 32)%Z.
  Hypothesis Hbs : length bs = Z.to_nat (8 * sz).
  Hypothesis Rsz : rdn BSEGS MB (at_ args 8) 4 = Some (LE4 (Z_to_bv 64 sz)).
  Hypothesis Rtag : rdn BSEGS MB (at_ args 12) 4 = Some (LE4 (Z_to_bv 64 tag)).
  Hypothesis Rtr : rdn BSEGS MB args 8 = Some (LE8 tr).
  Hypothesis Rws : rdn BSEGS MB tr (length bs) = Some bs.
  Hypothesis Rtot : rdn BSEGS MB SSW 8 = Some (LE8 (Z_to_bv 64 tot)).
  Hypothesis Rblk : rdn BSEGS MB (Z_to_bv 64 (U SSW + 16 * (tot / 2 ^ 20) + 16)) 8 = Some (LE8 blkd).
  Hypothesis Rso : rdn BSEGS MB (st_cell SSW tot) 4 = Some (LE4 (Z_to_bv 64 sov)).
  Hypothesis Rcfp : rdn BSEGS MB (Z_to_bv 64 1072904) 8 = Some (LE8 CF).
  Hypothesis Rflag : rdn BSEGS MB (at_ CF 240) 4 = Some (LE4 (Z_to_bv 64 0)).
  Hypothesis SLQ : forall (k : Z) (v : word), In (k, v) [(-8, (0x8f790%bv : word)); (-16, Z_to_bv 64 0); (-24, Z_to_bv 64 (NIDS + 1)); (-32, b)]%Z -> rdn BSEGS MB (at_ Q k) 8 = Some (LE8 v).
  Hypothesis SL : forall (k : Z) (v : word),
    In (k, v) [(-8, ra); (-16, s0v); (-24, s1v); (-32, s2v); (-40, s3v); (-48, s4v); (-56, s5v); (-64, s6v); (-72, s7v); (-80, s8v); (-88, s9v)]%Z ->
    rdn BSEGS MB (at_ P k) 8 = Some (LE8 v).
  Hypothesis SOKs : store_ok BSEGS MB (tl_slot MU idx) 8 = true.
  Hypothesis SOKl : store_ok BSEGS MB MU 1 = true.
  Hypothesis SOKb : store_ok BSEGS MB b 4 = true.
  Hypothesis SOKn : store_ok BSEGS MB nd 16 = true.
  Hypothesis Hstk : store_ok BSEGS MB (at_ P (-224)) 112 = true.
  Hypothesis SOKS : store_ok BSEGS MB SSW 8 = true.
  Hypothesis SOKso : store_ok BSEGS MB (st_cell SSW tot) 4 = true.
  Hypothesis SOKd : store_ok BSEGS MB (st_dst blkd tot) (8 + length bs) = true.

  Lemma put_n1_tail :
    exists r M', msteps BSEGS (mkst regs (0x8fdb8 : word) MB rom) (mkst r ra M' rom)
      /\ msum (n1tail_W P MU nd b idx cellz dstz (8 + 8 * sz)) MB M'
      /\ getr r 10 = Z_to_bv 64 (NIDS + 1) /\ getr r 2 = P /\ getr r 1 = ra
      /\ getr r 8 = s0v /\ getr r 9 = s1v /\ getr r 18 = s2v /\ getr r 19 = s3v /\ getr r 20 = s4v /\ getr r 21 = s5v
      /\ getr r 22 = s6v /\ getr r 23 = s7v /\ getr r 24 = s8v /\ getr r 25 = s9v
      /\ rdn BSEGS M' b 4 = Some (LE4 (Z_to_bv 64 (NIDS + 1)))
      /\ rdn BSEGS M' nd 8 = Some (LE8 hsh) /\ rdn BSEGS M' (at_ nd 8) 4 = Some (LE4 (Z_to_bv 64 hd)) /\ rdn BSEGS M' (at_ nd 12) 4 = Some (LE4 (st_id tot))
      /\ rdn BSEGS M' SSW 8 = Some (LE8 (v_add (Z_to_bv 64 tot) (Z_to_bv 64 (sz + 1))))
      /\ rdn BSEGS M' (st_cell SSW tot) 4 = Some (LE4 (v_add (Z_to_bv 64 sov) (Z_to_bv 64 (sz + 1))))
      /\ rdn BSEGS M' (tl_slot MU idx) 8 = Some (LE8 newblk)
      /\ rdn BSEGS M' MU 1 = Some [Z_to_bv 8 0]
      /\ regs_agree (fun i : reg => In i put_clob) regs r.
  Proof using SOKd SOKso SOKS Hstk SOKn SOKb SOKl SOKs SL SLQ Rflag Rcfp Rso Rblk Rtot Rws Rtr Rtag Rsz Hbs Hsov Hsame Htot Hhd Htag Hsz HtrP Hblkd Hb Hblk Hn HCF HMU Hret HP H23 H22 H21 H19 H10 H9 H8 H2 bs tag CF tr.
    pose proof (u64_range P) as HPr. pose proof (u64_range MU) as HMr. pose proof (u64_range newblk) as Hbr. pose proof (u64_range blkd) as Hbdr.
    pose proof (u64_range tr) as Htrr. pose proof (u64_range CF) as HCr. pose proof (u64_range b) as Hbbr.
    destruct HP as [P1 P2]. destruct Hn as [N0 N1]. destruct HMU as [MU1 MU2]. destruct Hblk as [BK1 BK2]. destruct Hb as [B1 B2]. destruct Hblkd as (BD1 & BD2 & BD3).
    destruct HtrP as [T1 T2]. destruct Htot as [T0 T32].
    assert (USS : U SSW = 1966216%Z) by reflexivity.
    assert (UQ : U Q = (U P - 112)%Z) by (first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ]).
    assert (Uargs : U args = (U P - 104)%Z) by (first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ]).
    assert (I16 : (0 <= idx < 2 ^ 15)%Z) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
    assert (M16 : (0 <= (NIDS + 1) mod 2 ^ 16 < 2 ^ 16)%Z) by (apply Z.mod_pos_bound; lia).
    assert (Und : U nd = (U newblk + 16 * ((NIDS + 1) mod 2 ^ 16))%Z) by ((lazymatch goal with |- ?G => let G' := eval unfold di_node in G in change_no_check G' end); rewrite u_Z2bv by lia; reflexivity).
    assert (Uslot : U (tl_slot MU idx) = (U MU + 8 + 8 * idx)%Z) by ((lazymatch goal with |- ?G => let G' := eval unfold tl_slot in G in change_no_check G' end); rewrite u_Z2bv by lia; reflexivity).
    assert (Q20 : (0 <= tot / 2 ^ 20 < 2 ^ 12)%Z) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
    assert (M20 : (0 <= tot mod 2 ^ 20 /\ tot mod 2 ^ 20 + sz < 2 ^ 20)%Z).
    { pose proof (Z.div_mod tot (2 ^ 20) ltac:(lia)) as E1. pose proof (Z.mod_pos_bound tot (2 ^ 20) ltac:(lia)) as B1'.
      pose proof (Z.div_mod (tot + sz) (2 ^ 20) ltac:(lia)) as E2. pose proof (Z.mod_pos_bound (tot + sz) (2 ^ 20) ltac:(lia)) as B2'.
      rewrite <- Hsame in E2. lia. }
    assert (Lbs : Z.of_nat (length bs) = (8 * sz)%Z) by (rewrite Hbs, Z2Nat.id by lia; reflexivity).
    assert (Ucell : U (st_cell SSW tot) = cellz) by ((lazymatch goal with |- ?G => let G' := eval unfold st_cell in G in change_no_check G' end); rewrite USS; rewrite u_Z2bv by lia; reflexivity).
    assert (Udst : U (st_dst blkd tot) = dstz) by ((lazymatch goal with |- ?G => let G' := eval unfold st_dst in G in change_no_check G' end); rewrite u_Z2bv by lia; reflexivity).
    (* [comment removed for export] *)
    destruct (put_n1_post MB rom P MU hsh newblk b hd NIDS regs H2 H8 H9 H10 H19 H21 H22 H23 ltac:(lia) ltac:(lia) (conj N0 N1) ltac:(lia) ltac:(lia)
                SOKs SOKl)
      as (r1 & M1 & RUN1 & S1 & AT & Rslot1 & Rmu1 & AG1).
    { eapply (store_ok_sub BSEGS MB nd _ 16); [lia | exact SOKn | lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia]. }
    { rewrite at_at. eapply (store_ok_sub BSEGS MB (at_ P (-224)) _ 112); [first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ] | exact Hstk | first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite !at_u by lia; lia ] | first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite !at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ]]. }
    { exact SLQ. }
    assert (THRU1 : forall (a : word) (n : nat) v, (U a + Z.of_nat n <= 2 ^ 64)%Z ->
              (U a + Z.of_nat n <= U P - 144 \/ U P - 112 <= U a)%Z -> (U a + Z.of_nat n <= U MU \/ U MU + 8 + 8 * 2 ^ 15 <= U a)%Z ->
              (U a + Z.of_nat n <= U nd \/ U nd + 8 <= U a)%Z -> rdn BSEGS MB a n = Some v -> rdn BSEGS M1 a n = Some v).
    { intros a n v B0 X1 X2 X3 Hr. apply (msum_rdn_eq BSEGS _ MB M1 _ _ _ S1 B0); [| exact Hr].
      intros z Hz. (lazymatch goal with |- ?G => let G' := eval unfold n1post_W, wun, ivl in G in change_no_check G' end). lia. }
    (* [comment removed for export] *)
    destruct (put_from_store M1 rom P ra nd b hsh tr blkd CF hd (NIDS + 1) sz tag tot sov bs s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v r1
                AT ltac:(lia) Hret HCF ltac:(rewrite Und; lia) ltac:(rewrite Und; lia) ltac:(rewrite Und; lia) ltac:(lia) Hsz Htag Hhd (conj T0 T32) Hsame Hsov Hbs)
      as (r2 & M2 & RUN2 & S2 & C10 & C2 & C1 & C8 & C9 & C18 & C19 & C20 & C21 & C22 & C23 & C24 & C25 & Kb & Kl & Ks & Kt & Kso & AG2).
    { apply THRU1; [first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | exact Rsz]. }
    { apply THRU1; [first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | exact Rtag]. }
    { apply THRU1; [(lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | exact Rtr]. }
    { apply THRU1; [rewrite Lbs; lia | rewrite Lbs; lia | rewrite Lbs; lia | rewrite Lbs; lia | exact Rws]. }
    { apply THRU1; [rewrite USS; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite USS; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite USS; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite USS; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | exact Rtot]. }
    { apply THRU1; [rewrite USS, u_Z2bv by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite USS, u_Z2bv by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite USS, u_Z2bv by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite USS, u_Z2bv by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | exact Rblk]. }
    { apply THRU1; [rewrite Ucell; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite Ucell; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite Ucell; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite Ucell; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | exact Rso]. }
    { apply THRU1; [first [ solve [ wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite u_Z2bv by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | first [ solve [ wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite u_Z2bv by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | first [ solve [ wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite u_Z2bv by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | first [ solve [ wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite u_Z2bv by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | exact Rcfp]. }
    { apply THRU1; [first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | exact Rflag]. }
    { intros k v Hin.
      assert (K : (-88 <= k <= -8)%Z) by (cbn [In] in Hin; repeat (destruct Hin as [E|Hin]; [injection E as <- <-; lia|]); destruct Hin).
      apply THRU1; [first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | exact (SL k v Hin)]. }
    { exact (msum_store_ok BSEGS _ MB M1 _ _ S1 SOKb). }
    { exact (msum_store_ok BSEGS _ MB M1 _ _ S1 SOKn). }
    { exact (msum_store_ok BSEGS _ MB M1 _ _ S1 Hstk). }
    { exact (msum_store_ok BSEGS _ MB M1 _ _ S1 SOKS). }
    { exact (msum_store_ok BSEGS _ MB M1 _ _ S1 SOKso). }
    { exact (msum_store_ok BSEGS _ MB M1 _ _ S1 SOKd). }
    assert (THRU2 : forall (a : word) (n : nat) v, (U a + Z.of_nat n <= 2 ^ 64)%Z ->
              (U MU <= U a /\ U a + Z.of_nat n <= U MU + 8 + 8 * 2 ^ 15)%Z -> rdn BSEGS M1 a n = Some v -> rdn BSEGS M2 a n = Some v).
    { intros a n v B0 X1 Hr. apply (msum_rdn_eq BSEGS _ M1 M2 _ _ _ S2 B0); [| exact Hr].
      intros z Hz. (lazymatch goal with |- ?G => let G' := eval unfold fstore_W, wun, ivl in G in change_no_check G' end). rewrite Und. lia. }
    destruct AT as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Rhsh1 & _).
    exists r2, M2. split; [eapply msteps_trans; [exact RUN1 | exact RUN2]|].
    split; [exact (msum_trans _ _ _ _ _ S1 S2)|].
    repeat (split; [assumption|]).
    split.
    { apply (msum_rdn_eq BSEGS _ M1 M2 _ _ _ S2); [(lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | | exact Rhsh1]. intros z Hz. cbn in Hz. (lazymatch goal with |- ?G => let G' := eval unfold fstore_W, wun, ivl in G in change_no_check G' end). rewrite Und in *. lia. }
    split; [exact Kl|]. split; [exact Ks|]. split; [exact Kt|]. split; [exact Kso|].
    split; [apply THRU2; [rewrite Uslot; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite Uslot; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | exact Rslot1]|].
    split; [apply THRU2; [(lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | exact Rmu1]|].
    apply (regs_agree_trans _ regs r1 r2 AG1 AG2).
  Qed.
End N1TAIL.
End FPGen.
End BoDepotRunN2.
Require Stdlib.Sorting.Permutation OSSVerify.Proofs.glaze.binary_reflection.lib.MuslMemmove OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsDp3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsDp23 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFree3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvZone3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsRc73 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8La.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module BoDepotTopN1a.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.MemSplit OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.MuslMemmove.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsKInst OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsRtK.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinv3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinvGeom3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOps3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsDp3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsDp23 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d.AsAinvFreeS OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFree3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvZone3b.AsAinvFacts3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsRc73.AsAinvRepX3.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFHyp OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8La OSSVerify.Proofs.glaze.binary_reflection.lib.BoDepotHit OSSVerify.Proofs.glaze.binary_reflection.lib.BoDepotRunI.BoDepotIns OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRc4c.BoDepotStore OSSVerify.Proofs.glaze.binary_reflection.lib.BoDepotRunI.BoDepotStoreR OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFHyp.BoDepotImg OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtIMemmove.AsDepotSum OSSVerify.Proofs.glaze.binary_reflection.lib.BoDepotRunI.BoDepotRunT OSSVerify.Proofs.glaze.binary_reflection.lib.BoDepotRunI.BoDepotRunH OSSVerify.Proofs.glaze.binary_reflection.lib.BoDepotRunI.BoDepotRunS OSSVerify.Proofs.glaze.binary_reflection.lib.BoDepotRunI OSSVerify.Proofs.glaze.binary_reflection.lib.BoDepotTop3.BoDepotRunP OSSVerify.Proofs.glaze.binary_reflection.lib.BoDepotRunI.BoDepotMap OSSVerify.Proofs.glaze.binary_reflection.lib.BoDepotRunI.BoDepotIns2 BoDepotRunF OSSVerify.Proofs.glaze.binary_reflection.lib.BoDepotRunI.BoDepotRunN OSSVerify.Proofs.glaze.binary_reflection.lib.BoDepotTop3.BoDepotHyp9 OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys10.AsDepotTop0 OSSVerify.Proofs.glaze.binary_reflection.lib.BoDepotTop3.BoDepotTop1.
Import OSSVerify.glaze.binary_reflection.images.AsanUbsan.
Import ListNotations.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Ltac wm_clear_disj2_or T := lazymatch T with | _ \/ _ => idtac | ?A /\ ?B => first [wm_clear_disj2_or A | wm_clear_disj2_or B] | ?A <-> ?B => first [wm_clear_disj2_or A | wm_clear_disj2_or B] | ?A -> ?B => first [wm_clear_disj2_or A | wm_clear_disj2_or B] end.
Ltac wm_clear_disj2 := repeat match goal with H : ?T |- _ => wm_clear_disj2_or T; clear H end.
Ltac wm_lia02 := tryif noncert_goal_has_var then (Zify.zify; xlia zchecker)
                 else first [ solve [noncert_clear_all; Zify.zify; xlia zchecker] | Zify.zify; xlia zchecker ].
#[local] Ltac lia ::= first [ solve [wm_clear_disj2; wm_lia02] | wm_lia02 ].
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation BSEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).
#[local] Abbreviation LE4 v := (word_to_le_bytes 4 v).
#[local] Abbreviation U := bv_unsigned.


Lemma rdn4_head : forall segs (m : word -> option byte) (a : word) bs b0, rdn segs m a 4 = Some bs -> rdn segs m a 1 = Some [b0] ->
  exists b1 b2 b3, bs = [b0; b1; b2; b3].
Proof.
  intros segs m a bs b0 H4 H1. rewrite rdn_S, H1 in H4. destruct (rdn segs m (a + 1)%bv 3) as [r3|] eqn:E3; [| discriminate H4].
  injection H4 as <-. pose proof (rdn_length _ _ _ _ _ E3) as L3.
  destruct r3 as [|b1 [|b2 [|b3 [|b4 t]]]]; try discriminate L3. exists b1, b2, b3. reflexivity.
Qed.

Section TOPN1A.
  Context {RC : run_ceil}.
  Variable bt : as_boot.
  Variable FXOK : FPState -> Prop.
  Hypothesis BT_segs : bt_segs bt = BSEGS.
  Hypothesis BT_ia : bt_ia bt = both_addrs.
  Hypothesis DCELLS : depot_cells bt.
  Hypothesis DOBL : depot_obls bt.
  Hypothesis DEPOT_FRAMES_ROOM : forall st Lc FF, WF bt st Lc FF -> depot_room bt st -> a_kact st <= KCAP -> dp_frames (a_dep st) + 2 * FRW <= 2 ^ 32.
  Hypothesis DEP0 : dp_nids (bt_dep0 bt) <= 2 ^ 20.

  (* [comment removed for export] *)
  Definition depot_cells2 : Prop :=
    In (0x105ef8, 8%nat, 0x19dc60) (bt_consts bt) /\ In (0x19dc60, 8%nat, 0x1000) (bt_consts bt)
    /\ In (0x19fdec, 1%nat, 0) (bt_consts bt) /\ In (0x19fd78, 8%nat, 0) (bt_consts bt)
    /\ In (0x105f58, 8%nat, 1) (bt_consts bt) /\ In (0x19fcdc, 4%nat, 0) (bt_consts bt).
  Hypothesis DCELLS2 : depot_cells2.

  (* [comment removed for export] *)
  Definition grow_n1 (st : ast) (sz : Z) : Prop :=
    let d := a_dep st in
    (dp_nids d + 1) / 2 ^ 16 <> dp_nids d / 2 ^ 16
    /\ dp_frames d / 2 ^ 20 = (dp_frames d + sz) / 2 ^ 20 /\ (dp_frames d mod 2 ^ 20 <> 0 \/ dp_frames d = 0).

  Lemma miss_n1_run1 : forall KD, 464 <= KD ->
    forall fx (X : Z -> Prop) st Lc FF (M M0 : mem) mdl (R r : bvmap 5 word) (sp buf ret : word) (sz tag : Z) (ws : list word),
      WF bt st Lc FF -> Rep bt st Lc FF M0 mdl -> (forall a : word, M a <> M0 a -> X (U a) /\ M a <> None) ->
      (forall a, X a -> ~ (ia_img_lo (bt_ia bt) <= a < ia_img_hi (bt_ia bt))) -> PX bt st X ->
      depot_room bt st -> a_kact st <= KCAP ->
      getr R 1 = ret -> getr R 2 = sp ->
      CEIL + KD <= U sp -> U sp + 2192 <= 2 ^ 47 -> ret_ok ret ->
      (forall a : word, U sp - KD <= U a < U sp -> M a <> None /\ store_ok BSEGS M a 1%nat = true) ->
      1 <= sz <= 8 -> 0 <= tag < 256 -> U sp <= U buf -> U buf + 8 * sz < 2 ^ 64 ->
      (forall i, U buf <= i < U buf + 8 * sz -> M (Z_to_bv 64 i) <> None) ->
      (dp_nids (a_dep st) + 1) / 2 ^ 16 <> dp_nids (a_dep st) / 2 ^ 16 ->                 (* [comment removed for export] *)
      let Hd := HID st mdl in let Mr := mrestrict Hd M in let h := sd_hashN ws tag in
      let d := a_dep st in let b := sd_bix h in let idx := (dp_nids d + 1) / 2 ^ 16 in
      let SM := sd_frame Mr sp R ret buf (Z_to_bv 64 (sz + tag * 2 ^ 32)) in
      let DW : word := Z_to_bv 64 0x1f0098 in let MU : word := Z_to_bv 64 (0x1f0098 + 4194312) in
      getr r 2 = at_ sp (-112) /\ getr r 8 = Z_to_bv 64 0 /\ getr r 9 = Z_to_bv 64 0x1f0098
      /\ getr r 18 = Z_to_bv 64 (0x1f0098 + 4 * b) /\ getr r 19 = h /\ getr r 20 = Z_to_bv 64 (0x1f0098 + 4194312)
      /\ getr r 22 = Z_to_bv 64 65535 /\ getr r 24 = Z_to_bv 64 (0x1f0098 + 4194320) /\ getr r 25 = Z_to_bv 64 (dp_tab d b)
      /\ regs_agree (fun i : reg => In i sd_clobx) R r ->
      exists r1 Mtr,
        msteps BSEGS (@mkst fx r (Z_to_bv 64 0x8f688) SM (seg_rom BSEGS)) (@mkst fx r1 (Z_to_bv 64 0x82878) Mtr (seg_rom BSEGS))
        /\ msum (wun (ivl (U sp - 112) 112) (n1pre_W sp DW (Z_to_bv 64 (0x1f0098 + 4 * b)))) Mr Mtr
        /\ getr r1 1 = Z_to_bv 64 0x8fdb8 /\ getr r1 2 = at_ (at_ sp (-112)) (-32)
        /\ getr r1 10 = Z_to_bv 64 1048576 /\ getr r1 11 = Z_to_bv 64 138627 /\ getr r1 12 = Z_to_bv 64 0
        /\ getr r1 8 = MU /\ getr r1 9 = Z_to_bv 64 (0x1f0098 + 4194312 + 8 * idx)
        /\ getr r1 19 = h /\ getr r1 21 = Z_to_bv 64 (dp_tab d b) /\ getr r1 22 = Z_to_bv 64 65535 /\ getr r1 23 = Z_to_bv 64 (dp_nids d + 1)
        /\ rdn BSEGS Mtr (Z_to_bv 64 (0x1f0098 + 4194304)) 4 = Some (LE4 (Z_to_bv 64 (dp_nids d + 1)))
        /\ (forall (k : Z) (v : word), In (k, v) [(-8, (Z_to_bv 64 0x8f790 : word)); (-16, Z_to_bv 64 0); (-24, Z_to_bv 64 (dp_nids d + 1)); (-32, Z_to_bv 64 (0x1f0098 + 4 * b))]%Z ->
               rdn BSEGS Mtr (at_ (at_ sp (-112)) k) 8 = Some (LE8 v))
        /\ regs_agree (fun i : reg => In i put_clob) r r1
        (* [comment removed for export] *)
        /\ rdn BSEGS Mtr (at_ sp (-104)) 8 = Some (LE8 buf) /\ rdn BSEGS Mtr (at_ (at_ sp (-104)) 8) 4 = Some (LE4 (Z_to_bv 64 sz))
        /\ rdn BSEGS Mtr (at_ (at_ sp (-104)) 12) 4 = Some (LE4 (Z_to_bv 64 tag))
        /\ (forall (k : Z) (v : word),
              In (k, v) [(-8, ret); (-16, getr R 8); (-24, getr R 9); (-32, getr R 18); (-40, getr R 19); (-48, getr R 20);
                         (-56, getr R 21); (-64, getr R 22); (-72, getr R 23); (-80, getr R 24); (-88, getr R 25)]%Z ->
              rdn BSEGS Mtr (at_ sp k) 8 = Some (LE8 v))
        (* [comment removed for export] *)
        /\ idx = Z.of_nat (length (node_blocks bt d)) /\ 0 <= idx < 2 ^ 15 /\ 0 <= dp_nids d /\ dp_nids d + 1 < 2 ^ 31.
  Proof using DCELLS2 BT_ia BT_segs.
    intros KD HKD fx X st Lc FF M M0 mdl R r sp buf ret sz tag ws W RP DIFF XIMG PXH ROOM KC E1 E2 SPC SPHI RET STK SZ Htag BUFS BUFW BUFD NG
           Hd Mr h d b idx SM DW MU (F2 & F8 & F9 & F18 & F19 & F20 & F22 & F24 & F25 & AGp).
    pose proof ceil_rng as CR. pose proof (u64_range sp) as Hspr. pose proof (u64_range buf) as Hbufr.
    pose proof NG as CA. fold d in CA.
    pose proof RP as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10 & R11 & R12 & R13 & R14 & R15).
    rewrite BT_segs in R1.
    destruct R9 as (Dtab & Dnids & Dmu & Dmap & Dnode & Dnw & Dfr & Dblk & Dsw).
    assert (ETAB : DEPOT_TAB bt = 0x1f0098) by ((lazymatch goal with |- ?G => let G' := eval unfold DEPOT_TAB in G in change_no_check G' end); rewrite BT_ia; reflexivity).
    assert (EMAP : DEPOT_MAP1 bt = 0x1f0098 + 4194320) by ((lazymatch goal with |- ?G => let G' := eval unfold DEPOT_MAP1 in G in change_no_check G' end); rewrite ETAB; reflexivity).
    assert (ENID : DEPOT_NIDS bt = 0x1f0098 + 4194304) by ((lazymatch goal with |- ?G => let G' := eval unfold DEPOT_NIDS in G in change_no_check G' end); rewrite ETAB; reflexivity).
    pose proof W as (_ & _ & _ & _ & _ & _ & (D1 & D2 & D3 & D4 & D5 & D6 & D7 & D8 & D9 & D10 & D11 & D12) & _).
    fold d in D1, D2, D3, D4, D5, D6, D7, D8, D9, D10, D11, D12, Dtab, Dnids, Dmu, Dmap.
    set (NIDS := dp_nids d) in *.
    assert (N0 : 0 <= NIDS) by (first [clear - D4 | idtac]; (pose proof (D4 0 ltac:(lia)); lia)).
    destruct DCELLS2 as (C_gpg & C_pg & _).
    assert (I16 : 0 <= idx < 2 ^ 15) by ((lazymatch goal with |- ?G => let G' := eval unfold idx in G in change_no_check G' end); split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
    assert (EIDX : idx = Z.of_nat (length (node_blocks bt d))).
    { (lazymatch goal with |- ?G => let G' := eval unfold node_blocks in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [length] in G in change_no_check G' end). rewrite Nat2Z.inj_succ, D6. (lazymatch goal with |- ?G => let G' := eval unfold idx in G in change_no_check G' end).
      pose proof (Z.div_mod NIDS (2 ^ 16) ltac:(lia)) as X1. pose proof (Z.mod_pos_bound NIDS (2 ^ 16) ltac:(lia)) as X2.
      pose proof (Z.div_mod (NIDS + 1) (2 ^ 16) ltac:(lia)) as X3. pose proof (Z.mod_pos_bound (NIDS + 1) (2 ^ 16) ltac:(lia)) as X4.
      clear -X1 X2 X3 X4 CA. nia. }
    (* [comment removed for export] *)
    assert (NHs : forall z, 0 <= z < 2 ^ 64 -> (CEIL <= z \/ (AIMGLO <= z /\ z < AIMGHI)) -> Hd (Z_to_bv 64 z) = false).
    { intros z Hz Hr. apply (HID_off_zone bt st mdl z R13 Hz). rewrite BT_ia. (lazymatch goal with |- ?G => let G' := eval cbn [ia_img_lo ia_img_hi both_addrs] in G in change_no_check G' end). lia. }
    assert (NHx : forall x : word, U sp - KD <= U x -> Hd x = false).
    { intros x Hx. pose proof (u64_range x) as Hxr. rewrite <- (Z_to_bv_bv_unsigned 64 x). apply NHs; [(first [clear - Hxr | idtac]; lia) | left; (first [clear - Hx SPC | idtac]; lia)]. }
    assert (EQ0 : forall a : word, ~ X (U a) -> M a = M0 a).
    { intros a NX. destruct (decide (M a = M0 a)) as [E|NE]; [exact E|]. exfalso. exact (NX (proj1 (DIFF a NE))). }
    assert (XMr : forall (z : Z) (k : nat) bs,
              (forall i, z <= i < z + Z.of_nat k -> ~ X i /\ Hd (Z_to_bv 64 i) = false) -> 0 <= z -> z + Z.of_nat k < 2 ^ 64 ->
              rdn BSEGS M0 (Z_to_bv 64 z) k = Some bs -> rdn BSEGS Mr (Z_to_bv 64 z) k = Some bs).
    { intros z k bs F Hz Hk Hr. rewrite <- Hr. apply rdn_ext; [rewrite u_Z2bv by (first [clear - Hz Hk | idtac]; lia); (first [clear - Hk | idtac]; lia)|].
      intros x Hx. rewrite u_Z2bv in Hx by (first [clear - Hz Hk | idtac]; lia). destruct (F (U x) Hx) as [NX NHx']. rewrite Z_to_bv_bv_unsigned in NHx'.
      (lazymatch goal with |- ?G => let G' := eval unfold Mr in G in change_no_check G' end). rewrite (mrestrict_off Hd M x NHx'). apply EQ0. exact NX. }
    assert (XI : forall i, AIMGLO <= i < AIMGHI -> ~ X i /\ Hd (Z_to_bv 64 i) = false).
    { intros i Hi. split; [| apply NHs; lia]. intros Xi. apply (XIMG i Xi). rewrite BT_ia. (lazymatch goal with |- ?G => let G' := eval cbn [ia_img_lo ia_img_hi both_addrs] in G in change_no_check G' end). lia. }
    assert (SF : msum (ivl (U sp - 112) 112) Mr SM) by (first [clear - CR SPHI SPC HKD | idtac]; (apply (sdf_sum Mr sp ret buf sz tag R); lia)).
    assert (THRU : forall (z : Z) (k : nat) bs, 0 <= z -> z + Z.of_nat k <= U sp - 112 -> rdn BSEGS Mr (Z_to_bv 64 z) k = Some bs -> rdn BSEGS SM (Z_to_bv 64 z) k = Some bs).
    { intros z k bs Hz Hk Hr. apply (msum_rdn_eq BSEGS _ Mr SM _ _ _ SF); [rewrite u_Z2bv by (first [clear - Hz Hk SPHI | idtac]; lia); (first [clear - Hk SPHI | idtac]; lia) | | exact Hr].
      intros i Hi. rewrite u_Z2bv in Hi by (first [clear - Hz Hk SPHI | idtac]; lia). (lazymatch goal with |- ?G => let G' := eval unfold ivl in G in change_no_check G' end). lia. }
    assert (IMG : forall (z : Z) (k : nat) v, AIMGLO <= z -> z + Z.of_nat k <= AIMGHI -> cellZ BSEGS M0 z k v ->
              rdn BSEGS SM (Z_to_bv 64 z) k = Some (word_to_le_bytes k (Z_to_bv 64 v))).
    { intros z k v Hz Hk C. apply THRU; [(first [clear - Hz | idtac]; lia) | (first [clear - Hk CR SPC HKD | idtac]; lia)|]. apply (XMr z k); [intros i Hi; apply XI; (first [clear - Hi Hk Hz | idtac]; lia) | (first [clear - Hz | idtac]; lia) | (first [clear - Hk | idtac]; lia) | exact C]. }
    pose proof (Dtab b ltac:(apply bix_range)) as Cb. rewrite ETAB, BT_segs in Cb.
    pose proof Dnids as Cn. rewrite ENID, BT_segs in Cn.
    pose proof (Dmap idx I16) as Cm. rewrite EMAP, BT_segs in Cm.
    rewrite (nth_overflow (node_blocks bt d) 0) in Cm by (rewrite EIDX, Nat2Z.id; apply Nat.le_refl).
    pose proof Dmu as Cmu. rewrite ENID, BT_segs in Cmu.
    pose proof (bix_range h) as Hbix. fold b in Hbix.
    assert (UDW : U DW = 0x1f0098) by reflexivity.
    assert (UMU : U MU = 0x1f0098 + 4194312) by reflexivity.
    assert (Rb : rdn BSEGS SM (Z_to_bv 64 (U DW + 4 * b)) 4 = Some (LE4 (Z_to_bv 64 (dp_tab d b)))) by (first [clear - UDW Hbix Cb IMG | idtac]; (rewrite UDW; apply IMG; [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | exact Cb])).
    assert (Rcnt : rdn BSEGS SM (at_ DW 0x400000) 4 = Some (LE4 (Z_to_bv 64 NIDS))).
    { replace (at_ DW 0x400000) with (Z_to_bv 64 (0x1f0098 + 4194304) : word) by (apply bv_eq; reflexivity). apply IMG; [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | exact Cn]. }
    assert (Rmap : rdn BSEGS SM (Z_to_bv 64 (U DW + 0x400010 + 8 * idx)) 8 = Some (LE8 (Z_to_bv 64 0))).
    { rewrite UDW. apply IMG; [(first [clear - N0 | idtac]; lia) | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); (first [clear - I16 | idtac]; lia) | exact Cm]. }
    assert (Rmu1 : rdn BSEGS SM MU 1 = Some [Z_to_bv 8 0]).
    { change (Some [Z_to_bv 8 0]) with (Some (word_to_le_bytes 1 (Z_to_bv 64 0))). apply IMG; [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | exact Cmu]. }
    destruct (rwseg_rdn BSEGS 16 (Z_to_bv 64 0x5f0098) SM MU 4 mu_img_ok) as (lbs & Rl4 & _);
      [change (U (Z_to_bv 64 0x5f0098)) with 0x5f0098; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite UMU; change (U (Z_to_bv 64 0x5f0098)) with 0x5f0098; lia
       | rewrite UMU; change (U (Z_to_bv 64 0x5f0098)) with 0x5f0098; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia |].
    destruct (rdn4_head BSEGS SM MU lbs _ Rl4 Rmu1) as (b1 & b2 & b3 & ->).
    set (lkw := Z_to_bv 64 (bytes_le_to_Z [Z_to_bv 8 0; b1; b2; b3]) : word).
    assert (V_lock : bytes_le_to_Z [Z_to_bv 8 0; b1; b2; b3] = U lkw).
    { (lazymatch goal with |- ?G => let G' := eval unfold lkw in G in change_no_check G' end). pose proof (bytes_le_to_Z_nonneg [Z_to_bv 8 0; b1; b2; b3]) as X1. pose proof (bytes_le_to_Z_bound [Z_to_bv 8 0; b1; b2; b3]) as X2.
      cbn [length] in X2. change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32) in X2. rewrite u_Z2bv by lia. reflexivity. }
    assert (Rgpg : rdn BSEGS SM (Z_to_bv 64 1072888) 8 = Some (LE8 (Z_to_bv 64 0x19dc60))).
    { apply IMG; [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | exact (const_cell bt M0 _ _ _ R1 C_gpg)]. }
    assert (Rpg : rdn BSEGS SM (Z_to_bv 64 0x19dc60) 8 = Some (LE8 (Z_to_bv 64 4096))).
    { apply IMG; [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | exact (const_cell bt M0 _ _ _ R1 C_pg)]. }
    assert (DEFr : forall x : word, M x <> None -> Hd x = false -> SM x <> None).
    { intros x Dx Hx. apply (proj2 SF). (lazymatch goal with |- ?G => let G' := eval unfold Mr in G in change_no_check G' end). rewrite (mrestrict_off Hd M x Hx). exact Dx. }
    assert (Hstk : store_ok BSEGS SM (at_ (at_ sp (-112)) (-48)) 48 = true).
    { rewrite at_at. apply store_ok_bytes; [| rewrite at_u by (first [clear - CR SPC HKD SPHI | idtac]; lia); (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); (first [clear - SPHI | idtac]; lia)]. intros x Hx. rewrite at_u in Hx by lia. cbn in Hx. apply store_ok1_some.
      apply DEFr; [apply STK; (first [clear - Hx HKD | idtac]; lia) | apply NHx; (first [clear - Hx HKD | idtac]; lia)]. }
    pose proof (D4 b Hbix) as Htab.
    (* [comment removed for export] *)
    destruct (put_n1_pre SM (seg_rom BSEGS) sp DW h lkw b1 b2 b3 (dp_tab d b) NIDS b 0x19dc60 r
                F2 F8 F9 ltac:(rewrite UDW; exact F18) F19 F20 ltac:(rewrite UDW; exact F24) F25
                ltac:((first [clear - CR SPHI SPC HKD | idtac]; lia)) ltac:(rewrite UDW; split; [reflexivity | (repeat match goal with H : _ |- _ => clear H end; lia)]) Hbix ltac:((first [clear - Htab D3 | idtac]; lia)) ltac:((first [clear - N0 D3 | idtac]; lia)) ltac:(rewrite UDW; (repeat match goal with H : _ |- _ => clear H end; lia)) Rb)
      as (r1 & Mt & RUN & SI & G1 & G2 & G10 & G11 & G12 & G8 & G9 & G19 & G21 & G22 & G23 & Kn & SLt & AGi).
    { eapply (readable_store_ok BSEGS 0x107000 SM _ 4 _ both_rw_above); [rewrite UDW, u_Z2bv by (first [clear - Hbix | idtac]; lia); (first [clear - Hbix | idtac]; lia) | rewrite UDW, u_Z2bv by (first [clear - Hbix | idtac]; lia); (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); (first [clear - Hbix | idtac]; lia) | exact Rb]. }
    { exact Hstk. } { exact Rcnt. }
    { eapply (readable_store_ok BSEGS 0x107000 SM _ 4 _ both_rw_above); [rewrite at_u; rewrite UDW; lia | rewrite at_u; rewrite UDW; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | exact Rcnt]. }
    { exact Rmap. } { exact Rl4. } { exact V_lock. }
    { eapply (readable_store_ok BSEGS 0x107000 SM _ 4 _ both_rw_above); [rewrite UDW, u_Z2bv by lia; lia | rewrite UDW, u_Z2bv by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | exact Rl4]. }
    { exact Rgpg. } { exact Rpg. }
    exists r1, Mt. split; [replace (Z_to_bv 64 0x8f688) with (0x8f688%bv : word) by (apply bv_eq; reflexivity);
                           replace (Z_to_bv 64 0x82878) with (0x82878%bv : word) by (apply bv_eq; reflexivity); exact RUN|].
    split.
    { apply (msum_trans _ _ Mr SM Mt SF). replace (Z_to_bv 64 (0x1f0098 + 4 * b)) with (Z_to_bv 64 (U DW + 4 * b) : word) by (rewrite UDW; reflexivity). exact SI. }
    split; [rewrite G1; apply bv_eq; reflexivity|]. split; [exact G2|]. split; [exact G10|]. split; [exact G11|]. split; [exact G12|].
    split; [exact G8|]. split; [rewrite G9; reflexivity|]. split; [exact G19|]. split; [exact G21|]. split; [rewrite G22; exact F22|]. split; [exact G23|].
    split.
    { replace (Z_to_bv 64 (0x1f0098 + 4194304)) with (at_ DW 0x400000 : word) by (apply bv_eq; reflexivity). rewrite Kn. f_equal. f_equal.
      (lazymatch goal with |- ?G => let G' := eval unfold v_add in G in change_no_check G' end). rewrite !u_Z2bv by lia. reflexivity. }
    split.
    { intros k v Hin. apply SLt. cbn [In] in Hin |- *.
      replace (Z_to_bv 64 (U DW + 4 * b)) with (Z_to_bv 64 (0x1f0098 + 4 * b) : word) by (rewrite UDW; reflexivity).
      replace (0x8f790%bv : word) with (Z_to_bv 64 0x8f790 : word) by (apply bv_eq; reflexivity). exact Hin. }
    split; [exact AGi|].
    assert (THRUpre : forall (x : word) (n : nat) v, U x + Z.of_nat n <= 2 ^ 64 -> U sp - 112 <= U x -> rdn BSEGS SM x n = Some v -> rdn BSEGS Mt x n = Some v).
    { intros x n v B0 Hx Hr. apply (msum_rdn_eq BSEGS _ SM Mt _ _ _ SI B0); [| exact Hr].
      intros z Hz. (lazymatch goal with |- ?G => let G' := eval unfold n1pre_W, wun, ivl in G in change_no_check G' end). rewrite UDW, u_Z2bv by (first [clear - Hbix | idtac]; lia). (first [clear - Hz Hx Hbix CR SPC HKD | idtac]; lia). }
    destruct (sdf_args Mr sp ret buf sz tag R ltac:((first [clear - CR SPHI SPC HKD | idtac]; lia)) ltac:((first [clear - SZ | idtac]; lia)) ltac:((first [clear - Htag | idtac]; lia))) as (Atr & Asz & Atag). fold SM in Atr, Asz, Atag.
    pose proof (sdf_slots Mr sp ret buf sz tag R ltac:(lia)) as SLs. fold SM in SLs.
    split; [apply THRUpre; [rewrite at_u by (first [clear - CR SPC HKD SPHI | idtac]; lia); (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); (first [clear - SPHI | idtac]; lia) | rewrite at_u by (first [clear - CR SPC HKD SPHI | idtac]; lia); (repeat match goal with H : _ |- _ => clear H end; lia) | exact Atr]|].
    split; [apply THRUpre; [rewrite at_at, at_u by (first [clear - CR SPC HKD SPHI | idtac]; lia); (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); (first [clear - SPHI | idtac]; lia) | rewrite at_at, at_u by (first [clear - CR SPC HKD SPHI | idtac]; lia); (repeat match goal with H : _ |- _ => clear H end; lia) | exact Asz]|].
    split; [apply THRUpre; [rewrite at_at, at_u by (first [clear - CR SPC HKD SPHI | idtac]; lia); (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); (first [clear - SPHI | idtac]; lia) | rewrite at_at, at_u by (first [clear - CR SPC HKD SPHI | idtac]; lia); (repeat match goal with H : _ |- _ => clear H end; lia) | exact Atag]|].
    split.
    { intros k v Hin.
      assert (K : -88 <= k <= -8) by (cbn [In] in Hin; repeat (destruct Hin as [E|Hin]; [injection E as <- <-; lia|]); destruct Hin).
      apply THRUpre; [rewrite at_u by (first [clear - K CR SPC HKD SPHI | idtac]; lia); (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); (first [clear - K SPHI | idtac]; lia) | rewrite at_u by (first [clear - K CR SPC HKD SPHI | idtac]; lia); (first [clear - K | idtac]; lia) | exact (SLs k v Hin)]. }
    split; [exact EIDX|]. split; [exact I16|]. split; [exact N0 | lia].
  Qed.
End TOPN1A.
End BoDepotTopN1a.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.MuslMemmove OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocSim. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.MemSplit OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.MuslMemmove OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocSim.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3. Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsKInst OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsRtK.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsDp3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsDp23 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFree3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvZone3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsRc73. Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinv3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinvGeom3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOps3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsDp3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsDp23 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d.AsAinvFreeS OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFree3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvZone3b.AsAinvFacts3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsRc73.AsAinvRepX3.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFHyp OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8La OSSVerify.Proofs.glaze.binary_reflection.lib.BoDepotHit OSSVerify.Proofs.glaze.binary_reflection.lib.BoDepotRunI OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRc4c OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtIMemmove OSSVerify.Proofs.glaze.binary_reflection.lib.BoDepotTop3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys10 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM9i OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys6. Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFHyp OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8La OSSVerify.Proofs.glaze.binary_reflection.lib.BoDepotHit OSSVerify.Proofs.glaze.binary_reflection.lib.BoDepotRunI.BoDepotIns OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRc4c.BoDepotStore OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtIMemmove.AsDepotSum OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtIMemmove.AsDepotSum2 OSSVerify.Proofs.glaze.binary_reflection.lib.BoDepotRunI.BoDepotRunT OSSVerify.Proofs.glaze.binary_reflection.lib.BoDepotRunI OSSVerify.Proofs.glaze.binary_reflection.lib.BoDepotTop3.BoDepotRunP OSSVerify.Proofs.glaze.binary_reflection.lib.BoDepotTop3.BoDepotHyp9 OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys10.AsDepotTop0 OSSVerify.Proofs.glaze.binary_reflection.lib.BoDepotTop3.BoDepotTop1 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFHyp.BoDepotImg OSSVerify.Proofs.glaze.binary_reflection.lib.BoDepotRunI.BoDepotStoreR OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM9i.BoDepotMod OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM9i.BoDepotModK OSSVerify.Proofs.glaze.binary_reflection.lib.BoDepotRunI.BoDepotMap BoDepotRunF OSSVerify.Proofs.glaze.binary_reflection.lib.BoDepotRunI.BoDepotRunN BoDepotRunN2 BoDepotTopN1a OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys10.AsDepotBud BoDepotHyp9w OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys6.AsKSys7 OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys10.AsKSys9 OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys10.AsKSys9b.
From OSSVerify.glaze.binary_reflection.images Require Import AsanUbsan.
Import ListNotations.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Import HsLia.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Ltac wm_clear_disj_or T := lazymatch T with | _ \/ _ => idtac | ?A /\ ?B => first [wm_clear_disj_or A | wm_clear_disj_or B] | ?A <-> ?B => first [wm_clear_disj_or A | wm_clear_disj_or B] | ?A -> ?B => first [wm_clear_disj_or A | wm_clear_disj_or B] end.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AmLia.   (* [comment removed for export] *)
Ltac wm_clear_disj := am_wm_clear_disj.   (* [comment removed for export] *)
Ltac wm_lia0 := tryif noncert_goal_has_var then (Zify.zify; xlia zchecker)
                else first [ solve [noncert_clear_all; Zify.zify; xlia zchecker] | Zify.zify; xlia zchecker ].
(* [comment removed for export] *)
Tactic Notation "tclr" ident(H) := try clear H.
Ltac wm_bl := tclr D1; tclr D2; tclr D3; tclr D6; tclr D8; tclr D9; tclr D10; tclr CA; tclr CI1; tclr CI2; tclr LQ; tclr EIDX; tclr KC; tclr DEP0; tclr L10; tclr AL; tclr Htag; tclr Lbs; tclr GQ0; tclr GQ3; tclr DY; tclr E1; tclr E2; tclr APQ.
#[local] Ltac lia ::= first [ solve [wm_bl; wm_clear_disj; wm_lia0] | solve [wm_clear_disj; wm_lia0] | wm_lia0 ].
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation BSEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).
#[local] Abbreviation LE4 v := (word_to_le_bytes 4 v).
#[local] Abbreviation U := bv_unsigned.

Ltac nin5 := let HX := fresh "HX" in intro HX; cbn [In] in HX; repeat (destruct HX as [HX|HX]; [discriminate HX|]); exact HX.

Lemma zfill_in' : forall (a n : word) m (x : word),
  bv_unsigned a <= bv_unsigned x < bv_unsigned a + bv_unsigned n -> zfill a n m x = Some (Z_to_bv 8 0).
Proof.
  intros a n m x Hx. (lazymatch goal with |- ?G => let G' := eval unfold zfill, AllocSim.zmem in G in change_no_check G' end).
  rewrite (proj2 (Z.leb_le _ _)) by lia. rewrite (proj2 (Z.ltb_lt _ _)) by lia. reflexivity.
Qed.

Lemma rdn1_grows : forall segs (M M' : word -> option byte) (x : word) b, mem_grows M M' -> rdn segs M x 1 = Some [b] -> exists b', rdn segs M' x 1 = Some [b'].
Proof.
  intros segs M M' x b G H. cbn [rdn] in *. destruct (M' x) as [b1|] eqn:E1; [exists b1; reflexivity|].
  destruct (M x) as [b2|] eqn:E2; [exfalso; apply (G x); [rewrite E2; discriminate | exact E1]|]. exists b. exact H.
Qed.

Lemma zfill_grows2 : forall (a n : word) (Mb : word -> option byte), mem_grows Mb (zfill a n Mb).
Proof. intros a n Mb x Hx. (lazymatch goal with |- ?G => let G' := eval unfold zfill, AllocSim.zmem in G in change_no_check G' end). destruct (_ && _)%bool; [discriminate | exact Hx]. Qed.

Lemma max_blocks_nogrow2 : forall tot sz, 0 <= tot -> 1 <= sz -> tot / 2 ^ 20 = (tot + sz) / 2 ^ 20 -> (tot mod 2 ^ 20 <> 0 \/ tot = 0) ->
  Z.max 0 ((tot - 1) / 2 ^ 20) = Z.max 0 ((tot + sz + 1 - 1) / 2 ^ 20).
Proof.
  intros tot sz T0 S1 E [NZ | Z0].
  - replace (tot + sz + 1 - 1) with (tot + sz) by lia. rewrite <- E. f_equal.
    pose proof (Z.div_mod tot (2 ^ 20) ltac:(lia)) as X1. pose proof (Z.mod_pos_bound tot (2 ^ 20) ltac:(lia)) as X2.
    symmetry. apply (Z.div_unique (tot - 1) (2 ^ 20) (tot / 2 ^ 20) (tot mod 2 ^ 20 - 1)); lia.
  - subst tot. replace (0 + sz + 1 - 1) with (0 + sz) by lia. rewrite <- E. reflexivity.
Qed.

Lemma stored_le4b : forall sov c, 0 <= sov < 2 ^ 32 -> 0 <= c < 2 ^ 32 ->
  word_to_le_bytes 4 (v_add (Z_to_bv 64 sov) (Z_to_bv 64 c)) = word_to_le_bytes 4 (Z_to_bv 64 ((sov + c) mod 2 ^ 32)).
Proof.
  intros sov c Hs Hc. apply le4_congr. pose proof (Z.mod_pos_bound (sov + c) (2 ^ 32) ltac:(lia)) as MB.
  (lazymatch goal with |- ?G => let G' := eval unfold v_add in G in change_no_check G' end). rewrite (u_Z2bv sov), (u_Z2bv c) by lia. rewrite (u_Z2bv (sov + c)) by lia. rewrite (u_Z2bv ((sov + c) mod 2 ^ 32)) by lia.
  (lazymatch goal with |- ?G => let G' := eval unfold bv_wrap in G in change_no_check G' end). change (bv_modulus 32) with (2 ^ 32). rewrite Z.mod_mod by lia. reflexivity.
Qed.

Section TOPN1B.
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

  (* [comment removed for export] *)
  Lemma miss_n1_cont : forall KD, 464 <= KD ->
    forall fx (X : Z -> Prop) st Lc FF (M M0 : mem) mdl (R r r1 r' : bvmap 5 word) (sp buf ret a : word) (sz tag : Z) (ws : list word)
           (Mtr MB : mem) (mdlm mdl4 : Model) (h0 : option Z),
      FXOK fx -> m_halted mdl = None -> BackingAlgebra.model_ivs_wf mdl ->
      WF bt st Lc FF -> Rep bt st Lc FF M0 mdl -> (forall a : word, M a <> M0 a -> X (U a) /\ M a <> None) ->
      (forall a, X a -> ~ (ia_img_lo (bt_ia bt) <= a < ia_img_hi (bt_ia bt))) -> PX bt st X -> holes_le h0 st ->
      depot_room bt st -> a_kact st <= KCAP ->
      getr R 1 = ret -> getr R 2 = sp ->
      CEIL + KD <= U sp -> U sp + 2192 <= 2 ^ 47 -> ret_ok ret ->
      (forall a : word, U sp - KD <= U a < U sp -> M a <> None /\ store_ok BSEGS M a 1%nat = true) ->
      1 <= sz <= 8 -> 0 <= tag < 256 -> U sp <= U buf -> U buf + 8 * sz < 2 ^ 64 ->
      (forall i, U buf <= i < U buf + 8 * sz -> M (Z_to_bv 64 i) <> None) ->
      grow_n1 st sz ->
      let Hd := HID st mdl in let h := sd_hashN ws tag in
      let d := a_dep st in let b := sd_bix h in let idx := (dp_nids d + 1) / 2 ^ 16 in
      let DW : word := Z_to_bv 64 0x1f0098 in let MUW : word := Z_to_bv 64 (0x1f0098 + 4194312) in let bW : word := Z_to_bv 64 (0x1f0098 + 4 * b) in
      let W1 := wun (ivl (U sp - 112) 112) (n1pre_W sp DW bW) in let M1f := munrestrict Hd M Mtr in
      let spM := at_ (at_ sp (-112)) (-32) in let szW : word := Z_to_bv 64 1048576 in
      let WB := wun (ivl (U sp - 464) 320) (ivl (U a) (2 ^ 20)) in
      regs_agree (fun i : reg => In i sd_clobx) R r -> regs_agree (fun i : reg => In i put_clob) r r1 ->
      msum W1 M M1f ->
      getr r1 8 = MUW -> getr r1 9 = Z_to_bv 64 (0x1f0098 + 4194312 + 8 * idx) -> getr r1 19 = h -> getr r1 21 = Z_to_bv 64 (dp_tab d b) ->
      getr r1 22 = Z_to_bv 64 65535 -> getr r1 23 = Z_to_bv 64 (dp_nids d + 1) ->
      rdn BSEGS Mtr (Z_to_bv 64 (0x1f0098 + 4194304)) 4 = Some (LE4 (Z_to_bv 64 (dp_nids d + 1))) ->
      (forall (k : Z) (v : word), In (k, v) [(-8, (Z_to_bv 64 0x8f790 : word)); (-16, Z_to_bv 64 0); (-24, Z_to_bv 64 (dp_nids d + 1)); (-32, bW)]%Z ->
           rdn BSEGS Mtr (at_ (at_ sp (-112)) k) 8 = Some (LE8 v)) ->
      rdn BSEGS Mtr (at_ sp (-104)) 8 = Some (LE8 buf) -> rdn BSEGS Mtr (at_ (at_ sp (-104)) 8) 4 = Some (LE4 (Z_to_bv 64 sz)) ->
      rdn BSEGS Mtr (at_ (at_ sp (-104)) 12) 4 = Some (LE4 (Z_to_bv 64 tag)) ->
      (forall (k : Z) (v : word),
          In (k, v) [(-8, ret); (-16, getr R 8); (-24, getr R 9); (-32, getr R 18); (-40, getr R 19); (-48, getr R 20);
                     (-56, getr R 21); (-64, getr R 22); (-72, getr R 23); (-80, getr R 24); (-88, getr R 25)]%Z ->
          rdn BSEGS Mtr (at_ sp k) 8 = Some (LE8 v)) ->
      idx = Z.of_nat (length (node_blocks bt d)) -> 0 <= idx < 2 ^ 15 ->
      (* [comment removed for export] *)
      same_but_materialized mdl mdlm -> grant_ok (Z_to_bv 64 0) mdlm a (2 ^ 20) = true ->
      same_but_materialized (mmap_model a szW mdlm) mdl4 -> MInv (a_aa st) mdl4 ->
      mo_ret' r1 r' spM (Z_to_bv 64 0x8fdb8) (getr r1 8) (getr r1 9) (getr r1 18) (getr r1 19) a ->
      msum WB M1f MB -> (forall x : word, U a <= U x < U a + 2 ^ 20 -> MB x <> None) ->
      katD BSEGS (mkCfg (@mkst fx r' (Z_to_bv 64 0x8fdb8) MB (seg_rom BSEGS)) mdl4)
           (depot_post_w bt FXOK KD X st Lc FF M mdl R sp ret).
  Proof using BOOTG DEP0 DEPOT_FRAMES_ROOM DOBL DCELLS BT_ia BT_segs.
    intros KD HKD fx X st Lc FF M M0 mdl R r r1 r' sp buf ret a sz tag ws Mtr MB mdlm mdl4 h0
           HFX HH MW W RP DIFF XIMG PXH HOLE ROOM KC E1 E2 SPC SPHI RET STK SZ Htag BUFS BUFW BUFD NG
           Hd h d b idx DW MUW bW W1 M1f spM szW WB AGp AG1 [FR1 GR1] A8 A9 A19 A21 A22 A23 Kn1 SLt Atr Asz Atag SLs EIDX I16
           SBM0m G SBM4 MI4 MR [FRB GRB] DEFA.
    pose proof ceil_rng as CR. pose proof (u64_range sp) as Hspr. pose proof (u64_range buf) as Hbufr. pose proof (u64_range a) as Har.
    destruct NG as (CA & CI1 & CI2). fold d in CA, CI1, CI2.
    set (tot := dp_frames d) in *. set (q := tot / 2 ^ 20) in *. set (NIDS := dp_nids d) in *.
    set (blkd := nth (Z.to_nat q) (store_blocks bt d) 0) in *.
    pose proof (bix_range h) as Hbix. fold b in Hbix.
    assert (UDW : U DW = 0x1f0098) by reflexivity. assert (UMU : U MUW = 0x1f0098 + 4194312) by reflexivity.
    assert (UbW : U bW = 0x1f0098 + 4 * b) by ((lazymatch goal with |- ?G => let G' := eval unfold bW in G in change_no_check G' end); rewrite u_Z2bv by lia; reflexivity).
    assert (UspM : U spM = U sp - 144) by ((lazymatch goal with |- ?G => let G' := eval unfold spM in G in change_no_check G' end); rewrite at_at, at_u by lia; lia).
    assert (Usz : U szW = 2 ^ 20) by reflexivity.
    pose proof W as (_ & _ & _ & _ & _ & _ & (D1 & D2 & D3 & D4 & D5 & D6 & D7 & D8 & D9 & D10 & D11 & D12) & _).
    fold d in D1, D2, D3, D4, D5, D6, D7, D8, D9, D10, D11, D12. fold tot in D7, D9, D10. fold NIDS in D1, D2, D3, D4, D5, D6.
    assert (NN0 : 0 <= NIDS) by (pose proof (D4 0 ltac:(lia)) as X0; lia).
    pose proof (depot_nids_room bt st Lc FF W ROOM KC DEP0) as NROOM. fold d NIDS in NROOM.
    pose proof (DEPOT_FRAMES_ROOM st Lc FF W ROOM KC) as FROOM. fold d tot in FROOM. unfold FRW in FROOM.
    assert (Q20 : 0 <= q < 2 ^ 12) by ((lazymatch goal with |- ?G => let G' := eval unfold q in G in change_no_check G' end); split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
    assert (CLS1 : forall z, W1 z -> (U sp - 160 <= z < U sp) \/ (0x1f0098 + 4 * b <= z < 0x1f0098 + 4 * b + 4) \/ (0x1f0098 + 4194304 <= z < 0x1f0098 + 4194304 + 4)
                                    \/ (0x1f0098 + 4194312 <= z < 0x1f0098 + 4194312 + 4)).
    { intros z Hz. unfold W1, n1pre_W, wun, ivl in Hz. rewrite UDW, UbW in Hz. clear - Hz. lia. }
    pose proof RP as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10 & R11 & R12 & R13 & R14 & R15).
    rewrite BT_segs in R1.
    destruct R14 as (Bw1 & Bw2 & _ & _ & _ & _ & Bw7 & _).
    assert (NHs : forall z, 0 <= z < 2 ^ 64 -> (CEIL <= z \/ (AIMGLO <= z /\ z < AIMGHI)) -> Hd (Z_to_bv 64 z) = false).
    { intros z Hz Hr. apply (HID_off_zone bt st mdl z R13 Hz). rewrite BT_ia. (lazymatch goal with |- ?G => let G' := eval cbn [ia_img_lo ia_img_hi both_addrs] in G in change_no_check G' end). hs_lia. }
    assert (NHw : forall x : word, (CEIL <= U x \/ (AIMGLO <= U x /\ U x < AIMGHI)) -> Hd x = false).
    { intros x Hx. pose proof (u64_range x) as Hxr. rewrite <- (Z_to_bv_bv_unsigned 64 x). apply NHs; [lia | exact Hx]. }
    assert (EQ0 : forall a : word, ~ X (U a) -> M a = M0 a).
    { intros x NX. destruct (decide (M x = M0 x)) as [E|NE]; [exact E|]. exfalso. exact (NX (proj1 (DIFF x NE))). }
    assert (XI : forall i, AIMGLO <= i < AIMGHI -> ~ X i).
    { intros i Hi Xi. apply (XIMG i Xi). rewrite BT_ia. (lazymatch goal with |- ?G => let G' := eval cbn [ia_img_lo ia_img_hi both_addrs] in G in change_no_check G' end). hs_lia. }
    pose proof (HID_off_segments bt st Lc FF M0 mdl BT_ia RP) as HOFF.
    assert (OUT1 : forall i, AIMGLO <= i < 0x1f0098 -> ~ W1 i).
    { intros i Hi WZ. destruct (CLS1 _ WZ) as [C|[C|[C|C]]]; clear - C Hi Hspr SPC CR HKD Hbix; lia. }
    destruct DCELLS as (_ & _ & _ & C_cf & C_csd).
    (* [comment removed for export] *)
    destruct (sbm_vmmaps _ _ SBM0m) as [EVm ELm].
    assert (SZ19 : 2 ^ 19 < 2 ^ 20) by lia.
    destruct (grant_ok_facts bt st Lc FF M0 mdl mdlm (2 ^ 20) (2 ^ 28) W RP BOOTG EVm (Z_to_bv 64 0) a (2 ^ 20) h0 ltac:(lia) ltac:(reflexivity)
                (or_intror (conj SZ19 HOLE)) G) as (DY & AL & AP).
    assert (GAC : AIMGHI <= U a /\ U a + 2 ^ 20 <= CEIL).
    { destruct DY as (Y1 & Y2 & Y3 & Y4 & Y5). rewrite BT_ia in Y4. cbn [ia_img_lo ia_img_hi both_addrs] in Y4. clear - Y3 Y4 Y1 Har. lia. }
    destruct GAC as [GA GC].
    destruct MR as (B10 & B2 & B1 & B8 & B9 & B18 & B19 & AGm).
    destruct (plain_child_ledger mdl mdlm mdl4 a szW MW EVm ELm ltac:(rewrite Usz; lia) SBM4) as (L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8 & L9 & L10 & L11).
    assert (HL4 : m_halted mdl4 = None).
    { pose proof (same_but_materialized_frame _ _ SBM4) as F. destruct F as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HLa & _). rewrite HLa, mmap_model_halted.
      pose proof (same_but_materialized_frame mdl mdlm SBM0m) as F. destruct F as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HLb & _). rewrite HLb. exact HH. }
    assert (NHa : forall z, U a <= z < U a + 2 ^ 20 -> Hd (Z_to_bv 64 z) = false).
    { intros z Hz. apply HID_notlazy; [lia|]. exact (grant_not_lazy bt st Lc FF M0 mdl (U a) (2 ^ 20) W RP DY AP z Hz). }
    set (MBr := mrestrict Hd MB).
    (* [comment removed for export] *)
    assert (M20 : 0 <= tot mod 2 ^ 20 /\ tot mod 2 ^ 20 + sz < 2 ^ 20).
    { pose proof (Z.div_mod tot (2 ^ 20) ltac:(lia)) as X1. pose proof (Z.mod_pos_bound tot (2 ^ 20) ltac:(lia)) as X2.
      pose proof (Z.div_mod (tot + sz) (2 ^ 20) ltac:(lia)) as X3. pose proof (Z.mod_pos_bound (tot + sz) (2 ^ 20) ltac:(lia)) as X4.
      fold tot in CI1. rewrite <- CI1 in X3. lia. }
    assert (M16 : 0 <= (NIDS + 1) mod 2 ^ 16 < 2 ^ 16) by (apply Z.mod_pos_bound; lia).
    assert (LQ : Z.of_nat (length (dp_storeblocks d)) = q \/ (tot = 0 /\ q = 0)).
    { fold tot in CI2. destruct CI2 as [NZ | Z0]; [left | right; (lazymatch goal with |- ?G => let G' := eval unfold q in G in change_no_check G' end); rewrite Z0; split; reflexivity].
      assert (E : (tot - 1) / 2 ^ 20 = q).
      { (lazymatch goal with |- ?G => let G' := eval unfold q in G in change_no_check G' end). pose proof (Z.div_mod tot (2 ^ 20) ltac:(lia)) as X1. pose proof (Z.mod_pos_bound tot (2 ^ 20) ltac:(lia)) as X2.
        symmetry. apply (Z.div_unique (tot - 1) (2 ^ 20) (tot / 2 ^ 20) (tot mod 2 ^ 20 - 1)); lia. }
      rewrite D10, E. lia. }
    assert (INQ : In blkd (store_blocks bt d)).
    { (lazymatch goal with |- ?G => let G' := eval unfold blkd in G in change_no_check G' end). apply nth_In. (lazymatch goal with |- ?G => let G' := eval unfold store_blocks in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [length] in G in change_no_check G' end). destruct LQ as [LQ | [_ LQ]]; hs_lia. }
    destruct (store_blocks_dyn bt st Lc FF W blkd INQ) as ((GQ0 & GQ1 & GQ2 & GQ3 & _) & _ & INQr). rewrite BT_ia in GQ3. cbn [ia_img_lo ia_img_hi both_addrs] in GQ3.
    assert (GQ4 : AIMGHI <= blkd) by (clear - GQ3 GQ0; lia).
    assert (NHq : forall z, blkd <= z < blkd + 2 ^ 23 -> Hd (Z_to_bv 64 z) = false).
    { intros z Hz. apply HID_allowed. apply (Bw7 blkd INQ). exact Hz. }
    pose proof (AP _ _ INQr) as APQ.
    (* [comment removed for export] *)
    assert (DEFB : forall x : word, M x <> None -> Hd x = false -> MBr x <> None).
    { intros x Dx Hx. (lazymatch goal with |- ?G => let G' := eval unfold MBr in G in change_no_check G' end). rewrite (mrestrict_off Hd MB x Hx). apply GRB. apply GR1. exact Dx. }
    assert (IMGB : forall (z : Z) (k : nat) v, AIMGLO <= z -> z + Z.of_nat k <= AIMGHI -> (forall i, z <= i < z + Z.of_nat k -> ~ W1 i) -> cellZ BSEGS M0 z k v ->
                   rdn BSEGS MBr (Z_to_bv 64 z) k = Some (word_to_le_bytes k (Z_to_bv 64 v))).
    { intros z k v Hz Hk NW C. unfold cellZ, cellN in C. rewrite <- C. apply rdn_ext; [first [ solve [ wd_unorm1; wd_zofnat; lia ] | rewrite u_Z2bv by lia; lia ]|].
      intros x Hx. rewrite u_Z2bv in Hx by lia. (lazymatch goal with |- ?G => let G' := eval unfold MBr in G in change_no_check G' end). rewrite (mrestrict_off Hd MB x (NHw x ltac:(right; lia))).
      rewrite (FRB x) by ((lazymatch goal with |- ?G => let G' := eval unfold WB, wun, ivl in G in change_no_check G' end); lia). rewrite (FR1 x (NW _ Hx)). apply EQ0. apply XI. lia. }
    assert (TB : forall (x : word) (n : nat) v, U x + Z.of_nat n <= 2 ^ 64 ->
                   (forall i, U x <= i < U x + Z.of_nat n -> (CEIL <= i \/ (AIMGLO <= i /\ i < AIMGHI)) /\ ~ WB i) -> rdn BSEGS Mtr x n = Some v -> rdn BSEGS MBr x n = Some v).
    { intros x n v B0 F Hr. rewrite <- Hr. apply rdn_ext; [exact B0|]. intros y Hy. destruct (F (U y) Hy) as [NH NW].
      (lazymatch goal with |- ?G => let G' := eval unfold MBr in G in change_no_check G' end). rewrite (mrestrict_off Hd MB y (NHw y NH)). rewrite (FRB y NW). (lazymatch goal with |- ?G => let G' := eval unfold M1f in G in change_no_check G' end). apply munrestrict_off. exact (NHw y NH). }
    destruct R9 as (Dtab & Dnids & Dmu & Dmap & Dnode & Dnw & Dfr & Dblk & Dsw).
    assert (ESS : SSOBJ bt = 1966216) by ((lazymatch goal with |- ?G => let G' := eval unfold SSOBJ in G in change_no_check G' end); rewrite BT_ia; reflexivity).
    pose proof Dfr as Ct. rewrite ESS, BT_segs in Ct. fold d tot in Ct.
    destruct (Dblk q Q20) as (Cbd & Cso & _). rewrite ESS, BT_segs in Cbd, Cso. fold d blkd in Cbd. fold d in Cso.
    set (blkdW := Z_to_bv 64 blkd : word). assert (UbdW : U blkdW = blkd) by ((lazymatch goal with |- ?G => let G' := eval unfold blkdW in G in change_no_check G' end); rewrite u_Z2bv by lia; reflexivity).
    set (CFW := Z_to_bv 64 0x19fce8 : word). assert (UCF : U CFW = 0x19fce8) by reflexivity.
    assert (Rtot : rdn BSEGS MBr SSW 8 = Some (LE8 (Z_to_bv 64 tot))) by (apply IMGB; [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | intros i Hi; apply OUT1; cbn in Hi; lia | exact Ct]).
    assert (Rblk : rdn BSEGS MBr (Z_to_bv 64 (U SSW + 16 * (tot / 2 ^ 20) + 16)) 8 = Some (LE8 blkdW)).
    { replace (U SSW + 16 * (tot / 2 ^ 20) + 16) with (1966216 + 16 + 16 * q) by ((lazymatch goal with |- ?G => let G' := eval unfold q in G in change_no_check G' end); change (U SSW) with 1966216; lia).
      apply IMGB; [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | intros i Hi; apply OUT1; cbn in Hi; lia | exact Cbd]. }
    assert (Rso : rdn BSEGS MBr (st_cell SSW tot) 4 = Some (LE4 (Z_to_bv 64 (dp_stored d q)))).
    { (lazymatch goal with |- ?G => let G' := eval unfold st_cell in G in change_no_check G' end). replace (U SSW + 16 * (tot / 2 ^ 20) + 24) with (1966216 + 24 + 16 * q) by ((lazymatch goal with |- ?G => let G' := eval unfold q in G in change_no_check G' end); change (U SSW) with 1966216; lia).
      apply IMGB; [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | intros i Hi; apply OUT1; cbn in Hi; lia | exact Cso]. }
    assert (Rcfp : rdn BSEGS MBr (Z_to_bv 64 1072904) 8 = Some (LE8 CFW)) by (apply IMGB; [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | intros i Hi; apply OUT1; cbn in Hi; lia | exact (const_cell bt M0 _ _ _ R1 C_cf)]).
    assert (Rflag : rdn BSEGS MBr (at_ CFW 240) 4 = Some (LE4 (Z_to_bv 64 0))).
    { replace (at_ CFW 240) with (Z_to_bv 64 0x19fdd8 : word) by (apply bv_eq; reflexivity).
      apply IMGB; [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | intros i Hi; apply OUT1; cbn in Hi; lia | exact (const_cell bt M0 _ _ _ R1 C_csd)]. }
    (* [comment removed for export] *)
    assert (STKB : forall i, U sp - 144 <= i -> (CEIL <= i \/ (AIMGLO <= i /\ i < AIMGHI)) /\ ~ WB i).
    { intros i Hi. split; [left; lia | (lazymatch goal with |- ?G => let G' := eval unfold WB, wun, ivl in G in change_no_check G' end); lia]. }
    assert (Rtr : rdn BSEGS MBr (at_ sp (-104)) 8 = Some (LE8 buf)).
    { apply TB; [first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | intros i Hi; rewrite at_u in Hi by lia; apply STKB; lia | exact Atr]. }
    assert (Rsz : rdn BSEGS MBr (at_ (at_ sp (-104)) 8) 4 = Some (LE4 (Z_to_bv 64 sz))).
    { apply TB; [rewrite at_at, at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | intros i Hi; rewrite at_at, at_u in Hi by lia; apply STKB; lia | exact Asz]. }
    assert (Rtag : rdn BSEGS MBr (at_ (at_ sp (-104)) 12) 4 = Some (LE4 (Z_to_bv 64 tag))).
    { apply TB; [rewrite at_at, at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | intros i Hi; rewrite at_at, at_u in Hi by lia; apply STKB; lia | exact Atag]. }
    assert (SLB : forall (k : Z) (v : word),
              In (k, v) [(-8, ret); (-16, getr R 8); (-24, getr R 9); (-32, getr R 18); (-40, getr R 19); (-48, getr R 20);
                         (-56, getr R 21); (-64, getr R 22); (-72, getr R 23); (-80, getr R 24); (-88, getr R 25)]%Z ->
              rdn BSEGS MBr (at_ sp k) 8 = Some (LE8 v)).
    { intros k v Hin.
      assert (K : -88 <= k <= -8) by (cbn [In] in Hin; repeat (destruct Hin as [E|Hin]; [injection E as <- <-; lia|]); destruct Hin).
      apply TB; [first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | intros i Hi; rewrite at_u in Hi by lia; apply STKB; lia | exact (SLs k v Hin)]. }
    assert (SLQ : forall (k : Z) (v : word), In (k, v) [(-8, (0x8f790%bv : word)); (-16, Z_to_bv 64 0); (-24, Z_to_bv 64 (NIDS + 1)); (-32, bW)]%Z ->
              rdn BSEGS MBr (at_ (at_ sp (-112)) k) 8 = Some (LE8 v)).
    { intros k v Hin.
      assert (K : -32 <= k <= -8) by (cbn [In] in Hin; repeat (destruct Hin as [E|Hin]; [injection E as <- <-; lia|]); destruct Hin).
      apply TB; [rewrite at_at, at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | intros i Hi; rewrite at_at, at_u in Hi by lia; apply STKB; lia |].
      apply SLt. cbn [In] in Hin |- *. replace (Z_to_bv 64 0x8f790) with (0x8f790%bv : word) by (apply bv_eq; reflexivity). exact Hin. }
    destruct (rdn_defined_ex BSEGS MBr buf (Z.to_nat (8 * sz))) as (bs & Rws & Lbs).
    { intros i Hi. rewrite Z2Nat.id in Hi by lia. apply DEFB; [apply BUFD; lia|]. apply NHw. rewrite u_Z2bv by lia. left. lia. }
    { rewrite Z2Nat.id by lia. lia. }
    assert (Lbs' : Z.of_nat (length bs) = 8 * sz) by (rewrite Lbs, Z2Nat.id by lia; reflexivity).
    rewrite <- Lbs in Rws.
    (* [comment removed for export] *)
    set (ndW := di_node a NIDS).
    assert (Und : U ndW = U a + 16 * ((NIDS + 1) mod 2 ^ 16)) by ((lazymatch goal with |- ?G => let G' := eval unfold ndW, di_node in G in change_no_check G' end); rewrite u_Z2bv by lia; reflexivity).
    assert (SOKI : forall (x : word) (n : nat) v, 0x107000 <= U x -> U x + Z.of_nat n <= 2 ^ 64 -> rdn BSEGS MBr x n = Some v -> store_ok BSEGS MBr x n = true).
    { intros x n v H1 H2 Hr. exact (readable_store_ok BSEGS 0x107000 MBr x n v both_rw_above H1 H2 Hr). }
    assert (Rslot0 : rdn BSEGS MBr (tl_slot MUW idx) 8 = Some (LE8 (Z_to_bv 64 0))).
    { (lazymatch goal with |- ?G => let G' := eval unfold tl_slot in G in change_no_check G' end). rewrite UMU. pose proof (Dmap idx I16) as Cm.
      assert (ETAB : DEPOT_TAB bt = 0x1f0098) by ((lazymatch goal with |- ?G => let G' := eval unfold DEPOT_TAB in G in change_no_check G' end); rewrite BT_ia; reflexivity).
      assert (EMAP : DEPOT_MAP1 bt = 0x1f0098 + 4194320) by ((lazymatch goal with |- ?G => let G' := eval unfold DEPOT_MAP1 in G in change_no_check G' end); rewrite ETAB; reflexivity). rewrite EMAP, BT_segs in Cm.
      fold d in Cm. rewrite (nth_overflow (node_blocks bt d) 0) in Cm by (rewrite EIDX, Nat2Z.id; apply Nat.le_refl).
      replace (0x1f0098 + 4194312 + 8 + 8 * idx) with (0x1f0098 + 0x400010 + 8 * idx) by lia.
      apply IMGB; [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | | exact Cm]. intros i Hi WZ. cbn in Hi. destruct (CLS1 _ WZ) as [C|[C|[C|C]]]; clear - C Hi I16 Hspr SPC CR HKD Hbix; lia. }
    assert (Uslot : U (tl_slot MUW idx) = 0x1f0098 + 4194320 + 8 * idx) by ((lazymatch goal with |- ?G => let G' := eval unfold tl_slot in G in change_no_check G' end); rewrite UMU; first [ solve [ wd_unorm1; wd_zofnat; lia ] | rewrite u_Z2bv by lia; lia ]).
    assert (SOKs : store_ok BSEGS MBr (tl_slot MUW idx) 8 = true) by (refine (SOKI _ _ _ _ _ Rslot0); [rewrite Uslot; lia | rewrite Uslot; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia]).
    assert (SOKl : store_ok BSEGS MBr MUW 1 = true).
    { apply (rwseg_store_ok BSEGS 16 (Z_to_bv 64 0x5f0098) MBr MUW 1 mu_img_ok);
        [change (U (Z_to_bv 64 0x5f0098)) with 0x5f0098; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite UMU; change (U (Z_to_bv 64 0x5f0098)) with 0x5f0098; lia
         | rewrite UMU; change (U (Z_to_bv 64 0x5f0098)) with 0x5f0098; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia]. }
    assert (SOKb : store_ok BSEGS MBr bW 4 = true).
    { assert (ETAB : DEPOT_TAB bt = 0x1f0098) by ((lazymatch goal with |- ?G => let G' := eval unfold DEPOT_TAB in G in change_no_check G' end); rewrite BT_ia; reflexivity).
      pose proof (Dtab b Hbix) as Cb. rewrite ETAB, BT_segs in Cb. unfold cellZ, cellN in Cb. fold bW in Cb.
      destruct (rdn_of_bytes BSEGS MBr 4 bW) as (v1 & Rv1 & _); [rewrite UbW; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | | refine (SOKI _ _ _ _ _ Rv1); [rewrite UbW; lia | rewrite UbW; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia]].
      intros y Hy. rewrite UbW in Hy. cbn in Hy.
      destruct (rdn_bytes BSEGS M0 4 bW _ Cb ltac:(rewrite UbW; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia) y ltac:(rewrite UbW; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia)) as [b0 Hb0].
      assert (Hb1 : rdn BSEGS M y 1 = Some [b0]) by (cbn [rdn] in Hb0 |- *; rewrite (EQ0 y ltac:(apply XI; lia)); exact Hb0).
      destruct (rdn1_grows BSEGS M MB y b0 ltac:(eapply mem_grows_trans; [exact GR1 | exact GRB]) Hb1) as [b' Hb'].
      exists b'. cbn [rdn] in Hb' |- *. (lazymatch goal with |- ?G => let G' := eval unfold MBr in G in change_no_check G' end). rewrite (mrestrict_off Hd MB y (NHw y ltac:(right; lia))). exact Hb'. }
    assert (SOKn : store_ok BSEGS MBr ndW 16 = true).
    { apply store_ok_bytes; [| rewrite Und; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia]. intros x Hx. rewrite Und in Hx. cbn in Hx. apply store_ok1_some.
      (lazymatch goal with |- ?G => let G' := eval unfold MBr in G in change_no_check G' end). rewrite (mrestrict_off Hd MB x) by (rewrite <- (Z_to_bv_bv_unsigned 64 x); apply NHa; lia).
      apply DEFA. lia. }
    assert (Hstk : store_ok BSEGS MBr (at_ sp (-224)) 112 = true).
    { apply store_ok_bytes; [| first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ]]. intros x Hx. rewrite at_u in Hx by lia. cbn in Hx. apply store_ok1_some.
      apply DEFB; [apply STK; lia | apply NHw; left; lia]. }
    assert (SOKS : store_ok BSEGS MBr SSW 8 = true) by (refine (SOKI _ _ _ _ _ Rtot); [change (U SSW) with 1966216; lia | change (U SSW) with 1966216; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia]).
    assert (Ucell : U (st_cell SSW tot) = 1966216 + 16 * q + 24) by ((lazymatch goal with |- ?G => let G' := eval unfold st_cell in G in change_no_check G' end); change (U SSW) with 1966216; fold q; rewrite u_Z2bv by lia; reflexivity).
    assert (SOKso : store_ok BSEGS MBr (st_cell SSW tot) 4 = true) by (refine (SOKI _ _ _ _ _ Rso); [rewrite Ucell; lia | rewrite Ucell; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia]).
    assert (Udst : U (st_dst blkdW tot) = blkd + 8 * (tot mod 2 ^ 20)) by ((lazymatch goal with |- ?G => let G' := eval unfold st_dst in G in change_no_check G' end); rewrite UbdW; rewrite u_Z2bv by lia; reflexivity).
    assert (SOKd : store_ok BSEGS MBr (st_dst blkdW tot) (8 + length bs) = true).
    { apply store_ok_bytes; [| rewrite Udst, Nat2Z.inj_add, Lbs'; change (Z.of_nat 8) with 8; lia].
      intros x Hx. rewrite Udst, Nat2Z.inj_add, Lbs' in Hx. change (Z.of_nat 8) with 8 in Hx. apply store_ok1_some.
      pose proof (Dsw blkd INQ) as WQ. pose proof (u64_range x) as Hxr.
      apply DEFB; [| rewrite <- (Z_to_bv_bv_unsigned 64 x); apply NHq; lia].
      assert (D0 : M0 x <> None) by (rewrite <- (Z_to_bv_bv_unsigned 64 x); apply (WQ (U x)); lia).
      destruct (decide (M x = M0 x)) as [E|NE]; [rewrite E; exact D0 | exact (proj2 (DIFF x NE))]. }
    (* [comment removed for export] *)
    assert (NIm : forall i : reg, In i [20%bv; 21%bv; 22%bv; 23%bv; 24%bv; 25%bv; 26%bv; 27%bv; 3%bv; 4%bv] -> ~ In i mo_clob).
    { intros i Hi Hx. unfold mo_clob in Hx. cbn [In] in Hi, Hx. repeat (destruct Hi as [<-|Hi]; [repeat (destruct Hx as [Hx|Hx]; [discriminate Hx|]); exact Hx|]). exact Hi. }
    assert (T21 : getr r' 21 = Z_to_bv 64 (dp_tab d b)) by (rewrite (AGm 21%bv) by (apply NIm; in_l); exact A21).
    assert (T22 : getr r' 22 = Z_to_bv 64 65535) by (rewrite (AGm 22%bv) by (apply NIm; in_l); exact A22).
    assert (T23 : getr r' 23 = Z_to_bv 64 (NIDS + 1)) by (rewrite (AGm 23%bv) by (apply NIm; in_l); exact A23).
    (* [comment removed for export] *)
    destruct (put_n1_tail MBr (seg_rom BSEGS) sp ret MUW h a bW buf blkdW CFW (dp_tab d b) NIDS sz tag tot (dp_stored d q) bs
                (getr R 8) (getr R 9) (getr R 18) (getr R 19) (getr R 20) (getr R 21) (getr R 22) (getr R 23) (getr R 24) (getr R 25) r'
                B2 ltac:(rewrite B8; exact A8) ltac:(rewrite B9, A9, UMU; reflexivity) B10 ltac:(rewrite B19; exact A19) T21 T22 T23
                ltac:(lia) RET ltac:(rewrite UMU; lia) ltac:(rewrite UCF; lia) ltac:(lia) ltac:(rewrite UMU; lia) ltac:(rewrite UbW, UMU; lia)
                ltac:(rewrite UMU, UbdW; clear - GQ4 GQ2 APQ SPC HKD CR GA GC; lia) ltac:(lia) ltac:(lia) Htag ltac:(pose proof (D4 b Hbix); lia) ltac:(lia) CI1 (D11 q) Lbs
                Rsz Rtag Rtr Rws Rtot Rblk Rso Rcfp Rflag SLQ SLB SOKs SOKl SOKb SOKn Hstk SOKS SOKso SOKd)
      as (r2 & M'r & RUN2 & S2 & C10 & C2 & C1 & C8 & C9 & C18 & C19 & C20 & C21 & C22 & C23 & C24 & C25 & Kb & Kh & Kl & Ks & Kt & Kso & Kslot & Kmu & AG2).
    set (Qpost := depot_post_w bt FXOK KD X st Lc FF M mdl R sp ret).
    set (W2 := n1tail_W sp MUW ndW bW idx (1966216 + 16 * (tot / 2 ^ 20) + 24) (U blkdW + 8 * (tot mod 2 ^ 20)) (8 + 8 * sz)) in *.
    assert (CLS2 : forall z, W2 z -> (U sp - 224 <= z < U sp - 112) \/ (0x1f0098 + 4 * b <= z < 0x1f0098 + 4 * b + 4)
                                    \/ (0x1f0098 + 4194312 <= z < 0x1f0098 + 4194312 + 1) \/ (0x1f0098 + 4194320 + 8 * idx <= z < 0x1f0098 + 4194320 + 8 * idx + 8)
                                    \/ (U a <= z < U a + 2 ^ 20) \/ (1966216 <= z < 1966216 + 8) \/ (1966216 + 16 * q + 24 <= z < 1966216 + 16 * q + 24 + 4)
                                    \/ (blkd + 8 * (tot mod 2 ^ 20) <= z < blkd + 8 * (tot mod 2 ^ 20) + 8 + 8 * sz)).
    { intros z Hz. unfold W2, n1tail_W, n1post_W, fstore_W, wun, ivl in Hz. rewrite UMU, UbW, UbdW, Und in Hz. fold q in Hz. clear - Hz M16. first [ solve [ repeat match goal with H : _ \/ _ |- _ => destruct H as [H|H] end; repeat (first [ left; solve [lia] | right ]); lia ] | lia ]. }
    assert (NHW2 : forall x : word, W2 (U x) -> Hd x = false).
    { intros x Hx. pose proof (u64_range x) as Hxr. destruct (CLS2 _ Hx) as [C|[C|[C|[C|[C|[C|[C|C]]]]]]].
      - apply NHw. left. clear - C SPC HKD. lia.
      - apply NHw. right. clear - C Hbix. lia.
      - apply NHw. right. clear - C. lia.
      - apply NHw. right. clear - C I16. lia.
      - rewrite <- (Z_to_bv_bv_unsigned 64 x). apply NHa. exact C.
      - apply NHw. right. clear - C. lia.
      - apply NHw. right. clear - C Q20. lia.
      - rewrite <- (Z_to_bv_bv_unsigned 64 x). apply NHq. clear - C M20 SZ. lia. }
    (* [comment removed for export] *)
    apply (katD_msteps_acct BSEGS Hd HOFF asanF_segs_wx (a_aa st)
             (@mkst fx r' (Z_to_bv 64 0x8fdb8) MB (seg_rom BSEGS)) (@mkst fx r2 ret M'r (seg_rom BSEGS)) mdl4).
    { rewrite L3. apply lazy_cover_HID. } { exact Bw1. } { exact MI4. } { exact HL4. }
    { rewrite restrict_mkst9. fold MBr. replace (Z_to_bv 64 0x8fdb8) with (0x8fdb8%bv : word) by (apply bv_eq; reflexivity). exact RUN2. }
    intros mdl5 MI5 SBM5 HC5. rewrite unrestrict_mkst.
    replace (ms_mem (@mkst fx r' (Z_to_bv 64 0x8fdb8) MB (seg_rom BSEGS))) with MB by reflexivity.
    set (M' := munrestrict Hd MB M'r).
    pose proof (msum_unrestrict Hd W2 MB M'r NHW2 S2) as [FR2 GR2]. fold M' in FR2, GR2.
    pose proof (same_but_materialized_frame mdl4 mdl5 SBM5) as (_ & Evm5 & Elz5 & _ & _ & _ & _ & _ & _ & _ & _ & _ & Ehl5 & _ & _ & _ & Eeg5).
    assert (VIS : forall (z : Z) (k : nat), 0 <= z -> z + Z.of_nat k < 2 ^ 64 -> (forall i, z <= i < z + Z.of_nat k -> Hd (Z_to_bv 64 i) = false) ->
              rdn BSEGS M' (Z_to_bv 64 z) k = rdn BSEGS M'r (Z_to_bv 64 z) k).
    { intros z k Hz Hk F. apply rdn_munrestrict; [first [ solve [ wd_unorm1; wd_zofnat; lia ] | rewrite u_Z2bv by lia; lia ]|]. intros x Hx. rewrite u_Z2bv in Hx by lia.
      rewrite <- (Z_to_bv_bv_unsigned 64 x). apply F. exact Hx. }
    set (Wall := wun W1 (wun WB W2)).
    assert (SALL : msum Wall M M') by (exact (msum_trans _ _ _ _ _ (conj FR1 GR1) (msum_trans _ _ _ _ _ (conj FRB GRB) (conj FR2 GR2)))).
    destruct SALL as [FRA GRA].
    assert (CLS : forall z, Wall z -> (U sp - 464 <= z < U sp) \/ (0x1f0098 + 4 * b <= z < 0x1f0098 + 4 * b + 4) \/ (0x1f0098 + 4194304 <= z < 0x1f0098 + 4194304 + 4)
                                   \/ (0x1f0098 + 4194312 <= z < 0x1f0098 + 4194312 + 4) \/ (0x1f0098 + 4194320 + 8 * idx <= z < 0x1f0098 + 4194320 + 8 * idx + 8)
                                   \/ (U a <= z < U a + 2 ^ 20) \/ (1966216 <= z < 1966216 + 8) \/ (1966216 + 16 * q + 24 <= z < 1966216 + 16 * q + 24 + 4)
                                   \/ (blkd + 8 * (tot mod 2 ^ 20) <= z < blkd + 8 * (tot mod 2 ^ 20) + 8 + 8 * sz)).
    { intros z [Hz | [Hz | Hz]].
      - destruct (CLS1 _ Hz) as [C|[C|[C|C]]]; clear - C; lia.
      - unfold WB, wun, ivl in Hz. clear - Hz. lia.
      - destruct (CLS2 _ Hz) as [C|[C|[C|[C|[C|[C|[C|C]]]]]]]; clear - C; lia. }
    (* [comment removed for export] *)
    set (std' := fupdZ (dp_stored d) q ((dp_stored d q + sz + 1) mod 2 ^ 32)).
    set (st' := op_depot_insert st b (U h) (dp_tab d b) (tot + 1) (tot + sz + 1) std' (Some (U a)) None).
    assert (ELEN : Z.of_nat (length (dp_nodeblocks d)) + 1 = idx).
    { rewrite EIDX. (lazymatch goal with |- ?G => let G' := eval unfold node_blocks in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [length] in G in change_no_check G' end). rewrite Nat2Z.inj_succ. clear. lia. }
    assert (W' : WF bt st' Lc FF).
    { apply (OPS_WF_depot_insert_pf bt st Lc FF b (U h) (dp_tab d b) (tot + 1) (tot + sz + 1) std' (Some (U a)) None W Hbix).
      - pose proof (u64_range h) as Hh. clear - Hh. lia.
      - clear - D7 FROOM. lia.
      - intros i. (lazymatch goal with |- ?G => let G' := eval unfold std', fupdZ in G in change_no_check G' end). destruct (i =? q); [apply Z.mod_pos_bound; clear; lia | exact (D11 i)].
      - reflexivity.
      - exact ROOM.
      - exact NROOM.
      - fold d NIDS. split; [intros E; discriminate E | intros E; exfalso; fold idx in E; clear - E ELEN; lia].
      - fold d tot. (lazymatch goal with |- ?G => let G' := eval cbn [blk_opt length Z.of_nat] in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval unfold FRW in G in change_no_check G' end). clear - SZ. lia.
      - fold d tot. (lazymatch goal with |- ?G => let G' := eval cbn [blk_opt] in G in change_no_check G' end). rewrite app_nil_r. rewrite D10. rewrite (max_blocks_nogrow2 tot sz D7 ltac:(clear - SZ; lia) CI1 CI2). reflexivity.
      - fold d. (lazymatch goal with |- ?G => let G' := eval cbn [blk_opt] in G in change_no_check G' end). rewrite app_nil_r. exact D8.
      - intros p E. injection E as <-. exact (conj DY (conj AL AP)).
      - intros p E. discriminate E.
      - intros p q0 _ E. discriminate E.
      - intros p b0 n0 E Hin. injection E as <-.
        exact (grant_apart_maps0 bt st Lc FF M0 mdl mdlm (2 ^ 20) (2 ^ 28) (Z_to_bv 64 0) a (2 ^ 20) W RP EVm ltac:(clear; lia) eq_refl G b0 n0 Hin).
      - intros p b0 n0 E. discriminate E. }
    assert (EST : st' = depot_st st (a_dep st') []) by ((lazymatch goal with |- ?G => let G' := eval unfold st', op_depot_insert, depot_st in G in change_no_check G' end); (lazymatch goal with |- ?G => let G' := eval cbn [blk_opt store_aa List.map a_dep] in G in change_no_check G' end); reflexivity).
    assert (ETAB : DEPOT_TAB bt = 0x1f0098) by ((lazymatch goal with |- ?G => let G' := eval unfold DEPOT_TAB in G in change_no_check G' end); rewrite BT_ia; reflexivity).
    assert (ENID : DEPOT_NIDS bt = 0x1f0098 + 4194304) by ((lazymatch goal with |- ?G => let G' := eval unfold DEPOT_NIDS in G in change_no_check G' end); rewrite ETAB; reflexivity).
    assert (EMAP : DEPOT_MAP1 bt = 0x1f0098 + 4194320) by ((lazymatch goal with |- ?G => let G' := eval unfold DEPOT_MAP1 in G in change_no_check G' end); rewrite ETAB; reflexivity).
    assert (ENB : node_blocks bt (a_dep st') = node_blocks bt d ++ [U a]) by reflexivity.
    assert (ESB : store_blocks bt (a_dep st') = store_blocks bt d).
    { (lazymatch goal with |- ?G => let G' := eval unfold store_blocks, st', op_depot_insert in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [a_dep dp_storeblocks blk_opt] in G in change_no_check G' end). rewrite app_nil_r. reflexivity. }
    set (nda := U a + 16 * ((NIDS + 1) mod 2 ^ 16)) in *.
    assert (ENA : node_addr bt (a_dep st') (NIDS + 1) = nda).
    { (lazymatch goal with |- ?G => let G' := eval unfold node_addr in G in change_no_check G' end). rewrite ENB. fold idx. rewrite EIDX, Nat2Z.id. rewrite app_nth2 by apply Nat.le_refl. rewrite Nat.sub_diag. reflexivity. }
    assert (ENNI : nn_idx st = idx) by ((lazymatch goal with |- ?G => let G' := eval unfold nn_idx in G in change_no_check G' end); fold d; exact ELEN).
    assert (INA : In (U a) (node_blocks bt (a_dep st'))) by (rewrite ENB; apply in_or_app; right; left; reflexivity).
    (* [comment removed for export] *)
    assert (XOFF : forall z, Wall z -> z < U sp - 464 -> ~ X z).
    { intros z Hz Hlt Xz. destruct (CLS _ Hz) as [C|[C|[C|[C|[C|[C|[C|[C|C]]]]]]]].
      - clear - C Hlt. lia.
      - apply (XI z); [clear - C Hbix; lia | exact Xz].
      - apply (XI z); [clear - C; lia | exact Xz].
      - apply (XI z); [clear - C; lia | exact Xz].
      - apply (XI z); [clear - C I16; lia | exact Xz].
      - exact (px_off_fresh bt st Lc FF X (U a) (2 ^ 20) z W PXH Xz AP DY C).
      - apply (XI z); [clear - C; lia | exact Xz].
      - apply (XI z); [clear - C Q20; lia | exact Xz].
      - apply (px_off_stores bt st Lc FF W X z blkd PXH Xz INQ). clear - C M20 SZ. lia. }
    (* [comment removed for export] *)
    assert (Kt' : rdn BSEGS M'r (Z_to_bv 64 1966216) 8 = Some (LE8 (Z_to_bv 64 (tot + sz + 1)))).
    { change (Z_to_bv 64 1966216) with SSW. rewrite Kt. f_equal. f_equal. (lazymatch goal with |- ?G => let G' := eval unfold v_add in G in change_no_check G' end). rewrite !u_Z2bv by lia. f_equal. clear. lia. }
    assert (Kso' : rdn BSEGS M'r (Z_to_bv 64 (1966216 + 16 * q + 24)) 4 = Some (LE4 (Z_to_bv 64 ((dp_stored d q + sz + 1) mod 2 ^ 32)))).
    { replace (Z_to_bv 64 (1966216 + 16 * q + 24)) with (st_cell SSW tot : word) by ((lazymatch goal with |- ?G => let G' := eval unfold st_cell in G in change_no_check G' end); change (U SSW) with 1966216; fold q; reflexivity).
      rewrite Kso. f_equal. replace (dp_stored d q + sz + 1) with (dp_stored d q + (sz + 1)) by (clear; lia). apply stored_le4b; [exact (D11 q) | clear - SZ; lia]. }
    assert (Ks' : rdn BSEGS M'r (at_ ndW 12) 4 = Some (LE4 (Z_to_bv 64 (tot + 1)))).
    { (lazymatch goal with |- ?G => let G' := eval unfold ndW in G in change_no_check G' end). rewrite Ks. f_equal. apply st_id_le4; [exact D7 | clear - FROOM; lia]. }
    assert (OUTW : forall z, AIMGLO <= z < AIMGHI -> ~ (0x1f0098 + 4 * b <= z < 0x1f0098 + 4 * b + 4) -> ~ (0x1f0098 + 4194304 <= z < 0x1f0098 + 4194304 + 4)
                     -> ~ (0x1f0098 + 4194312 <= z < 0x1f0098 + 4194312 + 4) -> ~ (0x1f0098 + 4194320 + 8 * idx <= z < 0x1f0098 + 4194320 + 8 * idx + 8)
                     -> ~ (1966216 <= z < 1966216 + 8) -> ~ (1966216 + 16 * q + 24 <= z < 1966216 + 16 * q + 24 + 4) -> ~ Wall z).
    { intros z Hz N1 N2 N3 N4 N5 N6 WZ.
      destruct (CLS _ WZ) as [C|[C|[C|[C|[C|[C|[C|[C|C]]]]]]]];
        [clear - C Hz SPC CR HKD; lia | exact (N1 C) | exact (N2 C) | exact (N3 C) | exact (N4 C) | clear - C Hz GA; lia | exact (N5 C) | exact (N6 C) | clear - C Hz GQ4 M20; lia]. }
    assert (XIMG' : forall i, AIMGLO <= i < AIMGHI -> ~ X i /\ Hd (Z_to_bv 64 i) = false).
    { intros i Hi. split; [apply XI; exact Hi | apply NHs; [clear - Hi; lia | right; clear - Hi; lia]]. }
    assert (XND : forall i, U a <= i < U a + 2 ^ 20 -> ~ X i /\ Hd (Z_to_bv 64 i) = false).
    { intros i Hi. split; [intros Xi; exact (px_off_fresh bt st Lc FF X (U a) (2 ^ 20) i W PXH Xi AP DY Hi) | apply NHa; exact Hi]. }
    assert (ESS' : SSOBJ bt = 1966216) by exact ESS.
    assert (NDR : 0 <= nda /\ nda + 16 < 2 ^ 64) by ((lazymatch goal with |- ?G => let G' := eval unfold nda in G in change_no_check G' end); clear - Har M16 GC CR; lia).
    assert (Kl' : rdn BSEGS M'r (Z_to_bv 64 (nda + 8)) 4 = Some (LE4 (Z_to_bv 64 (dp_tab d b)))).
    { replace (Z_to_bv 64 (nda + 8)) with (at_ (di_node a NIDS) 8 : word); [exact Kl|].
      apply bv_eq. fold ndW. rewrite at_u by (rewrite Und; fold nda; clear - NDR; lia). rewrite Und. fold nda. rewrite u_Z2bv by (clear - NDR; lia). reflexivity. }
    assert (Ks'' : rdn BSEGS M'r (Z_to_bv 64 (nda + 12)) 4 = Some (LE4 (Z_to_bv 64 (tot + 1)))).
    { replace (Z_to_bv 64 (nda + 12)) with (at_ ndW 12 : word); [exact Ks'|].
      apply bv_eq. rewrite at_u by (rewrite Und; fold nda; clear - NDR; lia). rewrite Und. fold nda. rewrite u_Z2bv by (clear - NDR; lia). reflexivity. }
    assert (Kslot' : rdn BSEGS M'r (Z_to_bv 64 (0x1f0098 + 4194320 + 8 * idx)) 8 = Some (LE8 a)).
    { replace (Z_to_bv 64 (0x1f0098 + 4194320 + 8 * idx)) with (tl_slot MUW idx : word); [exact Kslot|]. (lazymatch goal with |- ?G => let G' := eval unfold tl_slot in G in change_no_check G' end). rewrite UMU. f_equal; try (clear; lia). }
    (* [comment removed for export] *)
    assert (RX' : RepX bt X st' Lc FF M' mdl5).
    { apply (RepX_mono bt (fun z => X z /\ ~ False) X); [intros z [Hz _]; exact Hz|].
      apply (repx_step bt X (fun _ => False) Wall Xdec_false st st' Lc Lc FF FF M M' mdl mdl5).
      - exists M0. split; [exact RP | exact DIFF].
      - intros x NE. apply (msum_changed Wall M M'); [(lazymatch goal with |- ?G => let G' := eval unfold Wall, W1, WB, W2, n1tail_W, n1post_W, fstore_W, n1pre_W in G in change_no_check G' end); repeat apply wun_dec; apply ivl_dec | split; [exact FRA | exact GRA] | exact NE].
      - intros x F. destruct F.
      - intros N0 N0' RPn Dn DIFF' EQX EQM.
        assert (CELLNEW : forall (z : Z) (k : nat) bz, 0 <= z -> z + Z.of_nat k < 2 ^ 64 -> (forall i, z <= i < z + Z.of_nat k -> ~ X i /\ Hd (Z_to_bv 64 i) = false) ->
                  rdn BSEGS M'r (Z_to_bv 64 z) k = Some bz -> rdn BSEGS N0' (Z_to_bv 64 z) k = Some bz).
        { intros z k bz Hz Hk F Hr. rewrite <- Hr, <- (VIS z k Hz Hk (fun i Hi => proj2 (F i Hi))). apply rdn_ext; [first [ solve [ wd_unorm1; wd_zofnat; lia ] | rewrite u_Z2bv by lia; lia ]|].
          intros x Hx. rewrite u_Z2bv in Hx by lia. apply EQX. left. exact (proj1 (F (U x) Hx)). }
        assert (CELLOLD : forall (z : Z) (k : nat) bz, 0 <= z -> z + Z.of_nat k < 2 ^ 64 -> (forall i, z <= i < z + Z.of_nat k -> ~ Wall i) ->
                  rdn BSEGS N0 (Z_to_bv 64 z) k = Some bz -> rdn BSEGS N0' (Z_to_bv 64 z) k = Some bz).
        { intros z k bz Hz Hk F Hr. rewrite <- Hr. apply rdn_ext; [first [ solve [ wd_unorm1; wd_zofnat; lia ] | rewrite u_Z2bv by lia; lia ]|]. intros x Hx. rewrite u_Z2bv in Hx by lia.
          destruct (decide (N0' x = N0 x)) as [E|NE]; [exact E|]. exfalso. destruct (DIFF' x NE) as [[WA|[]] _]. exact (F (U x) Hx WA). }
        pose proof RPn as (_ & _ & _ & _ & _ & _ & _ & _ & (Dtab' & Dnids' & Dmu' & Dmap' & Dnode' & Dnw' & Dfr' & Dblk' & Dsw') & _ & _ & _ & (_ & _ & _ & FAl & _) & _).
        fold d in Dtab', Dnids', Dmu', Dmap', Dnode', Dnw', Dfr', Dblk', Dsw'.
        apply (OPS_REP_depot_insert_pf bt st Lc FF N0 N0' mdl mdl5 b (U h) (dp_tab d b) (tot + 1) (tot + sz + 1) std' (Some (U a)) None W W' RPn Hbix).
        + intros p E. injection E as <-. exact (conj DY (conj AL AP)).
        + intros p E. discriminate E.
        + intros p q0 _ E. discriminate E.
        + intros x NE. destruct (DIFF' x NE) as [[WA|[]] DF]. split; [| exact DF]. (lazymatch goal with |- ?G => let G' := eval unfold foot_depot_ins in G in change_no_check G' end). rewrite ETAB, ENID, EMAP, ESS', ENNI. fold st' d; fold NIDS; rewrite ENA, ESB.
          destruct (CLS _ WA) as [C|[C|[C|[C|[C|[C|[C|[C|C]]]]]]]].
          * do 7 right. clear - C SPC HKD. lia.
          * left. exact C.
          * right; left. clear - C. lia.
          * right; left. clear - C. lia.
          * right; right; left. split; [discriminate | clear - C; lia].
          * do 6 right; left. exists (U a). split; [reflexivity | exact C].
          * do 3 right; left. clear - C. lia.
          * do 3 right; left. clear - C Q20. lia.
          * do 5 right; left. exists blkd. split; [exact INQ | clear - C M20 SZ; lia].
        + rewrite BT_segs, ETAB. apply CELLNEW; [clear - Hbix; lia | (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); clear - Hbix; lia
                                                 | intros i Hi; apply XIMG'; cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in Hi; clear - Hi Hbix; lia | exact Kb].
        + rewrite BT_segs, ENID. (lazymatch goal with |- ?G => let G' := eval unfold cellZ, cellN in G in change_no_check G' end). refine (eq_trans _ Kn1). apply rdn_ext; [rewrite u_Z2bv by (clear; lia); (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear; lia|].
          intros x Hx. rewrite u_Z2bv in Hx by (clear; lia). cbn in Hx.
          rewrite (EQX x) by (left; apply XI; clear - Hx; lia).
          rewrite (FR2 x) by (intros WZ; destruct (CLS2 _ WZ) as [C|[C|[C|[C|[C|[C|[C|C]]]]]]]; clear - C Hx SPC CR HKD Hbix I16 GA GQ4 M20 Q20; lia).
          rewrite (FRB x) by ((lazymatch goal with |- ?G => let G' := eval unfold WB, wun, ivl in G in change_no_check G' end); clear - Hx SPC CR HKD GA; lia).
          (lazymatch goal with |- ?G => let G' := eval unfold M1f in G in change_no_check G' end). apply munrestrict_off. apply NHw. right. clear - Hx. lia.
        + rewrite BT_segs, ENID. (lazymatch goal with |- ?G => let G' := eval unfold byteZ, cellN in G in change_no_check G' end). change (word_to_le_bytes 1 (Z_to_bv 64 0)) with [Z_to_bv 8 0].
          replace (Z_to_bv 64 (0x1f0098 + 4194304 + 8)) with MUW by (apply bv_eq; reflexivity). (lazymatch goal with |- ?G => let G' := eval unfold MUW in G in change_no_check G' end).
          apply CELLNEW; [clear; lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear; lia | intros i Hi; apply XIMG'; cbn in Hi; clear - Hi; lia | exact Kmu].
        + rewrite BT_segs. fold st' d; fold NIDS; rewrite ENA. (lazymatch goal with |- ?G => let G' := eval unfold cellZ, cellN in G in change_no_check G' end). rewrite Z_to_bv_bv_unsigned.
          apply CELLNEW; [(lazymatch goal with |- ?G => let G' := eval unfold nda in G in change_no_check G' end); clear - Har M16; lia | (lazymatch goal with |- ?G => let G' := eval unfold nda in G in change_no_check G' end); (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); clear - M16 GC CR; lia
                          | intros i Hi; apply XND; cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in Hi; unfold nda in Hi; clear - Hi M16; lia | exact Kh].
        + rewrite BT_segs. fold st' d; fold NIDS; rewrite ENA.
          apply CELLNEW; [clear - NDR; lia | (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); clear - NDR; lia
                          | intros i Hi; apply XND; cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in Hi; unfold nda in Hi; clear - Hi M16; lia | exact Kl'].
        + rewrite BT_segs. fold st' d; fold NIDS; rewrite ENA.
          apply CELLNEW; [clear - NDR; lia | (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); clear - NDR; lia
                          | intros i Hi; apply XND; cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in Hi; unfold nda in Hi; clear - Hi M16; lia | exact Ks''].
        + intros p E. injection E as <-. split.
          * rewrite BT_segs, EMAP, ENNI. (lazymatch goal with |- ?G => let G' := eval unfold cellZ, cellN in G in change_no_check G' end). rewrite Z_to_bv_bv_unsigned.
            apply CELLNEW; [clear - I16; lia | (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); clear - I16; lia
                            | intros i Hi; apply XIMG'; cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in Hi; clear - Hi I16; lia | exact Kslot'].
          * rewrite BT_segs. intros i Hi. destruct (XND i Hi) as [NXi NHi].
            assert (DI : N0' (Z_to_bv 64 i) <> None).
            { rewrite (EQX (Z_to_bv 64 i)) by (left; rewrite u_Z2bv by (clear - Hi Har GC CR; lia); exact NXi). apply GR2. apply DEFA. rewrite u_Z2bv by (clear - Hi Har GC CR; lia). exact Hi. }
            split; [exact DI | apply store_ok1_some; exact DI].
        + rewrite BT_segs, ESS'. apply CELLNEW; [clear; lia | (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); clear; lia
                                                 | intros i Hi; apply XIMG'; cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in Hi; clear - Hi; lia | exact Kt'].
        + intros i Hi. fold st'. rewrite ESB. fold d. destruct (Dblk' i Hi) as (Cq1 & Cq2 & Cq3). rewrite BT_segs, ESS' in *.
          split; [| split].
          * apply CELLOLD; [clear - Hi; lia | (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); clear - Hi; lia | | exact Cq1].
            intros j Hj. cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in Hj. apply OUTW; clear - Hj Hi Q20 Hbix I16; lia.
          * destruct (Z.eq_dec i q) as [->|NEq].
            -- (lazymatch goal with |- ?G => let G' := eval unfold std' in G in change_no_check G' end). rewrite fupdZ_same. replace (1966216 + 24 + 16 * q) with (1966216 + 16 * q + 24) by (clear; lia).
               apply CELLNEW; [clear - Q20; lia | (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); clear - Q20; lia
                               | intros j Hj; apply XIMG'; cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in Hj; clear - Hj Q20; lia | exact Kso'].
            -- (lazymatch goal with |- ?G => let G' := eval unfold std' in G in change_no_check G' end). rewrite fupdZ_other by exact NEq. apply CELLOLD; [clear - Hi; lia | (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); clear - Hi; lia | | exact Cq2].
               intros j Hj. cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in Hj. apply OUTW; clear - Hj Hi Q20 Hbix I16 NEq; lia.
          * apply CELLOLD; [clear - Hi; lia | (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); clear - Hi; lia | | exact Cq3].
            intros j Hj. cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in Hj. apply OUTW; clear - Hj Hi Q20 Hbix I16; lia.
        + intros q0 E. discriminate E.
        + (lazymatch goal with |- ?G => let G' := eval cbn [blk_opt List.map app] in G in change_no_check G' end). rewrite Evm5, L1. rewrite Z_to_bv_bv_unsigned. apply Permutation_refl.
        + rewrite Evm5. exact L2.
        + intros x. rewrite Elz5, L3. split; [intros H; left; exact H | intros [H | (q0 & E & _)]; [exact H | discriminate E]].
        + rewrite Elz5, L3. exact FAl.
        + rewrite Evm5. exact L4.
        + rewrite Evm5. exact L5.
        + rewrite Evm5. exact L6.
        + rewrite Evm5. exact L7.
        + rewrite Evm5. exact L8.
        + rewrite Evm5. exact L9.
        + (lazymatch goal with |- ?G => let G' := eval cbn [store_aa blk_opt List.map] in G in change_no_check G' end). rewrite app_nil_r. exact MI5.
        + rewrite Eeg5. (lazymatch goal with |- ?G => let G' := eval cbn [blk_opt length Z.of_nat] in G in change_no_check G' end). rewrite Usz in L10. clear - L10. lia. }
    (* [comment removed for export] *)
    assert (CHG : forall x : word, M' x <> M x -> Wall (U x) /\ M' x <> None).
    { intros x NE. apply (msum_changed Wall M M'); [(lazymatch goal with |- ?G => let G' := eval unfold Wall, W1, WB, W2, n1tail_W, n1post_W, fstore_W, n1pre_W in G in change_no_check G' end); repeat apply wun_dec; apply ivl_dec | split; [exact FRA | exact GRA] | exact NE]. }
    apply katD_refl. exists fx, st', M', mdl5, r2, (NIDS + 1).
    split; [reflexivity|]. split; [exact HFX|]. split; [exists (a_dep st'), []; exact EST|]. split; [exact W'|]. split; [exact RX'|].
    split.
    { intros x Xx OUT. apply FRA. intros WA. destruct (Z_lt_le_dec (U x) (U sp - 464)) as [L|L]; [exact (XOFF _ WA L Xx)|].
      destruct (CLS _ WA) as [C|[C|[C|[C|[C|[C|[C|[C|C]]]]]]]]; clear - C L OUT HKD SPC CR Hbix I16 GC Q20 GQ2 M20 SZ; lia. }
    split.
    { intros x NE. destruct (CHG x NE) as [WA DF]. split; [| exact DF]. (lazymatch goal with |- ?G => let G' := eval unfold depot_foot_w, depot_foot, foot_depot_static in G in change_no_check G' end). rewrite ETAB, ENID, EMAP, ESS', ESB.
      destruct (CLS _ WA) as [C|[C|[C|[C|[C|[C|[C|[C|C]]]]]]]].
      - left. do 3 right. clear - C HKD. lia.
      - left. left. left. clear - C Hbix. lia.
      - left. left. left. clear - C. lia.
      - right. right. clear - C. lia.
      - left. left. right; right; left. clear - C I16. lia.
      - left. right; left. exists (U a). split; [exact INA | exact C].
      - left. left. do 3 right; left. clear - C. lia.
      - left. left. do 4 right. clear - C Q20. lia.
      - left. right; right; left. exists blkd. split; [exact INQ | clear - C M20 SZ; lia]. }
    split.
    { intros x NE. destruct (CHG x NE) as [WA DF]. destruct DOBL as (_ & DO2 & DO3).
      assert (IP : forall z, 0x1a0061 <= z < 0x630810 -> in_wins (ia_priv (bt_ia bt)) z).
      { intros z Hz. rewrite BT_ia. exists 0x1a0061, 0x630810. split; [(lazymatch goal with |- ?G => let G' := eval cbn [ia_priv both_addrs In] in G in change_no_check G' end); do 6 right; left; reflexivity | exact Hz]. }
      destruct (CLS _ WA) as [C|[C|[C|[C|[C|[C|[C|[C|C]]]]]]]].
      - left. clear - C HKD. lia.
      - right; right. apply IP. clear - C Hbix. lia.
      - right; right. apply IP. clear - C. lia.
      - right; right. apply IP. clear - C. lia.
      - right; right. apply IP. clear - C I16. lia.
      - right; left. exact (DO2 st' Lc FF (U a) (U x) W' INA C).
      - right; right. apply IP. clear - C. lia.
      - right; right. apply IP. clear - C Q20. lia.
      - right; left. apply (DO3 st Lc FF blkd (U x) W INQ). clear - C M20 SZ. lia. }
    split.
    { intros z Hz. unfold as_callee_saved in Hz. cbn [In] in Hz.
      destruct Hz as [<-|Hz]; [transitivity sp; [exact C2 | symmetry; exact E2]|].
      assert (KEEP : forall k, ~ In (Z_to_bv 5 k) put_clob -> ~ In (Z_to_bv 5 k) mo_clob -> ~ In (Z_to_bv 5 k) sd_clobx -> getr r2 (Z_to_bv 5 k) = getr R (Z_to_bv 5 k)).
      { intros k N1 N2 N3. rewrite (AG2 _ N1), (AGm _ N2), (AG1 _ N1). exact (AGp _ N3). }
      assert (GS : forall k, In k [8; 9; 18; 19; 20; 21; 22; 23; 24; 25] -> getr r2 (Z_to_bv 5 k) = getr R (Z_to_bv 5 k)).
      { intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [assumption|]). destruct Hk. }
      repeat (destruct Hz as [<-|Hz]; [first [apply GS; (lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); solve [repeat (first [left; reflexivity | right])] | apply KEEP; [(lazymatch goal with |- ?G => let G' := eval unfold put_clob in G in change_no_check G' end); nin5 | (lazymatch goal with |- ?G => let G' := eval unfold mo_clob in G in change_no_check G' end); nin5 | (lazymatch goal with |- ?G => let G' := eval unfold sd_clobx in G in change_no_check G' end); nin5]]|]).
      destruct Hz. }
    split; [exact C10|]. split; [clear - NN0 NROOM; lia|].
    split.
    { apply (same_except_vm_trans mdl mdlm mdl5); [exact (same_but_materialized_except_vm mdl mdlm SBM0m)|].
      apply (same_except_vm_trans mdlm (mmap_model a szW mdlm) mdl5); [apply sev_mmap_model|].
      apply (same_except_vm_trans _ mdl4 mdl5); [exact (same_but_materialized_except_vm _ _ SBM4) | exact (same_but_materialized_except_vm _ _ SBM5)]. }
    split; [intros x _; left; (lazymatch goal with |- ?G => let G' := eval unfold lzb in G in change_no_check G' end); rewrite Elz5, L3; reflexivity|].
    split; [rewrite Ehl5; exact HL4 | exact (model_ivs_wf_sbm mdl4 mdl5 SBM5 L11)].
  Qed.
End TOPN1B.
