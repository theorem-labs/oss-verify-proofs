(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
Require Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtUnwindT OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRc4R OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRc4b OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRc4c OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8e OSSVerify.glaze.binary_reflection.images.AsanUbsan OSSVerify.Proofs.glaze.binary_reflection.lib.AmLia.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module BoAllocFRc4Ra.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.MemSplit.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtUnwindT OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRc4R.BoAllocFMem OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRc4R.BoAllocFRc4a OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRc4b OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRc4c OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRc4R.BoAllocFRc4U OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8e OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRc4R.
Import OSSVerify.glaze.binary_reflection.images.AsanUbsan.
Import ListNotations.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AmLia.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac am_inner ::= tryif noncert_goal_has_var then (Zify.zify; xlia zchecker) else first [ solve [noncert_clear_all; Zify.zify; xlia zchecker] | Zify.zify; xlia zchecker ].
#[local] Ltac lia ::= am_lia.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation U := bv_unsigned.
#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).
#[local] Abbreviation LE4 z := (word_to_le_bytes 4 (Z_to_bv 64 z)).

Section FPGen.
Context {fx : FPState}.

Definition fr_fullA (mem : word -> option byte) (S ra0 s0v s1v s2v s3v s4v x21 x22 x23 x24 x25 x26 x27 : word) (T spb c e mx : Z) : word -> option byte :=
  let pcz := T + 208 + 80 * c in let RIz := spb + 2 ^ 37 + 128 * c in
  let M1 := fr_drn (fr_dlf mem S ra0 s0v s1v s2v s3v s4v) S pcz (mx - mx / 2) in
  fr_rta0 M1 S (Z_to_bv 64 0x4f0a0) (Z_to_bv 64 pcz) (Z_to_bv 64 (T + 208)) (Z_to_bv 64 0x10ab58) (Z_to_bv 64 c)
          (Z_to_bv 64 (spb + c * 2 ^ 32 + e)) x21 x22 x23 x24 x25 x26 x27 RIz.

(* [comment removed for export] *)
Definition fullA_cells (M : word -> option byte) (S ra0 s0v s1v s2v s3v s4v x21 x22 x23 x24 x25 x26 x27 : word) (T spb c e mx : Z) : Prop :=
  let pcz := T + 208 + 80 * c in let RIz := spb + 2 ^ 37 + 128 * c in
  rdn BSEGS M (Z_to_bv 64 RIz) 8 = Some (LE8 (Z_to_bv 64 (2 ^ 60)))
  /\ rdn BSEGS M (at_ S (-2520)) 8 = Some (LE8 (Z_to_bv 64 0x4f0a0)) /\ rdn BSEGS M (at_ S (-2528)) 8 = Some (LE8 (Z_to_bv 64 pcz))
  /\ rdn BSEGS M (at_ S (-2536)) 8 = Some (LE8 (Z_to_bv 64 (T + 208))) /\ rdn BSEGS M (at_ S (-2544)) 8 = Some (LE8 (Z_to_bv 64 0x10ab58))
  /\ rdn BSEGS M (at_ S (-2552)) 8 = Some (LE8 (Z_to_bv 64 c)) /\ rdn BSEGS M (at_ S (-2560)) 8 = Some (LE8 (Z_to_bv 64 (spb + c * 2 ^ 32 + e)))
  /\ rdn BSEGS M (at_ S (-2568)) 8 = Some (LE8 x21) /\ rdn BSEGS M (at_ S (-2576)) 8 = Some (LE8 x22) /\ rdn BSEGS M (at_ S (-2584)) 8 = Some (LE8 x23)
  /\ rdn BSEGS M (at_ S (-2592)) 8 = Some (LE8 x24) /\ rdn BSEGS M (at_ S (-2600)) 8 = Some (LE8 x25) /\ rdn BSEGS M (at_ S (-2608)) 8 = Some (LE8 x26)
  /\ rdn BSEGS M (at_ S (-2616)) 8 = Some (LE8 x27)
  /\ rdn BSEGS M (Z_to_bv 64 pcz) 4 = Some (LE4 (mx - mx / 2))
  /\ rdn BSEGS M (at_ S (-2480)) 8 = Some (LE8 (Z_to_bv 64 0)) /\ rdn BSEGS M (at_ S (-2472)) 8 = Some (LE8 (Z_to_bv 64 0))
  /\ rdn BSEGS M (at_ S (-2456)) 8 = Some (LE8 (Z_to_bv 64 0x4ee58))
  /\ rdn BSEGS M (at_ S (-2408)) 8 = Some (LE8 ra0) /\ rdn BSEGS M (at_ S (-2416)) 8 = Some (LE8 s0v) /\ rdn BSEGS M (at_ S (-2424)) 8 = Some (LE8 s1v)
  /\ rdn BSEGS M (at_ S (-2432)) 8 = Some (LE8 s2v) /\ rdn BSEGS M (at_ S (-2440)) 8 = Some (LE8 s3v) /\ rdn BSEGS M (at_ S (-2448)) 8 = Some (LE8 s4v).

Section RUNFULLA.
  Variables (mem rom : word -> option byte) (r0 : bvmap 5 word).
  Variables (S ra0 s0v s1v s2v s3v s4v x21 x22 x23 x24 x25 x26 x27 : word) (T spb c e mx nf mfa pgp : Z) (ks : list Z).
  Variables (b80 b88 b470 bst bcs : list byte).
  #[local] Abbreviation pc_ := (T + 208 + 80 * c).
  #[local] Abbreviation RIz := (spb + 2 ^ 37 + 128 * c).
  #[local] Abbreviation fa := (spb + c * 2 ^ 32 + 0xE0000000).
  #[local] Abbreviation stw := (v_add (Z_to_bv 64 (bytes_le_to_Z bst)) (v_sub (Z_to_bv 64 0) (Z_to_bv 64 (bytes_le_to_Z bcs)))).
  Hypothesis H1 : getr r0 1 = ra0.
  Hypothesis H2 : getr r0 2 = at_ S (-2400).
  Hypothesis H10 : getr r0 10 = Z_to_bv 64 (T + 208).
  Hypothesis H11 : getr r0 11 = Z_to_bv 64 0x10ab58.
  Hypothesis H12 : getr r0 12 = Z_to_bv 64 c.
  Hypothesis H13 : getr r0 13 = Z_to_bv 64 (spb + c * 2 ^ 32 + e).
  Hypothesis H8 : getr r0 8 = s0v.   Hypothesis H9 : getr r0 9 = s1v.   Hypothesis H18 : getr r0 18 = s2v.
  Hypothesis H19 : getr r0 19 = s3v. Hypothesis H20 : getr r0 20 = s4v.
  Hypothesis H21 : getr r0 21 = x21. Hypothesis H22 : getr r0 22 = x22. Hypothesis H23 : getr r0 23 = x23. Hypothesis H24 : getr r0 24 = x24.
  Hypothesis H25 : getr r0 25 = x25. Hypothesis H26 : getr r0 26 = x26. Hypothesis H27 : getr r0 27 = x27.
  (* [comment removed for export] *)
  Hypothesis GS : 2 ^ 32 + 4096 <= U S /\ U S + 16 <= 2 ^ 47.
  Hypothesis GT : 4096 <= T /\ (TSIDE T /\ T + 4096 <= U S - 3584) /\ T mod 16 = 0.
  Hypothesis Gspb : 0x10007fff8000 <= spb /\ spb + 2 ^ 37 + 4096 <= U S - 3584 /\ spb mod 8 = 0.
  Hypothesis GTsp : hideW (T + 4096 <= spb \/ spb + 2 ^ 37 + 4096 <= T).
  Hypothesis Gce : 1 <= c <= 30 /\ 0 <= e < 2 ^ 32.
  Hypothesis Gmx : 2 <= mx <= 16.
  Hypothesis Gnf : 0 <= nf /\ 4 * (nf + mx / 2) <= 2 ^ 29.
  Hypothesis Gks : Z.of_nat (length ks) = mx / 2.
  Hypothesis Fks : Forall (fun k => 0 <= k < 2 ^ 31) ks.
  Hypothesis Gpgp : AIMGLO <= pgp /\ pgp + 8 <= AIMGHI.
  Hypothesis Hret : ret_ok ra0.
  Hypothesis L80 : length b80 = 8%nat.  Hypothesis L88 : length b88 = 8%nat.  Hypothesis L470 : length b470 = 8%nat.
  Hypothesis Lst : length bst = 8%nat.  Hypothesis Lcs : length bcs = 8%nat.
  (* [comment removed for export] *)
  Hypothesis Hstk : store_ok BSEGS mem (at_ S (-2720)) 320 = true.
  Hypothesis OkT : store_ok BSEGS mem (Z_to_bv 64 T) (Z.to_nat 4096) = true.
  Hypothesis OkRI : store_ok BSEGS mem (Z_to_bv 64 RIz) 128 = true.
  Hypothesis Okfa : store_ok BSEGS mem (Z_to_bv 64 (fa + 4 * nf)) (4 * length ks) = true.
  (* [comment removed for export] *)
  Hypothesis C_mx : rdn BSEGS mem (Z_to_bv 64 (pc_ + 4)) 4 = Some (LE4 mx).
  Hypothesis C_cnt : rdn BSEGS mem (Z_to_bv 64 pc_) 4 = Some (LE4 mx).
  Hypothesis C_cs : rdn BSEGS mem (Z_to_bv 64 (pc_ + 8)) 8 = Some bcs.
  Hypothesis C_st : rdn BSEGS mem (Z_to_bv 64 (T + 2784)) 8 = Some bst.
  Hypothesis C_src : forall i k, nth_error ks i = Some k -> rdn BSEGS mem (Z_to_bv 64 (pc_ + 16 + 4 * (mx - mx / 2) + 4 * Z.of_nat i)) 4 = Some (LE4 k).
  Hypothesis C_spb : rdn BSEGS mem (Z_to_bv 64 (0x10ab58 + 32)) 8 = Some (LE8 (Z_to_bv 64 spb)).
  Hypothesis C_rib : rdn BSEGS mem (Z_to_bv 64 (0x10ab58 + 48)) 8 = Some (LE8 (Z_to_bv 64 (spb + 2 ^ 37))).
  Hypothesis C_int : rdn BSEGS mem (Z_to_bv 64 (0x10ab58 + 40)) 4 = Some (LE4 0xffffffff).
  Hypothesis C_gpg : rdn BSEGS mem (Z_to_bv 64 0x105ef8) 8 = Some (LE8 (Z_to_bv 64 pgp)).
  Hypothesis C_pg : rdn BSEGS mem (Z_to_bv 64 pgp) 8 = Some (LE8 (Z_to_bv 64 4096)).
  Hypothesis C_470 : rdn BSEGS mem (Z_to_bv 64 0x10468) 8 = Some b470.
  Hypothesis C_mu : rdn BSEGS mem (Z_to_bv 64 RIz) 8 = Some (LE8 (Z_to_bv 64 0)).
  Hypothesis C_nf : rdn BSEGS mem (Z_to_bv 64 (RIz + 16)) 8 = Some (LE8 (Z_to_bv 64 nf)).
  Hypothesis C_mfa : rdn BSEGS mem (Z_to_bv 64 (RIz + 24)) 8 = Some (LE8 (Z_to_bv 64 mfa)).
  Hypothesis C_80 : rdn BSEGS mem (Z_to_bv 64 (RIz + 80)) 8 = Some b80.
  Hypothesis C_88 : rdn BSEGS mem (Z_to_bv 64 (RIz + 88)) 8 = Some b88.

  Ltac grows_tac := repeat (eapply mem_grows_trans; [|apply wbytes_grows]); apply mem_grows_refl.
  Ltac xq Q H :=
    eapply rd_same; [ intros x Hx; apply Q; revert Hx; (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); unorm; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); intros Hx; lia
                    | (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); first [ solve [ wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); wd_zofnat; lia ] | unorm; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); lia ] | exact H ].
  Ltac rch := repeat (first [ reflexivity | assumption
                            | match goal with |- getr ?r ?n = _ => match goal with H : getr r n = _ |- _ => rewrite H end end ]).

  Definition fullA_regs (r : bvmap 5 word) : Prop :=
      getr r 1 = Z_to_bv 64 0x4f344 /\ getr r 2 = at_ S (-2640) /\ getr r 10 = Z_to_bv 64 0x10ab58 /\ getr r 11 = Z_to_bv 64 RIz
      /\ getr r 12 = Z_to_bv 64 (spb + c * 2 ^ 32) /\ getr r 13 = Z_to_bv 64 (nf + mx / 2)
      /\ getr r 8 = Z_to_bv 64 RIz /\ getr r 9 = Z_to_bv 64 nf /\ getr r 18 = Z_to_bv 64 c /\ getr r 19 = at_ S (-2504) /\ getr r 20 = Z_to_bv 64 0x10ab58
      /\ getr r 21 = Z_to_bv 64 (mx / 2) /\ getr r 22 = Z_to_bv 64 (pc_ + 16 + 4 * (mx - mx / 2)) /\ getr r 23 = Z_to_bv 64 (nf + mx / 2)
      /\ getr r 24 = Z_to_bv 64 (2 ^ 61) /\ getr r 25 = Z_to_bv 64 fa /\ getr r 3 = getr r0 3 /\ getr r 4 = getr r0 4.

  #[local] Abbreviation MA := (fr_fullA mem S ra0 s0v s1v s2v s3v s4v x21 x22 x23 x24 x25 x26 x27 T spb c e mx).

  Theorem run_dfull_A :
    exists r, msteps BSEGS (mkst r0 (0x4eca8%bv : word) mem rom) (mkst r (0x4f508%bv : word) MA rom)
      /\ fullA_regs r
      /\ fullA_cells MA S ra0 s0v s1v s2v s3v s4v x21 x22 x23 x24 x25 x26 x27 T spb c e mx
      /\ mem_grows mem MA
      /\ (forall x : word, (U x < U S - 2640 \/ U S - 2400 <= U x) -> (U x < pc_ \/ pc_ + 4 <= U x) -> (U x < RIz \/ RIz + 8 <= U x) -> MA x = mem x).
  Proof using C_nf C_mu C_rib C_spb C_cnt C_mx OkRI OkT Hstk Lcs Lst L470 L88 L80 Gnf Gmx Gce GTsp Gspb GT GS H27 H26 H25 H24 H23 H22 H21 H20 H19 H18 H9 H8 H13 H12 H11 H10 H2 H1 bcs bst b470 b88 b80 ks.
    pose proof (u64_range S) as HSr.
    destruct GS as (GS1 & GS2). destruct Gspb as (Gs1 & Gs2 & Gs8). destruct Gce as (Hc & He). destruct GT as (GT1 & (GTS & GT2) & GT16).
    destruct Gnf as (Gnf0 & Gnf1).
    assert (DF : 1 <= mx / 2 <= 8 /\ mx - mx / 2 >= 1) by (clear - Gmx; Z.div_mod_to_equations; lia). destruct DF as (DF1 & DF2).
    assert (GTU : (T + 4096 <= AIMGLO \/ AIMGHI <= T) /\ (T + 4096 <= spb \/ spb + 2 ^ 37 + 4096 <= T)).
    { unfold hideW in GTS, GTsp. split; [exact (proj1 GTS) | exact GTsp]. }
    hidehypW GTU.
    assert (GSs : 2 ^ 24 <= U S /\ U S + 16 <= 2 ^ 47) by lia.
    assert (GTk : 4096 <= T /\ (TSIDE T /\ T + 4096 <= U S - 3584) /\ T mod 16 = 0) by (split; [exact GT1 | split; [split; [exact GTS | exact GT2] | exact GT16]]).
    assert (FAB : fa + 4 * nf + 4 * (mx / 2) <= spb + 2 ^ 37 /\ spb + 2 ^ 32 <= fa).
    { assert (c * 2 ^ 32 + 2 ^ 32 <= 2 ^ 37) by (replace (2 ^ 37) with (32 * 2 ^ 32) by reflexivity; nia). assert (2 ^ 32 <= c * 2 ^ 32) by nia. lia. }
    destruct FAB as (FAB1 & FAB2).
    assert (RIB : spb + 2 ^ 37 <= RIz /\ RIz + 128 <= spb + 2 ^ 37 + 4096 /\ RIz mod 8 = 0).
    { split; [lia|]. split; [lia|]. clear - Gs8. Z.div_mod_to_equations. lia. }
    destruct RIB as (RIB1 & RIB2 & RIB8).
    (* [comment removed for export] *)
    destruct (dlf_drn_head mem rom S ra0 s0v s1v s2v s3v s4v T c (spb + c * 2 ^ 32 + e) mx r0 H1 H2 H10 H11 H12 H13 H8 H9 H18 H19 H20 GSs GTk Hc Gmx
                ltac:(eapply (store_ok_sub BSEGS mem (at_ S (-2720)) _ 320); [rewrite at_u; lia | exact Hstk | rewrite !at_u; lia | rewrite !at_u; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia])
                OkT C_mx C_cnt)
      as (r1 & RUN1 & A1 & A2 & A10 & A11 & A13 & A14 & A15 & A8 & A9 & A18 & A19 & A20 & A3 & A4 & A21 & A22 & A23 & A24 & A25 & A26 & A27).
    assert (GR1 : mem_grows mem (fr_drn (fr_dlf mem S ra0 s0v s1v s2v s3v s4v) S pc_ (mx - mx / 2))).
    { eapply mem_grows_trans; [apply fr_dlf_grows | apply fr_drn_grows]. }
    assert (Q1 : forall x : word, (U x < U S - 2512 \/ U S - 2400 <= U x) -> (U x < pc_ \/ pc_ + 4 <= U x) ->
                 fr_drn (fr_dlf mem S ra0 s0v s1v s2v s3v s4v) S pc_ (mx - mx / 2) x = mem x).
    { intros x X1 X2. rewrite (fr_drn_outside _ S GSs pc_ (mx - mx / 2) ltac:(lia) x ltac:(lia) X2). apply (fr_dlf_outside mem S GSs). lia. }
    pose proof (fr_drn_cnt (fr_dlf mem S ra0 s0v s1v s2v s3v s4v) S GSs pc_ (mx - mx / 2) ltac:(lia)) as K1cnt.
    pose proof (fr_drn_b0 (fr_dlf mem S ra0 s0v s1v s2v s3v s4v) S GSs pc_ (mx - mx / 2) ltac:(lia)) as K1b0.
    pose proof (fr_drn_b1 (fr_dlf mem S ra0 s0v s1v s2v s3v s4v) S GSs pc_ (mx - mx / 2) ltac:(lia)) as K1b1.
    pose proof (fr_drn_ra (fr_dlf mem S ra0 s0v s1v s2v s3v s4v) S GSs pc_ (mx - mx / 2) ltac:(lia)) as K1ra.
    assert (K1f : forall k v, (k = -2408 \/ k = -2416 \/ k = -2424 \/ k = -2432 \/ k = -2440 \/ k = -2448) ->
               rdn BSEGS (fr_dlf mem S ra0 s0v s1v s2v s3v s4v) (at_ S k) 8 = Some (LE8 v) ->
               rdn BSEGS (fr_drn (fr_dlf mem S ra0 s0v s1v s2v s3v s4v) S pc_ (mx - mx / 2)) (at_ S k) 8 = Some (LE8 v)).
    { intros k v Hk Hv. eapply rd_same; [| | exact Hv].
      - intros x Hx. apply (fr_drn_outside _ S GSs pc_ (mx - mx / 2) ltac:(lia)); revert Hx; rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); intros Hx; lia.
      - rewrite at_u by lia. (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end). lia. }
    pose proof (K1f (-2408) _ ltac:(lia) (fr_dlf_ra mem S GSs ra0 s0v s1v s2v s3v s4v)) as K1c0.
    pose proof (K1f (-2416) _ ltac:(lia) (fr_dlf_s0 mem S GSs ra0 s0v s1v s2v s3v s4v)) as K1c1.
    pose proof (K1f (-2424) _ ltac:(lia) (fr_dlf_s1 mem S GSs ra0 s0v s1v s2v s3v s4v)) as K1c2.
    pose proof (K1f (-2432) _ ltac:(lia) (fr_dlf_s2 mem S GSs ra0 s0v s1v s2v s3v s4v)) as K1c3.
    pose proof (K1f (-2440) _ ltac:(lia) (fr_dlf_s3 mem S GSs ra0 s0v s1v s2v s3v s4v)) as K1c4.
    pose proof (K1f (-2448) _ ltac:(lia) (fr_dlf_s4 mem S GSs ra0 s0v s1v s2v s3v s4v)) as K1c5.
    clear K1f.
    remember (fr_drn (fr_dlf mem S ra0 s0v s1v s2v s3v s4v) S pc_ (mx - mx / 2)) as M1 eqn:EM1 in RUN1, GR1, Q1, K1cnt, K1b0, K1b1, K1ra, K1c0, K1c1, K1c2, K1c3, K1c4, K1c5.
    idtac "PROGRESS 4R: stage 1".
    Ltac sokstk M GR := eapply (store_ok_sub BSEGS M (at_ S (-2720)) _ 320); [rewrite at_u; lia | eapply store_ok_mono; [exact GR | exact Hstk] | rewrite !at_u; lia | rewrite !at_u; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia].
    Ltac xqh TS Q H := unfold hideW in TS; xq Q H.
    (* [comment removed for export] *)
    assert (HribP : AIMGHI <= spb + 2 ^ 37 /\ spb + 2 ^ 37 + 4096 <= U S - 3584 /\ (spb + 2 ^ 37) mod 8 = 0).
    { split; [lia|]. split; [lia|]. clear - Gs8. Z.div_mod_to_equations. lia. }
    destruct (rta_lock M1 rom S (Z_to_bv 64 0x4f0a0) (Z_to_bv 64 pc_) (Z_to_bv 64 (T + 208)) (Z_to_bv 64 0x10ab58) (Z_to_bv 64 c)
                (Z_to_bv 64 (spb + c * 2 ^ 32 + e)) x21 x22 x23 x24 x25 x26 x27 (at_ S (-2504)) spb (spb + 2 ^ 37) c
                (pc_ + 16 + 4 * (mx - mx / 2)) (mx / 2) nf r1
                A1 A2 A10 A11 A13 A14 A15 A8 A9 A18 A19 A20
                ltac:(rewrite A21; exact H21) ltac:(rewrite A22; exact H22) ltac:(rewrite A23; exact H23) ltac:(rewrite A24; exact H24)
                ltac:(rewrite A25; exact H25) ltac:(rewrite A26; exact H26) ltac:(rewrite A27; exact H27)
                GSs Hc ltac:(lia) HribP ltac:(lia) ltac:(lia)
                ltac:(sokstk M1 GR1)
                ltac:(eapply (store_ok_sub BSEGS M1 (Z_to_bv 64 RIz) _ 128); [wd_ulia | eapply store_ok_mono; [exact GR1 | exact OkRI] | wd_ulia | wd_ulia_c])
                ltac:(xqh GTU Q1 C_spb) ltac:(xqh GTU Q1 C_rib) ltac:(xqh GTU Q1 C_mu) ltac:(xqh GTU Q1 C_nf))
      as (r2 & RUN2 & RR & B1 & B10 & B11 & B12 & B13 & B9 & B23).
    destruct RR as (B2 & B8 & B18 & B19 & B20 & B21 & B22 & B24 & B25 & B3 & B4).
    match type of RUN2 with msteps _ _ (mkst _ _ ?mf _) => remember mf as M2 eqn:EM2 end.
    assert (GR2 : mem_grows mem M2) by (rewrite EM2; eapply mem_grows_trans; [exact GR1 | apply fr_rta0_grows]).
    assert (QC2 : forall x : word, (U x < U S - 2640 \/ U S - 2512 <= U x) -> (U x < RIz \/ RIz + 8 <= U x) -> M2 x = M1 x).
    { intros x X1 X2. rewrite EM2. apply fr_rta0_outside; [exact GSs | lia | exact X1 | exact X2]. }
    assert (QM2 : forall x : word, (U x < U S - 2640 \/ U S - 2400 <= U x) -> (U x < pc_ \/ pc_ + 4 <= U x) -> (U x < RIz \/ RIz + 8 <= U x) -> M2 x = mem x).
    { intros x X1 X2 X3. rewrite QC2 by lia. apply Q1; lia. }
    assert (K2mu : rdn BSEGS M2 (Z_to_bv 64 RIz) 8 = Some (LE8 (Z_to_bv 64 (2 ^ 60)))) by (rewrite EM2; apply fr_rta0_mu; [exact GSs | lia]).
    assert (K2ra : rdn BSEGS M2 (at_ S (-2520)) 8 = Some (LE8 (Z_to_bv 64 0x4f0a0))) by (rewrite EM2; apply fr_rta0_ra; [exact GSs | lia]).
    assert (K2s0 : rdn BSEGS M2 (at_ S (-2528)) 8 = Some (LE8 (Z_to_bv 64 pc_))) by (rewrite EM2; apply fr_rta0_s0; [exact GSs | lia]).
    assert (K2s1 : rdn BSEGS M2 (at_ S (-2536)) 8 = Some (LE8 (Z_to_bv 64 (T + 208)))) by (rewrite EM2; apply fr_rta0_s1; [exact GSs | lia]).
    assert (K2s2 : rdn BSEGS M2 (at_ S (-2544)) 8 = Some (LE8 (Z_to_bv 64 0x10ab58))) by (rewrite EM2; apply fr_rta0_s2; [exact GSs | lia]).
    assert (K2s3 : rdn BSEGS M2 (at_ S (-2552)) 8 = Some (LE8 (Z_to_bv 64 c))) by (rewrite EM2; apply fr_rta0_s3; [exact GSs | lia]).
    assert (K2s4 : rdn BSEGS M2 (at_ S (-2560)) 8 = Some (LE8 (Z_to_bv 64 (spb + c * 2 ^ 32 + e)))) by (rewrite EM2; apply fr_rta0_s4; [exact GSs | lia]).
    assert (K2s5 : rdn BSEGS M2 (at_ S (-2568)) 8 = Some (LE8 x21)) by (rewrite EM2; apply fr_rta0_s5; [exact GSs | lia]).
    assert (K2s6 : rdn BSEGS M2 (at_ S (-2576)) 8 = Some (LE8 x22)) by (rewrite EM2; apply fr_rta0_s6; [exact GSs | lia]).
    assert (K2s7 : rdn BSEGS M2 (at_ S (-2584)) 8 = Some (LE8 x23)) by (rewrite EM2; apply fr_rta0_s7; [exact GSs | lia]).
    assert (K2s8 : rdn BSEGS M2 (at_ S (-2592)) 8 = Some (LE8 x24)) by (rewrite EM2; apply fr_rta0_s8; [exact GSs | lia]).
    assert (K2s9 : rdn BSEGS M2 (at_ S (-2600)) 8 = Some (LE8 x25)) by (rewrite EM2; apply fr_rta0_s9; [exact GSs | lia]).
    assert (K2s10 : rdn BSEGS M2 (at_ S (-2608)) 8 = Some (LE8 x26)) by (rewrite EM2; apply fr_rta0_s10; [exact GSs | lia]).
    assert (K2s11 : rdn BSEGS M2 (at_ S (-2616)) 8 = Some (LE8 x27)) by (rewrite EM2; apply fr_rta0_s11; [exact GSs | lia]).
    assert (TR : forall k v, -2512 <= k -> k + 8 <= -2400 -> rdn BSEGS M1 (at_ S k) 8 = Some v -> rdn BSEGS M2 (at_ S k) 8 = Some v).
    { intros k v Hk1 Hk2 Hv. eapply rd_same; [| | exact Hv].
      - intros x Hx. apply QC2; revert Hx; rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); intros Hx; unfold hideW in GTU; lia.
      - rewrite at_u by lia. (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end). lia. }
    assert (K2cnt : rdn BSEGS M2 (Z_to_bv 64 pc_) 4 = Some (LE4 (mx - mx / 2))) by (xqh GTU QC2 K1cnt).
    exists r2. split.
    { subst M2 M1. (lazymatch goal with |- ?G => let G' := eval unfold fr_fullA in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbv zeta in G in change_no_check G' end). eapply msteps_trans; [exact RUN1 | exact RUN2]. }
    split.
    { (lazymatch goal with |- ?G => let G' := eval unfold fullA_regs in G in change_no_check G' end). repeat match goal with |- _ /\ _ => split end; try assumption; rch. }
    split.
    { (lazymatch goal with |- ?G => let G' := eval unfold fullA_cells in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbv zeta in G in change_no_check G' end). replace MA with M2 by (subst M2 M1; reflexivity).
      repeat match goal with |- _ /\ _ => split end; try assumption; apply TR; try assumption; lia. }
    split; [replace MA with M2 by (subst M2 M1; reflexivity); exact GR2|].
    replace MA with M2 by (subst M2 M1; reflexivity). exact QM2.
  Qed.
End RUNFULLA.

(* [comment removed for export] *)
Lemma fullA_cells_same : forall (M M' : word -> option byte) (S ra0 s0v s1v s2v s3v s4v x21 x22 x23 x24 x25 x26 x27 : word) (T spb c e mx : Z),
  2 ^ 24 <= U S /\ U S + 16 <= 2 ^ 47 -> 0 <= T + 208 + 80 * c /\ T + 208 + 80 * c + 4 < 2 ^ 63 -> 0 <= spb + 2 ^ 37 + 128 * c /\ spb + 2 ^ 37 + 128 * c + 8 < 2 ^ 63 ->
  (forall x : word, (U S - 2640 <= U x < U S - 2400) \/ (T + 208 + 80 * c <= U x < T + 208 + 80 * c + 4)
                    \/ (spb + 2 ^ 37 + 128 * c <= U x < spb + 2 ^ 37 + 128 * c + 8) -> M' x = M x) ->
  fullA_cells M S ra0 s0v s1v s2v s3v s4v x21 x22 x23 x24 x25 x26 x27 T spb c e mx ->
  fullA_cells M' S ra0 s0v s1v s2v s3v s4v x21 x22 x23 x24 x25 x26 x27 T spb c e mx.
Proof using.
  intros M M' S ra0 s0v s1v s2v s3v s4v x21 x22 x23 x24 x25 x26 x27 T spb c e mx GS GP GR SAME H.
  pose proof (u64_range S) as HSr. unfold fullA_cells in *. cbv zeta in *.
  repeat match type of H with _ /\ _ => let H1 := fresh "C" in destruct H as [H1 H] end.
  repeat match goal with |- _ /\ _ => split end;
    (eapply rd_same; [ intros x Hx; apply SAME; revert Hx; rewrite ?at_u by lia; unorm; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); intros Hx; lia
                     | rewrite ?at_u by lia; first [ solve [ wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); wd_zofnat; lia ] | unorm; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); lia ] | eassumption ]).
Qed.
End FPGen.
End BoAllocFRc4Ra.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.MemSplit.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtUnwindT OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRc4R OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRc4b OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRc4c OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8e. Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtUnwindT OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRc4R.BoAllocFMem OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRc4R.BoAllocFRc4a OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRc4b OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRc4c OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRc4R.BoAllocFRc4U OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8e OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRc4R BoAllocFRc4Ra.
From OSSVerify.glaze.binary_reflection.images Require Import AsanUbsan.
Import ListNotations.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Import HsAtom.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac ha_prev := tryif noncert_goal_has_var then (Zify.zify; (xlia zchecker)) else (first [ solve [ noncert_clear_all; Zify.zify; (xlia zchecker) ] | Zify.zify; (xlia zchecker) ]).
#[local] Ltac lia ::= first [ solve [ ha_tiers ltac:(ha_lia0) ] | ha_prev ].   (* [comment removed for export] *)
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation U := bv_unsigned.
#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).
#[local] Abbreviation LE4 z := (word_to_le_bytes 4 (Z_to_bv 64 z)).

Section FPGen.
Context {fx : FPState}.

Definition fr_fullC (mem : word -> option byte) (S : word) (T spb c e mx nf : Z) (ks : list Z) (b80 : list byte) (w9 w22 stw : word) : word -> option byte :=
  let RIz := spb + 2 ^ 37 + 128 * c in let fa := spb + c * 2 ^ 32 + 0xE0000000 in
  let M4 := fa_fill mem (fa + 4 * nf) ks in
  let M5 := fr_rtac M4 RIz (nf + mx / 2) (v_add (Z_to_bv 64 (bytes_le_to_Z b80)) (Z_to_bv 64 (mx / 2))) in
  let M6 := fr_mro M5 S (Z_to_bv 64 0x4f394) (Z_to_bv 64 RIz) w9 (Z_to_bv 64 c) (at_ S (-2504)) (Z_to_bv 64 0x10ab58)
                   (Z_to_bv 64 (mx / 2)) w22 (Z_to_bv 64 (nf + mx / 2)) in
  let M7 := wbytes M6 (Z_to_bv 64 RIz) (LE8 (Z_to_bv 64 0)) in
  fr_dtl M7 S T c (mx - mx / 2) e stw.

Section RUNFULLC.
  Variables (mem rom : word -> option byte) (r3 : bvmap 5 word).
  Variables (S ra0 s0v s1v s2v s3v s4v x21 x22 x23 x24 x25 x26 x27 : word) (T spb c e mx nf mfa pgp : Z) (ks : list Z).
  Variables (b80 b88 b470 bst bcs : list byte).
  #[local] Abbreviation pc_ := (T + 208 + 80 * c).
  #[local] Abbreviation RIz := (spb + 2 ^ 37 + 128 * c).
  #[local] Abbreviation fa := (spb + c * 2 ^ 32 + 0xE0000000).
  #[local] Abbreviation stw := (v_add (Z_to_bv 64 (bytes_le_to_Z bst)) (v_sub (Z_to_bv 64 0) (Z_to_bv 64 (bytes_le_to_Z bcs)))).
  Hypothesis E10 : getr r3 10 = Z_to_bv 64 1.
  Hypothesis E2 : getr r3 2 = at_ S (-2640).
  Hypothesis E8 : getr r3 8 = Z_to_bv 64 RIz.   Hypothesis E9 : getr r3 9 = Z_to_bv 64 nf.   Hypothesis E18 : getr r3 18 = Z_to_bv 64 c.
  Hypothesis E19 : getr r3 19 = at_ S (-2504).  Hypothesis E20 : getr r3 20 = Z_to_bv 64 0x10ab58.
  Hypothesis E21 : getr r3 21 = Z_to_bv 64 (mx / 2).
  Hypothesis E22 : getr r3 22 = Z_to_bv 64 (pc_ + 16 + 4 * (mx - mx / 2)).
  Hypothesis E23 : getr r3 23 = Z_to_bv 64 (nf + mx / 2).
  Hypothesis E24 : getr r3 24 = Z_to_bv 64 (2 ^ 61).
  Hypothesis E25 : getr r3 25 = Z_to_bv 64 fa.
  (* [comment removed for export] *)
  Hypothesis GS : 2 ^ 32 + 4096 <= U S /\ U S + 16 <= 2 ^ 47.
  Hypothesis GT : 4096 <= T /\ (TSIDE T /\ T + 4096 <= U S - 3584) /\ T mod 16 = 0.
  Hypothesis Gspb : 0x10007fff8000 <= spb /\ spb + 2 ^ 37 + 4096 <= U S - 3584 /\ spb mod 8 = 0.
  Hypothesis GTsp : hideW (T + 4096 <= spb \/ spb + 2 ^ 37 + 4096 <= T).
  Hypothesis Gce : 1 <= c <= 30 /\ 0 <= e < 2 ^ 32.
  Hypothesis Gmx : 2 <= mx <= 16.
  Hypothesis Gnf : 0 <= nf /\ 4 * (nf + mx / 2) <= 2 ^ 29.
  Hypothesis Gks : Z.of_nat (length ks) = mx / 2.
  Hypothesis Fks : Forall (fun k => 0 <= k < 2 ^ 31) ks.
  Hypothesis Gpgp : AIMGLO <= pgp /\ pgp + 8 <= AIMGHI.
  Hypothesis Hret : ret_ok ra0.
  Hypothesis L80 : length b80 = 8%nat.  Hypothesis L88 : length b88 = 8%nat.  Hypothesis L470 : length b470 = 8%nat.
  Hypothesis Lst : length bst = 8%nat.  Hypothesis Lcs : length bcs = 8%nat.
  (* [comment removed for export] *)
  Hypothesis Hstk : store_ok BSEGS mem (at_ S (-2720)) 320 = true.
  Hypothesis OkT : store_ok BSEGS mem (Z_to_bv 64 T) (Z.to_nat 4096) = true.
  Hypothesis OkRI : store_ok BSEGS mem (Z_to_bv 64 RIz) 128 = true.
  Hypothesis Okfa : store_ok BSEGS mem (Z_to_bv 64 (fa + 4 * nf)) (4 * length ks) = true.
  (* [comment removed for export] *)
  Hypothesis C_mx : rdn BSEGS mem (Z_to_bv 64 (pc_ + 4)) 4 = Some (LE4 mx).
  Hypothesis C_cnt : rdn BSEGS mem (Z_to_bv 64 pc_) 4 = Some (LE4 mx).
  Hypothesis C_cs : rdn BSEGS mem (Z_to_bv 64 (pc_ + 8)) 8 = Some bcs.
  Hypothesis C_st : rdn BSEGS mem (Z_to_bv 64 (T + 2784)) 8 = Some bst.
  Hypothesis C_src : forall i k, nth_error ks i = Some k -> rdn BSEGS mem (Z_to_bv 64 (pc_ + 16 + 4 * (mx - mx / 2) + 4 * Z.of_nat i)) 4 = Some (LE4 k).
  Hypothesis C_spb : rdn BSEGS mem (Z_to_bv 64 (0x10ab58 + 32)) 8 = Some (LE8 (Z_to_bv 64 spb)).
  Hypothesis C_rib : rdn BSEGS mem (Z_to_bv 64 (0x10ab58 + 48)) 8 = Some (LE8 (Z_to_bv 64 (spb + 2 ^ 37))).
  Hypothesis C_int : rdn BSEGS mem (Z_to_bv 64 (0x10ab58 + 40)) 4 = Some (LE4 0xffffffff).
  Hypothesis C_gpg : rdn BSEGS mem (Z_to_bv 64 0x105ef8) 8 = Some (LE8 (Z_to_bv 64 pgp)).
  Hypothesis C_pg : rdn BSEGS mem (Z_to_bv 64 pgp) 8 = Some (LE8 (Z_to_bv 64 4096)).
  Hypothesis C_470 : rdn BSEGS mem (Z_to_bv 64 0x10468) 8 = Some b470.
  Hypothesis C_mu : rdn BSEGS mem (Z_to_bv 64 RIz) 8 = Some (LE8 (Z_to_bv 64 0)).
  Hypothesis C_nf : rdn BSEGS mem (Z_to_bv 64 (RIz + 16)) 8 = Some (LE8 (Z_to_bv 64 nf)).
  Hypothesis C_mfa : rdn BSEGS mem (Z_to_bv 64 (RIz + 24)) 8 = Some (LE8 (Z_to_bv 64 mfa)).
  Hypothesis C_80 : rdn BSEGS mem (Z_to_bv 64 (RIz + 80)) 8 = Some b80.
  Hypothesis C_88 : rdn BSEGS mem (Z_to_bv 64 (RIz + 88)) 8 = Some b88.

  Hypothesis CA : fullA_cells mem S ra0 s0v s1v s2v s3v s4v x21 x22 x23 x24 x25 x26 x27 T spb c e mx.

  Definition fullC_regs (r : bvmap 5 word) : Prop :=
      getr r 2 = at_ S (-2400) /\ getr r 8 = s0v /\ getr r 9 = s1v /\ getr r 18 = s2v /\ getr r 19 = s3v /\ getr r 20 = s4v
      /\ getr r 3 = getr r3 3 /\ getr r 4 = getr r3 4
      /\ getr r 21 = x21 /\ getr r 22 = x22 /\ getr r 23 = x23 /\ getr r 24 = x24 /\ getr r 25 = x25 /\ getr r 26 = x26 /\ getr r 27 = x27.

  Ltac grows_tac := repeat (eapply mem_grows_trans; [|apply wbytes_grows]); apply mem_grows_refl.
  Ltac xq Q H :=
    eapply rd_same; [ intros x Hx; apply Q; revert Hx; (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); unorm; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); intros Hx; lia
                    | (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); first [ solve [ wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); wd_zofnat; lia ] | unorm; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); lia ] | exact H ].
  Ltac rch := repeat (first [ reflexivity | assumption
                            | match goal with |- getr ?r ?n = _ => match goal with H : getr r n = _ |- _ => rewrite H end end ]).

  Ltac sokstk M GR := eapply (store_ok_sub BSEGS M (at_ S (-2720)) _ 320); [rewrite at_u; lia | eapply store_ok_mono; [exact GR | exact Hstk] | rewrite !at_u; lia | rewrite !at_u; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia].
  Ltac xqh TS Q H := unfold hideW in TS; xq Q H.

  Theorem run_dfull_C :
    exists r w9 w22, msteps BSEGS (mkst r3 (0x4f344%bv : word) mem rom)
        (mkst r ra0 (fr_fullC mem S T spb c e mx nf ks b80 w9 w22 stw) rom)
      /\ fullC_regs r.
  Proof using CA C_88 C_80 C_470 C_pg C_gpg C_int C_rib C_spb C_src C_st C_cs Okfa OkRI OkT Hstk Lcs Lst L470 L88 L80 Hret Gpgp Fks Gks Gnf Gmx Gce GTsp Gspb GT GS E25 E24 E23 E22 E21 E20 E19 E18 E9 E8 E2 E10 b470 b88 pgp.
    (lazymatch goal with |- ?G => let G' := eval unfold fullC_regs in G in change_no_check G' end).
    pose proof (u64_range S) as HSr.
    destruct GS as (GS1 & GS2). destruct Gspb as (Gs1 & Gs2 & Gs8). destruct Gce as (Hc & He). destruct GT as (GT1 & (GTS & GT2) & GT16).
    destruct Gnf as (Gnf0 & Gnf1).
    assert (DF : 1 <= mx / 2 <= 8 /\ mx - mx / 2 >= 1) by (clear - Gmx; Z.div_mod_to_equations; lia). destruct DF as (DF1 & DF2).
    assert (GTU : (T + 4096 <= AIMGLO \/ AIMGHI <= T) /\ (T + 4096 <= spb \/ spb + 2 ^ 37 + 4096 <= T)).
    { unfold hideW in GTS, GTsp. split; [exact (proj1 GTS) | exact GTsp]. }
    hidehypW GTU.
    assert (GSs : 2 ^ 24 <= U S /\ U S + 16 <= 2 ^ 47) by lia.
    assert (GTk : 4096 <= T /\ (TSIDE T /\ T + 4096 <= U S - 3584) /\ T mod 16 = 0) by (split; [exact GT1 | split; [split; [exact GTS | exact GT2] | exact GT16]]).
    assert (FAB : fa + 4 * nf + 4 * (mx / 2) <= spb + 2 ^ 37 /\ spb + 2 ^ 32 <= fa).
    { assert (c * 2 ^ 32 + 2 ^ 32 <= 2 ^ 37) by (replace (2 ^ 37) with (32 * 2 ^ 32) by reflexivity; nia). assert (2 ^ 32 <= c * 2 ^ 32) by nia. lia. }
    destruct FAB as (FAB1 & FAB2).
    assert (RIB : spb + 2 ^ 37 <= RIz /\ RIz + 128 <= spb + 2 ^ 37 + 4096 /\ RIz mod 8 = 0).
    { split; [lia|]. split; [lia|]. clear - Gs8. Z.div_mod_to_equations. lia. }
    destruct RIB as (RIB1 & RIB2 & RIB8).
    destruct CA as (K2mu & K2ra & K2s0 & K2s1 & K2s2 & K2s3 & K2s4 & K2s5 & K2s6 & K2s7 & K2s8 & K2s9 & K2s10 & K2s11
                    & K1cnt & K1b0 & K1b1 & K1ra & K1c0 & K1c1 & K1c2 & K1c3 & K1c4 & K1c5). cbv zeta in *.
    pose (M1 := mem). pose (M2 := mem). pose (M3 := mem).
    assert (GR1 : mem_grows mem M1) by apply mem_grows_refl. assert (GR2 : mem_grows mem M2) by apply mem_grows_refl. assert (GR3 : mem_grows mem M3) by apply mem_grows_refl.
    assert (QC2 : forall x : word, (U x < U S - 2640 \/ U S - 2512 <= U x) -> (U x < RIz \/ RIz + 8 <= U x) -> M2 x = M1 x) by (intros; reflexivity).
    assert (QM2 : forall x : word, (U x < U S - 2640 \/ U S - 2400 <= U x) -> (U x < pc_ \/ pc_ + 4 <= U x) -> (U x < RIz \/ RIz + 8 <= U x) -> M2 x = mem x) by (intros; reflexivity).
    assert (QB3 : forall x : word, (U x < U S - 2688 \/ U S - 2640 <= U x) -> M3 x = M2 x) by (intros; reflexivity).
    assert (QM3 : forall x : word, (U x < U S - 2688 \/ U S - 2400 <= U x) -> (U x < pc_ \/ pc_ + 4 <= U x) -> (U x < RIz \/ RIz + 8 <= U x) -> M3 x = mem x) by (intros; reflexivity).
    assert (Q1 : forall x : word, (U x < U S - 2512 \/ U S - 2400 <= U x) -> (U x < pc_ \/ pc_ + 4 <= U x) -> M1 x = mem x) by (intros; reflexivity).
    (* [comment removed for export] *)
    destruct (rta_to_copy M3 rom S (at_ S (-2504)) RIz c (pc_ + 16 + 4 * (mx - mx / 2)) (mx / 2) nf fa r3 E2 E8 E9 E18 E19 E20 E21 E22 E23 E25
                ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) E10)
      as (r4 & RUN4 & D22 & D25 & D10 & D1 & D2 & D3 & D4 & D8 & D18 & D19 & D20 & D21 & D23 & D24 & D26 & D27).
    assert (KSNE : ks <> []) by (intros E; rewrite E in Gks; cbn in Gks; lia).
    destruct (rta_copy_loop ks r4 M3 rom (pc_ + 16 + 4 * (mx - mx / 2)) (fa + 4 * nf) KSNE D22 D25 ltac:(rewrite Gks; exact D10)
                ltac:(rewrite Gks; lia) ltac:(rewrite Gks; lia) ltac:(rewrite Gks; unfold hideW in GTU; lia) Fks
                ltac:(intros i k Hik; assert (Z.of_nat i < mx / 2) by (rewrite <- Gks; apply Nat2Z.inj_lt; apply nth_error_Some; rewrite Hik; discriminate);
                      xqh GTU QM3 (C_src i k Hik))
                ltac:(eapply store_ok_mono; [exact GR3 | exact Okfa]))
      as (r5 & RUN5 & KP).
    destruct KP as (P1 & P2 & P3 & P4 & P8 & P9 & P10 & P18 & P19 & P20 & P21 & P23 & P24 & P26 & P27).
    match type of RUN5 with msteps _ _ (mkst _ _ ?mf _) => remember mf as M4 eqn:EM4 end.
    assert (GR4 : mem_grows mem M4) by (rewrite EM4; eapply mem_grows_trans; [exact GR3 | apply fa_fill_grows]).
    assert (QB4 : forall x : word, (U x < U S - 2688 \/ U S - 2640 <= U x) -> (U x < fa + 4 * nf \/ fa + 4 * nf + 4 * (mx / 2) <= U x) -> M4 x = M2 x).
    { intros x X1 X2. rewrite EM4. rewrite fa_fill_outside by (rewrite ?Gks; lia). apply QB3; exact X1. }
    assert (QM4 : forall x : word, (U x < U S - 2688 \/ U S - 2400 <= U x) -> (U x < pc_ \/ pc_ + 4 <= U x) -> (U x < RIz \/ RIz + 8 <= U x) ->
                  (U x < fa + 4 * nf \/ fa + 4 * nf + 4 * (mx / 2) <= U x) -> M4 x = mem x).
    { intros x X1 X2 X3 X4. rewrite QB4 by lia. apply QM2; lia. }
    idtac "PROGRESS 4R: stage 5".
    (* [comment removed for export] *)
    destruct (rta_counters M4 rom S (at_ S (-2504)) RIz c (mx / 2) nf b80 r5
                ltac:(rewrite P2, D2; exact E2) ltac:(rewrite P8, D8; exact E8) ltac:(rewrite P18, D18; exact E18) ltac:(rewrite P19, D19; exact E19)
                ltac:(rewrite P20, D20; exact E20) ltac:(rewrite P21, D21; exact E21) ltac:(rewrite P23, D23; exact E23)
                GSs ltac:(lia) L80 ltac:(xqh GTU QM4 C_80) ltac:(eapply store_ok_mono; [exact GR4 | exact OkRI]))
      as (r6 & RUN6 & F1 & F10 & F11 & F12 & F13 & F2 & F3 & F4 & F8 & F18 & F19 & F20 & F21 & F23 & F24 & F26 & F27).
    match type of RUN6 with msteps _ _ (mkst _ _ ?mf _) => remember mf as M5 eqn:EM5 end.
    assert (GR5 : mem_grows mem M5) by (rewrite EM5; eapply mem_grows_trans; [exact GR4 | apply fr_rtac_grows]).
    assert (QB5 : forall x : word, (U x < U S - 2688 \/ U S - 2640 <= U x) -> (U x < fa + 4 * nf \/ fa + 4 * nf + 4 * (mx / 2) <= U x) ->
                  (U x < RIz + 16 \/ RIz + 24 <= U x) -> (U x < RIz + 80 \/ RIz + 88 <= U x) -> M5 x = M2 x).
    { intros x X1 X2 X3 X4. rewrite EM5. rewrite fr_rtac_outside by lia. apply QB4; assumption. }
    assert (QM5 : forall x : word, (U x < U S - 2688 \/ U S - 2400 <= U x) -> (U x < pc_ \/ pc_ + 4 <= U x) -> (U x < RIz \/ RIz + 8 <= U x) ->
                  (U x < fa + 4 * nf \/ fa + 4 * nf + 4 * (mx / 2) <= U x) -> (U x < RIz + 16 \/ RIz + 24 <= U x) -> (U x < RIz + 80 \/ RIz + 88 <= U x) -> M5 x = mem x).
    { intros x X1 X2 X3 X4 X5 X6. rewrite QB5 by lia. apply QM2; lia. }
    assert (K5nf : rdn BSEGS M5 (Z_to_bv 64 (RIz + 16)) 8 = Some (LE8 (Z_to_bv 64 (nf + mx / 2)))) by (rewrite EM5; apply fr_rtac_nf; lia).
    assert (K5w80 : rdn BSEGS M5 (Z_to_bv 64 (RIz + 80)) 8 = Some (LE8 (v_add (Z_to_bv 64 (bytes_le_to_Z b80)) (Z_to_bv 64 (mx / 2))))) by (rewrite EM5; apply fr_rtac_w80; lia).
    idtac "PROGRESS 4R: stage 6".
    (* [comment removed for export] *)
    destruct (mro_run M5 rom S (Z_to_bv 64 0x4f394) (Z_to_bv 64 RIz) (getr r6 9) (Z_to_bv 64 c) (at_ S (-2504)) (Z_to_bv 64 0x10ab58)
                (Z_to_bv 64 (mx / 2)) (getr r6 22) (Z_to_bv 64 (nf + mx / 2)) (at_ S (-2504)) (spb + 2 ^ 37) c (nf + mx / 2) pgp
                (LE8 (v_add (Z_to_bv 64 (bytes_le_to_Z b80)) (Z_to_bv 64 (mx / 2)))) b88 r6
                F1 ltac:(rewrite F2, P2, D2; exact E2) F10 F11 F12 F13 ltac:(rewrite F8, P8, D8; exact E8) eq_refl
                ltac:(rewrite F18, P18, D18; exact E18) ltac:(rewrite F19, P19, D19; exact E19) ltac:(rewrite F20, P20, D20; exact E20)
                ltac:(rewrite F21, P21, D21; exact E21) eq_refl ltac:(rewrite F23, P23, D23; exact E23)
                GSs Hc ltac:(lia) ltac:(lia) (length_N_to_le_bytes 8 _) L88 Gpgp ltac:(apply ret_ok_lit; [lia | reflexivity])
                ltac:(sokstk M5 GR5)
                ltac:(xqh GTU QM5 C_rib) ltac:(xqh GTU QM5 C_gpg) ltac:(xqh GTU QM5 C_pg) K5nf K5w80 ltac:(xqh GTU QM5 C_88) ltac:(xqh GTU QM5 C_int))
      as (r7 & RUN7 & MP).
    destruct MP as (J2 & J8 & J9 & J18 & J19 & J20 & J21 & J22 & J23 & J3 & J4 & J24 & J25 & J26 & J27).
    match type of RUN7 with msteps _ _ (mkst _ _ ?mf _) => remember mf as M6 eqn:EM6 end.
    assert (GR6 : mem_grows mem M6) by (rewrite EM6; eapply mem_grows_trans; [exact GR5 | apply fr_mro_grows]).
    assert (QB6 : forall x : word, (U x < U S - 2720 \/ U S - 2640 <= U x) -> (U x < fa + 4 * nf \/ fa + 4 * nf + 4 * (mx / 2) <= U x) ->
                  (U x < RIz + 16 \/ RIz + 24 <= U x) -> (U x < RIz + 80 \/ RIz + 88 <= U x) -> M6 x = M2 x).
    { intros x X1 X2 X3 X4. rewrite EM6. rewrite (fr_mro_outside M5 S GSs) by lia. apply QB5; [lia | assumption | assumption | assumption]. }
    assert (QM6 : forall x : word, (U x < U S - 2720 \/ U S - 2400 <= U x) -> (U x < pc_ \/ pc_ + 4 <= U x) -> (U x < RIz \/ RIz + 8 <= U x) ->
                  (U x < fa + 4 * nf \/ fa + 4 * nf + 4 * (mx / 2) <= U x) -> (U x < RIz + 16 \/ RIz + 24 <= U x) -> (U x < RIz + 80 \/ RIz + 88 <= U x) -> M6 x = mem x).
    { intros x X1 X2 X3 X4 X5 X6. rewrite QB6 by lia. apply QM2; lia. }
    idtac "PROGRESS 4R: stage 7".
    (* [comment removed for export] *)
    destruct (rta_unlock M6 rom S (Z_to_bv 64 0x4f0a0) (Z_to_bv 64 pc_) (Z_to_bv 64 (T + 208)) (Z_to_bv 64 0x10ab58) (Z_to_bv 64 c)
                (Z_to_bv 64 (spb + c * 2 ^ 32 + e)) x21 x22 x23 x24 x25 x26 x27 RIz b470 r7
                J2 J8 ltac:(rewrite J24, F24, P24, D24; exact E24) GSs ltac:(lia) ltac:(apply ret_ok_lit; [lia | reflexivity]) L470
                ltac:(eapply (store_ok_sub BSEGS M6 (Z_to_bv 64 RIz) _ 128); [wd_ulia | eapply store_ok_mono; [exact GR6 | exact OkRI] | wd_ulia | wd_ulia_c])
                ltac:(xq QB6 K2mu) ltac:(xqh GTU QM6 C_470)
                ltac:(xq QB6 K2ra) ltac:(xq QB6 K2s0) ltac:(xq QB6 K2s1) ltac:(xq QB6 K2s2) ltac:(xq QB6 K2s3) ltac:(xq QB6 K2s4) ltac:(xq QB6 K2s5)
                ltac:(xq QB6 K2s6) ltac:(xq QB6 K2s7) ltac:(xq QB6 K2s8) ltac:(xq QB6 K2s9) ltac:(xq QB6 K2s10) ltac:(xq QB6 K2s11))
      as (r8 & RUN8 & L2 & L8 & L9 & L18 & L19 & L20 & L21 & L22 & L23 & L24 & L25 & L26 & L27 & L3 & L4).
    match type of RUN8 with msteps _ _ (mkst _ _ ?mf _) => remember mf as M7 eqn:EM7 end.
    assert (GR7 : mem_grows mem M7) by (rewrite EM7; eapply mem_grows_trans; [exact GR6 | apply wbytes_grows]).
    assert (QC7 : forall x : word, (U x < U S - 2720 \/ U S - 2512 <= U x) -> (U x < RIz \/ RIz + 128 <= U x) ->
                  (U x < fa + 4 * nf \/ fa + 4 * nf + 4 * (mx / 2) <= U x) -> M7 x = M1 x).
    { intros x X1 X2 X3. rewrite EM7. rewrite wbytes_outside by (rewrite length_N_to_le_bytes; wd_ulia). rewrite QB6 by lia. apply QC2; lia. }
    assert (QM7 : forall x : word, (U x < U S - 2720 \/ U S - 2400 <= U x) -> (U x < pc_ \/ pc_ + 4 <= U x) -> (U x < RIz \/ RIz + 128 <= U x) ->
                  (U x < fa + 4 * nf \/ fa + 4 * nf + 4 * (mx / 2) <= U x) -> M7 x = mem x).
    { intros x X1 X2 X3 X4. rewrite QC7 by lia. apply Q1; lia. }
    idtac "PROGRESS 4R: stage 8".
    (* [comment removed for export] *)
    destruct (drn_dlf_tail M7 rom S ra0 s0v s1v s2v s3v s4v T spb c e (mx - mx / 2) bst bcs r8 L2 L8 L9 L18 L19 L20 GSs GTk ltac:(lia) Hc He ltac:(lia) Hret Lst Lcs
                ltac:(sokstk M7 GR7) ltac:(eapply store_ok_mono; [exact GR7 | exact OkT])
                ltac:(xq QC7 K1b0) ltac:(xq QC7 K1b1) ltac:(xq QC7 K1ra)
                ltac:(xq QC7 K1c0) ltac:(xq QC7 K1c1) ltac:(xq QC7 K1c2) ltac:(xq QC7 K1c3) ltac:(xq QC7 K1c4) ltac:(xq QC7 K1c5)
                ltac:(xqh GTU QC7 K1cnt) ltac:(xqh GTU QM7 C_cs) ltac:(xqh GTU QM7 C_st) ltac:(xqh GTU QM7 C_spb))
      as (r9 & RUN9 & N2 & N8 & N9 & N18 & N19 & N20 & N3 & N4 & N21 & N22 & N23 & N24 & N25 & N26 & N27).
    idtac "PROGRESS 4R: stage 9".
    (* [comment removed for export] *)
    exists r9, (getr r6 9), (getr r6 22). split.
    { replace (Z_to_bv 64 0x4f394 : word) with (0x4f394%bv : word) in RUN7 by (apply bv_eq; reflexivity).
      replace (Z_to_bv 64 0x4f0a0 : word) with (0x4f0a0%bv : word) in RUN8 by (apply bv_eq; reflexivity).
      subst M7 M6 M5 M4 M3 M2 M1. (lazymatch goal with |- ?G => let G' := eval unfold fr_fullC in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbv zeta in G in change_no_check G' end).
      eapply msteps_trans; [exact RUN4|]. eapply msteps_trans; [exact RUN5|]. eapply msteps_trans; [exact RUN6|].
      eapply msteps_trans; [exact RUN7|]. eapply msteps_trans; [exact RUN8 | exact RUN9]. }
    repeat match goal with |- _ /\ _ => split end; try assumption; rch.
  Qed.
End RUNFULLC.
End FPGen.
