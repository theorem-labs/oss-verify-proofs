(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare StoreOk RefMemcpyLib.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Leptonica Require Import PortLib.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Leptonica Require Import Frame SumSpecs.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Reloc Require Import RelocKit .
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Musl Require Import MuslTac MemcpyBase.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Leptonica Require Import PFLib PFSpecLib.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Reloc Require Import RelocKit .
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Musl Require Import MuslTac PFBase PFFwx PFStr PFCore PFCoreTop PFLept.
Import ListNotations.
Open Scope Z_scope.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Section GD_1.
  Context {RL : Reloc}.
Definition ls_ok (nS : nat) (fmts : list Z) (L : SSP.ls_addrs) : bool :=
  (SSP.ls_entry L =? A_LEPT_STDERR) && (SSP.ls_handler_cell L =? A_HANDLER_CELL) && (SSP.ls_devnull L =? A_DEVNULL)
  && (SSP.ls_canary_got L =? A_CANARY_GOT) && (SSP.ls_canary L =? A_CANARY)
  && (0 <=? SSP.ls_img_lo L) && (SSP.ls_img_lo L <=? IMG_LO) && (IMG_HI <=? SSP.ls_img_hi L)
  && (FR <=? SSP.ls_frame L) && (IMG_TOP + SSP.ls_frame L <=? SSP.ls_sp_lo L) && (SSP.ls_sp_hi L <=? 0x800000000000)
  && forallb (fmt_check SEGS nS (SSP.ls_img_lo L) (SSP.ls_img_hi L) IMG_LO IMG_TOP) fmts.
End GD_1.
Section GD_2.
  Context {RL : Reloc}.
Definition ls_ok1 (L : SSP.ls_addrs) : bool := ls_ok 1 (SSP.ls_fmts1 L) L.
End GD_2.
Section GD_3.
  Context {RL : Reloc}.
Definition ls_ok2 (L : SSP.ls_addrs) : bool := ls_ok 2 (SSP.ls_fmts2 L) L.
End GD_3.

(* [comment removed for export] *)
Section VP1.
  Context {fx : FPState} {RL : Reloc} {RLC : RelocCode RL} {RLS : RelocSites RL} {RLD : RelocData RL} {RLI : RelocImg RL} {RLW : RelocRW RL RLD} {RLP : RelocPF RL}.
Lemma all_int_convs_ok : forall cs nS k, all_int cs = true -> convs_ok nS k cs.
Proof.
  induction cs as [|c r IH]; intros nS k H; cbn; [exact I|].
  cbn in H. apply andb_prop in H as [H1 H2]. split; [|apply IH; exact H2].
  right. destruct c; cbn in H1; try discriminate; intros E; discriminate E.
Qed.
End VP1.
Section VP2.
  Context {fx : FPState} {RL : Reloc} {RLC : RelocCode RL} {RLS : RelocSites RL} {RLD : RelocData RL} {RLI : RelocImg RL} {RLW : RelocRW RL RLD} {RLP : RelocPF RL}.
Lemma class_convs_ok : forall n cs k, class_ok n cs = true -> convs_ok (k + Z.of_nat n) k cs.
Proof.
  induction n as [|n IH]; intros cs k H.
  - cbn [class_ok] in H. apply all_int_convs_ok. destruct cs; exact H.
  - destruct cs as [|c r]; [discriminate H|]. cbn [class_ok] in H. apply andb_prop in H as [H1 H2].
    cbn [convs_ok]. split.
    + left. split; [destruct c; cbn in H1; try discriminate; reflexivity | lia].
    + replace (k + Z.of_nat (S n)) with (k + 1 + Z.of_nat n) by lia. apply IH. exact H2.
Qed.
End VP2.

Section CORE.
  Context {fx : FPState} {RL : Reloc} {RLC : RelocCode RL} {RLS : RelocSites RL} {RLD : RelocData RL} {RLI : RelocImg RL} {RLW : RelocRW RL RLD} {RLP : RelocPF RL}.
  Variables (L : SSP.ls_addrs) (nS : nat) (fmts : list Z).
  Hypothesis OK : ls_ok nS fmts L = true.

  (* [comment removed for export] *)
  Lemma lept_core : forall (fmt : Z) (R : bvmap 5 word) (M rom : word -> option byte) (hv cg cv : Z)
                          (saddr slen : Z -> Z),
    let sp0 := bv_unsigned (getr R 2) in
    getr R 10 = Z_to_bv 64 fmt -> In fmt fmts ->
    SSP.cell_holds SEGS M (SSP.ls_handler_cell L + 0) 8 hv -> hv = SSP.ls_devnull L ->
    SSP.cell_holds SEGS M (SSP.ls_canary_got L + 0) 8 cg -> cg = SSP.ls_canary L ->
    SSP.cell_holds SEGS M (SSP.ls_canary L + 0) 8 cv ->
    (forall i, SSP.ls_img_lo L <= i < SSP.ls_img_hi L -> M (Z_to_bv 64 i) = None) ->
    sp0 mod 16 = 0 -> SSP.ls_sp_lo L <= sp0 <= SSP.ls_sp_hi L ->
    SSP.flatZ (sp0 - SSP.ls_frame L) (SSP.ls_frame L) ->
    store_ok SEGS M (Z_to_bv 64 (sp0 - SSP.ls_frame L)) (Z.to_nat (SSP.ls_frame L)) = true ->
    ret_ok (getr R 1) ->
    (forall q, 0 <= q < Z.of_nat nS ->
       vaf R q = Z_to_bv 64 (saddr q) /\ SSP.rostr SEGS M (saddr q) (slen q) /\ slen q <= 200) ->
    exists R' M',
      msteps SEGS (mkst R (Z_to_bv 64 (SSP.ls_entry L)) M rom) (mkst R' (getr R 1) M' rom)
      /\ getr R' 2 = getr R 2
      /\ (forall x : reg, In x [3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr R' x = getr R x)
      /\ (forall x : word, bv_unsigned x < sp0 - SSP.ls_frame L \/ sp0 <= bv_unsigned x -> M' x = M x)
      /\ mem_grows M M'.
  Proof.
    intros fmt R M rom hv cg cv saddr slen sp0 H10 INf CHh Ehv CHg Ecg CHc IMG AL SPR FL SOK Hret SARGS.
    unfold ls_ok in OK.
    apply andb_prop in OK as [OK FMTS]. apply andb_prop in OK as [OK Ohi]. apply andb_prop in OK as [OK Olo].
    apply andb_prop in OK as [OK Ofr]. apply andb_prop in OK as [OK Oih]. apply andb_prop in OK as [OK Oil].
    apply andb_prop in OK as [OK Oi0].
    apply andb_prop in OK as [OK Ocan]. apply andb_prop in OK as [OK Ogot]. apply andb_prop in OK as [OK Odev].
    apply andb_prop in OK as [Oent Ohdl].
    apply Z.eqb_eq in Oent. apply Z.eqb_eq in Ohdl. apply Z.eqb_eq in Odev. apply Z.eqb_eq in Ogot. apply Z.eqb_eq in Ocan.
    apply Z.leb_le in Oi0. apply Z.leb_le in Oil. apply Z.leb_le in Oih. apply Z.leb_le in Ofr. apply Z.leb_le in Olo. apply Z.leb_le in Ohi.
    (* [comment removed for export] *)
    pose proof (proj1 (forallb_forall _ _) FMTS fmt INf) as FC.
    destruct (fmt_check_sound SEGS _ _ _ _ _ _ FC) as (fbs & its & Fimg & Fbyte & Flo & Fhi & Frlo & Frhi & ITS & WF & CL & NC7 & REM).
    (* [comment removed for export] *)
    destruct CHh as [Rhv CHh]. destruct CHg as [Rcg CHg]. destruct CHc as [Rcv CHc].
    rewrite Z.add_0_r in CHh, CHg, CHc. subst hv cg.
    rewrite Ohdl, Odev in CHh. rewrite Ogot, Ocan in CHg. rewrite Ocan in CHc.
    destruct FL as (FL1 & FL2 & FL3).
    assert (CTX : ctxH sp0 M cv).
    { split.
      - lay. lia.
      - exact AL.
      - intros i Hi. apply IMG. lay. lia.
      - lay. eapply (store_ok_sub SEGS M (Z_to_bv 64 (sp0 - SSP.ls_frame L)) _ (Z.to_nat (SSP.ls_frame L)));
          [ rewrite u_Z2bv by lia; lia | exact SOK | rewrite !u_Z2bv by lia; lia | rewrite !u_Z2bv by lia; lia ].
      - rewrite CHh. unfold word_to_le_bytes. rewrite u_Z2bv by (lay; lia). reflexivity.
      - rewrite CHg. unfold word_to_le_bytes. rewrite u_Z2bv by (lay; lia). reflexivity.
      - rewrite CHc. unfold word_to_le_bytes. rewrite u_Z2bv by lia. reflexivity.
      - exact Rcv. }
    assert (FMT0 : forall i, 0 <= i < Z.of_nat (length fbs) ->
              M (Z_to_bv 64 (fmt + i)) = None /\ seg_rom SEGS (Z_to_bv 64 (fmt + i)) = Some (Z_to_bv 8 (nth (Z.to_nat i) fbs 0))).
    { intros i Hi. split; [apply IMG; lia | apply Fimg; exact Hi]. }
    assert (H2 : getr R 2 = Z_to_bv 64 sp0) by (subst sp0; symmetry; apply Z_to_bv_bv_unsigned).
    destruct (lept_stderr_run sp0 M cv rom CTX fmt fbs FMT0 ltac:(lia) Fbyte its ITS WF NC7
                ltac:(unfold rem, INT_MAX; lia) R (getr R 1) (Z.of_nat nS) saddr slen
                SARGS ltac:(pose proof (class_convs_ok nS (convs its) 0 CL) as X; exact X)
                Hret eq_refl H2 H10)
      as (r' & m' & RUN & S2 & SK & [FE FG]).
    exists r', m'. split; [|split; [|split; [exact SK | split; [|exact FG]]]].
    - rewrite Oent. unfold A_LEPT_STDERR. exact RUN.   (* [comment removed for export] *)
    - rewrite S2. symmetry. exact H2.
    - intros x Hx. apply FE. cbn [outside]. split; [|exact I]. unfold in_rng. lay. rewrite u_Z2bv by lia. lia.
  Qed.
End CORE.

(* [comment removed for export] *)
Section VP3.
  Context {fx : FPState} {RL : Reloc} {RLC : RelocCode RL} {RLS : RelocSites RL} {RLD : RelocData RL} {RLI : RelocImg RL} {RLW : RelocRW RL RLD} {RLP : RelocPF RL}.
Theorem lept_stderr_s1_contract : forall L, ls_ok1 L = true -> SSP.sum_contract SEGS (SSP.spec_lept_stderr_s1 L).
Proof.
  intros L OK.
  apply SSP.sum_contract_in5; [reflexivity | reflexivity |].
  intros fmt a1 hv cg cv R M rom PRE.
  unfold SSP.spec_lept_stderr_s1 in PRE. SSP.spec_unfold_in PRE.
  destruct PRE as (ITEMS & EFF & APART & RET).
  destruct ITEMS as ([R10 _] & INf & ROf & [R11 _] & ROa1 & (_ & _ & CHh) & Ehv & (_ & _ & CHg) & Ecg & (_ & _ & CHc)
                     & IMG & [_ AL] & SPR & _).
  destruct EFF as (_ & FL & SOK & _).
  destruct ROa1 as (k1 & Hk1 & RO1).
  destruct (lept_core L 1 (SSP.ls_fmts1 L) OK fmt R M rom hv cg cv (fun _ => a1) (fun _ => k1)
              R10 INf CHh Ehv CHg Ecg CHc IMG AL SPR FL SOK RET)
    as (R' & M' & RUN & K2 & KK & FE & FG).
  { intros q Hq. replace q with 0 by lia. cbn. split; [exact R11 | split; [exact RO1 | exact Hk1]]. }
  exists R', M'. split; [exact RUN|].
  unfold SSP.spec_lept_stderr_s1. SSP.spec_unfold.
  split; [|split; [exact I | split; [| split; [exact FG | split; [split; exact I | exact I]]]]].
  - split; [exact K2|]. repeat (split; [apply KK; clear; cbv [In]; tauto|]). exact I.
  - intros x [Hx _]. apply FE. exact Hx.
Qed.
End VP3.

(* [comment removed for export] *)
Section VP4.
  Context {fx : FPState} {RL : Reloc} {RLC : RelocCode RL} {RLS : RelocSites RL} {RLD : RelocData RL} {RLI : RelocImg RL} {RLW : RelocRW RL RLD} {RLP : RelocPF RL}.
Theorem lept_stderr_s2_contract : forall L, ls_ok2 L = true -> SSP.sum_contract SEGS (SSP.spec_lept_stderr_s2 L).
Proof.
  intros L OK.
  apply SSP.sum_contract_in6; [reflexivity | reflexivity |].
  intros fmt a1 a2 hv cg cv R M rom PRE.
  unfold SSP.spec_lept_stderr_s2 in PRE. SSP.spec_unfold_in PRE.
  destruct PRE as (ITEMS & EFF & APART & RET).
  destruct ITEMS as ([R10 _] & INf & ROf & [R11 _] & ROa1 & [R12 _] & ROa2 & (_ & _ & CHh) & Ehv & (_ & _ & CHg) & Ecg
                     & (_ & _ & CHc) & IMG & [_ AL] & SPR & _).
  destruct EFF as (_ & FL & SOK & _).
  destruct ROa1 as (k1 & Hk1 & RO1). destruct ROa2 as (k2 & Hk2 & RO2).
  destruct (lept_core L 2 (SSP.ls_fmts2 L) OK fmt R M rom hv cg cv
              (fun q => if q =? 0 then a1 else a2) (fun q => if q =? 0 then k1 else k2)
              R10 INf CHh Ehv CHg Ecg CHc IMG AL SPR FL SOK RET)
    as (R' & M' & RUN & K2 & KK & FE & FG).
  { intros q Hq. assert (E : q = 0 \/ q = 1) by lia. destruct E as [-> | ->]; cbn.
    - split; [exact R11 | split; [exact RO1 | exact Hk1]].
    - split; [exact R12 | split; [exact RO2 | exact Hk2]]. }
  exists R', M'. split; [exact RUN|].
  unfold SSP.spec_lept_stderr_s2. SSP.spec_unfold.
  split; [|split; [exact I | split; [| split; [exact FG | split; [split; exact I | exact I]]]]].
  - split; [exact K2|]. repeat (split; [apply KK; clear; cbv [In]; tauto|]). exact I.
  - intros x [Hx _]. apply FE. exact Hx.
Qed.
End VP4.
