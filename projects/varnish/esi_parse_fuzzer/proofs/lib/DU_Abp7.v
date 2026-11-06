(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.varnish.esi_parse_fuzzer.images Require Import Ubsan.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Amb PropExec.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require WallSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require CatSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require WallSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require StoreOk SimInv ShapeAlg Shapi1s Nodes MmapSim AgentLib Frame SymExec SymExec2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require SymRun.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require SymRun SymDrive SymDe08 SymAux LibK2dm RefMocc D_Kn21w ImgU.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Amb OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.PropExec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.WallSim.CatExec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.CatSim OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.WallSim.SeqExec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.StoreOk OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.SimInv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.ShapeAlg OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Shapi1s OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Nodes OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.MmapSim OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.AgentLib OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Frame OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.SymExec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.SymExec2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.SymRun.SymEo0r OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.SymRun OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.SymDrive OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.SymDe08 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.SymAux OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.LibK2dm OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.RefMocc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.D_Kn21w OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.ImgU.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Mem Frame Regs6ss RzEqv.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Ceiling.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Import AllocSpec LayoutPU DriverKit.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.
Import SX2. Import SX2S.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Dieta54.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Dieta54.dlia.
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac mem_side := cbn; first [ (let E := fresh "E" in intros E; discriminate E) | solve [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; first [ exact I | reflexivity ] ] | solve [ repeat first [ left; reflexivity | right ] ] | tauto ].
Local Ltac mem_hyp Hr := cbn in Hr; first [ solve [ repeat (destruct Hr as [Hr|Hr]; [discriminate Hr|]); first [ discriminate Hr | destruct Hr ] ] | intuition discriminate ].
(* [comment removed for export] *)

Abbreviation RSEGS := Ubsan.M.loaded_segments.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition STATICS_LO : Z := 0x627f8.
Definition STATICS_HI : Z := 0x62ba4.
Definition ERRNO_CELL : Z := 0x42454.
Definition HEAP_LO : Z := 0x64000.
(* [comment removed for export] *)
Definition HEAP_HI : Z := 0x7fff7f800000.
Definition CSLACK : Z := 0x80000000.

(* [comment removed for export] *)
Definition LOW_LO : Z := 0.
Definition LOW_HI : Z := 0x10000.

(* [comment removed for export] *)
Definition RS_call (spk win : Z) : list frange :=
  [(EVar 0, (spk - win)%Z, win); (ELit 0, ERRNO_CELL, 4%Z);
   (ELit 0, STATICS_LO, (STATICS_HI - STATICS_LO)%Z); (ELit 0, HEAP_LO, (HEAP_HI - HEAP_LO)%Z);
   (EVar 0, (-8388608 - CSLACK)%Z, CSLACK);
   (ELit 0, LOW_LO, (LOW_HI - LOW_LO)%Z)].
(* [comment removed for export] *)
Definition VICT : list frange := [(ELit 0, 0%Z, HEAP_HI); (EVar 0, (-8388608 - CSLACK)%Z, CSLACK)].

(* [comment removed for export] *)
Section CEIL.
Context {Clg : Ceiling}.

Definition azone (a : Z) : Prop :=
  (STATICS_LO <= a < STATICS_HI)%Z \/ (HEAP_LO <= a < alloc_ceiling)%Z \/ (LOW_LO <= a < LOW_HI)%Z.

Section WithAlloc.
  Context {AI : AllocSpec LayoutPU}.

  Lemma heap_azone : forall a, heap_zone LayoutPU a -> azone a.
  Proof.
    intros a [Ha Hni]. unfold in_image in Hni. cbn [al_image_lo al_image_hi LayoutPU] in Hni.
    unfold azone, HEAP_LO, LOW_LO, LOW_HI. lia.
  Qed.

  Lemma owned_azone : forall A m md a, ainv A m md -> owned A a -> azone a.
  Proof.
    intros A m md a AI0 Ho. destruct (as_owned_where A m md a AI0 Ho) as [Hs|Hh].
    - left. exact Hs.
    - apply heap_azone. exact Hh.
  Qed.

  Lemma static_azone : forall a, al_static LayoutPU a -> azone a.
  Proof. intros a Hs. left. exact Hs. Qed.

  Lemma live_azone : forall A m md p n i, ainv A m md -> a_live A p = Some n -> (0 <= i < n)%Z -> azone (p + i).
  Proof.
    intros A m md p n i AI0 HL Hi. (first [ pose proof ((as_live_ok A m md p n AI0 HL)) as dR_1; dand7 dR_1 as N0 AL P1 HI IMG MP NO | destruct (as_live_ok A m md p n AI0 HL) as (N0 & AL & P1 & HI & IMG & MP & NO) ]).
    right. cbn [al_image_lo al_image_hi LayoutPU] in IMG. unfold HEAP_LO, LOW_LO, LOW_HI. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma frame_outside : forall (O O' : Z -> Prop) (E : env) (spk win : Z) victim newb m m',
    (forall a, O a -> azone a) -> (forall a, O' a -> azone a) ->
    (forall a, victim a -> azone a) -> (forall a, newb a -> azone a) ->
    frame_ok LayoutPU O O' (bv_unsigned (ev E 0) + spk) win victim newb m m' ->
    (0 <= win)%Z -> (win <= bv_unsigned (ev E 0) + spk)%Z -> (bv_unsigned (ev E 0) + spk < 2 ^ 64)%Z ->
    (alloc_ceiling + 8388608 <= bv_unsigned (ev E 0))%Z -> (bv_unsigned (ev E 0) <= 0x800000000000)%Z ->
    (forall x : word, outside_all E (RS_call spk win) x -> m' x = m x)
    /\ (forall x : word, outside_all E VICT x -> m x <> None -> m' x <> None).
  Proof.
    intros O O' E spk win victim newb m m' HO HO' HV HN FR Hw0 Hw1 Hw2 Hce Hsphi.
    (first [ pose proof (FR) as dR_2; dand7 dR_2 as F1 F2 F3 F4 F5 F6 F7 | pose proof FR as (F1 & F2 & F3 & F4 & F5 & F6 & F7) ]). pose proof alloc_ceiling_val as CV.
    assert (Z0 : bv_unsigned (edenot E (ELit 0)) = 0%Z) by (cbn [edenot]; reflexivity).
    split.
    - intros x OUT. pose proof (u64_range x) as Hx.
      assert (A1 := OUT (EVar 0) (spk - win)%Z win ltac:(mem_side)).
      assert (A2 := OUT (ELit 0) ERRNO_CELL 4%Z ltac:(mem_side)).
      assert (A3 := OUT (ELit 0) STATICS_LO (STATICS_HI - STATICS_LO)%Z ltac:(mem_side)).
      assert (A4 := OUT (ELit 0) HEAP_LO (HEAP_HI - HEAP_LO)%Z ltac:(mem_side)).
      assert (A6 := OUT (EVar 0) (-8388608 - CSLACK)%Z CSLACK ltac:(mem_side)).
      assert (A5 := OUT (ELit 0) LOW_LO (LOW_HI - LOW_LO)%Z ltac:(mem_side)).
      unfold estart in A1, A2, A3, A4, A5, A6. cbn [a_base a_off] in A1, A2, A3, A4, A5, A6. cbn [edenot] in A1, A6. rewrite Z0 in A2, A3, A4, A5.
      unfold CSLACK in A6.
      rewrite <- (Z_to_bv_bv_unsigned 64 x). apply F1.
      + exact Hx.
      + intros Ho. destruct (HO _ Ho) as [S|[S|S]]; unfold STATICS_LO, STATICS_HI, HEAP_LO, HEAP_HI, LOW_LO, LOW_HI in *; lia.
      + intros Ho. destruct (HO' _ Ho) as [S|[S|S]]; unfold STATICS_LO, STATICS_HI, HEAP_LO, HEAP_HI, LOW_LO, LOW_HI in *; lia.
      + lia.
      + unfold al_errno. cbn [al_tp LayoutPU]. rewrite u_small by lia. unfold ERRNO_CELL in A2. lia.
      + intros Hv. destruct (HV _ Hv) as [S|[S|S]]; unfold STATICS_LO, STATICS_HI, HEAP_LO, HEAP_HI, LOW_LO, LOW_HI in *; lia.
      + intros Hn. destruct (HN _ Hn) as [S|[S|S]]; unfold STATICS_LO, STATICS_HI, HEAP_LO, HEAP_HI, LOW_LO, LOW_HI in *; lia.
    - intros x OUT Hm. pose proof (u64_range x) as Hx.
      assert (A4 := OUT (ELit 0) 0%Z HEAP_HI ltac:(mem_side)).
      assert (A6 := OUT (EVar 0) (-8388608 - CSLACK)%Z CSLACK ltac:(mem_side)).
      unfold estart in A4, A6. cbn [a_base a_off] in A4, A6. cbn [edenot] in A6. rewrite Z0 in A4. unfold CSLACK in A6.
      rewrite <- (Z_to_bv_bv_unsigned 64 x) in Hm |- *.
      destruct (F2 _ Hx ltac:(unfold in_image; cbn [al_image_lo al_image_hi LayoutPU]; unfold HEAP_HI in A4; lia) Hm)
        as [Ho|[Hv|Hm']]; [| |exact Hm'].
      + destruct (HO _ Ho) as [S|[S|S]]; unfold STATICS_LO, STATICS_HI, HEAP_LO, HEAP_HI, LOW_LO, LOW_HI in *; lia.
      + destruct (HV _ Hv) as [S|[S|S]]; unfold STATICS_LO, STATICS_HI, HEAP_LO, HEAP_HI, LOW_LO, LOW_HI in *; lia.
  Qed.
End WithAlloc.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition mkR_sr (E : env) (sr : list expr) : bvmap 5 word :=
  Frame.mkR (edenot E (sr_get sr 1)) (edenot E (sr_get sr 2)) (edenot E (sr_get sr 3)) (edenot E (sr_get sr 4))
      (edenot E (sr_get sr 5)) (edenot E (sr_get sr 6)) (edenot E (sr_get sr 7)) (edenot E (sr_get sr 8))
      (edenot E (sr_get sr 9)) (edenot E (sr_get sr 10)) (edenot E (sr_get sr 11)) (edenot E (sr_get sr 12))
      (edenot E (sr_get sr 13)) (edenot E (sr_get sr 14)) (edenot E (sr_get sr 15)) (edenot E (sr_get sr 16))
      (edenot E (sr_get sr 17)) (edenot E (sr_get sr 18)) (edenot E (sr_get sr 19)) (edenot E (sr_get sr 20))
      (edenot E (sr_get sr 21)) (edenot E (sr_get sr 22)) (edenot E (sr_get sr 23)) (edenot E (sr_get sr 24))
      (edenot E (sr_get sr 25)) (edenot E (sr_get sr 26)) (edenot E (sr_get sr 27)) (edenot E (sr_get sr 28))
      (edenot E (sr_get sr 29)) (edenot E (sr_get sr 30)) (edenot E (sr_get sr 31)).

Lemma realizes_of_sr : forall E sr R pc m rom md T,
  regs_ok E sr R ->
  realizes RSEGS (mkCfg (mkst (mkR_sr E sr) pc m rom) md) T ->
  realizes RSEGS (mkCfg (mkst R pc m rom) md) T.
Proof.
  intros E sr R pc m rom md T HR H. unfold mkR_sr in H.
  eapply RzEqv.realizes_of_mkR; [ .. | exact H]; apply HR.
Qed.

(* [comment removed for export] *)
Definition KEPT : list nat := map ridx callee_saved.
Definition sr_post (sr : list expr) (N : nat) : list expr := sr_after_call_j sr KEPT N.

Lemma callee_saved_no0 : ~ In (0%bv : reg) callee_saved.
Proof.
  unfold callee_saved. intros Hin.
  repeat (destruct Hin as [Hin|Hin]; [apply (f_equal bv_unsigned) in Hin; cbn in Hin; discriminate Hin|]). exact Hin.
Qed.

(* [comment removed for export] *)
Lemma regs_ok_post : forall vals ebs sr R (R' : bvmap 5 word),
  sr_vars_lt (length vals) sr = true ->
  regs_ok (Env (vals_ev vals) ebs) sr R ->
  (forall r : reg, In r callee_saved -> getr R' r = edenot (Env (vals_ev vals) ebs) (sr_get sr r)) ->
  regs_ok (Env (vals_ev (vals ++ junk_vals R')) ebs) (sr_post sr (length vals)) R'.
Proof.
  intros vals ebs sr R R' Hsv HR HK. unfold sr_post, KEPT.
  apply (regs_after_keeps vals ebs sr R R' callee_saved Hsv HR); [| apply callee_saved_no0].
  intros r Hr. rewrite (HK r Hr). symmetry. apply HR.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)


Section WithAlloc2.
  Context {AI : AllocSpec LayoutPU}.

  Lemma RS_call_flat : forall vals ebs spk win,
    (0 <= win)%Z -> (win <= bv_unsigned (vals_ev vals 0) + spk)%Z -> (bv_unsigned (vals_ev vals 0) + spk < 2 ^ 64)%Z ->
    (alloc_ceiling + 8388608 <= bv_unsigned (vals_ev vals 0))%Z ->
    Forall (fun r : frange => match r with (ub, uk, un) => flat (Env (vals_ev vals) ebs) (SA ub uk) un end) (RS_call spk win).
  Proof.
    intros vals ebs spk win H0 H1 H2 Hce. pose proof alloc_ceiling_val as CV. pose proof (u64_range (vals_ev vals 0)) as Hsp.
    unfold RS_call, ERRNO_CELL, STATICS_LO, STATICS_HI, HEAP_LO, HEAP_HI, LOW_LO, LOW_HI, CSLACK.
    repeat constructor; unfold estart; cbn [a_base a_off edenot ev]; try change (bv_unsigned (Z_to_bv 64 0)) with 0%Z; try lia.
  Qed.

  (* [comment removed for export] *)
  Lemma know_ok_acall : forall (O O' : Z -> Prop) vals ebs M M' kn spk win victim newb (R' : bvmap 5 word),
    know_ok RSEGS (Env (vals_ev vals) ebs) M kn -> kn_vars_lt (length vals) kn = true -> (0 < length vals)%nat ->
    (forall a, O a -> azone a) -> (forall a, O' a -> azone a) ->
    (forall a, victim a -> azone a) -> (forall a, newb a -> azone a) ->
    frame_ok LayoutPU O O' (bv_unsigned (vals_ev vals 0) + spk) win victim newb M M' ->
    (0 <= win)%Z -> (win <= bv_unsigned (vals_ev vals 0) + spk)%Z -> (bv_unsigned (vals_ev vals 0) + spk < 2 ^ 64)%Z ->
    (alloc_ceiling + 8388608 <= bv_unsigned (vals_ev vals 0))%Z -> (bv_unsigned (vals_ev vals 0) <= 0x800000000000)%Z ->
    know_ok RSEGS (Env (vals_ev (vals ++ junk_vals R')) ebs) M' (kn_keep2 kn (RS_call spk win) VICT).
  Proof.
    intros O O' vals ebs M M' kn spk win victim newb R' HK Hkv Hlen HO HO' HV HN FR W0 W1 W2 Hce Hsphi.
    assert (E0 : vals_ev (vals ++ junk_vals R') 0 = vals_ev vals 0) by (apply vals_ev_app_l; exact Hlen).
    destruct (frame_outside O O' (Env (vals_ev (vals ++ junk_vals R')) ebs) spk win victim newb M M' HO HO' HV HN)
      as [OUT DOM]; cbn [ev]; rewrite ?E0; try assumption.
    apply (know_ok_keep2 RSEGS _ M M'); [apply env_app_know; [exact Hkv| exact HK] | | exact OUT | exact DOM].
    apply RS_call_flat; rewrite ?E0; assumption.
  Qed.

  (* [comment removed for export] *)
  #[using="AI Clg"] Lemma win_mapped : forall vals ebs M kn i kk len spk win,
    know_ok RSEGS (Env (vals_ev vals) ebs) M kn ->
    nth_error kn i = Some (KWr (SA (EVar 0) kk) len) ->
    (kk <= spk - win)%Z -> (spk <= kk + len)%Z -> (0 <= win)%Z ->
    (HEAP_HI <= bv_unsigned (vals_ev vals 0) + kk)%Z -> (bv_unsigned (vals_ev vals 0) + spk <= 2 ^ 64)%Z ->
    mapped M (bv_unsigned (vals_ev vals 0) + spk - win) win.
  Proof.
    intros vals ebs M kn i kk len spk win HK Hn H1 H2 H0 Hc Hhi j Hj.
    unfold HEAP_HI in Hc. pose proof (u64_range (vals_ev vals 0)) as Hsp.
    pose proof (kwr_store_ok RSEGS _ M kn i (EVar 0) kk len (spk - win) (Z.to_nat win) HK Hn ltac:(lia) ltac:(lia)) as ST.
    unfold adenot, v_addi in ST. cbn [a_base a_off edenot ev] in ST.
    pose proof (store_ok_all RSEGS M (Z.to_nat win) (Z_to_bv 64 (bv_unsigned (vals_ev vals 0) + (spk - win)))) as W0.
    rewrite !u_small in W0 by lia.
    pose proof (W0 ltac:(lia) ST (Z_to_bv 64 (bv_unsigned (vals_ev vals 0) + spk - win + j))) as W. clear W0.
    rewrite !u_small in W by lia. specialize (W ltac:(lia)).
    unfold wview in W. destruct (M (Z_to_bv 64 (bv_unsigned (vals_ev vals 0) + spk - win + j))) eqn:EM; [congruence|].
    rewrite (as_find_segment_above (AI:=AI)) in W; [exact W|].
    cbn [al_image_hi LayoutPU]. rewrite u_small by lia. lia.
  Qed.
End WithAlloc2.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Lemma mod16_add : forall a b, (a mod 16 = 0)%Z -> (b mod 16 = 0)%Z -> ((a + b) mod 16 = 0)%Z.
Proof. intros a b Ha Hb. lia. Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Lemma sp_expr_val : forall vals ebs spk,
  (0 <= bv_unsigned (vals_ev vals 0) + spk < 2 ^ 64)%Z ->
  bv_unsigned (edenot (Env (vals_ev vals) ebs) (EAlu ALU_ADD (EVar 0) (ELit spk))) = (bv_unsigned (vals_ev vals 0) + spk)%Z.
Proof.
  intros vals ebs spk H. rewrite edenot_add_lit. unfold adenot, v_addi. cbn [a_base a_off edenot ev].
  apply u_small. exact H.
Qed.

Section Wrapped.
  Context {AI : AllocSpec LayoutPU} {DK : DriverKit LayoutPU InitPU}.

  (* [comment removed for export] *)
  Record callH (vals : list word) (ebs : nat -> list byte) (sr : list expr) (kn : list kentry)
                (arg spk ra : Z) : Prop := CALLH {
    ch_sv  : sr_vars_lt (length vals) sr = true;
    ch_kv  : kn_vars_lt (length vals) kn = true;
    ch_len : (0 < length vals)%nat;
    ch_a0  : edenot (Env (vals_ev vals) ebs) (sr_get sr 10) = Z_to_bv 64 arg;
    ch_tp  : sr_get sr 4 = ELit 0x424f8;
    ch_ra  : sr_get sr 1 = ELit ra;
    ch_sp  : sr_get sr 2 = EAlu ALU_ADD (EVar 0) (ELit spk);
    ch_ra4 : (ra mod 4 = 0)%Z;
    ch_ra64 : (0 <= ra < 2 ^ 64)%Z;
    ch_sp16 : (bv_unsigned (vals_ev vals 0) mod 16 = 0)%Z;
    ch_spk16 : (spk mod 16 = 0)%Z;
    ch_splo : (alloc_ceiling + 8388608 <= bv_unsigned (vals_ev vals 0))%Z;   (* [comment removed for export] *)
    ch_sphi : (bv_unsigned (vals_ev vals 0) <= 2 ^ 47)%Z;
    ch_spk  : (-8388608 + 8192 + 64 <= spk <= 0)%Z;
    (* [comment removed for export] *)
    ch_win  : exists iw, nth_error kn iw = Some (KWr (SA (EVar 0) (-8388608)) 8388608)
  }.

  (* [comment removed for export] *)
  Theorem W_malloc_nf :
    forall vals ebs sr kn R M md A (n spk ra : Z) T,
    let E := Env (vals_ev vals) ebs in
    let sp0 := vals_ev vals 0 in
    regs_ok E sr R -> know_ok RSEGS E M kn -> callH vals ebs sr kn n spk ra ->
    ainv A M md -> (exists q k, a_live A q = Some k) -> Mem.mem_inv RSEGS M -> (0 <= n < 2 ^ 32)%Z -> (n <= NREQ_CAP)%Z ->
    (a_livebytes A + n <= LIVE_MAX)%Z -> (a_nlive A + 1 <= NLIVE_MAX)%Z ->
    (forall (R' : bvmap 5 word) M' md' A' r, r <> 0%Z ->
       vals_ev (vals ++ junk_vals R') (length vals + 10) = Z_to_bv 64 r ->
       regs_ok (Env (vals_ev (vals ++ junk_vals R')) ebs) (sr_post sr (length vals)) R' ->
       know_ok RSEGS (Env (vals_ev (vals ++ junk_vals R')) ebs) M' (kn_keep2 kn (RS_call spk MALLOC_STACK) VICT) ->
       ainv A' M' md' -> Mem.mem_inv RSEGS M' -> md_frame md md' ->
       a_live A r = None -> a_live A' r = Some n -> (forall q, q <> r -> a_live A' q = a_live A q) ->
       a_livebytes A' = (a_livebytes A + n)%Z -> a_nlive A' = (a_nlive A + 1)%Z ->
       frame_ok LayoutPU (owned A) (owned A') (bv_unsigned sp0 + spk) MALLOC_STACK nowhere (blk r n) M M' ->
       realizes RSEGS (mkCfg (mkst R' (Z_to_bv 64 ra) M' (seg_rom RSEGS)) md') T) ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x23364) M (seg_rom RSEGS)) md) T.
  Proof.
    intros vals ebs sr kn R M md A n spk ra T E sp0 HR HK CH AI0 HEX MI Hn Hcap HLB HNL K1.
    destruct CH as [Hsv Hkv Hlen H10 H4 H1 H2 Hra4 Hra64 Hsp16 Hspk16 Hsplo Hsphi Hspk [iw Hiw]].
    subst sp0. pose proof (u64_range (vals_ev vals 0)) as Hsp0. pose proof alloc_ceiling_val as CV.
    assert (SPV : bv_unsigned (edenot E (sr_get sr 2)) = (bv_unsigned (vals_ev vals 0) + spk)%Z).
    { rewrite H2. apply sp_expr_val. lia. }
    apply (realizes_of_sr E sr R _ _ _ _ _ HR). unfold mkR_sr.
    change (realizes RSEGS (mkCfg (mkst ?RR (Z_to_bv 64 0x23364) M (seg_rom RSEGS)) md) T)
      with (realizes (al_segs LayoutPU) (mkCfg (mkst RR (al_malloc_pc LayoutPU) M (al_rom LayoutPU)) md) T).
    eapply (as_malloc_cps (L:=LayoutPU)); try exact AI0; try exact HEX; try exact MI; try exact Hn; try exact Hcap;
      try exact HLB; try exact HNL.
    - exact H10.
    - rewrite H4. reflexivity.
    - rewrite SPV. apply mod16_add; assumption.
    - rewrite H1. cbn [edenot]. rewrite u_small by lia. exact Hra4.
    - rewrite SPV. unfold MALLOC_STACK. lia.
    - rewrite SPV. unfold MALLOC_STACK.
      apply (win_mapped vals ebs M kn iw (-8388608) 8388608 spk 8192 HK Hiw); unfold HEAP_HI; lia.
    - intros t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' r A' m' md' AI' MI' MF (Hr & NEW & LIVE & OTHER & LB' & NL') FR.
      rewrite H1. cbn [edenot].
      lazymatch goal with |- realizes _ (mkCfg (mkst ?RR _ _ _) _) _ =>
        assert (HR' : regs_ok (Env (vals_ev (vals ++ junk_vals RR)) ebs) (sr_post sr (length vals)) RR)
          by (apply (regs_ok_post vals ebs sr R RR Hsv HR); intros rr Hrr; unfold callee_saved in Hrr; cbn [In] in Hrr;
              repeat (destruct Hrr as [<-|Hrr]; [first [reflexivity | rewrite H1; reflexivity] |]); destruct Hrr);
        assert (Hv10 : vals_ev (vals ++ junk_vals RR) (length vals + 10) = Z_to_bv 64 r)
          by (rewrite vals_ev_app_r; reflexivity)
      end.
      eapply (K1 _ m' md' A' r Hr Hv10 HR'); try eassumption.
      + eapply (know_ok_acall (owned A) (owned A') vals ebs M m' kn spk MALLOC_STACK nowhere (blk r n));
          try eassumption; try (unfold MALLOC_STACK; lia).
        * intros a Ho. exact (owned_azone A M md a AI0 Ho).
        * intros a Ho. exact (owned_azone A' m' md' a AI' Ho).
        * intros a Hv. unfold nowhere in Hv. destruct Hv.
        * intros a [Hr0 Ha]. replace a with (r + (a - r))%Z by lia. eapply (live_azone A' m' md' r n); [exact AI'| exact LIVE| lia].
        * rewrite <- SPV. exact FR.
      + rewrite <- SPV. exact FR.
  Qed.

  (* [comment removed for export] *)
  Ltac post_regs vals ebs sr R Hsv HR H1 :=
    lazymatch goal with |- realizes _ (mkCfg (mkst ?RR _ _ _) _) _ =>
      assert (HR' : regs_ok (Env (vals_ev (vals ++ junk_vals RR)) ebs) (sr_post sr (length vals)) RR)
        by (apply (regs_ok_post vals ebs sr R RR Hsv HR); intros rr Hrr; unfold callee_saved in Hrr; cbn [In] in Hrr;
            repeat (destruct Hrr as [<-|Hrr]; [first [reflexivity | rewrite H1; reflexivity] |]); destruct Hrr)
    end.

  (* [comment removed for export] *)
  #[using="DK"] Theorem W_malloc_first :
    forall vals ebs sr kn R M md (lo n spk ra : Z) T,
    let E := Env (vals_ev vals) ebs in
    let sp0 := vals_ev vals 0 in
    regs_ok E sr R -> know_ok RSEGS E M kn -> callH vals ebs sr kn n spk ra ->
    init_ok LayoutPU InitPU lo M md -> (bv_unsigned sp0 + spk <= lo)%Z -> Mem.mem_inv RSEGS M -> (n = 65536)%Z ->
    (forall (R' : bvmap 5 word) M' md' A' r, r <> 0%Z ->
       vals_ev (vals ++ junk_vals R') (length vals + 10) = Z_to_bv 64 r ->
       regs_ok (Env (vals_ev (vals ++ junk_vals R')) ebs) (sr_post sr (length vals)) R' ->
       know_ok RSEGS (Env (vals_ev (vals ++ junk_vals R')) ebs) M' (kn_keep2 kn (RS_call spk MALLOC_STACK) VICT) ->
       ainv A' M' md' -> Mem.mem_inv RSEGS M' -> md_frame md md' ->
       a_live A' r = Some n -> (forall q, q <> r -> a_live A' q = None) ->
       a_livebytes A' = n -> a_nlive A' = 1%Z ->
       frame_ok LayoutPU (al_static LayoutPU) (owned A') (bv_unsigned sp0 + spk) MALLOC_STACK nowhere (blk r n) M M' ->
       realizes RSEGS (mkCfg (mkst R' (Z_to_bv 64 ra) M' (seg_rom RSEGS)) md') T) ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x23364) M (seg_rom RSEGS)) md) T.
  Proof.
    intros vals ebs sr kn R M md lo n spk ra T E sp0 HR HK CH IO Hlo MI Hn K1.
    destruct CH as [Hsv Hkv Hlen H10 H4 H1 H2 Hra4 Hra64 Hsp16 Hspk16 Hsplo Hsphi Hspk [iw Hiw]].
    subst sp0. pose proof (u64_range (vals_ev vals 0)) as Hsp0. pose proof alloc_ceiling_val as CV.
    assert (SPV : bv_unsigned (edenot E (sr_get sr 2)) = (bv_unsigned (vals_ev vals 0) + spk)%Z).
    { rewrite H2. apply sp_expr_val. lia. }
    apply (realizes_of_sr E sr R _ _ _ _ _ HR). unfold mkR_sr.
    change (realizes RSEGS (mkCfg (mkst ?RR (Z_to_bv 64 0x23364) M (seg_rom RSEGS)) md) T)
      with (realizes (al_segs LayoutPU) (mkCfg (mkst RR (al_malloc_pc LayoutPU) M (al_rom LayoutPU)) md) T).
    eapply (dk_malloc_first_nf (L:=LayoutPU) (IL:=InitPU)); try exact IO; try exact MI; try exact Hn.
    - rewrite SPV. exact Hlo.
    - exact H10.
    - rewrite H4. reflexivity.
    - rewrite SPV. apply mod16_add; assumption.
    - rewrite H1. cbn [edenot]. rewrite u_small by lia. exact Hra4.
    - rewrite SPV. unfold MALLOC_STACK. lia.
    - rewrite SPV. unfold MALLOC_STACK.
      apply (win_mapped vals ebs M kn iw (-8388608) 8388608 spk 8192 HK Hiw); unfold HEAP_HI; lia.
    - intros t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' r A' m' md' Hr AI' MI' MF LIVE OTHER LB' NL' FR.
      rewrite H1. cbn [edenot]. post_regs vals ebs sr R Hsv HR H1.
      lazymatch goal with |- realizes _ (mkCfg (mkst ?RR _ _ _) _) _ =>
        assert (Hv10 : vals_ev (vals ++ junk_vals RR) (length vals + 10) = Z_to_bv 64 r)
          by (rewrite vals_ev_app_r; reflexivity) end.
      eapply (K1 _ m' md' A' r Hr Hv10 HR'); try eassumption.
      + eapply (know_ok_acall (al_static LayoutPU) (owned A') vals ebs M m' kn spk MALLOC_STACK nowhere (blk r n));
          try eassumption; try (unfold MALLOC_STACK; lia).
        * intros a Ho. exact (static_azone a Ho).
        * intros a Ho. exact (owned_azone A' m' md' a AI' Ho).
        * intros a Hv. unfold nowhere in Hv. destruct Hv.
        * intros a [Hr0 Ha]. replace a with (r + (a - r))%Z by lia. eapply (live_azone A' m' md' r n); [exact AI'| exact LIVE| lia].
        * rewrite <- SPV. exact FR.
      + rewrite <- SPV. exact FR.
  Qed.

  (* [comment removed for export] *)
  Theorem W_free_as :
    forall vals ebs sr kn R M md A (p n0 spk ra : Z) T,
    let E := Env (vals_ev vals) ebs in
    let sp0 := vals_ev vals 0 in
    regs_ok E sr R -> know_ok RSEGS E M kn -> callH vals ebs sr kn p spk ra ->
    ainv A M md -> ((p = 0 /\ n0 = 0)%Z \/ a_live A p = Some n0) -> Mem.mem_inv RSEGS M ->
    (forall (R' : bvmap 5 word) M' md' A',
       regs_ok (Env (vals_ev (vals ++ junk_vals R')) ebs) (sr_post sr (length vals)) R' ->
       know_ok RSEGS (Env (vals_ev (vals ++ junk_vals R')) ebs) M' (kn_keep2 kn (RS_call spk FREE_STACK) VICT) ->
       ainv A' M' md' -> Mem.mem_inv RSEGS M' -> md_frame md md' ->
       a_live A' p = None -> (forall q, q <> p -> a_live A' q = a_live A q) ->
       a_livebytes A' = (a_livebytes A - n0)%Z -> a_nlive A' = (a_nlive A - (if Z.eqb p 0 then 0 else 1))%Z ->
       frame_ok LayoutPU (owned A) (owned A') (bv_unsigned sp0 + spk) FREE_STACK (blk p n0) nowhere M M' ->
       realizes RSEGS (mkCfg (mkst R' (Z_to_bv 64 ra) M' (seg_rom RSEGS)) md') T) ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x23224) M (seg_rom RSEGS)) md) T.
  Proof.
    intros vals ebs sr kn R M md A p n0 spk ra T E sp0 HR HK CH AI0 HP MI K.
    destruct CH as [Hsv Hkv Hlen H10 H4 H1 H2 Hra4 Hra64 Hsp16 Hspk16 Hsplo Hsphi Hspk [iw Hiw]].
    subst sp0. pose proof (u64_range (vals_ev vals 0)) as Hsp0. pose proof alloc_ceiling_val as CV.
    assert (SPV : bv_unsigned (edenot E (sr_get sr 2)) = (bv_unsigned (vals_ev vals 0) + spk)%Z).
    { rewrite H2. apply sp_expr_val. lia. }
    apply (realizes_of_sr E sr R _ _ _ _ _ HR). unfold mkR_sr.
    change (realizes RSEGS (mkCfg (mkst ?RR (Z_to_bv 64 0x23224) M (seg_rom RSEGS)) md) T)
      with (realizes (al_segs LayoutPU) (mkCfg (mkst RR (al_free_pc LayoutPU) M (al_rom LayoutPU)) md) T).
    eapply (as_free_cps (L:=LayoutPU)); try exact AI0; try exact HP; try exact MI.
    - exact H10.
    - rewrite H4. reflexivity.
    - rewrite SPV. apply mod16_add; assumption.
    - rewrite H1. cbn [edenot]. rewrite u_small by lia. exact Hra4.
    - rewrite SPV. unfold FREE_STACK. lia.
    - rewrite SPV. unfold FREE_STACK.
      apply (win_mapped vals ebs M kn iw (-8388608) 8388608 spk 8192 HK Hiw); unfold HEAP_HI; lia.
    - intros t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' A' m' md' AI' MI' MF GONE OTHER LB' NL' ERRNO FR.
      rewrite H1. cbn [edenot]. post_regs vals ebs sr R Hsv HR H1.
      eapply (K _ m' md' A' HR'); try eassumption.
      + eapply (know_ok_acall (owned A) (owned A') vals ebs M m' kn spk FREE_STACK (blk p n0) nowhere);
          try eassumption; try (unfold FREE_STACK; lia).
        * intros a Ho. exact (owned_azone A M md a AI0 Ho).
        * intros a Ho. exact (owned_azone A' m' md' a AI' Ho).
        * intros a [Hp0 Ha]. destruct HP as [[P0 _]|HL]; [lia|].
          replace a with (p + (a - p))%Z by lia. eapply (live_azone A M md p n0); [exact AI0| exact HL| lia].
        * intros a Hv. unfold nowhere in Hv. destruct Hv.
        * rewrite <- SPV. exact FR.
      + rewrite <- SPV. exact FR.
  Qed.
End Wrapped.
End CEIL.
