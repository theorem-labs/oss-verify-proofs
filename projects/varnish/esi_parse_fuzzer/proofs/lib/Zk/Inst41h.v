(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Require OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ox.F80_004.   (* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation Classical_Prop.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import ShapeAlg.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require PropExec.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module HW := OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.PropExec.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Tac Image ZBridge SysStep Bytes Walk Arr.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Nodes.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Nodes Decode.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Image OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.SysStep OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Bytes OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Walk OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Arr OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Nodes.ITree OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Nodes OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Decode.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import Img0 R_memcpy.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Import MRepAux Mall5lv Mallj6y Mallwlb Mallrkx Malllim Mallzvh.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Import STree Malloc Mall7vg Monad MProg MProg MTree MRep MRepAux.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require KInv MI_Inv Mallkgx Mall1es Mall79j KNodes RzImpl KLink KLinkC MSafe KFrame.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require RzBridge.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require RzAux.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.KInv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Inv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Mallkgx OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Mall1es OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Mall79j OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.KNodes OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.RzImpl OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.KLink OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.KLinkC OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MSafe OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.KFrame OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.RzBridge.RzEvt OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.RzAux.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require W_ge3a6 W_redqm.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require W_rejt8.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require W_rejt8.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require W_rejt8 W_retp0 Instfes Inst8ld InstDefs InstFree Instjhg Instffk Instrcx Instjk7.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.W_ge3a6 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.W_redqm OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.W_rejt8.W_re997 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.W_rejt8.W_reagh OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.W_rejt8 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.W_retp0 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Instfes OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Inst8ld OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.InstDefs OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.InstFree OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Instjhg OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Instffk OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Instrcx OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Instjk7.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Malls6g Mallx0l.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Import AllocSpec LayoutP0.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Import LB_Inv LB_Sum InstQ.   (* [comment removed for export] *)
Import ListNotations.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Nodes.ITree.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma rw_cells_C8x8 m A junk :
  rw_cells rsegs m A [CB 64 junk] ->
  exists j0 j1 j2 j3 j4 j5 j6 j7 : word, rw_cells rsegs m A [C8 j0; C8 j1; C8 j2; C8 j3; C8 j4; C8 j5; C8 j6; C8 j7].
Proof.
  intros H.
  pose proof (rw_cells_split_CB rsegs m A [] 64 junk [] [32; 32]%nat H eq_refl) as H2. cbn [mk_CB_cells app] in H2.
  apply (proj1 (rw_cells_app rsegs m A [CB 32 (take 32 junk)] [CB 32 (take 32 (drop 32 junk))])) in H2. destruct H2 as [HA HB].
  cbn [cells_size csize Nat.add] in HB.
  (first [ pose proof ((rw_cells_C8x4 m A _ HA)) as dR_1; dex4 dR_1 as j0 j1 j2 j3; rename dR_1 into HA' | pose proof ((rw_cells_C8x4 m A _ HA)) as dR_1; dand5 dR_1 as j0 j1 j2 j3 HA' | destruct (rw_cells_C8x4 m A _ HA) as (j0 & j1 & j2 & j3 & HA') ]).
  (first [ pose proof ((rw_cells_C8x4 m _ _ HB)) as dR_2; dex4 dR_2 as j4 j5 j6 j7; rename dR_2 into HB' | pose proof ((rw_cells_C8x4 m _ _ HB)) as dR_2; dand5 dR_2 as j4 j5 j6 j7 HB' | destruct (rw_cells_C8x4 m _ _ HB) as (j4 & j5 & j6 & j7 & HB') ]).
  exists j0, j1, j2, j3, j4, j5, j6, j7.
  apply (proj2 (rw_cells_app rsegs m A [C8 j0; C8 j1; C8 j2; C8 j3] [C8 j4; C8 j5; C8 j6; C8 j7])). split; [exact HA'| exact HB'].
Qed.

Lemma md_frame_trans a b c : md_frame a b -> md_frame b c -> md_frame a c.
Proof. unfold md_frame. intros H1 H2. decompose [and] H1; decompose [and] H2. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; congruence. Qed.

(* [comment removed for export] *)
Section CEIL.
Context {Clg : Ceiling} {Rr : MRep.RunRandom}.  (* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma frame_ok_fb_compose (O O2 O3 : Z -> Prop) sp' p old r n k m1 m2 m3 m4 :
  frame_ok LayoutP0 O O2 sp' 8192 nowhere (blk r n) m1 m2 ->
  r <> 0 -> 0 <= k <= n ->
  (forall a, 0 <= a < 2^64 -> ~ (r <= a < r + k) -> m3 (Z_to_bv 64 a) = m2 (Z_to_bv 64 a)) ->
  (forall a, 0 <= a < 2^64 -> m2 (Z_to_bv 64 a) <> None -> m3 (Z_to_bv 64 a) <> None) ->
  frame_ok LayoutP0 O2 O3 sp' 8192 (blk p old) nowhere m3 m4 ->
  mapped m4 sp' 64 ->
  (forall a, O a -> a < sp' - 8192 /\ ~ (al_errno LayoutP0 <= a < al_errno LayoutP0 + 4)) ->
  frame_ok LayoutP0 O O3 (sp' + 64) 8256 (blk p old) (blk r n) m1 m4.
Proof.
  ((first [ intro dR_12; dand7 dR_12 as F1 F2 F3 F4 F5 F6 F7 | intros (F1 & F2 & F3 & F4 & F5 & F6 & F7) ]); intros Rnz Kn AG3 MONO3; (first [ intro dR_13; dand7 dR_13 as G1 G2 G3 G4 G5 G6 G7 | intros (G1 & G2 & G3 & G4 & G5 & G6 & G7) ]); intros TOP OB).
  split; [|split; [|split; [|split; [|split; [|split]]]]].
  - intros a Ha NO NO3 NW NE NV NN.
    destruct (Classical_Prop.classic (O2 a)) as [Y|Y].
    + destruct (F5 a Ha Y) as [X|[[]|[X _]]]; [exfalso; exact (NO X)|].
      destruct (G6 a Ha Y NO3) as [[]|Z4]. rewrite X, Z4. reflexivity.
    + rewrite (G1 a Ha Y NO3) by (auto; lia). rewrite (AG3 a Ha) by (intros Hin; apply NN; split; [exact Rnz| lia]).
      apply F1; auto; try lia; try (intros []).
  - intros a Ha NI Hm1. destruct (F2 a Ha NI Hm1) as [X|[[]|X]]; [left; exact X|].
    destruct (G2 a Ha NI (MONO3 a Ha X)) as [Y|[Y|Y]]; [| right; left; exact Y| right; right; exact Y].
    destruct (F5 a Ha Y) as [Z1|[[]|[Z1 _]]]; [left; exact Z1| exfalso; exact (Hm1 Z1)].
  - intros i Hi. destruct (Z_lt_le_dec (sp' + 64 - 8256 + i) sp').
    + replace (sp' + 64 - 8256 + i) with (sp' - 8192 + i) by lia. apply G3. lia.
    + replace (sp' + 64 - 8256 + i) with (sp' + (i - 8192)) by lia. apply TOP. lia.
  - intros a Ha Hn. destruct (F4 a Ha Hn) as [X|[[]|X]]; [left; exact X| right; right; exact X].
  - intros a Ha Ho3. destruct (G5 a Ha Ho3) as [Y|[Y|[Y HZ]]].
    + destruct (F5 a Ha Y) as [X|[[]|X]]; [left; exact X| right; right; exact X].
    + right; left; exact Y.
    + destruct (Classical_Prop.classic (m1 (Z_to_bv 64 a) = None)) as [E|E]; [right; right; split; [exact E| exact HZ]|].
      destruct (F2 a Ha ltac:(intros IM; exact (proj2 HZ IM)) E) as [X|[[]|X]]; [left; exact X|].
      exfalso. exact (MONO3 a Ha X Y).
  - intros a Ha Ho NO3. destruct (Classical_Prop.classic (O2 a)) as [Y|Y].
    + destruct (G6 a Ha Y NO3) as [[]|Z4]; right; exact Z4.
    + destruct (F6 a Ha Ho Y) as [X|X]; [left; exact X|].
      destruct (Classical_Prop.classic (blk r n a)) as [B|B]; [left; exact B| right].
      destruct (Classical_Prop.classic (blk p old a)) as [V|V].
      { destruct (G7 a Ha V) as [Z1|[[]|Z1]]; [exfalso; exact (NO3 Z1)| exact Z1]. }
      destruct (OB a Ho) as [OB1 OB2].
      rewrite (G1 a Ha Y NO3) by (auto; lia). rewrite (AG3 a Ha) by (intros Hin; apply B; split; [exact Rnz| lia]). exact X.
  - intros a Ha V. destruct (G7 a Ha V) as [X|[[]|X]]; [left; exact X| right; right; exact X].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma realloc_fallback_cps :
  forall (ra0 sp' gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (RA S0 S1 S2 S3 S4 S5 S6 : word) (m1 : mem) (md : Model) (A : ias) (p n old : Z) (T : TSet),
    p0_ainv A m1 md -> mem_inv rsegs m1 ->
    p0_live A p = Some old -> p <> 0 ->
    bv_unsigned a1 = n -> 0 <= n < 2^32 ->
    p0_livebytes A + n <= LIVE_MAX -> p0_nlive A + 1 <= NLIVE_MAX ->   (* [comment removed for export] *)
    tp = al_tp LayoutP0 -> bv_unsigned sp' mod 16 = 0 -> bv_unsigned RA mod 4 = 0 ->
    alloc_ceiling <= bv_unsigned sp' - 8192 -> bv_unsigned sp' + 64 <= 2^64 ->
    mapped m1 (bv_unsigned sp' - 8192) 8192 ->
    rw_cells rsegs m1 (bv_unsigned sp') [C8 S6; C8 S5; C8 S4; C8 S3; C8 S2; C8 S1; C8 S0; C8 RA] ->
    (forall (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (r : Z) (A' : ias) (m' : mem) (md' : Model),
        p0_ainv A' m' md' -> mem_inv rsegs m' -> md_frame md md' ->
        (* [comment removed for export] *)
        (r <> 0 /\ p0_live A' r = Some n /\ (p0_live A r = None /\ p0_live A' p = None) /\
             (forall q, q <> r -> q <> p -> p0_live A' q = p0_live A q) /\
             (forall i, 0 <= i < Z.min n old -> m' (wz (r + i)) = m1 (wz (p + i))) /\
             p0_livebytes A' = p0_livebytes A + n - old /\ p0_nlive A' = p0_nlive A /\
             frame_ok LayoutP0 (p0_owned A) (p0_owned A') (bv_unsigned sp' + 64) 8256 (blk p old) (blk r n) m1 m') ->
        realizes rsegs (mkCfg (HW.mkst (mkR RA (wz (bv_unsigned sp' + 64)) gp tp t0' t1' t2' S0 S1 (wz r) a1' a2' a3' a4' a5' a6' a7'
                                          S2 S3 S4 S5 S6 s7 s8 s9 s10 s11 t3' t4' t5' t6') RA m' (seg_rom rsegs)) md') T) ->
    realizes rsegs (mkCfg (HW.mkst (mkR ra0 sp' gp tp t0 t1 t2 s0 s1 (wz p) a1 a2 a3 a4 a5 a6 a7 (wz (p + old)) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                      (Z_to_bv 64 0x24bbc) m1 (seg_rom rsegs)) md) T.
Proof.
  intros until T. intros AI MI LV PNZ HN NR BYTES NLV TP SPA RAA CEIL SPHI MAP FR K.
  pose proof (ainv_KI _ _ _ AI) as [Hh Hl].
  pose proof (bv_unsigned_in_range _ sp') as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose proof (bv_unsigned_in_range _ a1) as A1R. change (bv_modulus 64) with (2^64) in A1R.
  pose proof alloc_ceiling_val as ACV.
  (first [ pose proof ((p0_live_ok A m1 md p old AI LV)) as dR_3; dand7 dR_3 as OLD0 P16 P4096 PC PIMG PM PNO | pose proof (p0_live_ok A m1 md p old AI LV) as (OLD0 & P16 & P4096 & PC & PIMG & PM & PNO) ]). cbn [al_image_lo al_image_hi LayoutP0] in PIMG.
  rewrite mkst_MS'.
  (* [comment removed for export] *)
  eapply rz_evt; [apply realloc_fb_call_malloc| exact Hh| exact Hl|]. intros ms1 ->. unfold realloc_fb_malloc_pre.
  (* [comment removed for export] *)
  apply (rz_evt_fwd rsegs _ _ md T (malloc_sym_evt _ bvmap_empty (Z_to_bv 32 0) m1) Hh Hl).
  rewrite <- mkst_MS'. change (Z_to_bv 64 malloc_sym) with (al_malloc_pc LayoutP0).
  assert (EA1 : a1 = wz n) by (rewrite <- HN; symmetry; apply Z_to_bv_bv_unsigned).
  eapply (p0_malloc_cpsX (Clg:=Clg) (wz 0x24bcc) sp' gp tp t0 t1 t2 a1 (wz p) a1 a1 a2 a3 a4 a5 a6 a7 (wz (p + old)) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
            m1 md A n T AI MI ltac:(exists p, old; exact LV) EA1 ltac:(lia) BYTES NLV TP SPA).
  { rewrite unsigned_lit by lia. reflexivity. }
  { exact CEIL. }
  { exact MAP. }
  intros t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' r A2 m2 md2 AI2 MI2 FRd RES FRM.
  pose proof (ainv_KI _ _ _ AI2) as [Hh2 Hl2].
  assert (RET : ret_pc RA = RA).
  { pose proof (bv_unsigned_in_range _ RA) as RAR. change (bv_modulus 64) with (2^64) in RAR.
    rewrite <- (definitions.Z_to_bv_bv_unsigned 64 RA) at 1. rewrite ret_pc_even; [apply definitions.Z_to_bv_bv_unsigned| lia| ].
    Z.div_mod_to_equations. lia. }
  unfold AllocSpec.MALLOC_STACK in FRM. rewrite mkst_MS'.
  assert (NBLK : forall a, bv_unsigned sp' - 8192 <= a -> ~ blk r n a).
  { intros a Ha [Rnz Hin]. destruct RES as (_ & _ & pb & junk' & EL & _).
    assert (LV2 : p0_live A2 r = Some n).
    { unfold p0_live. rewrite EL. unfold find_blk. cbn [find blk_addr fst snd]. rewrite Z.eqb_refl. reflexivity. }
    (first [ pose proof ((p0_live_ok A2 m2 md2 r n AI2 LV2)) as dR_4; dand5 dR_4 as _ _ _ RC _ | pose proof (p0_live_ok A2 m2 md2 r n AI2 LV2) as (_ & _ & _ & RC & _) ]). (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv). lia. }
  assert (FR2 : rw_cells rsegs m2 (bv_unsigned sp') [C8 S6; C8 S5; C8 S4; C8 S3; C8 S2; C8 S1; C8 S0; C8 RA]).
  { eapply rw_cells_agree'; [exact FR|]. intros x Hx. cbn [cells_size csize Nat.add] in Hx.
    pose proof (bv_unsigned_in_range _ x) as XR. change (bv_modulus 64) with (2^64) in XR.
    rewrite <- (definitions.Z_to_bv_bv_unsigned 64 x). destruct FRM as (F1 & _).
    apply F1; [lia| intros O; pose proof (p0_owned_below _ _ _ _ AI O); (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv); lia
             | intros O; pose proof (p0_owned_below _ _ _ _ AI2 O); (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv); lia
             | lia| rewrite errno_p0; unfold PERRNO; lia| intros []| apply NBLK; lia]. }
  assert (TOP2 : mapped m2 (bv_unsigned sp') 64).
  { intros i Hi. destruct FR2 as [_ (_ & _ & W)]. cbn [cells_size csize Nat.add] in W.
    specialize (W i ltac:(lia)). unfold MRep.wz. rewrite p0_wview_overlay in W by (unfold wa; rewrite unsigned_lit; (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv); lia). exact W. }
  (* [comment removed for export] *)
  assert (OLDEQ : forall i, 0 <= i < old -> m2 (wz (p + i)) = m1 (wz (p + i))).
  { intros i Hi. destruct FRM as (F1 & _). apply F1; [(let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv); lia| apply PNO; lia| | (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv); lia
      | rewrite errno_p0; unfold PERRNO; lia| intros []|].
    - destruct RES as (_ & _ & pb & junk' & EL & _).
      + intros [S|[HZ NI]]; [apply (PNO i Hi); left; exact S| apply (PNO i Hi); right; split; [exact HZ|]].
        ((first [ intro dR_14; dex1 dR_14 as b; destruct dR_14 as [Hb Hab] | intro dR_14; dand3 dR_14 as b Hb Hab | intros (b & Hb & Hab) ])). apply NI. exists b. split; [rewrite EL; right; exact Hb| exact Hab].
    - intros [Rnz Hin]. destruct RES as (_ & NL & pb & junk' & EL & _).
      assert (LV2 : p0_live A2 r = Some n).
      { unfold p0_live. rewrite EL. unfold find_blk. cbn [find blk_addr fst snd]. rewrite Z.eqb_refl. reflexivity. }
      assert (LVp2 : p0_live A2 p = Some old).
      { unfold p0_live. rewrite EL. unfold find_blk. cbn [find blk_addr fst snd].
        destruct (Z.eqb_spec r p) as [E|NE]; [exfalso; subst r; rewrite LV in NL; discriminate|]. exact LV. }
      destruct (p0_live_disjoint A2 m2 md2 r n p old AI2 LV2 LVp2 ltac:(intros E; subst r; rewrite LV in NL; discriminate)); lia. }
  destruct RES as (Rnz & NL & pb & junk & EL & RWJ & CLS2).
  (* [comment removed for export] *)
  {
    assert (LV2 : p0_live A2 r = Some n).
    { unfold p0_live. rewrite EL. unfold find_blk. cbn [find blk_addr fst snd]. rewrite Z.eqb_refl. reflexivity. }
    assert (RP : r <> p) by (intros E; subst r; rewrite LV in NL; discriminate).
    assert (LVp2 : p0_live A2 p = Some old).
    { unfold p0_live. rewrite EL. unfold find_blk. cbn [find blk_addr fst snd].
      destruct (Z.eqb_spec r p) as [E|NE]; [exfalso; exact (RP E)|]. exact LV. }
    (first [ pose proof ((p0_live_ok A2 m2 md2 r n AI2 LV2)) as dR_5; dand7 dR_5 as _ R16 R4096 RC RIMG RM RNO | pose proof (p0_live_ok A2 m2 md2 r n AI2 LV2) as (_ & R16 & R4096 & RC & RIMG & RM & RNO) ]). cbn [al_image_lo al_image_hi LayoutP0] in RIMG.
    (first [ pose proof ((p0_live_ok A2 m2 md2 p old AI2 LVp2)) as dR_6; dand7 dR_6 as _ _ _ _ _ PM2 PNO2 | pose proof (p0_live_ok A2 m2 md2 p old AI2 LVp2) as (_ & _ & _ & _ & _ & PM2 & PNO2) ]).
    pose proof (p0_live_disjoint A2 m2 md2 r n p old AI2 LV2 LVp2 RP) as DISJ.
    (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv).
    set (k := Z.min n old).
    assert (K0 : 0 <= k <= n /\ k <= old) by (subst k; lia).
    (* [comment removed for export] *)
    assert (WRp : wr_at rsegs m2 p k).
    { split; [lia|]. split; [lia|]. intros i Hi. unfold wa. rewrite p0_wview_overlay by (rewrite unsigned_lit; lia). apply PM2. lia. }
    (first [ pose proof ((wr_at_bytes_exist m2 p k WRp ltac:(lia) ltac:(lia))) as dR_7; dex1 dR_7 as src; destruct dR_7 as [LEN SRC] | pose proof ((wr_at_bytes_exist m2 p k WRp ltac:(lia) ltac:(lia))) as dR_7; dand3 dR_7 as src LEN SRC | destruct (wr_at_bytes_exist m2 p k WRp ltac:(lia) ltac:(lia)) as (src & LEN & SRC) ]).
    pose proof (rw_cells_split_CB rsegs m2 r [] (Z.to_nat n) junk [] [Z.to_nat k; Z.to_nat n - Z.to_nat k]%nat RWJ ltac:(cbn; lia)) as RWJ2.
    cbn [mk_CB_cells app] in RWJ2.
    apply (proj1 (rw_cells_app rsegs m2 r [CB (Z.to_nat k) (take (Z.to_nat k) junk)] _)) in RWJ2. destruct RWJ2 as [DST _].
    (* [comment removed for export] *)
    eapply rz_evt; [| exact Hh2| exact Hl2|].
    { eapply (realloc_fb_after_malloc_copy _ _ gp tp t0' t1' t2' a1 (wz p) (wz r) a1' a2' a3' a4' a5' a6' a7' s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6' _ _ m2 r p n old);
        [rewrite unsigned_lit; lia| exact Rnz| rewrite unsigned_lit; lia| rewrite EA1; rewrite unsigned_lit; lia| lia| lia]. }
    intros ms2 ->. unfold realloc_fb_memcpy_pre. fold k.
    (* [comment removed for export] *)
    eapply rz_evt; [| exact Hh2| exact Hl2|].
    { eapply (memcpy_spec (wz 0x24bec) sp' gp tp t0' t1' t2' (wz r) (wz p) (wz r) (wz p) (wz k) a3' a4' a5' a6' a7' (wz (p + old)) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6' _ _ m2 src (take (Z.to_nat k) junk));
        rewrite ?unsigned_lit by lia; [exact SRC| exact LEN| exact DST| lia| exact MI2]. }
    (intros ms3; (first [ intro dR_15; dex15 dR_15 as u0 u1 u2 v1 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6 m3; dand6 dR_15 as -> MU3 WM3 MI3 DST3 SRC3 | intro dR_15; dand21 dR_15 as u0 u1 u2 v1 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6 m3 -> MU3 WM3 MI3 DST3 SRC3 | intros (u0 & u1 & u2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & m3 & -> & MU3 & WM3 & MI3 & DST3 & SRC3) ])).
    rewrite !unsigned_lit in MU3 by lia. rewrite !unsigned_lit in DST3 by lia. rewrite !unsigned_lit in SRC3 by lia.
    replace (ret_pc (wz 0x24bec)) with (Z_to_bv 64 0x24bec) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    assert (AG3 : forall a, 0 <= a < 2^64 -> ~ (r <= a < r + k) -> m3 (Z_to_bv 64 a) = m2 (Z_to_bv 64 a)).
    { intros a Ha OUT. apply MU3. cbn. rewrite unsigned_lit by lia. lia. }
    assert (IN3 : forall i, 0 <= i < k -> m3 (Z_to_bv 64 (r + i)) = nth_error src (Z.to_nat i)).
    { intros i Hi. destruct DST3 as [[_ (_ & _ & B)] _]. cbn [cells_bytes cbytes app] in B. rewrite app_nil_r in B.
      specialize (B (Z.to_nat i) ltac:(lia)). rewrite Z2Nat.id in B by lia.
      rewrite p0_mrd_overlay in B by (unfold wa; rewrite unsigned_lit; lia). exact B. }
    assert (SRCi : forall i, 0 <= i < k -> m2 (Z_to_bv 64 (p + i)) = nth_error src (Z.to_nat i)).
    { intros i Hi. (first [ dand3 SRC as _ _ B | destruct SRC as (_ & _ & B) ]). specialize (B (Z.to_nat i) ltac:(lia)). rewrite Z2Nat.id in B by lia.
      rewrite p0_mrd_overlay in B by (unfold wa; rewrite unsigned_lit; lia). exact B. }
    assert (MP3 : forall a, r <= a < r + n -> m3 (Z_to_bv 64 a) <> None).
    { intros a Ha. destruct (Z_lt_le_dec a (r + k)).
      - replace a with (r + (a - r)) by lia. rewrite IN3 by lia. intros E. apply nth_error_None in E. lia.
      - rewrite AG3 by lia. replace a with (r + (a - r)) by lia. apply RM. lia. }
    pose proof (p0_ainv_block_write (Clg:=Clg) A2 m2 m3 md2 r n AI2 LV2 ltac:(intros a Ha OUT; apply AG3; lia) MP3) as AI3.
    assert (FR3 : rw_cells rsegs m3 (bv_unsigned sp') [C8 S6; C8 S5; C8 S4; C8 S3; C8 S2; C8 S1; C8 S0; C8 RA]).
    { eapply rw_cells_agree'; [exact FR2|]. intros x Hx. cbn [cells_size csize Nat.add] in Hx.
      pose proof (bv_unsigned_in_range _ x) as XR. change (bv_modulus 64) with (2^64) in XR.
      rewrite <- (definitions.Z_to_bv_bv_unsigned 64 x). apply AG3; lia. }
    assert (MAP3 : mapped m3 (bv_unsigned sp' - 8192) 8192).
    { intros i Hi. unfold MRep.wz. rewrite AG3 by lia. (first [ dand4 FRM as _ _ F3 _ | destruct FRM as (_ & _ & F3 & _) ]). apply F3. exact Hi. }
    (* [comment removed for export] *)
    eapply rz_evt; [apply realloc_fb_after_memcpy| exact Hh2| exact Hl2|]. intros ms4 ->. unfold realloc_fb_free_pre.
    apply (rz_evt_fwd rsegs _ _ md2 T (free_sym_evt _ bvmap_empty (Z_to_bv 32 0) m3) Hh2 Hl2).
    rewrite <- mkst_MS'. change (Z_to_bv 64 free_sym) with (al_free_pc LayoutP0).
    eapply (p0_free_cps (wz 0x24bf4) sp' gp tp u0 u1 u2 (wz r) (wz p) (wz p) v1 v2 v3 v4 v5 v6 v7 (wz (p + old)) s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6
              m3 md2 A2 p old T AI3 MI3 eq_refl (or_intror LVp2) TP SPA).
    { rewrite unsigned_lit by lia. reflexivity. }
    { exact CEIL. }
    { exact MAP3. }
    intros w0 w1 w2 x0 x1 x2 x3 x4 x5 x6 x7 w3 w4 w5 w6 A3 m4 md3 AI4 MI4 FRd3 NLp EQL DB3 DN3 ERRQ FRM3.
    pose proof (ainv_KI _ _ _ AI4) as [Hh4 Hl4]. unfold AllocSpec.FREE_STACK in FRM3. rewrite mkst_MS'.
    assert (LV4 : p0_live A3 r = Some n) by (rewrite (EQL r RP); exact LV2).
    (first [ pose proof ((p0_live_ok A3 m4 md3 r n AI4 LV4)) as dR_10; dand7 dR_10 as _ _ _ _ _ RM4 RNO4 | pose proof (p0_live_ok A3 m4 md3 r n AI4 LV4) as (_ & _ & _ & _ & _ & RM4 & RNO4) ]).
    assert (FR4 : rw_cells rsegs m4 (bv_unsigned sp') [C8 S6; C8 S5; C8 S4; C8 S3; C8 S2; C8 S1; C8 S0; C8 RA]).
    { eapply rw_cells_agree'; [exact FR3|]. intros x Hx. cbn [cells_size csize Nat.add] in Hx.
      pose proof (bv_unsigned_in_range _ x) as XR. change (bv_modulus 64) with (2^64) in XR.
      rewrite <- (definitions.Z_to_bv_bv_unsigned 64 x). destruct FRM3 as (F1 & _).
      apply F1; [lia| intros O; pose proof (p0_owned_below _ _ _ _ AI3 O); (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv); lia
               | intros O; pose proof (p0_owned_below _ _ _ _ AI4 O); (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv); lia
               | lia| rewrite errno_p0; unfold PERRNO; lia| intros [_ ?]; lia| intros []]. }
    (* [comment removed for export] *)
    eapply rz_evt; [| exact Hh4| exact Hl4|].
    { eapply (realloc_fb_after_free _ _ gp tp w0 w1 w2 (wz r) (wz p) x0 x1 x2 x3 x4 x5 x6 x7 (wz (p + old)) s3 s4 s5 s6 s7 s8 s9 s10 s11 w3 w4 w5 w6 _ _ m4 RA S0 S1 S2 S3 S4 S5 S6);
        [exact SPHI| exact FR4]. }
    intros ms5 ->. unfold realloc_epilogue_post, MRep.wz. rewrite RET, <- mkst_MS'.
    apply (K w0 w1 w2 x1 x2 x3 x4 x5 x6 x7 w3 w4 w5 w6 r A3 m4 md3 AI4 MI4 (md_frame_trans _ _ _ FRd FRd3)).
    split; [exact Rnz|]. split; [exact LV4|]. split; [split; [exact NL| exact NLp]|]. split.
    { intros q Hq Hqp. rewrite (EQL q Hqp). unfold p0_live. rewrite EL. unfold find_blk. cbn [find blk_addr fst snd].
      destruct (Z.eqb_spec r q); [lia| reflexivity]. }
    split.
    { intros i Hi. fold k in Hi. unfold MRep.wz. rewrite <- (OLDEQ i) by lia. rewrite SRCi by lia. rewrite <- IN3 by lia.
      destruct FRM3 as (F1 & _). apply F1; [lia| | | lia| rewrite errno_p0; unfold PERRNO; lia| intros [_ ?]; lia| intros []].
      - pose proof (RNO (i)) as X. intros O. apply (RNO i); [lia| exact O].
      - intros O. apply (RNO4 i); [lia| exact O]. }
    split.
    { rewrite DB3. unfold p0_livebytes. rewrite EL. rewrite lb_bytes_cons. cbn [blk_size snd]. lia. }
    split.
    { rewrite DN3. unfold p0_nlive. rewrite EL. rewrite zlen_cons. destruct (Z.eqb_spec p 0); lia. }
    apply (frame_ok_fb_compose (p0_owned A) (p0_owned A2) (p0_owned A3) (bv_unsigned sp') p old r n k m1 m2 m3 m4 FRM Rnz ltac:(lia) AG3).
    + intros a Ha Hm2. destruct (Classical_Prop.classic (r <= a < r + k)) as [IN|OUT]; [apply MP3; lia| rewrite AG3; auto].
    + exact FRM3.
    + intros i Hi. destruct FR4 as [_ (_ & _ & W)]. cbn [cells_size csize Nat.add] in W.
      specialize (W i ltac:(lia)). unfold MRep.wz. rewrite p0_wview_overlay in W by (unfold wa; rewrite unsigned_lit; (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv); lia). exact W.
    + intros a O. pose proof (p0_owned_below _ _ _ _ AI O) as R. rewrite errno_p0. split; [(let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv); lia|].
      unfold PERRNO. intros E. destruct O as [S|[HZ _]]; [unfold p0_static in S; lia|]. apply (proj1 (heap_zone_p0 a)) in HZ. lia. }
Qed.

End CEIL.
