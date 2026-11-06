(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib SegsA0.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzTac BzTac2 BzArr BzCMem BzCStream BzCState BzCMtf BzArrD CmpMem CmpCut CmpCutMtf BzCFactsGm CmpFsKit CmpHmKit CmpFsKit0 AsanKit AsanCut.
From Stdlib Require Lia. Unset Lia Cache.
Import ListNotations. Open Scope bv_scope.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzParams.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpCut6.   (* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpLiaP.   (* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StepFast.
Local Ltac Lib.Step.step_core segs R F pc fc rv m ro ::= StepFast.sf_step_core.
Local Ltac Lib.Step.zstep ::= StepFast.sf_zstep.
#[local] Ltac2 Set StepFast.sf_foldgoal := Ltac2.Init.true.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StoreFast StoreFastZ StoreFastC.
Local Ltac Lib.Step.transport_chunks segs m a bs ::= StoreFast.transport_chunks_fast segs m a bs.
Local Ltac Lib.Tac.footprint_after_store segs m a bs ::= StoreFast.footprint_after_store_fast segs m a bs.
Local Ltac Lib.Step.mem_after_store ::= first [ StoreFastC.mem_after_store_fastzc | StoreFastZ.mem_after_store_fastz | StoreFast.mem_after_store_fast ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpFast.
Local Ltac BzTac.mlia ::= CmpFast.mlia_fast.
Local Ltac Lib.ZBridge.mlia ::= CmpFast.mlia_fast.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require RangeFast RangeFastEnv.
#[local] Ltac2 Set RangeFast.RF.rc_atom_facts := RangeFastEnv.env_atom_facts.
Local Ltac Lib.ZBridge.flia ::= RangeFast.rc_decide ltac:(first [ assumption | Lib.ZBridge.slim; lia | lia ]).
Local Ltac Lib.ZBridge.mlia ::= RangeFast.rc_decide ltac:(CmpFast.mlia_fast).
Local Ltac Bz.BzTac.mlia ::= RangeFast.rc_decide ltac:(CmpFast.mlia_fast).
#[local] Ltac2 Set RangeFast.RF.rc_or_boxes := fun () => [constr:(@id); constr:(Lib.StoreFast.sf_hide)].
Local Ltac Lib.StoreFast.tlia ::= first [ Zify.zify; xlia zchecker | RangeFast.rc_prune_lia | Lib.StoreFast.sf_unhide; first [ Lib.StoreFast.zify_prune_neg; Zify.zify; xlia zchecker | Lib.StoreFast.zify_prune_plain; Zify.zify; xlia zchecker | lia ] ].
Local Ltac Bz.BzSepTac.tlia2 ::= first [ RangeFast.rc_prune_lia | Lib.StoreFast.sf_unhide; Bz.BzSepTac.unhide_disj; first [ Lib.StoreFast.zify_prune_neg; Zify.zify; xlia zchecker | Lib.StoreFast.zify_prune_plain; Zify.zify; xlia zchecker | Zify.zify; xlia zchecker ] ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpLiaC.
Local Ltac lia ::= CmpLiaC.lia_c.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpSepV.
Local Ltac Lib.Step.slia ::= CmpSepV.slia_v.
Local Ltac Lib.StoreFast.tslia ::= CmpSepV.tslia_v.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpStEq.
Local Ltac BzTac.st_eq ::= CmpStEq.st_eq_fast.
Local Ltac simpl_arr_sizes ::= CmpFast.sas10_all.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.
(* [comment removed for export] *)
Local Ltac Lib.Step.solve_load ::= AsanKit.asan_solve_load.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.A Require Import Shadow.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import A0_cmp_fsV A0_cmp_msV A0_cmp_cbV A0_cmp_gmA.
Local Ltac AsanKit.a_norm ::= AsanKit.sh_fold.
Section ACeilS1. Context {BZP : BzParams} {ACEIL__ : ACeil}.

Ltac lit_store :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 8 ?v)) _) => change (Z_to_le_bytes 8 v) with (le8 (Z_to_bv 64 v)); mem_after_store
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 4 ?v)) _) => change (Z_to_le_bytes 4 v) with (le4 (Z_to_bv 64 v)); mem_after_store
  | _ => idtac
  end.
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma repeat_zero_nth' : forall n k (b : byte), nth_error (repeat (Z_to_bv 8 0) n) k = Some b -> b = Z_to_bv 8 0.
Proof.
  intros n k b H. destruct (Nat.lt_ge_cases k n).
  - rewrite nth_error_repeat in H by lia. congruence.
  - rewrite (proj2 (nth_error_None _ _)) in H by (rewrite repeat_length; lia). discriminate.
Qed.
Lemma mtf_before_memset : forall segs m P p Jm N k,
  u32arr segs m P (ovw p Jm N) -> (0 <= k <= N)%Z ->
  rw_cells segs m P [CB (Z.to_nat (4 * k)) (u32s (firstn (Z.to_nat k) (ovw p Jm N)))] /\
  u32arr segs m (P + 4 * k)%Z (skipn (Z.to_nat k) (ovw p Jm N)).
Proof.
  intros segs m P p Jm N k H Hk. pose proof (ovw_length_nat p Jm N) as L.
  rewrite <- (firstn_skipn (Z.to_nat k) (ovw p Jm N)) in H. apply (proj1 (u32arr_app segs m P _ _)) in H. destruct H as [H1 H2].
  rewrite length_firstn, L in H2. replace (P + 4 * Z.of_nat (Nat.min (Z.to_nat k) (Z.to_nat N)))%Z with (P + 4 * k)%Z in H2 by lia.
  split; [|exact H2].
  apply (proj1 (u32arr_u8arr' segs m P _)) in H1. apply (rw_cells_of_u8arr segs) in H1.
  rewrite u32s_length, length_firstn, L in H1. replace (4 * Nat.min (Z.to_nat k) (Z.to_nat N))%nat with (Z.to_nat (4 * k)) in H1 by lia. exact H1.
Qed.
Lemma ovw_zfill0_split : forall p Jm N k, (0 <= k <= N)%Z ->
  ovw (zfill0 (Z.to_nat k) p 0) Jm N = zw32 znew k ++ skipn (Z.to_nat k) (ovw p Jm N).
Proof.
  intros p Jm N k Hk. apply nth_error_ext. intros i.
  pose proof (ovw_length_nat p Jm N) as L. pose proof (zw32_length_nat znew k) as Lz.
  destruct (Nat.lt_ge_cases i (Z.to_nat N)) as [Hi|Hi].
  2:{ rewrite (proj2 (nth_error_None _ _)) by (rewrite ovw_length_nat; lia). symmetry. apply (proj2 (nth_error_None _ _)).
      rewrite length_app, Lz, length_skipn, L. lia. }
  replace i with (Z.to_nat (Z.of_nat i)) by lia.
  rewrite ovw_nth_raw by lia. rewrite zfill0_def, zfill0_get.
  destruct (Nat.lt_ge_cases i (Z.to_nat k)) as [H1|H1].
  - rewrite nth_error_app1 by lia. rewrite zw32_nth by lia. rewrite zget_znew.
    replace ((0 <=? Z.of_nat i) && (Z.of_nat i <? 0 + Z.of_nat (Z.to_nat k)))%Z%bool with true
      by (symmetry; apply Bool.andb_true_iff; split; [apply Z.leb_le| apply Z.ltb_lt]; lia).
    reflexivity.
  - rewrite nth_error_app2 by lia. rewrite Lz, nth_error_skipn.
    replace (Z.to_nat k + (Z.to_nat (Z.of_nat i) - Z.to_nat k))%nat with (Z.to_nat (Z.of_nat i)) by lia.
    rewrite ovw_nth_raw by lia.
    replace ((0 <=? Z.of_nat i) && (Z.of_nat i <? 0 + Z.of_nat (Z.to_nat k)))%Z%bool with false
      by (symmetry; apply Bool.andb_false_iff; right; apply Z.ltb_ge; lia).
    reflexivity.
Qed.
Lemma mtf_after_memset : forall segs m P p Jm N k,
  rw_cells segs m P [CB (Z.to_nat (4 * k)) (repeat (Z_to_bv 8 0) (Z.to_nat (4 * k)))] ->
  u32arr segs m (P + 4 * k)%Z (skipn (Z.to_nat k) (ovw p Jm N)) -> (0 <= k <= N)%Z ->
  u32arr segs m P (ovw (zfill0 (Z.to_nat k) p 0) Jm N).
Proof.
  intros segs m P p Jm N k H1 H2 Hk. rewrite (ovw_zfill0_split p Jm N k Hk).
  apply (proj2 (u32arr_app segs m P _ _)). split.
  - eapply (zw32_init segs m P k _ H1); [lia| apply repeat_zero_nth'].
  - rewrite zw32_length_nat. replace (P + 4 * Z.of_nat (Z.to_nat k))%Z with (P + 4 * k)%Z by lia. exact H2.
Qed.

Section A0CBG1.
  Variable X : cbenv. Variable Y : acenv. Variables (g : eg) (e : est). Variable Q : machine_state -> Prop.
  Hypothesis XOK : cbenv_ok X. Hypothesis YOK : acenv_ok X Y.
  Hypothesis AE : sanchor (c_E (ce_cx X)) (ac_SHE Y).
  Hypothesis GF : gm_facts e.
  Notation cx := (ce_cx X).
  Notation usp := (bv_unsigned (ce_sp X)). Notation P := (ac_P Y). Notation FB := (ac_FB Y). Notation SHF := (ac_SHF Y). Notation SHE := (ac_SHE Y).
  Notation E := (c_E cx). Notation A1 := (c_A1 cx). Notation A2 := (c_A2 cx). Notation J := (c_J cx).
  Notation gp := (ce_gp X). Notation tp := (ce_tp X). Notation F := (ce_F X). Notation fc := (ce_fc X). Notation lo := (ce_lo X).
  Notation cSB := (Z_to_bv 64 2147450880).
  Notation nInUse := (gp_nInUse e). Notation unseq := (gp_unseq e).
  Definition cbG1_W : list (Z * Z) := [(E, E + 640); (P, P + 120)]%Z.

  Notation RW ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 :=
    (mkR ra (Z_to_bv 64 P) gp tp t0 t1 t2 (ce_sp X) (Z_to_bv 64 P) a0 a1 a2 a3 a4 a5 a6 a7
         s2 cSB (Z_to_bv 64 E) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6).
  Notation sl3 sl := (set40 (set24 (set72 (set32 (set16 (set8 sl (Z_to_bv 64 (E + 652))) (il_w (ce_il X))) (Z_to_bv 64 FB)) (Z_to_bv 64 A1)) (Z_to_bv 64 FB)) (Z_to_bv 64 nInUse)).

  #[local] Transparent gp_maps gp_nInUse gp_unseq.
  Lemma gp_maps_surj : forall e0 uns k, mk_maps 256 (e_inUse e0) (e_unseqToSeq e0) 0 0 = (uns, k) -> uns = gp_unseq e0 /\ k = gp_nInUse e0.
  Proof. intros e0 uns k H. unfold gp_unseq, gp_nInUse, gp_maps. rewrite H. split; reflexivity. Qed.
  #[local] Opaque gp_maps gp_nInUse gp_unseq.

  Lemma A0_cb_G1 : forall (m : word -> option byte) (sl : cbsl)
      (ra t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s5 t3 t4 t5 t6 : word),
    rw_cells a0segs m E (EHEAD1 cx g e) -> u8arr a0segs m (E + 128) (ovb (e_inUse e) (jseg J 128 256) 256) ->
    u8arr a0segs m (E + 384) (ovb (e_unseqToSeq e) (jseg J 384 256) 256) ->
    rw_cells a0segs m P (cbsl_cells sl) -> mem_inv a0segs m ->
    shzW a0segs cbG1_W m E (E + ESTATE_SIZE) ->
    (forall m' (y5 y6 y7 y11 y13 y14 y15 y16 y17 y28 y29 y31 : word),
      rw_cells a0segs m' E (EHEAD1n cx g e nInUse) -> u8arr a0segs m' (E + 128) (ovb (e_inUse e) (jseg J 128 256) 256) ->
      u8arr a0segs m' (E + 384) (ovb unseq (jseg J 384 256) 256) ->
      rw_cells a0segs m' P (cbsl_cells (sl3 sl)) -> mem_inv a0segs m' -> munch cbG1_W m m' -> wmono a0segs m m' ->
      evt a0segs Q (MS (RW (Z_to_bv 64 0x891c8) y5 y6 y7 (Z_to_bv 64 (E + 672)) (Z_to_bv 64 0) (Z_to_bv 64 (4 * (nInUse + 2))) y13 y14 y15 y16 y17
                           (Z_to_bv 64 A1) (Z_to_bv 64 (E + 672)) (Z_to_bv 64 SHF) (Z_to_bv 64 (FB + 32)) (Z_to_bv 64 (E + 384)) (Z_to_bv 64 (E + 644)) (Z_to_bv 64 (E + 640)) (Z_to_bv 64 A2)
                           y28 y29 t5 y31)
                       F (Z_to_bv 64 0x52ea0) fc None m' (seg_rom a0segs))) ->
    evt a0segs Q (MS (RW ra t0 t1 t2 (Z_to_bv 64 (E + 56)) a1 a2 a3 a4 a5 a6 a7
                         (il_w (ce_il X)) s5 (Z_to_bv 64 SHF) (Z_to_bv 64 FB) (Z_to_bv 64 FB) (Z_to_bv 64 (E + 644)) (Z_to_bv 64 (E + 640)) (Z_to_bv 64 (E + 652)) t3 t4 t5 t6)
                     F (Z_to_bv 64 0x8908c) fc None m (seg_rom a0segs)).
  Proof.
    intros m sl ra t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s5 t3 t4 t5 t6 EH1 INU UNS SL MI SHe K.
    cbenv_open XOK. acenv_open YOK. cb_ranges CX.
    pose proof GF as GF'. cps_destruct GF' as (BOK1 & BOK2 & NB & DEFI & IU01 & F5 & M1).
    cps_destruct (maps_facts e GF) as (NI & UB & UJ).
    pose proof (jseg_length J 128 256 ltac:(lia) ltac:(lia) ltac:(lia)) as LJ1.
    pose proof (jseg_length J 384 256 ltac:(lia) ltac:(lia) ltac:(lia)) as LJ2.
    pose proof (ovb_length (e_inUse e) (jseg J 128 256) 256 ltac:(lia)) as LI. pose proof (ovb_length (e_unseqToSeq e) (jseg J 384 256) 256 ltac:(lia)) as LU.
    pose proof (munch_refl cbG1_W m) as MU. pose proof (wmono_refl a0segs m) as WM. unfold cbG1_W, ESTATE_SIZE in MU, SHe.
    unfold EHEAD1 in EH1. unfold cbsl_cells in SL.
    (* [comment removed for export] *)
    arun_to 0x89100%Z. sh_norm.
    (* [comment removed for export] *)
    wstep; lit_store.
    (* [comment removed for export] *)
    arun_to 0x89118%Z.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m1 end.
    assert (EH1n : rw_cells a0segs m1 E (EHEAD1n cx g e 0)) by (unfold EHEAD1n, EHEAD1; cbn [removelast app]; exact EH1). clear EH1.
    enter_with (A0_gm_maps cx g e Q (Z_to_bv 64 P) gp tp (ce_sp X) (Z_to_bv 64 SHF) (Z_to_bv 64 (E + 644)) (Z_to_bv 64 (E + 640)) F fc P SHE CX SEP GF AE
                  256%nat 0 0 (e_unseqToSeq e) m1 m1);
      [st_eq| lia| lia| lia| lia| exact EH1n| exact INU| exact UNS| exact MI| apply munch_refl| apply wmono_refl
      | eapply (shzW_sub a0segs cbG1_W _ m m1); [exact SHe| exact MU| unfold cbG1_W; a_sub_fp| lia| unfold ESTATE_SIZE; lia] |].
    intros uns' k' m2 xa1 xa2 xa5 xa6 xa7 MK Hk' EH1_1 INU1 UNS1 MI1 MU1 WM1.
    clear EH1n INU UNS MI. transport_after_call a0segs m1 m2 MU1 WM1. clear MU1 WM1.
    destruct (gp_maps_surj e _ _ MK) as [-> ->]. clear MK Hk'.
    unfold EHEAD1n, EHEAD1 in EH1_1. cbn [removelast app] in EH1_1.
    (* [comment removed for export] *)
    arun_to 0x891ac%Z. try rewrite (sx32_of_Z nInUse) by lia.
    (* [comment removed for export] *)
    wstep; if_cases Km; zify_cond_z Km; [exfalso; lia|].
    (* [comment removed for export] *)
    arun_to 0x52ea0%Z.
    replace ((nInUse + 2) * 4294967296 / 1073741824)%Z with (4 * (nInUse + 2))%Z.
    2:{ replace ((nInUse + 2) * 4294967296)%Z with ((4 * (nInUse + 2)) * 1073741824)%Z by lia. rewrite Z.div_mul by lia. reflexivity. }
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      enter_with (K mm _ _ _ _ _ _ _ _ _ _ _ _) end;
      [st_eq| unfold EHEAD1n, EHEAD1; cbn [removelast app]; exact EH1_1| exact INU1| exact UNS1| sl_cbn; exact SL| exact MI1| unfold cbG1_W; exact MU| exact WM].
  Unshelve. all: try exact (Z_to_bv 64 0).
  Qed.
End A0CBG1.

End ACeilS1.
