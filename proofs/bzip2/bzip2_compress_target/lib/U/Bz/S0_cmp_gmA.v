(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib Require Import SegsS0.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzTac BzTac2. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzArr BzCMem BzCStream BzCState BzCMtf BzArrD CmpMem. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import CmpCut CmpCut0 CmpCutMtf CmpCutMtf0. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzCFactsGm. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import CmpFsKit0 CmpHmKit.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import UKit.
From Stdlib Require Lia. Unset Lia Cache.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeilTac.
Import ListNotations. Open Scope bv_scope.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzParams.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import CmpCut6.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpLiaP.   (* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StepFast.
Local Ltac Lib.Step.step_core segs R F pc fc rv m ro ::= StepFast.sf_step_core.
Local Ltac Lib.Step.zstep ::= StepFast.sf_zstep.
#[local] Ltac2 Set StepFast.sf_foldgoal := Ltac2.Init.true.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StoreFast StoreFastZ StoreFastC.
Local Ltac Lib.Step.transport_chunks segs m a bs ::= StoreFast.transport_chunks_fast segs m a bs.
Local Ltac Lib.Tac.footprint_after_store segs m a bs ::= StoreFast.footprint_after_store_fast segs m a bs.
Local Ltac Lib.Step.mem_after_store ::= first [ StoreFastC.mem_after_store_fastzc | StoreFastZ.mem_after_store_fastz | StoreFast.mem_after_store_fast ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpFast.   (* [comment removed for export] *)
Local Ltac BzTac.mlia ::= CmpFast.mlia_fast.   (* [comment removed for export] *)
Local Ltac Lib.ZBridge.mlia ::= CmpFast.mlia_fast.   (* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib Require RangeFast RangeFastEnv.
#[local] Ltac2 Set RangeFast.RF.rc_atom_facts := RangeFastEnv.env_atom_facts.
Local Ltac Lib.ZBridge.flia ::= RangeFast.rc_decide ltac:(first [ assumption | Lib.ZBridge.slim; lia | lia ]).
Local Ltac Lib.ZBridge.mlia ::= RangeFast.rc_decide ltac:(CmpFast.mlia_fast).
Local Ltac Bz.BzTac.mlia ::= RangeFast.rc_decide ltac:(CmpFast.mlia_fast).
#[local] Ltac2 Set RangeFast.RF.rc_or_boxes := fun () => [constr:(@id); constr:(Lib.StoreFast.sf_hide)].
Local Ltac Lib.StoreFast.tlia ::= first [ Zify.zify; xlia zchecker | RangeFast.rc_prune_lia | Lib.StoreFast.sf_unhide; first [ Lib.StoreFast.zify_prune_neg; Zify.zify; xlia zchecker | Lib.StoreFast.zify_prune_plain; Zify.zify; xlia zchecker | lia ] ].
Local Ltac Bz.BzSepTac.tlia2 ::= first [ RangeFast.rc_prune_lia | Lib.StoreFast.sf_unhide; Bz.BzSepTac.unhide_disj; first [ Lib.StoreFast.zify_prune_neg; Zify.zify; xlia zchecker | Lib.StoreFast.zify_prune_plain; Zify.zify; xlia zchecker | Zify.zify; xlia zchecker ] ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpLiaC.   (* [comment removed for export] *)
Local Ltac lia ::= CmpLiaC.lia_c.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpSepV.   (* [comment removed for export] *)
Local Ltac Lib.Step.slia ::= CmpSepV.slia_v.   (* [comment removed for export] *)
Local Ltac Lib.StoreFast.tslia ::= CmpSepV.tslia_v.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require CmpStEq.   (* [comment removed for export] *)
Local Ltac BzTac.st_eq ::= CmpStEq.st_eq_fast.   (* [comment removed for export] *)
Local Ltac simpl_arr_sizes ::= CmpFast.sas10_all.   (* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.
Section ACeilS1. Context {BZP : BzParams} {ACEIL__ : ACeil}.


Section S0GM.
  Variables (cx : cctx) (g : eg) (e : est) (Q : machine_state -> Prop).
  Variables (sp gp tp : word) (F : bvmap 5 word) (fc : bv 32).
  Hypothesis CX : cctx_ok cx. Hypothesis SEP : cctx_sep cx. Hypothesis GF : gm_facts e.
  Notation E := (c_E cx). Notation A1 := (c_A1 cx). Notation A2 := (c_A2 cx). Notation J := (c_J cx).
  Notation usp := (bv_unsigned sp). Notation nb := (e_nblock e).
  Notation inUse := (e_inUse e).
  Notation NOT z := (Z_to_bv 64 (18446744073709551615 - z)).

  (* [comment removed for export] *)
  Ltac open_EH1 H := unfold EHEAD1n, EHEAD1 in H; cbn [removelast app] in H.
  Ltac fold_EH1 H v := lazymatch type of H with rw_cells ?sg ?mm ?A _ => change (rw_cells sg mm A (EHEAD1n cx g e v)) in H end.
  Ltac openCX :=
    let H := fresh "CXL" in pose proof CX as H; bz_ceil; bz_params; unfold cctx_ok, ESTATE_SIZE, FTAB_WORDS, BZFILE_SIZE, CEIL in H; cbv zeta in H;
    cps_destruct H as (?XE0 & ?XE1 & ?XA10 & ?XA11 & ?XA20 & ?XA21 & ?XF0 & ?XF1 & ?Xb0 & ?Xb1 & ?Xf0 & ?Xf1 & ?ME & ?MA1 & ?MA2 & ?MF & ?Mb & ?Mf & ?LJ & ?LJb);
    let S := fresh "SP" in pose proof SEP as S; unfold cctx_sep, apart, ESTATE_SIZE, FTAB_WORDS, BZFILE_SIZE in S; cbv zeta in S;
    cps_destruct S as (?AEA1 & ?AEA2 & _ & _ & _ & ?AA12 & _).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma S0_gm_maps : forall (n : nat) (i k : Z) (uns : zarr) (me m : word -> option byte)
      (ra t1 t2 s1 a0 a4 a5 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word),
    (i + Z.of_nat n = 256)%Z -> (0 <= i)%Z -> (1 <= n)%nat -> (0 <= k <= i)%Z ->
    rw_cells s0segs m E (EHEAD1n cx g e k) -> u8arr s0segs m (E + 128) (ovb inUse (jseg J 128 256) 256) ->
    u8arr s0segs m (E + 384) (ovb uns (jseg J 384 256) 256) -> mem_inv s0segs m ->
    munch [(E, E + 640)]%Z me m -> wmono s0segs me m ->
    (forall uns' k' m' (t1 t2 : word),
      mk_maps n inUse uns i k = (uns', k') -> (0 <= k' <= 256)%Z ->
      rw_cells s0segs m' E (EHEAD1n cx g e k') -> u8arr s0segs m' (E + 128) (ovb inUse (jseg J 128 256) 256) ->
      u8arr s0segs m' (E + 384) (ovb uns' (jseg J 384 256) 256) -> mem_inv s0segs m' ->
      munch [(E, E + 640)]%Z me m' -> wmono s0segs me m' ->
      evt s0segs Q (MS (mkR ra sp gp tp (Z_to_bv 64 256) t1 t2 (Z_to_bv 64 E) s1 a0 (Z_to_bv 64 256) (NOT (E + 128)) (Z_to_bv 64 k')
                            a4 a5 (Z_to_bv 64 (E + 384)) (NOT (E + 384)) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                       F (Z_to_bv 64 0x16674) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (mkR ra sp gp tp (Z_to_bv 64 256) t1 t2 (Z_to_bv 64 E) s1 a0 (Z_to_bv 64 i) (NOT (E + 128)) (Z_to_bv 64 k)
                          a4 a5 (Z_to_bv 64 (E + 384)) (NOT (E + 384)) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x16640) fc None m (seg_rom s0segs)).
  Proof.
    induction n as [|n IH]. { intros; lia. }
    intros i k uns me m ra t1 t2 s1 a0 a4 a5 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 Hi Hi0 Hn Hk EH1 INU UNS MI MU WM K.
    openCX. try clear ME MA1 MA2 MF Mb Mf. open_EH1 EH1. cps_destruct GF as (BOK1 & BOK2 & NB & DEFI & IU01 & F5 & M1).
    pose proof (jseg_length J 128 256 ltac:(lia) ltac:(lia) ltac:(unfold ESTATE_SIZE in *; lia)) as LJ1.
    pose proof (jseg_length J 384 256 ltac:(lia) ltac:(lia) ltac:(unfold ESTATE_SIZE in *; lia)) as LJ2.
    pose proof (ovb_length inUse (jseg J 128 256) 256 ltac:(lia)) as LI. pose proof (ovb_length uns (jseg J 384 256) 256 ltac:(lia)) as LU.
    pose proof (DEFI i ltac:(lia)) as Di. pose proof (IU01 i ltac:(lia)) as Vi.
    urun.
    pose proof (ovb_read1 s0segs m (E + 128) inUse (jseg J 128 256) 256 i _ INU ltac:(lia) Di ltac:(unfold wa; f_equal; lia)) as RD.
    wstep. clear RD. try rewrite (unsigned_lit8 (zget inUse i)) by lia. try rewrite (zxb_lit8 (zget inUse i)) by lia.
    rewrite mk_maps_S in K.
    wstep; if_cases Kz; zify_cond_z Kz; rewrite ?(unsigned_lit8 (zget inUse i)) in Kz by lia.
    - replace (negb (zget inUse i =? 0))%Z with false in K by (symmetry; rewrite Kz; reflexivity).
      urun; if_cases Ke; zify_cond_z Ke.
      + fold_EH1 EH1 k. enter_with (IH (i + 1)%Z k uns me m); [st_eq| lia| lia| lia| lia| exact EH1| exact INU| exact UNS| exact MI| exact MU| exact WM| exact K].
      + assert (n = 0)%nat by lia. subst n. cbn [mk_maps] in K.
        fold_EH1 EH1 k. enter_with (K uns k m _ _ eq_refl); [st_eq| lia| exact EH1| exact INU| exact UNS| exact MI| exact MU| exact WM].
    - replace (negb (zget inUse i =? 0))%Z with true in K by (symmetry; apply Bool.negb_true_iff; apply Z.eqb_neq; lia).
      urun.
      pose proof (u8arr_store_ok s0segs m (E + 384) _ i _ UNS ltac:(rewrite ovb_length_nat; lia) ltac:(unfold wa; f_equal; lia)) as SO.
      wstep. store_addr (E + 384 + i)%Z. ovb_store1 UNS i.
      replace (wr8 uns i (bv_unsigned (Z_to_bv 64 k))) with (zset uns i k) in UNS by (unfold wr8; rewrite unsigned_lit by lia; rewrite Z.mod_small by lia; reflexivity).
      urun; if_cases Ke; zify_cond_z Ke.
      + fold_EH1 EH1 (k + 1)%Z. enter_with (IH (i + 1)%Z (k + 1)%Z (zset uns i k) me); [st_eq| lia| lia| lia| lia| exact EH1| exact INU| exact UNS| exact MI| exact MU| exact WM| exact K].
      + assert (n = 0)%nat by lia. subst n. cbn [mk_maps] in K.
        fold_EH1 EH1 (k + 1)%Z. enter_with (K (zset uns i k) (k + 1)%Z _ _ _ eq_refl); [st_eq| lia| exact EH1| exact INU| exact UNS| exact MI| exact MU| exact WM].
  Qed.

  Lemma S0_gm_mfzero : forall (n : nat) (i N : Z) (mf : zarr) (me m : word -> option byte)
      (ra s1 a0 a1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t4 t5 t6 : word),
    (i + Z.of_nat n = N)%Z -> (0 <= i)%Z -> (1 <= n)%nat -> (N <= 258)%Z ->
    u32arr s0segs m (E + 672) (ovw mf (jseg J 672 1032) 258) -> mem_inv s0segs m ->
    munch [(E + 672, E + 1704)]%Z me m -> wmono s0segs me m ->
    (forall m' (t4 : word),
      u32arr s0segs m' (E + 672) (ovw (zfill0 n mf i) (jseg J 672 1032) 258) -> mem_inv s0segs m' ->
      munch [(E + 672, E + 1704)]%Z me m' -> wmono s0segs me m' ->
      evt s0segs Q (MS (mkR ra sp gp tp (Z_to_bv 64 (4 * N)) (NOT (E + 672)) (Z_to_bv 64 (4 * N)) (Z_to_bv 64 E) s1 a0 a1 (Z_to_bv 64 (E + 672)) a3
                            a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 1032) t4 t5 t6)
                       F (Z_to_bv 64 0x166bc) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (mkR ra sp gp tp (Z_to_bv 64 (4 * i)) (NOT (E + 672)) (Z_to_bv 64 (4 * N)) (Z_to_bv 64 E) s1 a0 a1 (Z_to_bv 64 (E + 672)) a3
                          a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 1032) t4 t5 t6)
                     F (Z_to_bv 64 0x166a4) fc None m (seg_rom s0segs)).
  Proof.
    induction n as [|n IH]. { intros; lia. }
    intros i N mf me m ra s1 a0 a1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t4 t5 t6 Hi Hi0 Hn HN MTF MI MU WM K.
    openCX. try clear ME MA1 MA2 MF Mb Mf.
    pose proof (jseg_length J 672 1032 ltac:(lia) ltac:(lia) ltac:(unfold ESTATE_SIZE in *; lia)) as LJm.
    pose proof (ovw_length mf (jseg J 672 1032) 258 ltac:(lia)) as LM.
    urun.
    pose proof (u32arr_store_ok s0segs m (E + 672) _ i _ MTF ltac:(rewrite ovw_length_nat; lia) ltac:(unfold wa; f_equal; lia)) as SO.
    wstep. store_addr (E + 672 + 4 * i)%Z. ovw_store MTF i 0%Z (rewrite unsigned_lit by lia; reflexivity).
    rewrite zfill0_S in K.
    urun; if_cases Ke; zify_cond_z Ke.
    - enter_with (IH (i + 1)%Z N (zset mf i 0) me); [st_eq| lia| lia| lia| lia| exact MTF| exact MI| exact MU| exact WM| exact K].
    - assert (n = 0)%nat by lia. subst n. cbn [zfill0] in K.
      enter_with (K _ _); [st_eq| exact MTF| exact MI| exact MU| exact WM].
  Qed.

  (* [comment removed for export] *)
  Ltac zb8_store2 ARR i :=
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?m ?ad (le2 ?w)) _) =>
      lazymatch type of ARR with u8arr ?segs m ?A (zb8 ?a ?n) =>
        let H := fresh "ARRw" in
        pose proof (zb8_write2 segs m A a n i w ARR ltac:(lia) ltac:(lia)) as H; clear ARR; store_done; rename H into ARR
      end end.
  Notation EOB := (gp_EOB e). Notation nInUse := (gp_nInUse e). Notation unseq := (gp_unseq e).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma S0_gm_yyinit : forall (n : nat) (i nInUse : Z) (yy : zarr) (Jy : list byte) (me m : word -> option byte)
      (ra s1 a0 a1 a2 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word),
    (i + Z.of_nat n = nInUse)%Z -> (0 <= i)%Z -> (1 <= n)%nat -> (nInUse <= 256)%Z -> Z.of_nat (length Jy) = 256%Z ->
    (CEIL <= usp)%Z -> (usp + 384 <= 18446744073709551616)%Z ->
    u8arr s0segs m (usp + 24) (ovb yy Jy 256) -> mem_inv s0segs m ->
    munch [(usp + 24, usp + 280)]%Z me m -> wmono s0segs me m ->
    (forall m',
      u8arr s0segs m' (usp + 24) (ovb (yy_init n yy i) Jy 256) -> mem_inv s0segs m' ->
      munch [(usp + 24, usp + 280)]%Z me m' -> wmono s0segs me m' ->
      evt s0segs Q (MS (mkR ra sp gp tp (Z_to_bv 64 nInUse) (Z_to_bv 64 nInUse) (Z_to_bv 64 (usp + 24 + nInUse)) (Z_to_bv 64 E) s1 a0 a1 a2 (Z_to_bv 64 256)
                            a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                       F (Z_to_bv 64 0x166f0) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (mkR ra sp gp tp (Z_to_bv 64 i) (Z_to_bv 64 nInUse) (Z_to_bv 64 (usp + 24 + i)) (Z_to_bv 64 E) s1 a0 a1 a2 (Z_to_bv 64 256)
                          a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x166dc) fc None m (seg_rom s0segs)).
  Proof.
    induction n as [|n IH]. { intros; lia. }
    intros i nInUse yy Jy me m ra s1 a0 a1 a2 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 Hi Hi0 Hn HN LJy CE SPB YY MI MU WM K.
    bz_ceil; bz_params; unfold CEIL in CE. pose proof (ovb_length yy Jy 256 ltac:(lia)) as LY.
    urun.
    pose proof (u8arr_store_ok s0segs m (usp + 24) _ i _ YY ltac:(rewrite ovb_length_nat; lia) ltac:(unfold wa; f_equal; lia)) as SO.
    wstep. store_addr (usp + 24 + i)%Z. ovb_store1 YY i.
    replace (wr8 yy i (bv_unsigned (Z_to_bv 64 i))) with (zset yy i i) in YY by (unfold wr8; rewrite unsigned_lit by lia; rewrite Z.mod_small by lia; reflexivity).
    urun; if_cases Ke; zify_cond_z Ke.
    - enter_with (IH (i + 1)%Z nInUse (zset yy i i) Jy me); [st_eq| lia| lia| lia| lia| exact LJy| bz_ceil; bz_params; unfold CEIL; lia| exact SPB| exact YY| exact MI| exact MU| exact WM|].
      intros m'. rewrite <- yy_init_S. exact (K m').
    - assert (n = 0)%nat by lia. subst n.
      enter_with (K _); [st_eq| rewrite yy_init_S; cbn [yy_init]; exact YY| exact MI| exact MU| exact WM].
  Qed.
  Notation Wz := [(E + 672, E + 1704); (A1, A1 + ARR1_SIZE)]%Z.
  Notation RZ ra t1 t2 s1 a1 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 :=
    (mkR ra sp gp tp (Z_to_bv 64 1) t1 t2 (Z_to_bv 64 E) s1 (Z_to_bv 64 A1) a1 (Z_to_bv 64 (E + 672)) a3 a4 a5 a6 a7
         (Z_to_bv 64 2) (Z_to_bv 64 1) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6).
  Notation RZ2 ra t1 t2 s1 a1 a3 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 :=
    (mkR ra sp gp tp (Z_to_bv 64 1) t1 t2 (Z_to_bv 64 E) s1 (Z_to_bv 64 A1) a1 (Z_to_bv 64 (E + 672)) a3 (Z_to_bv 64 2) (Z_to_bv 64 1) a6 a7
         s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma S0_gm_zrun : forall (f : nat) (z wr : Z) (arr1 mf : zarr) (me m : word -> option byte)
      (ra t1 t2 s1 a1 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s10 s11 t3 t5 t6 : word),
    (0 <= z)%Z -> (z + 2 < 2 * 2 ^ Z.of_nat f)%Z -> (wr + z + 1 <= nb)%Z ->
    EMI e arr1 mf wr ->
    u8arr s0segs m A1 (zb8 arr1 ARR1_SIZE) -> u32arr s0segs m (E + 672) (ovw mf (jseg J 672 1032) 258) -> mem_inv s0segs m ->
    munch Wz me m -> wmono s0segs me m ->
    (forall arr1' mf' wr' m' (ra a1 s8 s9 t3 t4 : word),
      mtf_zrun f arr1 mf wr z = (arr1', mf', wr') -> EMI e arr1' mf' wr' -> wr' = (wr + zr_cnt f z)%Z ->
      u8arr s0segs m' A1 (zb8 arr1' ARR1_SIZE) -> u32arr s0segs m' (E + 672) (ovw mf' (jseg J 672 1032) 258) -> mem_inv s0segs m' ->
      munch Wz me m' -> wmono s0segs me m' ->
      evt s0segs Q (MS (RZ ra t1 t2 s1 a1 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 (Z_to_bv 64 wr') t3 t4 t5 t6)
                       F (Z_to_bv 64 0x16864) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (RZ ra t1 t2 s1 a1 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 (Z_to_bv 64 z) s10 s11 t3 (Z_to_bv 64 wr) t5 t6)
                     F (Z_to_bv 64 0x167c4) fc None m (seg_rom s0segs)).
  Proof.
    induction f as [|f IH]. { intros z; intros. cbn in *. lia. }
    intros z wr arr1 mf me m ra t1 t2 s1 a1 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s10 s11 t3 t5 t6 Hz Hf Hwr EM AR1 MTF MI MU WM K.
    openCX. try clear ME MA2 MF Mb Mf. cps_destruct GF as (BOK1 & BOK2 & NB & DEFI & IU01 & F5 & M1). bz_params.
    destruct (mod16_linq _ MA1) as [q1 HQ1]. try clear MA1.
    pose proof (proj1 (maps_facts e GF)) as NI. pose proof (gp_EOB_eq e) as EE.
    pose proof (jseg_length J 672 1032 ltac:(lia) ltac:(lia) ltac:(unfold ESTATE_SIZE in *; lia)) as LJm.
    pose proof (zb8_length arr1 ARR1_SIZE ltac:(lia)) as LA1. pose proof (ovw_length mf (jseg J 672 1032) 258 ltac:(lia)) as LM.
    pose proof EM as EM0. cps_destruct EM0 as (W0 & MD & SM & BOK & FR & MV).
    pose proof (EMI_get e arr1 mf wr 0 EM ltac:(lia)) as [D0 R0]. pose proof (EMI_get e arr1 mf wr 1 EM ltac:(lia)) as [D1 R1].
    rewrite mtf_zrun_S in K. zb_masks.
    replace (if (z mod 2 =? 0)%Z then BZ_RUNA else BZ_RUNB) with (z mod 2)%Z in K
      by (unfold BZ_RUNA, BZ_RUNB; destruct (Z.eqb_spec (z mod 2) 0); Z.div_mod_to_equations; lia).
    assert (FIN : forall (v : Z) m1,
      v = (z mod 2)%Z ->
      u8arr s0segs m1 A1 (zb8 (wr16 arr1 (2 * wr) v) ARR1_SIZE) -> u32arr s0segs m1 (E + 672) (ovw (zincr mf v) (jseg J 672 1032) 258) -> mem_inv s0segs m1 ->
      munch Wz me m1 -> wmono s0segs me m1 ->
      (z < 2 -> forall (qra qa1 qs8 qt3 : word), evt s0segs Q (MS (RZ qra t1 t2 s1 qa1 a3 a4 a5 a6 a7 s4 s5 s6 s7 qs8 (Z_to_bv 64 z) s10 (Z_to_bv 64 (wr + 1)) qt3 (Z_to_bv 64 wr) t5 t6)
                       F (Z_to_bv 64 0x16864) fc None m1 (seg_rom s0segs)))%Z /\
      (2 <= z -> forall (qra qa1 qs8 qt3 : word), evt s0segs Q (MS (RZ qra t1 t2 s1 qa1 a3 a4 a5 a6 a7 s4 s5 s6 s7 qs8 (Z_to_bv 64 z) s10 (Z_to_bv 64 (wr + 1)) qt3 (Z_to_bv 64 wr) t5 t6)
                       F (Z_to_bv 64 0x16854) fc None m1 (seg_rom s0segs)))%Z).
    { intros v m1 Ev AR1' MTF' MI' MU' WM'. clear AR1 MTF MI MU WM.
      assert (Hv : (0 <= v <= 1)%Z) by (subst v; Z.div_mod_to_equations; lia).
      pose proof (emit_ok e GF arr1 mf wr v EM ltac:(lia)) as EO. unfold mtf_emit in EO. destruct EO as [_ EM1].
      split; intros Hz2 qra qa1 qs8 qt3.
      - enter_with (K (wr16 arr1 (2 * wr) v) (zincr mf v) (wr + 1)%Z m1 _ _ _ _ _ _);
          [st_eq| | exact EM1| | exact AR1'| exact MTF'| exact MI'| exact MU'| exact WM'].
        + cbv zeta. subst v. unfold mtf_emit. replace (z <? 2)%Z with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
        + rewrite zr_cnt_S. replace (z <? 2)%Z with true by (symmetry; apply Z.ltb_lt; lia). lia.
      - urun_to 0x167c4%Z.
        enter_with (IH ((z - 2) / 2)%Z (wr + 1)%Z (wr16 arr1 (2 * wr) v) (zincr mf v) me m1);
          [st_eq| Z.div_mod_to_equations; lia| | Z.div_mod_to_equations; lia| exact EM1| exact AR1'| exact MTF'| exact MI'| exact MU'| exact WM'|].
        + rewrite Nat2Z.inj_succ, Z.pow_succ_r in Hf by lia. Z.div_mod_to_equations. nia.
        + intros arr1' mf' wr' m' y1 y2 y3 y4 y5 y6 E' EM' Hwr'. eapply K; [| exact EM'|].
          * cbv zeta. subst v. unfold mtf_emit. replace (z <? 2)%Z with false by (symmetry; apply Z.ltb_ge; lia). exact E'.
          * rewrite zr_cnt_S. replace (z <? 2)%Z with false by (symmetry; apply Z.ltb_ge; lia). lia. }
    urun; if_cases Kc; zify_cond_z Kc; zb_masks.
    - urun.
      pose proof (u8arr_storeN_ok s0segs m A1 _ (2 * wr) 2%nat _ AR1 ltac:(lia) ltac:(rewrite zb8_length_nat; lia) ltac:(unfold wa; f_equal; lia)) as SO.
      wstep. store_addr (A1 + 2 * wr)%Z. zb8_store2 AR1 (2 * wr)%Z. rewrite (unsigned_lit 1) in AR1 by lia.
      urun.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        pose proof (ovw_read s0segs mm (E + 672) mf (jseg J 672 1032) 258 1 _ MTF ltac:(lia) D1 ltac:(unfold wa; f_equal; lia)) as RD end.
      wstep. clear RD. try rewrite (sx32_of_Z (zget mf 1)) by lia.
      urun.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        pose proof (u32arr_store_ok s0segs mm (E + 672) _ 1 _ MTF ltac:(rewrite ovw_length_nat; lia) ltac:(unfold wa; f_equal; lia)) as SO2 end.
      wstep. store_addr (E + 672 + 4 * 1)%Z. ovw_store MTF 1%Z (zget mf 1 + 1)%Z wval_lit.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        destruct (FIN 1%Z mm) as [FIx FIc];
          [Z.div_mod_to_equations; lia| exact AR1| unfold zincr; exact MTF| assumption| exact MU| exact WM|] end.
      urun; if_cases Kb; zify_cond_z Kb.
      + enter_with (FIx ltac:(lia)); st_eq.
      + enter_with (FIc ltac:(lia)); st_eq.
    - urun.
      pose proof (u8arr_storeN_ok s0segs m A1 _ (2 * wr) 2%nat _ AR1 ltac:(lia) ltac:(rewrite zb8_length_nat; lia) ltac:(unfold wa; f_equal; lia)) as SO.
      wstep. try change (Z_to_le_bytes 2 0) with (le2 (Z_to_bv 64 0)). store_addr (A1 + 2 * wr)%Z. zb8_store2 AR1 (2 * wr)%Z. rewrite (unsigned_lit 0) in AR1 by lia.
      urun.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        pose proof (ovw_read s0segs mm (E + 672) mf (jseg J 672 1032) 258 0 _ MTF ltac:(lia) D0 ltac:(unfold wa; f_equal; lia)) as RD end.
      wstep. clear RD. try rewrite (sx32_of_Z (zget mf 0)) by lia.
      urun.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        pose proof (u32arr_store_ok s0segs mm (E + 672) _ 0 _ MTF ltac:(rewrite ovw_length_nat; lia) ltac:(unfold wa; f_equal; lia)) as SO2 end.
      wstep. store_addr (E + 672 + 4 * 0)%Z. ovw_store MTF 0%Z (zget mf 0 + 1)%Z wval_lit.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        destruct (FIN 0%Z mm) as [FIx FIc];
          [Z.div_mod_to_equations; lia| exact AR1| unfold zincr; exact MTF| assumption| exact MU| exact WM|] end.
      urun; if_cases Kb; zify_cond_z Kb.
      + enter_with (FIx ltac:(lia)); st_eq.
      + wstep. enter_with (FIc ltac:(lia)); st_eq.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma S0_gm_zrun2 : forall (f : nat) (z wr : Z) (arr1 mf : zarr) (me m : word -> option byte)
      (ra t1 t2 s1 a1 a3 a6 a7 s2 s3 s4 s5 s6 s7 s8 s10 s11 t3 t5 t6 : word),
    (0 <= z)%Z -> (z + 2 < 2 * 2 ^ Z.of_nat f)%Z -> (wr + z + 1 <= nb)%Z ->
    EMI e arr1 mf wr ->
    u8arr s0segs m A1 (zb8 arr1 ARR1_SIZE) -> u32arr s0segs m (E + 672) (ovw mf (jseg J 672 1032) 258) -> mem_inv s0segs m ->
    munch Wz me m -> wmono s0segs me m ->
    (forall arr1' mf' wr' m' (t1 t2 a1 a6 s9 t4 : word),
      mtf_zrun f arr1 mf wr z = (arr1', mf', wr') -> EMI e arr1' mf' wr' -> wr' = (wr + zr_cnt f z)%Z ->
      u8arr s0segs m' A1 (zb8 arr1' ARR1_SIZE) -> u32arr s0segs m' (E + 672) (ovw mf' (jseg J 672 1032) 258) -> mem_inv s0segs m' ->
      munch Wz me m' -> wmono s0segs me m' ->
      evt s0segs Q (MS (RZ2 ra t1 t2 s1 a1 a3 a6 (Z_to_bv 64 wr') s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                       F (Z_to_bv 64 0x169d4) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (RZ2 ra t1 t2 s1 a1 a3 a6 a7 s2 s3 s4 s5 s6 s7 s8 (Z_to_bv 64 z) s10 s11 t3 (Z_to_bv 64 wr) t5 t6)
                     F (Z_to_bv 64 0x16934) fc None m (seg_rom s0segs)).
  Proof.
    induction f as [|f IH]. { intros z; intros. cbn in *. lia. }
    intros z wr arr1 mf me m ra t1 t2 s1 a1 a3 a6 a7 s2 s3 s4 s5 s6 s7 s8 s10 s11 t3 t5 t6 Hz Hf Hwr EM AR1 MTF MI MU WM K.
    openCX. try clear ME MA2 MF Mb Mf. cps_destruct GF as (BOK1 & BOK2 & NB & DEFI & IU01 & F5 & M1). bz_params.
    destruct (mod16_linq _ MA1) as [q1 HQ1]. try clear MA1.
    pose proof (proj1 (maps_facts e GF)) as NI. pose proof (gp_EOB_eq e) as EE.
    pose proof (jseg_length J 672 1032 ltac:(lia) ltac:(lia) ltac:(unfold ESTATE_SIZE in *; lia)) as LJm.
    pose proof (zb8_length arr1 ARR1_SIZE ltac:(lia)) as LA1. pose proof (ovw_length mf (jseg J 672 1032) 258 ltac:(lia)) as LM.
    pose proof EM as EM0. cps_destruct EM0 as (W0 & MD & SM & BOK & FR & MV).
    pose proof (EMI_get e arr1 mf wr 0 EM ltac:(lia)) as [D0 R0]. pose proof (EMI_get e arr1 mf wr 1 EM ltac:(lia)) as [D1 R1].
    rewrite mtf_zrun_S in K. zb_masks.
    replace (if (z mod 2 =? 0)%Z then BZ_RUNA else BZ_RUNB) with (z mod 2)%Z in K
      by (unfold BZ_RUNA, BZ_RUNB; destruct (Z.eqb_spec (z mod 2) 0); Z.div_mod_to_equations; lia).
    assert (FIN : forall (v : Z) m1,
      v = (z mod 2)%Z ->
      u8arr s0segs m1 A1 (zb8 (wr16 arr1 (2 * wr) v) ARR1_SIZE) -> u32arr s0segs m1 (E + 672) (ovw (zincr mf v) (jseg J 672 1032) 258) -> mem_inv s0segs m1 ->
      munch Wz me m1 -> wmono s0segs me m1 ->
      (z < 2 -> forall (qt1 qt2 qa1 qa6 : word), evt s0segs Q (MS (RZ2 ra qt1 qt2 s1 qa1 a3 qa6 (Z_to_bv 64 (wr + 1)) s2 s3 s4 s5 s6 s7 s8 (Z_to_bv 64 z) s10 s11 t3 (Z_to_bv 64 wr) t5 t6)
                       F (Z_to_bv 64 0x169d4) fc None m1 (seg_rom s0segs)))%Z /\
      (2 <= z -> forall (qt1 qt2 qa1 qa6 : word), evt s0segs Q (MS (RZ2 ra qt1 qt2 s1 qa1 a3 qa6 (Z_to_bv 64 (wr + 1)) s2 s3 s4 s5 s6 s7 s8 (Z_to_bv 64 z) s10 s11 t3 (Z_to_bv 64 wr) t5 t6)
                       F (Z_to_bv 64 0x169c4) fc None m1 (seg_rom s0segs)))%Z).
    { intros v m1 Ev AR1' MTF' MI' MU' WM'. clear AR1 MTF MI MU WM.
      assert (Hv : (0 <= v <= 1)%Z) by (subst v; Z.div_mod_to_equations; lia).
      pose proof (emit_ok e GF arr1 mf wr v EM ltac:(lia)) as EO. unfold mtf_emit in EO. destruct EO as [_ EM1].
      split; intros Hz2 qt1 qt2 qa1 qa6.
      - enter_with (K (wr16 arr1 (2 * wr) v) (zincr mf v) (wr + 1)%Z m1 _ _ _ _ _ _);
          [st_eq| | exact EM1| | exact AR1'| exact MTF'| exact MI'| exact MU'| exact WM'].
        + cbv zeta. subst v. unfold mtf_emit. replace (z <? 2)%Z with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
        + rewrite zr_cnt_S. replace (z <? 2)%Z with true by (symmetry; apply Z.ltb_lt; lia). lia.
      - urun_to 0x16934%Z.
        enter_with (IH ((z - 2) / 2)%Z (wr + 1)%Z (wr16 arr1 (2 * wr) v) (zincr mf v) me m1);
          [st_eq| Z.div_mod_to_equations; lia| | Z.div_mod_to_equations; lia| exact EM1| exact AR1'| exact MTF'| exact MI'| exact MU'| exact WM'|].
        + rewrite Nat2Z.inj_succ, Z.pow_succ_r in Hf by lia. Z.div_mod_to_equations. nia.
        + intros arr1' mf' wr' m' y1 y2 y3 y4 y5 y6 E' EM' Hwr'. eapply K; [| exact EM'|].
          * cbv zeta. subst v. unfold mtf_emit. replace (z <? 2)%Z with false by (symmetry; apply Z.ltb_ge; lia). exact E'.
          * rewrite zr_cnt_S. replace (z <? 2)%Z with false by (symmetry; apply Z.ltb_ge; lia). lia. }
    urun; if_cases Kc; zify_cond_z Kc; zb_masks.
    - urun.
      pose proof (u8arr_storeN_ok s0segs m A1 _ (2 * wr) 2%nat _ AR1 ltac:(lia) ltac:(rewrite zb8_length_nat; lia) ltac:(unfold wa; f_equal; lia)) as SO.
      wstep. store_addr (A1 + 2 * wr)%Z. zb8_store2 AR1 (2 * wr)%Z. rewrite (unsigned_lit 1) in AR1 by lia.
      urun.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        pose proof (ovw_read s0segs mm (E + 672) mf (jseg J 672 1032) 258 1 _ MTF ltac:(lia) D1 ltac:(unfold wa; f_equal; lia)) as RD end.
      wstep. clear RD. try rewrite (sx32_of_Z (zget mf 1)) by lia.
      urun.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        pose proof (u32arr_store_ok s0segs mm (E + 672) _ 1 _ MTF ltac:(rewrite ovw_length_nat; lia) ltac:(unfold wa; f_equal; lia)) as SO2 end.
      wstep. store_addr (E + 672 + 4 * 1)%Z. ovw_store MTF 1%Z (zget mf 1 + 1)%Z wval_lit.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        destruct (FIN 1%Z mm) as [FIx FIc];
          [Z.div_mod_to_equations; lia| exact AR1| unfold zincr; exact MTF| assumption| exact MU| exact WM|] end.
      urun; if_cases Kb; zify_cond_z Kb.
      + enter_with (FIx ltac:(lia)); st_eq.
      + enter_with (FIc ltac:(lia)); st_eq.
    - urun.
      pose proof (u8arr_storeN_ok s0segs m A1 _ (2 * wr) 2%nat _ AR1 ltac:(lia) ltac:(rewrite zb8_length_nat; lia) ltac:(unfold wa; f_equal; lia)) as SO.
      wstep. try change (Z_to_le_bytes 2 0) with (le2 (Z_to_bv 64 0)). store_addr (A1 + 2 * wr)%Z. zb8_store2 AR1 (2 * wr)%Z. rewrite (unsigned_lit 0) in AR1 by lia.
      urun.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        pose proof (ovw_read s0segs mm (E + 672) mf (jseg J 672 1032) 258 0 _ MTF ltac:(lia) D0 ltac:(unfold wa; f_equal; lia)) as RD end.
      wstep. clear RD. try rewrite (sx32_of_Z (zget mf 0)) by lia.
      urun.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        pose proof (u32arr_store_ok s0segs mm (E + 672) _ 0 _ MTF ltac:(rewrite ovw_length_nat; lia) ltac:(unfold wa; f_equal; lia)) as SO2 end.
      wstep. store_addr (E + 672 + 4 * 0)%Z. ovw_store MTF 0%Z (zget mf 0 + 1)%Z wval_lit.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        destruct (FIN 0%Z mm) as [FIx FIc];
          [Z.div_mod_to_equations; lia| exact AR1| unfold zincr; exact MTF| assumption| exact MU| exact WM|] end.
      urun; if_cases Kb; zify_cond_z Kb.
      + enter_with (FIx ltac:(lia)); st_eq.
      + wstep. enter_with (FIc ltac:(lia)); st_eq.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma S0_gm_search : forall (f : nat) (p : Z) (Y : zarr) (ll rtmp : Z) (Jy : list byte) (me m : word -> option byte)
      (t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s5 s6 s7 s8 s9 s11 t3 t5 t6 : word),
    (1 <= p)%Z -> (Z.to_nat (nInUse - p) <= f)%nat -> Z.of_nat (length Jy) = 256%Z ->
    (CEIL <= usp)%Z -> (usp + 384 <= 18446744073709551616)%Z ->
    (0 <= ll < nInUse)%Z -> (0 <= rtmp < nInUse)%Z -> ll <> rtmp ->
    (exists p0, p < p0 < nInUse /\ zget Y p0 = ll)%Z ->
    (forall k, 1 <= k < nInUse -> zdef Y k = true /\ 0 <= zget Y k < nInUse)%Z ->
    u8arr s0segs m (usp + 24) (ovb Y Jy 256) -> mem_inv s0segs m ->
    munch [(usp + 24, usp + 280)]%Z me m -> wmono s0segs me m ->
    (forall Y' p' m' (ra a1 t4 : word),
      mtf_search f Y ll rtmp p = (Y', ll, p') -> (p < p' < nInUse)%Z ->
      (forall k, 1 <= k < nInUse -> zdef Y' k = true /\ 0 <= zget Y' k < nInUse)%Z ->
      zget Y' 0 = zget Y 0 -> zdef Y' 0 = zdef Y 0 ->
      u8arr s0segs m' (usp + 24) (ovb Y' Jy 256) -> mem_inv s0segs m' ->
      munch [(usp + 24, usp + 280)]%Z me m' -> wmono s0segs me m' ->
      evt s0segs Q (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 E) s1 a0 a1 a2 a3 a4 a5 a6 a7
                            s2 s3 (Z_to_bv 64 (-1)) s5 s6 s7 s8 s9 (Z_to_bv 64 ll) s11 (Z_to_bv 64 (usp + 24 + p')) t4 t5 t6)
                       F (Z_to_bv 64 0x168ac) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (mkR (Z_to_bv 64 (usp + 24 + p)) sp gp tp t0 t1 t2 (Z_to_bv 64 E) s1 a0 a1 a2 a3 a4 a5 a6 a7
                          s2 s3 (Z_to_bv 64 (-1)) s5 s6 s7 s8 s9 (Z_to_bv 64 ll) s11 t3 (Z_to_bv 64 rtmp) t5 t6)
                     F (Z_to_bv 64 0x16890) fc None m (seg_rom s0segs)).
  Proof.
    induction f as [|f IH]; intros p Y ll rtmp Jy me m t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s5 s6 s7 s8 s9 s11 t3 t5 t6 Hp Hf LJy CE SPB Hll Hrt NE EX YD YY MI MU WM K.
    { exfalso. cps_destruct EX as (p0 & Hp0 & _). lia. }
    bz_ceil; bz_params; unfold CEIL in CE. pose proof (proj1 (maps_facts e GF)) as NI.
    cps_destruct EX as (p0 & Hp0 & Ep0).
    pose proof (YD (p + 1)%Z ltac:(lia)) as [Dq Rq].
    pose proof (ovb_length Y Jy 256 ltac:(lia)) as LY.
    rewrite mtf_search_S in K. replace (ll =? rtmp)%Z with false in K by (symmetry; apply Z.eqb_neq; exact NE).
    urun.
    pose proof (ovb_read1 s0segs m (usp + 24) Y Jy 256 (p + 1) _ YY ltac:(lia) Dq ltac:(unfold wa; f_equal; lia)) as RD.
    wstep. clear RD.
    cbv beta. try rewrite (unsigned_lit8 (zget Y (p + 1))) by lia. try rewrite (zxb_lit8 (zget Y (p + 1))) by lia.
    urun.
    pose proof (u8arr_store_ok s0segs m (usp + 24) _ (p + 1) _ YY ltac:(rewrite ovb_length_nat; lia) ltac:(unfold wa; f_equal; lia)) as SO.
    wstep. store_addr (usp + 24 + (p + 1))%Z. ovb_store1 YY (p + 1)%Z.
    replace (wr8 Y (p + 1) (bv_unsigned (Z_to_bv 64 rtmp))) with (zset Y (p + 1) rtmp) in YY by (unfold wr8; rewrite unsigned_lit by lia; rewrite Z.mod_small by lia; reflexivity).
    assert (YD' : forall k, (1 <= k < nInUse)%Z -> zdef (zset Y (p + 1) rtmp) k = true /\ (0 <= zget (zset Y (p + 1) rtmp) k < nInUse)%Z).
    { intros k Hk. rewrite zdef_zset, zget_zset. destruct (Z.eqb_spec k (p + 1)); cbv [orb]; [lia| apply YD; exact Hk]. }
    urun; if_cases Kc; zify_cond_z Kc; rewrite ?(unsigned_lit8 (zget Y (p + 1))) in Kc by lia.
    - enter_with (IH (p + 1)%Z (zset Y (p + 1) rtmp) ll (zget Y (p + 1)) Jy me);
        [st_eq| lia| lia| exact LJy| bz_ceil; bz_params; unfold CEIL; lia| exact SPB| lia| lia| lia| | exact YD'| exact YY| exact MI| exact MU| exact WM|].
      + assert (Np : p0 <> (p + 1)%Z) by (intros Heq; rewrite Heq in Ep0; lia). exists p0. rewrite zget_zset_other by lia. split; [lia| exact Ep0].
      + intros Y' p' m' y1 y2 y3 E' Hp' YD2 G0 D0. eapply (K Y' p' m' y1 y2 y3); [exact E'| lia| exact YD2| | ].
        * rewrite G0. apply zget_zset_other. lia.
        * rewrite D0. apply zdef_zset_other. lia.
    - enter_with (K (zset Y (p + 1) rtmp) (p + 1)%Z _ _ _ _); [st_eq| | lia| exact YD'| apply zget_zset_other; lia| apply zdef_zset_other; lia| exact YY| exact MI| exact MU| exact WM].
      first [rewrite <- Kc | rewrite Kc]. apply mtf_search_stop. reflexivity.
  Qed.

  Notation Wy := [(usp + 24, usp + 280)]%Z.
  Notation Wi := [(E + 672, E + 1704); (A1, A1 + ARR1_SIZE); (usp + 24, usp + 280)]%Z.
  Notation RI ra t2 a1 s8 s9 s10 s11 t3 t4 :=
    (mkR ra sp gp tp (Z_to_bv 64 1) (Z_to_bv 64 nb) t2 (Z_to_bv 64 E) (Z_to_bv 64 (usp + 25)) (Z_to_bv 64 A1) a1 (Z_to_bv 64 (E + 672)) (NOT (E + 672))
         (Z_to_bv 64 A1) (Z_to_bv 64 A2) (Z_to_bv 64 (E + 384)) (NOT (E + 384)) (Z_to_bv 64 2) (Z_to_bv 64 1) (Z_to_bv 64 (-1)) (Z_to_bv 64 (usp + 24))
         (Z_to_bv 64 nb) (Z_to_bv 64 1) s8 s9 s10 s11 t3 t4 (Z_to_bv 64 1) (Z_to_bv 64 1)).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma S0_gm_iter : forall (i : Z) (s : gms) (Jy : list byte) (me m : word -> option byte)
      (ra a1 s8 s10 s11 t3 : word),
    (0 <= i < nb)%Z -> GI e i s -> Z.of_nat (length Jy) = 256%Z ->
    (CEIL <= usp)%Z -> (usp + 384 <= 18446744073709551616)%Z ->
    u8arr s0segs m A1 (zb8 (gm_arr1 s) ARR1_SIZE) -> u8arr s0segs m A2 (zb8 (e_arr2 e) ARR2_SIZE) ->
    u8arr s0segs m (E + 384) (ovb unseq (jseg J 384 256) 256) -> u32arr s0segs m (E + 672) (ovw (gm_mtfFreq s) (jseg J 672 1032) 258) ->
    u8arr s0segs m (usp + 24) (ovb (gm_yy s) Jy 256) -> mem_inv s0segs m ->
    munch Wi me m -> wmono s0segs me m ->
    (forall s' m' (ra a1 s8 s10 s11 t3 : word),
      s' = gm_iter (e_arr2 e) unseq nb i s -> GI e (i + 1) s' ->
      u8arr s0segs m' A1 (zb8 (gm_arr1 s') ARR1_SIZE) -> u8arr s0segs m' A2 (zb8 (e_arr2 e) ARR2_SIZE) ->
      u8arr s0segs m' (E + 384) (ovb unseq (jseg J 384 256) 256) -> u32arr s0segs m' (E + 672) (ovw (gm_mtfFreq s') (jseg J 672 1032) 258) ->
      u8arr s0segs m' (usp + 24) (ovb (gm_yy s') Jy 256) -> mem_inv s0segs m' ->
      munch Wi me m' -> wmono s0segs me m' ->
      evt s0segs Q (MS (RI ra (Z_to_bv 64 i) a1 s8 (Z_to_bv 64 (gm_zPend s')) s10 s11 t3 (Z_to_bv 64 (gm_wr s')))
                       F (Z_to_bv 64 0x1691c) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (RI ra (Z_to_bv 64 i) a1 s8 (Z_to_bv 64 (gm_zPend s)) s10 s11 t3 (Z_to_bv 64 (gm_wr s)))
                     F (Z_to_bv 64 0x16740) fc None m (seg_rom s0segs)).
  Proof.
    intros i s Jy me m ra a1 s8 s10 s11 t3 Hi G LJy CE SPB AR1 AR2 UNS MTF YY MI MU WM K.
    openCX. try clear ME MA2 MF Mb Mf. bz_ceil; bz_params; unfold CEIL in CE. pose proof GF as GF'. cps_destruct GF' as (BOK1 & BOK2 & NB & DEFI & IU01 & F5 & M1). unfold ESTATE_SIZE in *.
    destruct (mod16_linq _ MA1) as [q1 HQ1]. try clear MA1.
    cps_destruct (maps_facts e GF) as (NI & UB & UJ). pose proof (gp_EOB_eq e) as EE.
    pose proof G as G'. cps_destruct G' as (W0 & Z0 & WZ & YP & MD & SM & BOK & FR & MV). destruct YP as [YR YS].
    pose proof (jseg_length J 384 256 ltac:(lia) ltac:(lia) ltac:(lia)) as LJu. pose proof (jseg_length J 672 1032 ltac:(lia) ltac:(lia) ltac:(lia)) as LJm.
    pose proof (zb8_length (gm_arr1 s) ARR1_SIZE ltac:(lia)) as LA1. pose proof (zb8_length (e_arr2 e) ARR2_SIZE ltac:(lia)) as LA2.
    pose proof (ovb_length unseq (jseg J 384 256) 256 ltac:(lia)) as LU. pose proof (ovw_length (gm_mtfFreq s) (jseg J 672 1032) 258 ltac:(lia)) as LM.
    pose proof (ovb_length (gm_yy s) Jy 256 ltac:(lia)) as LY.
    assert (PTR : rd32 (gm_arr1 s) i = rd32 (e_arr1 e) i) by (unfold rd32; rewrite !FR by lia; reflexivity).
    pose proof (M1 i Hi) as PR.
    urun.
    pose proof (zb8_read4 s0segs m A1 (gm_arr1 s) ARR1_SIZE i _ AR1 ltac:(lia) ltac:(lia) BOK ltac:(unfold wa; f_equal; lia)) as RD.
    wstep. clear RD. rewrite PTR. try rewrite (sx32_of_Z (rd32 (e_arr1 e) i)) by lia.
    wstep. wstep. wstep. wstep. rewrite (sign_sel (rd32 (e_arr1 e) i + -1) nb) by lia. wstep.
    set (j := gm_j nb s i).
    assert (Hj : (0 <= j < nb)%Z) by (subst j; unfold gm_j; rewrite PTR; destruct (Z.ltb_spec (rd32 (e_arr1 e) i - 1) 0); lia).
    match goal with |- context [bv_swrap 32 ?x] => replace (bv_swrap 32 x) with j end.
    2:{ subst j. unfold gm_j. rewrite PTR. replace (rd32 (e_arr1 e) i + -1)%Z with (rd32 (e_arr1 e) i - 1)%Z by lia.
        rewrite swrap32_small by (destruct (Z.ltb_spec (rd32 (e_arr1 e) i - 1) 0); lia). destruct (Z.ltb_spec (rd32 (e_arr1 e) i - 1) 0); lia. }
    destruct (UJ j Hj) as [DU RU]. pose proof (BOK2 j) as Bj. unfold rd8 in DU, RU.
    urun.
    pose proof (zb8_read1 s0segs m A2 (e_arr2 e) ARR2_SIZE j _ AR2 ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD.
    wstep. clear RD. cbv beta. try rewrite (unsigned_lit8 (zget (e_arr2 e) j)) by lia. try rewrite (zxb_lit8 (zget (e_arr2 e) j)) by lia.
    urun.
    pose proof (ovb_read1 s0segs m (E + 384) unseq (jseg J 384 256) 256 (zget (e_arr2 e) j) _ UNS ltac:(lia) DU ltac:(unfold wa; f_equal; lia)) as RD.
    wstep. clear RD. cbv beta. try rewrite (unsigned_lit8 (zget unseq (zget (e_arr2 e) j))) by lia. try rewrite (zxb_lit8 (zget unseq (zget (e_arr2 e) j))) by lia.
    set (ll := zget unseq (zget (e_arr2 e) j)) in *.
    set (y0 := zget (gm_yy s) 0) in *.
    pose proof (YR 0%Z ltac:(lia)) as [DY0 RY0]. fold y0 in RY0.
    pose proof (ovb_read1 s0segs m (usp + 24) (gm_yy s) Jy 256 0 _ YY ltac:(lia) DY0 ltac:(unfold wa; f_equal; lia)) as RD.
    wstep. clear RD. cbv beta. fold y0. try rewrite (unsigned_lit8 y0) by lia. try rewrite (zxb_lit8 y0) by lia.
    urun.
    if_cases Kq; zify_cond_z Kq; rewrite ?(unsigned_lit8 y0), ?(unsigned_lit8 ll) in Kq by lia.
    - assert (FLUSH : forall arr1a mfa wra m1 (qra qa1 qs8 qt3 qt4 : word),
        (if 0 <? gm_zPend s then mtf_zrun 64%nat (gm_arr1 s) (gm_mtfFreq s) (gm_wr s) (gm_zPend s - 1) else (gm_arr1 s, gm_mtfFreq s, gm_wr s))%Z = (arr1a, mfa, wra) ->
        EMI e arr1a mfa wra -> (gm_wr s <= wra <= gm_wr s + gm_zPend s)%Z ->
        u8arr s0segs m1 A1 (zb8 arr1a ARR1_SIZE) -> u8arr s0segs m1 A2 (zb8 (e_arr2 e) ARR2_SIZE) ->
        u8arr s0segs m1 (E + 384) (ovb unseq (jseg J 384 256) 256) -> u32arr s0segs m1 (E + 672) (ovw mfa (jseg J 672 1032) 258) ->
        u8arr s0segs m1 (usp + 24) (ovb (gm_yy s) Jy 256) -> mem_inv s0segs m1 ->
        munch Wi me m1 -> wmono s0segs me m1 ->
        evt s0segs Q (MS (RI qra (Z_to_bv 64 i) qa1 qs8 (Z_to_bv 64 0) (Z_to_bv 64 ll) (Z_to_bv 64 wra) qt3 qt4)
                         F (Z_to_bv 64 0x16878) fc None m1 (seg_rom s0segs))).
      { intros arr1a mfa wra m1 qra qa1 qs8 qt3 qt4 E1 EMa Hwra AR1' AR2' UNS' MTF' YY' MI' MU' WM'. clear AR1 AR2 UNS MTF YY MI MU WM.
        assert (N2 : (2 <= nInUse)%Z).
        { cps_destruct (YS ll ltac:(lia)) as (p0 & Hp0 & Ep0). destruct (Z.eq_dec p0 0) as [->|]; [exfalso; subst y0; rewrite Ep0 in Kq; lia| lia]. }
        pose proof (YR 1%Z ltac:(lia)) as [DY1 RY1].
        pose proof (ovb_read1 s0segs m1 (usp + 24) (gm_yy s) Jy 256 0 _ YY' ltac:(lia) DY0 ltac:(unfold wa; f_equal; lia)) as RD.
        wstep. clear RD. cbv beta. fold y0. try rewrite (unsigned_lit8 y0) by lia. try rewrite (zxb_lit8 y0) by lia.
        pose proof (ovb_read1 s0segs m1 (usp + 24) (gm_yy s) Jy 256 1 _ YY' ltac:(lia) DY1 ltac:(unfold wa; f_equal; lia)) as RD.
        wstep. clear RD. cbv beta. try rewrite (unsigned_lit8 (zget (gm_yy s) 1)) by lia. try rewrite (zxb_lit8 (zget (gm_yy s) 1)) by lia.
        pose proof (u8arr_store_ok s0segs m1 (usp + 24) _ 1 _ YY' ltac:(rewrite ovb_length_nat; lia) ltac:(unfold wa; f_equal; lia)) as SO.
        wstep. store_addr (usp + 24 + 1)%Z. ovb_store1 YY' 1%Z.
        replace (wr8 (gm_yy s) 1 (bv_unsigned (Z_to_bv 64 y0))) with (zset (gm_yy s) 1 y0) in YY' by (unfold wr8; rewrite unsigned_lit by lia; rewrite Z.mod_small by lia; reflexivity).
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into mS end.
        assert (EMIT : forall Y' p' m2 (qra2 qa12 qt42 : word),
          mtf_search 258%nat (zset (gm_yy s) 1 y0) ll (zget (gm_yy s) 1) 1 = (Y', ll, p') -> (1 <= p' < nInUse)%Z ->
          (forall k, 1 <= k < nInUse -> zdef Y' k = true /\ 0 <= zget Y' k < nInUse)%Z ->
          u8arr s0segs m2 (usp + 24) (ovb Y' Jy 256) -> mem_inv s0segs m2 ->
          munch Wy mS m2 -> wmono s0segs mS m2 ->
          evt s0segs Q (MS (RI qra2 (Z_to_bv 64 i) qa12 qs8 (Z_to_bv 64 0) (Z_to_bv 64 ll) (Z_to_bv 64 wra) (Z_to_bv 64 (usp + 24 + p')) qt42)
                           F (Z_to_bv 64 0x168ac) fc None m2 (seg_rom s0segs))).
        { intros Y' p' m2 qra2 qa12 qt42 E2 Hp' YD' YY2 MI2 MU2 WM2.
          clear YY' MI'. transport_after_call s0segs mS m2 MU2 WM2. clear MU2 WM2.
          pose proof (ovb_length Y' Jy 256 ltac:(lia)) as LY2.
          pose proof (EMI_get e arr1a mfa wra (p' + 1) EMa ltac:(lia)) as [Dm Rm].
          pose proof (zb8_length arr1a ARR1_SIZE ltac:(lia)) as LA1'. pose proof (ovw_length mfa (jseg J 672 1032) 258 ltac:(lia)) as LM'.
          urun.
          try replace (usp + 24 + p' - (usp + 24) + 1)%Z with (p' + 1)%Z by lia. try replace (usp + 24 + p' - (usp + 24))%Z with p' by lia.
          pose proof (u8arr_store_ok s0segs m2 (usp + 24) _ 0 _ YY2 ltac:(rewrite ovb_length_nat; lia) ltac:(unfold wa; f_equal; lia)) as SO0.
          wstep. store_addr (usp + 24 + 0)%Z. ovb_store1 YY2 0%Z.
          replace (wr8 Y' 0 (bv_unsigned (Z_to_bv 64 ll))) with (zset Y' 0 ll) in YY2 by (unfold wr8; rewrite unsigned_lit by lia; rewrite Z.mod_small by lia; reflexivity).
          urun.
          lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
            pose proof (u8arr_storeN_ok s0segs mm A1 _ (2 * wra) 2%nat _ AR1' ltac:(lia) ltac:(rewrite zb8_length_nat; lia) ltac:(unfold wa; f_equal; lia)) as SO1 end.
          wstep. store_addr (A1 + 2 * wra)%Z. zb8_store2 AR1' (2 * wra)%Z.
          first [ rewrite (unsigned_lit (p' + 1)) in AR1' by lia
                | lazymatch type of AR1' with context [wr16 _ _ (bv_unsigned ?w)] =>
                    replace (bv_unsigned w) with (p' + 1)%Z in AR1' by (rewrite ?swrap32_small by (rewrite ?swrap32_small by lia; lia); rewrite unsigned_lit by lia; lia) end ].
          urun.
          lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
            pose proof (ovw_read s0segs mm (E + 672) mfa (jseg J 672 1032) 258 (p' + 1) _ MTF' ltac:(lia) Dm ltac:(unfold wa; f_equal; lia)) as RD end.
          wstep. clear RD. try rewrite (sx32_of_Z (zget mfa (p' + 1))) by lia.
          urun.
          lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
            pose proof (u32arr_store_ok s0segs mm (E + 672) _ (p' + 1) _ MTF' ltac:(rewrite ovw_length_nat; lia) ltac:(unfold wa; f_equal; lia)) as SO2 end.
          wstep. store_addr (E + 672 + 4 * (p' + 1))%Z. ovw_store MTF' (p' + 1)%Z (zget mfa (p' + 1) + 1)%Z wval_lit.
          assert (NEq : zget (gm_yy s) 0 <> ll) by (fold y0; lia).
          lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
            enter_with (K (GMS (wr16 arr1a (2 * wra) (p' + 1)) (zincr mfa (p' + 1)) (zset Y' 0 ll) (wra + 1) 0) mm _ _ _ _ _ _);
              [cbn [gm_yy gm_wr gm_zPend gm_arr1 gm_mtfFreq]; st_eq| | | exact AR1'| exact AR2'| exact UNS'| unfold zincr; exact MTF'| exact YY2| exact MI2| exact MU'| exact WM'] end.
          - symmetry. exact (gm_iter_new (e_arr2 e) unseq nb i s arr1a mfa wra Y' p' NEq E1 E2).
          - lazymatch goal with |- GI _ _ ?s1 => replace s1 with (gm_iter (e_arr2 e) unseq nb i s) by (exact (gm_iter_new (e_arr2 e) unseq nb i s arr1a mfa wra Y' p' NEq E1 E2)) end.
            apply (gm_iter_GI e GF); [lia| exact G]. }
        urun; if_cases Kf; zify_cond_z Kf; rewrite ?(unsigned_lit8 (zget (gm_yy s) 1)), ?(unsigned_lit8 ll) in Kf by lia.
        - enter_with (EMIT (zset (gm_yy s) 1 y0) 1%Z mS _ _ _); [st_eq| | lia| | exact YY'| exact MI'| apply munch_refl| apply wmono_refl].
          + etransitivity; [apply mtf_search_stop; first [exact Kf| symmetry; exact Kf]|]. rewrite <- ?Kf, ?Kf. reflexivity.
          + intros k Hk. rewrite zdef_zset, zget_zset. destruct (Z.eqb_spec k 1); cbv [orb]; [lia| apply YR; lia].
        - urun_to 0x16890%Z.
          cps_destruct (YS ll ltac:(lia)) as (p0 & Hp0 & Ep0).
          enter_with (S0_gm_search 258%nat 1 (zset (gm_yy s) 1 y0) ll (zget (gm_yy s) 1) Jy mS mS);
            [st_eq| lia| lia| exact LJy| exact CE| exact SPB| lia| lia| lia| | | exact YY'| exact MI'| apply munch_refl| apply wmono_refl|].
          + exists p0. assert (p0 <> 0%Z) by (intros ->; subst y0; lia). assert (p0 <> 1%Z) by (intros ->; lia).
            rewrite zget_zset_other by lia. split; [lia| exact Ep0].
          + intros k Hk. rewrite zdef_zset, zget_zset. destruct (Z.eqb_spec k 1); cbv [orb]; [lia| apply YR; lia].
          + intros Y' p' m2 y1 y2 y3 E2 Hp' YD2 G0 D0 YY2 MI2 MU2 WM2. eapply (EMIT Y' p' m2 y1 y2 y3); [exact E2| lia| exact YD2| exact YY2| exact MI2| exact MU2| exact WM2]. }
      urun; if_cases Kp; zify_cond_z Kp.
      + assert (Zp : gm_zPend s = 0%Z) by lia. rewrite Zp.
        urun_to 0x16878%Z.
        enter_with (FLUSH (gm_arr1 s) (gm_mtfFreq s) (gm_wr s) m _ _ _ _ _);
          [st_eq| rewrite Zp; reflexivity| apply (GI_EMI e i s G)| lia
          | exact AR1| exact AR2| exact UNS| exact MTF| exact YY| exact MI| exact MU| exact WM].
      + wstep. try rewrite (sx32_of_Z_signed (gm_zPend s + -1)) by lia. try rewrite (sx32_of_Z (gm_zPend s + -1)) by lia.
        enter_with (S0_gm_zrun 64%nat (gm_zPend s - 1)%Z (gm_wr s) (gm_arr1 s) (gm_mtfFreq s) m m);
          [st_eq| lia| cbn; lia| lia| apply (GI_EMI e i s G)| exact AR1| exact MTF| exact MI| apply munch_refl| apply wmono_refl|].
        intros arr1a mfa wra m1 y1 y2 y3 y4 y5 y6 E1 EMa Hwra AR1a MTFa MI1 MU1 WM1. bz_params.
        clear AR1 MTF MI. transport_after_call s0segs m m1 MU1 WM1. clear MU1 WM1.
        pose proof (zr_cnt_bound 64 (gm_zPend s - 1) ltac:(lia)) as ZB.
        urun_to 0x16878%Z.
        enter_with (FLUSH arr1a mfa wra m1 _ _ _ _ _);
          [st_eq| replace (0 <? gm_zPend s)%Z with true by (symmetry; apply Z.ltb_lt; lia); exact E1| exact EMa| lia
          | exact AR1a| exact AR2| exact UNS| exact MTFa| exact YY| exact MI1| exact MU| exact WM].
    - urun_to 0x1691c%Z.
      assert (EQy : zget (gm_yy s) 0 = ll) by (fold y0; lia).
      enter_with (K (GMS (gm_arr1 s) (gm_mtfFreq s) (gm_yy s) (gm_wr s) (gm_zPend s + 1)) m _ _ _ _ _ _);
        [cbn [gm_yy gm_wr gm_zPend gm_arr1 gm_mtfFreq]; st_eq| symmetry; exact (gm_iter_same (e_arr2 e) unseq nb i s EQy)| | exact AR1| exact AR2| exact UNS| exact MTF| exact YY| exact MI| exact MU| exact WM].
      lazymatch goal with |- GI _ _ ?s1 => replace s1 with (gm_iter (e_arr2 e) unseq nb i s) by (exact (gm_iter_same (e_arr2 e) unseq nb i s EQy)) end.
      apply (gm_iter_GI e GF); [lia| exact G].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma S0_gm_loop : forall (n : nat) (i : Z) (Jy : list byte) (me m : word -> option byte)
      (ra a1 s8 s10 s11 t3 : word),
    (i + Z.of_nat n = nb)%Z -> (0 <= i)%Z -> (1 <= n)%nat -> Z.of_nat (length Jy) = 256%Z ->
    (CEIL <= usp)%Z -> (usp + 384 <= 18446744073709551616)%Z ->
    let s := gp_st e (Z.to_nat i) in
    u8arr s0segs m A1 (zb8 (gm_arr1 s) ARR1_SIZE) -> u8arr s0segs m A2 (zb8 (e_arr2 e) ARR2_SIZE) ->
    u8arr s0segs m (E + 384) (ovb unseq (jseg J 384 256) 256) -> u32arr s0segs m (E + 672) (ovw (gm_mtfFreq s) (jseg J 672 1032) 258) ->
    u8arr s0segs m (usp + 24) (ovb (gm_yy s) Jy 256) -> mem_inv s0segs m ->
    munch Wi me m -> wmono s0segs me m ->
    (forall m' (ra a1 s8 s10 s11 t3 : word), let s' := gp_st e (Z.to_nat nb) in
      u8arr s0segs m' A1 (zb8 (gm_arr1 s') ARR1_SIZE) -> u8arr s0segs m' A2 (zb8 (e_arr2 e) ARR2_SIZE) ->
      u8arr s0segs m' (E + 384) (ovb unseq (jseg J 384 256) 256) -> u32arr s0segs m' (E + 672) (ovw (gm_mtfFreq s') (jseg J 672 1032) 258) ->
      u8arr s0segs m' (usp + 24) (ovb (gm_yy s') Jy 256) -> mem_inv s0segs m' ->
      munch Wi me m' -> wmono s0segs me m' ->
      evt s0segs Q (MS (RI ra (Z_to_bv 64 nb) a1 s8 (Z_to_bv 64 (gm_zPend s')) s10 s11 t3 (Z_to_bv 64 (gm_wr s')))
                       F (Z_to_bv 64 0x16924) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (RI ra (Z_to_bv 64 i) a1 s8 (Z_to_bv 64 (gm_zPend s)) s10 s11 t3 (Z_to_bv 64 (gm_wr s)))
                     F (Z_to_bv 64 0x16740) fc None m (seg_rom s0segs)).
  Proof.
    induction n as [|n IH]. { intros; lia. }
    intros i Jy me m ra a1 s8 s10 s11 t3 Hi Hi0 Hn LJy CE SPB s AR1 AR2 UNS MTF YY MI MU WM K.
    pose proof GF as GF'. cps_destruct GF' as (BOK1 & BOK2 & NB & DEFI & IU01 & F5 & M1).
    assert (G : GI e i s) by (subst s; rewrite <- (Z2Nat.id i) at 1 by lia; apply (gp_st_GI e GF); lia).
    eapply (S0_gm_iter i s Jy me m); [lia| exact G| exact LJy| exact CE| exact SPB| exact AR1| exact AR2| exact UNS| exact MTF| exact YY| exact MI| exact MU| exact WM|].
    intros s' m' y1 y2 y3 y4 y5 y6 Es' G' AR1' AR2' UNS' MTF' YY' MI' MU' WM'.
    assert (Es2 : s' = gp_st e (Z.to_nat (i + 1))).
    { rewrite Es'. subst s. replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia. rewrite gp_st_S. f_equal. lia. }
    clear AR1 AR2 UNS MTF YY MI MU WM.
    openCX. bz_ceil; bz_params; unfold CEIL in CE.
    urun; if_cases Kl; zify_cond_z Kl.
    - rewrite Es2 in *.
      enter_with (IH (i + 1)%Z Jy me m'); [st_eq| lia| lia| lia| exact LJy| bz_ceil; bz_params; unfold CEIL; lia| exact SPB| exact AR1'| exact AR2'| exact UNS'| exact MTF'| exact YY'| exact MI'| exact MU'| exact WM'| exact K].
    - assert (n = 0)%nat by lia. subst n. rewrite Es2 in *. replace (i + 1)%Z with nb in * by lia.
      enter_with (K m' _ _ _ _ _ _); [st_eq| exact AR1'| exact AR2'| exact UNS'| exact MTF'| exact YY'| exact MI'| exact MU'| exact WM'].
  Qed.

End S0GM.

End ACeilS1.
