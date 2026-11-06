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
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzTac BzTac2 BzArr BzCMem BzCSortF BzArrD CmpMem CmpCut BzCLemmasFs BzCFactsFs CmpFsKit0 AsanKit AsanCut.
From Stdlib Require Lia. Unset Lia Cache.
Import ListNotations. Open Scope bv_scope.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzParams.
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
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpLiaC.
Local Ltac lia ::= CmpLiaC.lia_c.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpSepV.
Local Ltac Lib.Step.slia ::= CmpSepV.slia_v.
Local Ltac Lib.StoreFast.tslia ::= CmpSepV.tslia_v.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpStEq.
Local Ltac BzTac.st_eq ::= CmpStEq.st_eq_fast.
Local Ltac simpl_arr_sizes ::= CmpFast.sas7_all.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.
(* [comment removed for export] *)
Local Ltac Lib.Step.solve_load ::= AsanKit.asan_solve_load.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzCFactsFs2 A0_cmp_fsV.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.A Require Import Shadow.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import A0_cmp_fsS A0_cmp_fsP.
Section ACeilS1. Context {BZP : BzParams} {ACEIL__ : ACeil}.

Ltac lit_store :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 8 ?v)) _) => change (Z_to_le_bytes 8 v) with (le8 (Z_to_bv 64 v)); mem_after_store
  | _ => idtac
  end.
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition f1b : byte := Z_to_bv 8 (bv_unsigned (Z_to_bv 64 (-15))).
Definition f3b : byte := Z_to_bv 8 (bv_unsigned (Z_to_bv 64 (-13))).

(* [comment removed for export] *)
Lemma cells_bytes_C1s : forall bs, cells_bytes (map C1 bs) = bs.
Proof. induction bs as [|b bs IH]; [reflexivity| cbn [map cells_bytes cbytes app]; rewrite IH; reflexivity]. Qed.
Lemma cells_size_C1s : forall bs, cells_size (map C1 bs) = length bs.
Proof. induction bs as [|b bs IH]; [reflexivity| cbn [map cells_size csize length Nat.add]; rewrite IH; reflexivity]. Qed.
Lemma cells_wf_C1s : forall bs, cells_wf (map C1 bs).
Proof. induction bs as [|b bs IH]; [exact I| cbn [map cells_wf cell_wf]; split; [exact I| exact IH]]. Qed.
Lemma rw_cells_CB_C1s : forall segs m A n bs, rw_cells segs m A [CB n bs] -> rw_cells segs m A (map C1 bs) /\ length bs = n.
Proof.
  intros segs m A n bs [[Hwf Hb] Hw]. cbn [cells_wf cell_wf] in Hwf. destruct Hwf as [Hl _].
  cbn [cells_bytes cbytes app] in Hb. rewrite app_nil_r in Hb. cbn [cells_size csize Nat.add] in Hw. rewrite Nat.add_0_r in Hw.
  split; [| exact Hl]. split; [split; [apply cells_wf_C1s| rewrite cells_bytes_C1s; exact Hb]| rewrite cells_size_C1s, Hl; exact Hw].
Qed.

Section A0FSP.
  Variable X : fsenv. Variable Y : afenv. Variable Q : machine_state -> Prop.
  Hypothesis XOK : fsenv_ok X. Hypothesis YOK : afenv_ok X Y. Hypothesis YOFF : afenv_offsh X Y. Hypothesis AX : sanchor (ae_FB Y) (ae_SHF Y).
  Notation usp := (bv_unsigned (fe_sp X)). Notation P := (ae_P Y). Notation FB := (ae_FB Y). Notation SHF := (ae_SHF Y).
  Notation A1 := (fe_A1 X). Notation A2 := (fe_A2 X). Notation FT := (fe_FT X). Notation nb := (fe_nb X).
  Notation gp := (fe_gp X). Notation tp := (fe_tp X). Notation F := (fe_F X). Notation fc := (fe_fc X). Notation lo := (fe_lo X).
  Notation cSB := (Z_to_bv 64 2147450880).
  (* [comment removed for export] *)
  Notation RB ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s9 s10 s11 t3 t4 t5 t6 :=
    (mkR ra (Z_to_bv 64 P) gp tp t0 t1 t2 (fe_sp X) (Z_to_bv 64 P) a0 a1 a2 a3 a4 a5 a6 a7
         s2 s3 (Z_to_bv 64 A2) (Z_to_bv 64 A1) cSB (Z_to_bv 64 0) (Z_to_bv 64 FT) s9 s10 s11 t3 t4 t5 t6).
  Ltac openY :=
    fsenv_open XOK; afenv_open YOK;
    let H := fresh "YO" in pose proof YOFF as H; unfold afenv_offsh, SH_LO, SH_HI in H; destruct H as (_ & _ & _ & ?YOF);
    assert (AFS : (FB + 2112 <= SHF \/ SHF + 264 <= FB)%Z) by lia; box_ors.

  Ltac sbf8 := wstep; change (le1 (Z_to_bv 64 (-8))) with [f8b]; mem_after_store.
  Ltac sbf2 := wstep; change (le1 (Z_to_bv 64 (-14))) with [f2b]; mem_after_store.
  Ltac sbf1 := wstep; change (le1 (Z_to_bv 64 (-15))) with [f1b]; mem_after_store.
  Ltac sbf3 := wstep; change (le1 (Z_to_bv 64 (-13))) with [f3b]; mem_after_store.
  Ltac sbx := first [sbf8 | sbf2 | sbf1 | sbf3].

  (* [comment removed for export] *)
  Lemma A0_fs_S1sb : forall (me m : word -> option byte) (bs : list byte)
      (ra sp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word),
    rw_cells a0segs m SHF [CB 120 bs] -> mem_inv a0segs m -> munch [(SHF, SHF + 120)]%Z me m -> wmono a0segs me m ->
    (forall m', rw_cells a0segs m' (SHF + 4) (shc f8b) -> mem_inv a0segs m' -> munch [(SHF, SHF + 120)]%Z me m' -> wmono a0segs me m' ->
       evt a0segs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (-8)) (Z_to_bv 64 (-14)) a2 a3 a4 a5 a6 a7 (Z_to_bv 64 SHF) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                        F (Z_to_bv 64 0x9ad04) fc None m' (seg_rom a0segs))) ->
    evt a0segs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (-8)) (Z_to_bv 64 (-15)) a2 a3 a4 a5 a6 a7 (Z_to_bv 64 SHF) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x9ab20) fc None m (seg_rom a0segs)).
  Proof.
    intros me m bs ra sp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 RZ MI MU WMo K.
    destruct (rw_cells_CB_C1s a0segs _ _ _ _ RZ) as [RZc L]. clear RZ. rename RZc into RZ.
    do 120 (destruct bs as [|? bs]; [discriminate L| cbn [length] in L; apply Nat.succ_inj in L]). destruct bs; [clear L| discriminate L].
    cbn [map] in RZ.
    do 4 sbx. wstep. do 116 sbx.
    destruct (rw_cells_cutZ a0segs _ _ _ 4 RZ) as [_ RZ1]. cbn [firstn skipn cells_size csize Nat.add] in RZ1. change (Z.of_nat 4) with 4%Z in RZ1.
    destruct (rw_cells_cutZ a0segs _ _ _ 108 RZ1) as [RZ2 _]. cbn [firstn] in RZ2.
    apply K; [exact RZ2| exact MI| exact MU| exact WMo].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Notation WS1 := [(P + 40, P + 48); (P + 232, P + 240); (FB, FB + 24); (SHF, SHF + 120)]%Z.
  Lemma A0_fs_S1 : forall (m : word -> option byte) (v0 v8 v16 v24 v32 v40 v48 v56 v64 v72 v224 v232 h0 h1 h2 : word) (j4 bs : list byte)
      (ra t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2 s3 s9 s10 s11 t3 t4 t5 t6 : word),
    rw_cells a0segs m P [C8 v0; C8 v8; C8 v16; C8 v24; C8 v32; C8 v40; C8 v48; C8 v56; C8 v64; C8 v72] ->
    rw_cells a0segs m (P + 224) [C8 v224; C8 v232; CB 4 j4] ->
    rw_cells a0segs m FB [C8 h0; C8 h1; C8 h2] -> rw_cells a0segs m SHF [CB 120 bs] -> mem_inv a0segs m ->
    (forall m' (y12 y13 y14 : word),
       rw_cells a0segs m' P [C8 v0; C8 v8; C8 v16; C8 v24; C8 v32; C8 (Z_to_bv 64 FB); C8 v48; C8 v56; C8 v64; C8 v72] ->
       rw_cells a0segs m' (P + 224) [C8 v224; C8 (Z_to_bv 64 FB); CB 4 j4] ->
       rw_cells a0segs m' FB [C8 (Z_to_bv 64 0x41b58ab3); C8 (Z_to_bv 64 0x10afd); C8 (Z_to_bv 64 0x9aa30)] ->
       rw_cells a0segs m' (SHF + 4) (shc f8b) -> mem_inv a0segs m' -> munch WS1 m m' -> wmono a0segs m m' ->
       evt a0segs Q (MS (RB (Z_to_bv 64 0x9ad14) t0 t1 t2 (Z_to_bv 64 (SHF + 120)) (Z_to_bv 64 128) y12 y13 y14 a5 a6 a7
                            (Z_to_bv 64 SHF) (Z_to_bv 64 FB) (Z_to_bv 64 (SHF + 120)) s10 s11 t3 t4 t5 t6)
                        F (Z_to_bv 64 0x559e4) fc None m' (seg_rom a0segs))) ->
    evt a0segs Q (MS (RB ra t0 t1 t2 (Z_to_bv 64 FB) a1 a2 a3 a4 a5 a6 a7 s2 s3 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x9aab4) fc None m (seg_rom a0segs)).
  Proof.
    intros m v0 v8 v16 v24 v32 v40 v48 v56 v64 v72 v224 v232 h0 h1 h2 j4 bs ra t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2 s3 s9 s10 s11 t3 t4 t5 t6 SLa SLc HD RZ MI K.
    openY.
    pose proof (munch_refl WS1 m) as MU. pose proof (wmono_refl a0segs m) as WM.
    (* [comment removed for export] *)
    wstep. wstep. wstep; if_cases Kz; zify_cond_z Kz; [| exfalso; lia].
    wstep. wstep.
    (* [comment removed for export] *)
    wstep. wstep. wstep. wstep. wstep. wstep. wstep. wstep.
    wstep. lit_store. wstep. lit_store. wstep. lit_store. wstep. wstep.
    rewrite (sanchor_addr0 FB SHF AX).
    (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => set (m1 := mm) in * end.
    enter_with (A0_fs_S1sb m1 m1 bs _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _);
      [st_eq| exact RZ| exact MI| apply munch_refl| apply wmono_refl|].
    intros m2 RZ2 MI2 MU2 WM2. clear RZ MI. transport_after_call a0segs m1 m2 MU2 WM2. clear MU2 WM2.
    (* [comment removed for export] *)
    wstep. wstep. wstep. wstep.
    eapply K; [exact SLa| exact SLc| exact HD| exact RZ2| exact MI2| exact MU| exact WM].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Notation WS2 := [(P + 32, P + 40); (P + 120, P + 128); (SHF + 248, SHF + 264)]%Z.
  Lemma A0_fs_S2 : forall (m : word -> option byte) (v0 v8 v16 v24 v32 v40 v48 v56 v64 v72 : word)
      (v80 v88 v96 v104 v112 v120 v128 v136 v144 v152 v160 v168 v176 v184 v192 v200 v208 v216 : word) (bs : list byte)
      (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s10 s11 t3 t4 t5 t6 : word),
    rw_cells a0segs m P [C8 v0; C8 v8; C8 v16; C8 v24; C8 v32; C8 v40; C8 v48; C8 v56; C8 v64; C8 v72] ->
    rw_cells a0segs m (P + 80) [C8 v80; C8 v88; C8 v96; C8 v104; C8 v112; C8 v120; C8 v128; C8 v136; C8 v144; C8 v152; C8 v160; C8 v168; C8 v176;
                                C8 v184; C8 v192; C8 v200; C8 v208; C8 v216] ->
    rw_cells a0segs m (SHF + 248) [CB 16 bs] -> mem_inv a0segs m ->
    (forall m',
       rw_cells a0segs m' P [C8 v0; C8 v8; C8 v16; C8 v24; C8 (Z_to_bv 64 (SHF + 120)); C8 v40; C8 v48; C8 v56; C8 v64; C8 v72] ->
       rw_cells a0segs m' (P + 80) [C8 v80; C8 v88; C8 v96; C8 v104; C8 v112; C8 (Z_to_bv 64 SHF); C8 v128; C8 v136; C8 v144; C8 v152; C8 v160; C8 v168; C8 v176;
                                    C8 v184; C8 v192; C8 v200; C8 v208; C8 v216] ->
       mem_inv a0segs m' -> munch WS2 m m' -> wmono a0segs m m' ->
       evt a0segs Q (MS (RB (Z_to_bv 64 0x9ad6c) t0 t1 t2 (Z_to_bv 64 (SHF + 120)) (Z_to_bv 64 128) a2 a3 a4 a5 a6 a7
                            (Z_to_bv 64 SHF) s3 (Z_to_bv 64 (SHF + 120)) s10 s11 t3 t4 t5 t6)
                        F (Z_to_bv 64 0x558c4) fc None m' (seg_rom a0segs))) ->
    evt a0segs Q (MS (RB ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 SHF) s3 (Z_to_bv 64 (SHF + 120)) s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x9ad14) fc None m (seg_rom a0segs)).
  Proof.
    intros m v0 v8 v16 v24 v32 v40 v48 v56 v64 v72 v80 v88 v96 v104 v112 v120 v128 v136 v144 v152 v160 v168 v176 v184 v192 v200 v208 v216 bs
      ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s10 s11 t3 t4 t5 t6 SLa SLb RZ MI K.
    openY.
    pose proof (munch_refl WS2 m) as MU. pose proof (wmono_refl a0segs m) as WM.
    destruct (rw_cells_CB_C1s a0segs _ _ _ _ RZ) as [RZc L]. clear RZ. rename RZc into RZ.
    do 16 (destruct bs as [|? bs]; [discriminate L| cbn [length] in L; apply Nat.succ_inj in L]). destruct bs; [clear L| discriminate L].
    cbn [map] in RZ.
    (* [comment removed for export] *)
    wstep. do 15 sbx. wstep. sbx. wstep. wstep. wstep. wstep.
    eapply K; [exact SLa| exact SLb| assumption| exact MU| exact WM].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma A0_fs_S3 : forall (m : word -> option byte) (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s9 s10 s11 t3 t4 t5 t6 : word),
    (evt a0segs Q (MS (RB (Z_to_bv 64 0x9ad8c) t0 t1 t2 (Z_to_bv 64 (P + 244)) (Z_to_bv 64 0) (Z_to_bv 64 1028) a3 a4 a5 a6 a7
                          (Z_to_bv 64 (P + 244)) s3 s9 s10 s11 t3 t4 t5 t6)
                      F (Z_to_bv 64 0x52ea0) fc None m (seg_rom a0segs))) ->
    evt a0segs Q (MS (RB ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x9ad6c) fc None m (seg_rom a0segs)).
  Proof.
    intros m ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s9 s10 s11 t3 t4 t5 t6 K.
    (* [comment removed for export] *)
    wstep. wstep; if_cases Kv; zify_cond_z Kv; [| exfalso; lia].
    wstep. wstep. wstep. wstep. wstep.
    exact K.
  Qed.
End A0FSP.
End ACeilS1.
