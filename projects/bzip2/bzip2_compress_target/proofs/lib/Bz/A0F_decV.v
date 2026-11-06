(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib SegsA0.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzDefs BzModel BzTac BzInv BzTables BzContracts AsanKit DecCutA.
From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Open Scope Z_scope.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.

Section ACeilS0. Context {ACEIL__ : ACeil}.
(* [comment removed for export] *)
Definition DI_A0 : dimg := DIMG a0segs 0x9e368 0xc06b8 0xbf950 0xc4000 0xc4500.
End ACeilS0.
(* [comment removed for export] *)
Notation AIHI0 := 6414336%Z (only parsing).
(* [comment removed for export] *)
Ltac a0img := cbn [di_segs di_got di_stderrp di_crc di_rnums di_dec DI_A0] in *.

(* [comment removed for export] *)
Definition df1b : byte := Z_to_bv 8 (-15).
Definition df3b : byte := Z_to_bv 8 (-13).
Definition df8b : byte := Z_to_bv 8 (-8).
Definition df5b : byte := Z_to_bv 8 (-11).

Section ACeilS1. Context {ACEIL__ : ACeil}.

(* [comment removed for export] *)
Definition FM_CELLS (A : act14) (zt : word) : list cell :=
  [C8 (Z_to_bv 64 (a_shs A + 8011)); C8 (Z_to_bv 64 (a_shs A + 8011)); C8 (Z_to_bv 64 (a_shs A + 8010)); C8 (Z_to_bv 64 (a_shs A + 8010));
   C8 (Z_to_bv 64 (a_shs A + 8009)); C8 (Z_to_bv 64 (a_shs A + 8009)); C8 (Z_to_bv 64 (a_shs A + 8008)); C8 (Z_to_bv 64 (a_shs A + 8008));
   C8 (Z_to_bv 64 (a_shs A + 8007)); C8 (Z_to_bv 64 (a_shs A + 8007)); C8 (Z_to_bv 64 (a_shs A + 8006)); C8 (Z_to_bv 64 (a_shs A + 8006));
   C8 (Z_to_bv 64 (a_shs A + 8005)); C8 (Z_to_bv 64 (a_shs A + 8005)); C8 (Z_to_bv 64 (a_shs A + 8004)); C8 (Z_to_bv 64 (a_shs A + 8017));
   C8 (Z_to_bv 64 (a_shs A + 8016)); C8 (Z_to_bv 64 (a_shs A + 8015)); C8 (Z_to_bv 64 (a_shs A + 8014)); C8 (Z_to_bv 64 (b_s (a_cx A) + 64136));
   C8 (Z_to_bv 64 (a_shs A + 8014)); C8 (Z_to_bv 64 (b_s (a_cx A) + 64128)); C8 (Z_to_bv 64 (b_s (a_cx A) + 64120)); C8 (Z_to_bv 64 (a_shs A + 8013));
   C8 (Z_to_bv 64 (a_shs A + 8013)); C8 zt; C8 (Z_to_bv 64 (a_shs A + 8012)); C8 (Z_to_bv 64 (a_shs A + 8012));
   C8 (Z_to_bv 64 (b_s (a_cx A) + 64040)); C8 (Z_to_bv 64 (b_s (a_cx A) + 64116)); C8 (Z_to_bv 64 (b_s (a_cx A) + 64112)); C8 (Z_to_bv 64 (b_s (a_cx A) + 64108));
   C8 (Z_to_bv 64 (b_s (a_cx A) + 64104)); C8 (Z_to_bv 64 (b_s (a_cx A) + 64100)); C8 (Z_to_bv 64 (b_s (a_cx A) + 64096)); C8 (Z_to_bv 64 (b_s (a_cx A) + 64092));
   C8 (Z_to_bv 64 (b_s (a_cx A) + 64088)); C8 (Z_to_bv 64 (b_s (a_cx A) + 64084)); C8 (Z_to_bv 64 (b_s (a_cx A) + 64080)); C8 (Z_to_bv 64 (b_s (a_cx A) + 64076));
   C8 (Z_to_bv 64 (b_s (a_cx A) + 64072)); C8 (Z_to_bv 64 (b_s (a_cx A) + 64068)); C8 (Z_to_bv 64 (b_s (a_cx A) + 64064)); C8 (Z_to_bv 64 (b_s (a_cx A) + 64060));
   C8 (Z_to_bv 64 (b_s (a_cx A) + 64056)); C8 (Z_to_bv 64 (b_s (a_cx A) + 64052)); C8 (Z_to_bv 64 (b_s (a_cx A) + 64048)); C8 (Z_to_bv 64 (b_s (a_cx A) + 64044));
   C8 (Z_to_bv 64 (a_fb A)); C8 (Z_to_bv 64 (a_shf A))].

(* [comment removed for export] *)
Definition FT_REGS (A : act14) : list cell :=
  [C8 (a_s11 A); C8 (a_s10 A); C8 (a_s9 A); C8 (a_s8 A); C8 (a_s7 A); C8 (a_s6 A); C8 (a_s5 A); C8 (a_s4 A); C8 (a_s3 A);
   C8 (a_s2 A); C8 (a_s1 A); C8 (a_s0 A); C8 (a_ra A)].

(* [comment removed for export] *)
Definition aframe (A : act14) (m : word -> option byte) : Prop :=
  exists (zt : word) (ng : nat) (jg j24 pos j38 : list byte) (fl : Z),
    a_P A + 728 + Z.of_nat ng + 104 = a_usp A /\ (ng = 0 \/ ng = 16)%nat /\
    (* [comment removed for export] *)
    ro_cells a0segs m (a_fb A + 56) [C8 (Z_to_bv 64 fl)] /\
    rw_cells a0segs m (a_P A + 96) (FM_CELLS A zt) /\
    rw_cells a0segs m (a_P A + 728) (CB ng jg :: FT_REGS A) /\
    rw_cells a0segs m (a_fb A) [C8 (Z_to_bv 64 1102416563); C8 (Z_to_bv 64 132751); C8 (Z_to_bv 64 648040); CB 8 j24; CB 6 pos; CB 18 j38] /\
    rw_cells a0segs m (a_shf A) [C1 df1b; C1 df1b; C1 df1b; C1 df1b; C1 df8b; C1 df3b; C1 df3b; C1 df3b].

Lemma disjoint_from_le : forall W a n n', disjoint_from W a n -> 0 <= n' <= n -> disjoint_from W a n'.
Proof.
  induction W as [|[lo hi] W IH]; cbn; intros a n n' H Hn; [exact I|].
  destruct H as [H1 H2]. split; [lia| exact (IH a n n' H2 Hn)].
Qed.

(* [comment removed for export] *)
Lemma aframe_tr : forall A W m m', aframe A m -> munch W m m' -> wmono a0segs m m' ->
  disjoint_from W (a_P A + 96) 400 -> disjoint_from W (a_P A + 728) 120 -> disjoint_from W (a_fb A) 64 -> disjoint_from W (a_shf A) 8 ->
  aframe A m'.
Proof.
  intros A W m m' (zt & ng & jg & j24 & pos & j38 & fl & GEO & NG & FLP & FRM & FRT & FF & FS) MU WM D1 D2 D3 D4.
  assert (D3a : disjoint_from W (a_fb A) 56) by (apply (disjoint_from_le W _ 64); [exact D3| lia]).
  assert (D3b : disjoint_from W (a_fb A + 56) 8).
  { clear - D3. induction W as [|[lo hi] W IH]; cbn in *; [exact I|]. destruct D3 as [H1 H2]. split; [lia| exact (IH H2)]. }
  exists zt, ng, jg, j24, pos, j38, fl. split; [exact GEO|]. split; [exact NG|].
  split; [exact (ro_cells_transport a0segs W m m' _ _ FLP MU D3b)|].
  split; [exact (rw_cells_transport a0segs W m m' _ _ FRM MU WM D1)|].
  split. { apply (rw_cells_transport a0segs W m m' _ _ FRT MU WM). apply (disjoint_from_le W _ 120); [exact D2|].
           cbn [cells_size csize FT_REGS Nat.add]. destruct NG as [-> | ->]; cbn; lia. }
  split; [exact (rw_cells_transport a0segs W m m' _ _ FF MU WM D3a)|].
  exact (rw_cells_transport a0segs W m m' _ _ FS MU WM D4).
Qed.

(* [comment removed for export] *)
Lemma aframe_mid : forall A m, aframe A m -> exists zt : word, rw_cells a0segs m (a_P A + 96) (FM_CELLS A zt).
Proof. intros A m (zt & ng & jg & j24 & pos & j38 & fl & GEO & NG & FLP & FRM & _). exists zt. exact FRM. Qed.

(* [comment removed for export] *)
Lemma aframe_gb_tr : forall ihi A m m', act_ok ihi A -> aframe A m ->
  munch [(b_s (a_cx A), b_s (a_cx A) + 68); (b_strm (a_cx A), b_strm (a_cx A) + 20); (a_P A, a_P A + 96); (a_P A + 496, a_P A + 728)] m m' -> wmono a0segs m m' -> aframe A m'.
Proof.
  intros ihi A m m' AOK AF MU WM.
  pose proof (alin_core _ _ AOK) as LIN.
  pose proof (act_sep_fb _ _ AOK) as (F1 & F2 & _ & _). pose proof (act_sep_shf _ _ AOK) as (H1 & H2 & _).
  apply (aframe_tr A _ m m' AF MU WM); cbn [disjoint_from].
  - clear F1 F2 H1 H2. lia.
  - clear F1 F2 H1 H2. lia.
  - clear H1 H2. lia.
  - clear F1 F2. lia.
Qed.
End ACeilS1.

(* [comment removed for export] *)
Ltac open_aframe AF :=
  let zt := fresh "zt" in let ng := fresh "ng" in let jg := fresh "jg" in let j24 := fresh "j24" in let pos := fresh "pos" in let j38 := fresh "j38" in
  let fl := fresh "fl" in
  destruct AF as (zt & ng & jg & j24 & pos & j38 & fl & GEO & NG & FLP & FRM & FRT & FF & FS); unfold FM_CELLS in FRM.
Ltac view_aframe_mid AF :=
  let zt := fresh "zt" in destruct (aframe_mid _ _ AF) as [zt FRM]; unfold FM_CELLS in FRM.
Ltac close_aframe :=
  lazymatch goal with |- aframe ?A ?m =>
    match goal with
    | FRM : rw_cells _ m (a_P A + 96)%Z _, FRT : rw_cells _ m (a_P A + 728)%Z _, FF : rw_cells _ m (a_fb A) _, FS : rw_cells _ m (a_shf A) _,
      FLP : ro_cells _ m (a_fb A + 56)%Z _,
      GEO : (a_P A + 728 + Z.of_nat ?ng + 104 = _)%Z, NG : (?ng = 0 \/ ?ng = 16)%nat |- _ =>
        unfold aframe; do 7 eexists; split; [exact GEO|]; split; [exact NG|]; split; [exact FLP|]; split; [unfold FM_CELLS; exact FRM|]; split; [exact FRT|]; split; [exact FF| exact FS]
    end
  end.

(* [comment removed for export] *)
Notation A0FL A mm w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 :=
  (rw_cells a0segs mm (a_P A) [C8 w0; C8 w8; C8 w16; C8 w24; C8 w32; C8 w40; C8 w48; C8 w56; C8 w64; C8 w72; C8 w80; C8 w88]) (only parsing).
Notation A0FH A mm w496 w504 w512 w520 w528 w536 w544 w552 w560 w568 w576 w584 w592 w600 w608 w616 w624 w632 w640 w648 w656 w664 w672 w680 w688 w696 w704 w712 w720 :=
  (rw_cells a0segs mm (a_P A + 496)
     [C8 w496; C8 w504; C8 w512; C8 w520; C8 w528; C8 w536; C8 w544; C8 w552; C8 w560; C8 w568; C8 w576; C8 w584; C8 w592; C8 w600; C8 w608; C8 w616; C8 w624; C8 w632; C8 w640; C8 w648; C8 w656; C8 w664; C8 w672; C8 w680; C8 w688; C8 w696; C8 w704; C8 w712; C8 w720]) (only parsing).
