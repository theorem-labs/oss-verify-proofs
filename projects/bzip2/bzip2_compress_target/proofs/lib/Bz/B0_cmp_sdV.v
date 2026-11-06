(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib SegsA0 SegsB0.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzTac BzArr BzCMem BzCStream BzCState BzArrD CmpMem CmpCut CmpCutSM CmpCutSmA AsanKit.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.A Require Import Shadow.
From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Open Scope Z_scope.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzParams.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpCut6.   (* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpLiaP.   (* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Record sdw := SDW { w1400 : word; w1408 : word; w1416 : word; w1424 : word; w1432 : word; w1448 : word; w1456 : word; w1472 : word; w1488 : word; w1496 : word; w1504 : word;
                     w1512 : word; w1520 : word; w1528 : word }.

Section ACeilS1. Context {BZP : BzParams} {ACEIL__ : ACeil}.

(* [comment removed for export] *)
Definition sd_loA (cx : cctx) (FB SHF SHE : Z) (w64 w72 w104 : word) : list cell :=
  let E := c_E cx in
  [C8 (Z_to_bv 64 FB); C8 (Z_to_bv 64 SHF); C8 (Z_to_bv 64 FB); C8 (Z_to_bv 64 E); C8 w64; C8 w72; C8 (Z_to_bv 64 (FB + 128)); C8 (Z_to_bv 64 (SHE + 83));
   C8 (Z_to_bv 64 (E + 668)); C8 w104; C8 (Z_to_bv 64 (SHE + 82)); C8 (Z_to_bv 64 (E + 656)); C8 (Z_to_bv 64 (E + 51640))].
(* [comment removed for export] *)
Definition sd_hi (cx : cctx) (nG : Z) (H : sdw) : list cell :=
  let E := c_E cx in
  [C8 (Z_to_bv 64 (E + 1704)); C8 (Z_to_bv 64 (18446744073709551615 - (E + 1704))); C8 (w1400 H); C8 (w1408 H); C8 (w1416 H); C8 (w1424 H); C8 (w1432 H);
   C8 (Z_to_bv 64 (flag6 nG)); C8 (w1448 H); C8 (w1456 H); C8 (Z_to_bv 64 (E + 37708)); C8 (w1472 H); C8 (Z_to_bv 64 nG); C8 (w1488 H); C8 (w1496 H); C8 (w1504 H);
   C8 (w1512 H); C8 (w1520 H); C8 (w1528 H); C8 (Z_to_bv 64 1); C8 (Z_to_bv 64 1); C8 (Z_to_bv 64 (c_A1 cx)); C8 (Z_to_bv 64 (18446744073709551615 - (E + 37708)))].

(* [comment removed for export] *)
Definition sdWA (cx : cctx) (P : Z) : list (Z * Z) :=
  [(c_E cx + 116, c_E cx + 120); (c_E cx + 640, c_E cx + 648); (c_A2 cx, c_A2 cx + ARR2_SIZE); (P + 1384, P + 1568); (P + 1576, P + 1592)].

(* [comment removed for export] *)
Lemma wr_at_munch : forall segs W (m m' : word -> option byte) A n, wr_at segs m A n -> munch W m m' -> disjoint_from W A n -> wr_at segs m' A n.
Proof.
  intros segs W m m' A n (Ha & Hn & H) MU D. split; [lia|]. split; [lia|]. intros i Hi.
  specialize (H i Hi). unfold wview in *. rewrite (MU (wa (A + i))); [exact H|].
  eapply disjoint_outside; [exact D|]. rewrite wa_unsigned by lia. lia.
Qed.
Lemma u8arr_munch : forall segs W (m m' : word -> option byte) A bs, u8arr segs m A bs -> munch W m m' -> disjoint_from W A (Z.of_nat (length bs)) -> u8arr segs m' A bs.
Proof. intros segs W m m' A bs [Hb Hw] MU D. split; [eapply bytes_at_transport; eauto| eapply wr_at_munch; eauto]. Qed.
Lemma u32arr_munch : forall segs W (m m' : word -> option byte) A ws, u32arr segs m A ws -> munch W m m' -> disjoint_from W A (4 * Z.of_nat (length ws)) -> u32arr segs m' A ws.
Proof.
  intros segs W m m' A ws [Hb Hw] MU D. split; [| eapply wr_at_munch; eauto].
  eapply bytes_at_transport; eauto. rewrite u32s_length. replace (Z.of_nat (4 * length ws)) with (4 * Z.of_nat (length ws)) by lia. exact D.
Qed.
Lemma rw_cells_munch : forall segs W (m m' : word -> option byte) A cs, rw_cells segs m A cs -> munch W m m' -> disjoint_from W A (Z.of_nat (cells_size cs)) -> rw_cells segs m' A cs.
Proof.
  intros segs W m m' A cs [[Hwf Hb] Hw] MU D. split; [split; [exact Hwf|]| eapply wr_at_munch; eauto].
  eapply bytes_at_transport; eauto. rewrite cells_bytes_length by assumption. exact D.
Qed.

(* [comment removed for export] *)
Definition sd_ro (cx : cctx) (e : est) (P FB SHF SHE : Z) (w64 w72 w104 : word) (m : word -> option byte) : Prop :=
  u8arr b0segs m (c_A1 cx) (zb8 (e_arr1 e) ARR1_SIZE) /\
  u8arr b0segs m (c_E cx + 128) (ovb (e_inUse e) (jseg (c_J cx) 128 256) 256) /\
  u8arr b0segs m (c_E cx + 19706) (ovb (e_selectorMtf e) (jseg (c_J cx) 19706 18002) 18002) /\
  u8arr b0segs m (c_E cx + 1704) (ovb (e_selector e) (jseg (c_J cx) 1704 18002) 18002) /\
  u8arr b0segs m (c_E cx + 37708) (ovb (e_len e) (jseg (c_J cx) 37708 1548) 1548) /\
  u32arr b0segs m (c_E cx + 39256) (ovw (e_code e) (jseg (c_J cx) 39256 6192) 1548) /\
  rw_cells b0segs m (P + 32) (sd_loA cx FB SHF SHE w64 w72 w104).
(* [comment removed for export] *)
Definition sd_vw (cx : cctx) (e : est) (P FB SHF SHE : Z) (w64 w72 w104 : word) (m0 : word -> option byte) : Prop :=
  forall m : word -> option byte, munch (sdWA cx P) m0 m -> sd_ro cx e P FB SHF SHE w64 w72 w104 m.

(* [comment removed for export] *)
Lemma sd_vw_intro : forall (cx : cctx) (e : est) (P FB SHF SHE : Z) (w64 w72 w104 : word) (m0 : word -> option byte),
  cctx_ok cx -> cctx_sep cx -> CEIL <= P -> P + 1712 <= 18446744073709551616 ->
  sd_ro cx e P FB SHF SHE w64 w72 w104 m0 -> sd_vw cx e P FB SHF SHE w64 w72 w104 m0.
Proof.
  intros cx e P FB SHF SHE w64 w72 w104 m0 CX SEP CEP PHI RO m MU.
  pose proof CX as CXL. bz_ceil; bz_params. unfold cctx_ok, ESTATE_SIZE, FTAB_WORDS, BZFILE_SIZE, CEIL in CXL. cbv zeta in CXL.
  cps_destruct CXL as (XE0 & XE1 & XA10 & XA11 & XA20 & XA21 & _).
  pose proof SEP as SP. unfold cctx_sep, apart, ESTATE_SIZE, FTAB_WORDS, BZFILE_SIZE in SP. cbv zeta in SP.
  cps_destruct SP as (AEA1 & AEA2 & _ & _ & _ & AA12 & _).
  unfold CEIL in CEP. unfold sdWA in MU.
  destruct RO as (AR1 & INU & SLM & SEL & LEN & COD & LOA).
  unfold sd_ro. refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _)))))).
  - eapply u8arr_munch; [exact AR1| exact MU|]. rewrite zb8_length by lia. cbn [disjoint_from]. repeat split; lia.
  - eapply u8arr_munch; [exact INU| exact MU|]. rewrite ovb_length by lia. cbn [disjoint_from]. repeat split; lia.
  - eapply u8arr_munch; [exact SLM| exact MU|]. rewrite ovb_length by lia. cbn [disjoint_from]. repeat split; lia.
  - eapply u8arr_munch; [exact SEL| exact MU|]. rewrite ovb_length by lia. cbn [disjoint_from]. repeat split; lia.
  - eapply u8arr_munch; [exact LEN| exact MU|]. rewrite ovb_length by lia. cbn [disjoint_from]. repeat split; lia.
  - eapply u32arr_munch; [exact COD| exact MU|]. rewrite ovw_length by lia. cbn [disjoint_from]. repeat split; lia.
  - eapply rw_cells_munch; [exact LOA| exact MU|]. cbn [disjoint_from sd_loA cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. repeat split; lia.
Qed.

(* [comment removed for export] *)
Definition MA3 (cx : cctx) (g : eg) (e : est) (nG P : Z) (m0 : word -> option byte) (H : sdw) (i16 : list byte) (b : bw) (m : word -> option byte) : Prop :=
  rw_cells b0segs m (c_E cx) (EHEAD1 cx g (est_set_bw e b)) /\
  rw_cells b0segs m (c_E cx + 640) (EHEAD2 cx g (est_set_bw e b)) /\
  u8arr b0segs m (c_A2 cx) (zb8 (zbl (e_arr2 e) (e_nblock e) b) ARR2_SIZE) /\
  rw_cells b0segs m (P + 1384) (sd_hi cx nG H) /\
  u8arr b0segs m (P + 1576) i16 /\
  mem_inv b0segs m /\
  munch (sdWA cx P) m0 m /\ wmono b0segs m0 m.

End ACeilS1.

(* [comment removed for export] *)
Ltac cbn_est_in H :=
  cbn [e_mode e_state e_avail_in_expect e_arr1 e_arr2 e_ftab e_origPtr e_state_in_ch e_state_in_len e_nblock e_state_out_pos
       e_nInUse e_inUse e_unseqToSeq e_bw e_blockCRC e_combinedCRC e_blockNo e_nMTF e_mtfFreq e_selector e_selectorMtf
       e_len e_code e_rfreq e_len_pack est_set_bw] in H.
Ltac cbn_est :=
  cbn [e_mode e_state e_avail_in_expect e_arr1 e_arr2 e_ftab e_origPtr e_state_in_ch e_state_in_len e_nblock e_state_out_pos
       e_nInUse e_inUse e_unseqToSeq e_bw e_blockCRC e_combinedCRC e_blockNo e_nMTF e_mtfFreq e_selector e_selectorMtf
       e_len e_code e_rfreq e_len_pack est_set_bw].

(* [comment removed for export] *)
Ltac openMA3 Gmtf Gbs Gzb H :=
  let EH1 := ident:(EH1) in let EH2 := ident:(EH2) in let HI := ident:(HI) in let MU := ident:(MU) in
  cps_destruct H as (?EH1 & ?EH2 & ?AR2 & ?HI & ?I16 & ?MI & ?MU & ?WM);
  unfold sdWA in MU;
  unfold EHEAD1, EHEAD2 in EH1, EH2; cbn_est_in EH1; cbn_est_in EH2;
  rewrite Gbs, Gmtf in EH2; rewrite Gzb, Gmtf in EH1;
  unfold sd_hi in HI; cbv zeta in HI; cbn [w1400 w1408 w1416 w1424 w1432 w1448 w1456 w1472 w1488 w1496 w1504 w1512 w1520 w1528] in HI.

Ltac closeMA3 Gmtf Gbs Gzb :=
  split; [|split; [| repeat (split; [eassumption|]); eassumption]];
  [ unfold EHEAD1; cbn_est; rewrite Gzb, Gmtf; eassumption
  | unfold EHEAD2; cbn_est; rewrite Gbs, Gmtf; eassumption ].

(* [comment removed for export] *)
Ltac openVW VW :=
  let AR1 := ident:(AR1) in let INU := ident:(INU) in let SLM := ident:(SLM) in let SEL := ident:(SEL) in let LEN := ident:(LEN) in
  let COD := ident:(COD) in let LOA := ident:(LOA) in
  lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      lazymatch goal with
      | MU' : munch (sdWA _ _) _ mm |- _ => pose proof (VW mm MU') as (AR1 & INU & SLM & SEL & LEN & COD & LOA)
      | MU' : munch _ _ mm |- _ => pose proof (VW mm ltac:(unfold sdWA; exact MU')) as (AR1 & INU & SLM & SEL & LEN & COD & LOA)
      end
  end;
  unfold sd_loA in LOA; cbv zeta in LOA.
Ltac closeVW :=
  let AR1 := ident:(AR1) in let INU := ident:(INU) in let SLM := ident:(SLM) in let SEL := ident:(SEL) in let LEN := ident:(LEN) in
  let COD := ident:(COD) in let LOA := ident:(LOA) in
  clear AR1 INU SLM SEL LEN COD LOA.
