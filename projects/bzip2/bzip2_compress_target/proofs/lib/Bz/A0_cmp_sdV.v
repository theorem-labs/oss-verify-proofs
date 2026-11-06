(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib SegsA0.
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
Record sdw := SDW { w1336 : word; w1344 : word; w1352 : word; w1360 : word; w1376 : word; w1384 : word; w1400 : word; w1408 : word }.

Section ACeilS1. Context {BZP : BzParams} {ACEIL__ : ACeil}.

(* [comment removed for export] *)
Definition sd_loA (cx : cctx) (A nG FB SHF SHE : Z) (w16 w24 : word) : list cell :=
  let E := c_E cx in
  [C8 w16; C8 w24; C8 (Z_to_bv 64 FB); C8 (Z_to_bv 64 FB); C8 (Z_to_bv 64 (FB + 128)); C8 (Z_to_bv 64 SHF); C8 (Z_to_bv 64 2147548970); C8 (Z_to_bv 64 784720);
   C8 (Z_to_bv 64 38998); C8 (Z_to_bv 64 38740); C8 (Z_to_bv 64 37708); C8 (Z_to_bv 64 51640); C8 (Z_to_bv 64 (flag6 nG));
   C8 (Z_to_bv 64 (4 * A)); C8 (Z_to_bv 64 (SHE + 82)); C8 (Z_to_bv 64 (E + 656)); C8 (Z_to_bv 64 E)].
Definition sd_loB (cx : cctx) (A nG nIU SHE : Z) (w208 : word) : list cell :=
  let E := c_E cx in
  [C8 (Z_to_bv 64 (E + 37708)); C8 (Z_to_bv 64 (E + 51640)); C8 (Z_to_bv 64 (E + 668)); C8 (Z_to_bv 64 (SHE + 83)); C8 (Z_to_bv 64 A);
   C8 (Z_to_bv 64 nG); C8 w208; C8 (Z_to_bv 64 (c_A1 cx)); C8 (Z_to_bv 64 nIU)].
(* [comment removed for export] *)
Definition sd_hi (cx : cctx) (A nG nSel : Z) (H : sdw) : list cell :=
  let E := c_E cx in
  [C8 (w1336 H); C8 (w1344 H); C8 (w1352 H); C8 (w1360 H); C8 (Z_to_bv 64 (flag6 nG)); C8 (w1376 H); C8 (w1384 H);
   C8 (Z_to_bv 64 (E + 1704)); C8 (w1400 H); C8 (w1408 H); C8 (Z_to_bv 64 A); C8 (Z_to_bv 64 nSel); C8 (Z_to_bv 64 (E + 39256))].

(* [comment removed for export] *)
Definition sdWA (cx : cctx) (P : Z) : list (Z * Z) :=
  [(c_E cx + 116, c_E cx + 120); (c_E cx + 640, c_E cx + 648); (c_A2 cx, c_A2 cx + ARR2_SIZE); (P + 1336, P + 1440); (P + 1472, P + 1488)].

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
Definition sd_ro (cx : cctx) (e : est) (A nG P FB SHF SHE : Z) (w16 w24 w208 : word) (m : word -> option byte) : Prop :=
  u8arr a0segs m (c_A1 cx) (zb8 (e_arr1 e) ARR1_SIZE) /\
  u8arr a0segs m (c_E cx + 128) (ovb (e_inUse e) (jseg (c_J cx) 128 256) 256) /\
  u8arr a0segs m (c_E cx + 19706) (ovb (e_selectorMtf e) (jseg (c_J cx) 19706 18002) 18002) /\
  u8arr a0segs m (c_E cx + 1704) (ovb (e_selector e) (jseg (c_J cx) 1704 18002) 18002) /\
  u8arr a0segs m (c_E cx + 37708) (ovb (e_len e) (jseg (c_J cx) 37708 1548) 1548) /\
  u32arr a0segs m (c_E cx + 39256) (ovw (e_code e) (jseg (c_J cx) 39256 6192) 1548) /\
  rw_cells a0segs m (P + 16) (sd_loA cx A nG FB SHF SHE w16 w24) /\
  rw_cells a0segs m (P + 160) (sd_loB cx A nG (e_nInUse e) SHE w208).
(* [comment removed for export] *)
Definition sd_vw (cx : cctx) (e : est) (A nG P FB SHF SHE : Z) (w16 w24 w208 : word) (m0 : word -> option byte) : Prop :=
  forall m : word -> option byte, munch (sdWA cx P) m0 m -> sd_ro cx e A nG P FB SHF SHE w16 w24 w208 m.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition MA3 (cx : cctx) (g : eg) (e : est) (A nG nSel P : Z) (m0 : word -> option byte) (H : sdw) (i16 : list byte) (b : bw) (m : word -> option byte) : Prop :=
  rw_cells a0segs m (c_E cx) (EHEAD1 cx g (est_set_bw e b)) /\
  rw_cells a0segs m (c_E cx + 640) (EHEAD2 cx g (est_set_bw e b)) /\
  u8arr a0segs m (c_A2 cx) (zb8 (zbl (e_arr2 e) (e_nblock e) b) ARR2_SIZE) /\
  rw_cells a0segs m (P + 1336) (sd_hi cx A nG nSel H) /\
  u8arr a0segs m (P + 1472) i16 /\
  mem_inv a0segs m /\
  munch (sdWA cx P) m0 m /\ wmono a0segs m0 m.

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
  unfold sd_hi in HI; cbv zeta in HI; cbn [w1336 w1344 w1352 w1360 w1376 w1384 w1400 w1408] in HI.

Ltac closeMA3 Gmtf Gbs Gzb :=
  split; [|split; [| repeat (split; [eassumption|]); eassumption]];
  [ unfold EHEAD1; cbn_est; rewrite Gzb, Gmtf; eassumption
  | unfold EHEAD2; cbn_est; rewrite Gbs, Gmtf; eassumption ].

(* [comment removed for export] *)
Ltac openVW VW :=
  let AR1 := ident:(AR1) in let INU := ident:(INU) in let SLM := ident:(SLM) in let SEL := ident:(SEL) in let LEN := ident:(LEN) in
  let COD := ident:(COD) in let LOA := ident:(LOA) in let LOB := ident:(LOB) in
  lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      lazymatch goal with
      | MU' : munch (sdWA _ _) _ mm |- _ => pose proof (VW mm MU') as (AR1 & INU & SLM & SEL & LEN & COD & LOA & LOB)
      | MU' : munch _ _ mm |- _ => pose proof (VW mm ltac:(unfold sdWA; exact MU')) as (AR1 & INU & SLM & SEL & LEN & COD & LOA & LOB)
      end
  end;
  unfold sd_loA in LOA; unfold sd_loB in LOB; cbv zeta in LOA, LOB.
Ltac closeVW :=
  let AR1 := ident:(AR1) in let INU := ident:(INU) in let SLM := ident:(SLM) in let SEL := ident:(SEL) in let LEN := ident:(LEN) in
  let COD := ident:(COD) in let LOA := ident:(LOA) in let LOB := ident:(LOB) in
  clear AR1 INU SLM SEL LEN COD LOA LOB.
