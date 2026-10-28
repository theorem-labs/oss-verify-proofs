(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas FseReadSound ZdFrame ZdDCtx ZdSeqTable.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import StrFun STRW_tac WStr FseWalkKit FseWalkMem MemRange ZdCellKit ZdWalkKit ZdSeqBuildW ZdSeqBuildW6 SepHide.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg RF_fse_iface RF_fse_rd_err RZ_blk_iface RZ_blk_iface2 RZ_bfse seqH_kit seqH_kit_seq.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition bs_hyps (SPV lo DTS DTP SRC W BASE BITS : Z) (dlen wlen slen : Z) : Prop :=
  626 <= wlen /\ 0 <= slen <= 1048576
  /\ 4096 <= DTS /\ DTS + dlen < 2^47 /\ 4096 <= DTP /\ DTP + 8 < 2^47 /\ 4096 <= W /\ W + wlen < 2^47
  /\ 4096 <= SRC /\ SRC + slen < 2^47 /\ 4096 <= BASE < 2^47 /\ 4096 <= BITS < 2^47
  /\ lo <= SPV - 448 /\ 4096 <= lo /\ SPV + 16 < 2^47
  /\ (DTS + dlen <= lo \/ SPV <= DTS) /\ (DTP + 8 <= lo \/ SPV <= DTP) /\ (W + wlen <= lo \/ SPV <= W)
  /\ (SRC + slen <= lo \/ SPV <= SRC) /\ (BASE + 212 <= lo \/ SPV <= BASE) /\ (BITS + 53 <= lo \/ SPV <= BITS)
  /\ (DTS + dlen <= DTP \/ DTP + 8 <= DTS) /\ (DTS + dlen <= W \/ W + wlen <= DTS)
  /\ (DTS + dlen <= SRC \/ SRC + slen <= DTS) /\ (DTS + dlen <= BASE \/ BASE + 212 <= DTS)
  /\ (DTS + dlen <= BITS \/ BITS + 53 <= DTS) /\ (DTS + dlen <= SPV \/ SPV + 16 <= DTS)
  /\ (DTP + 8 <= W \/ W + wlen <= DTP) /\ (DTP + 8 <= SRC \/ SRC + slen <= DTP) /\ (DTP + 8 <= BASE \/ BASE + 212 <= DTP)
  /\ (DTP + 8 <= BITS \/ BITS + 53 <= DTP) /\ (DTP + 8 <= SPV \/ SPV + 16 <= DTP)
  /\ (W + wlen <= SRC \/ SRC + slen <= W) /\ (W + wlen <= BASE \/ BASE + 212 <= W)
  /\ (W + wlen <= BITS \/ BITS + 53 <= W) /\ (W + wlen <= SPV \/ SPV + 16 <= W).
Ltac open_bsh HY := pose proof HY as (WLEN & SLEN & DTSL & DTSH & DTPL & DTPH & WL & WH & SRCL & SRCH & BASER & BITSR & LOS & LO0 & SPH
                                      & OFFDTS & OFFDTP & OFFW & OFFSRC & OFFBASE & OFFBITS & DTSDTP & DTSW & DTSSRC & DTSBASE & DTSBITS & DTSSP
                                      & DTPW & DTPSRC & DTPBASE & DTPBITS & DTPSP & WSRC & WBASE & WBITS & WSP).


(* [comment removed for export] *)
Lemma read_ncount_err_val : forall nc0 msv buf e, all_bytes buf -> 0 <= msv -> msv + 1 <= FseNCount.Zlength nc0 ->
  read_ncount nc0 msv buf = Err e -> e = 20 \/ e = 44.
Proof.
  intros nc0 msv buf e HB Hm HL. unfold read_ncount.
  destruct (Z.ltb_spec (FseNCount.Zlength buf) 8) as [Hs|Hl].
  - set (buf8 := buf ++ repeat 0 (Z.to_nat (8 - FseNCount.Zlength buf))).
    assert (HB8 : all_bytes buf8).
    { subst buf8. apply Forall_all_bytes. apply Forall_app. split; [apply all_bytes_Forall; exact HB|].
      apply Forall_forall. intros x Hx. apply repeat_spec in Hx. lia. }
    assert (HL8 : FseNCount.Zlength buf8 = 8) by (subst buf8; unfold FseNCount.Zlength in *; rewrite length_app, repeat_length; lia).
    destruct (read_ncount_body8 buf8 (msv + 1) nc0) as [[[[nc m1] tl] n]|e1| |] eqn:E; cbn [bind]; try discriminate.
    + destruct (Z.ltb_spec (FseNCount.Zlength buf) n); intros Q; [injection Q as <-; left; reflexivity | discriminate Q].
    + intros Q. injection Q as <-.
      destruct (read_body8_err_inv buf8 (msv + 1) nc0 e1 ltac:(unfold FseNCount.Zlength in *; lia) HB8 ltac:(unfold FseNCount.Zlength in *; lia) E) as [[_ ->]|[_ [-> _]]]; auto.
  - intros E.
    destruct (read_body8_err_inv buf (msv + 1) nc0 e ltac:(unfold FseNCount.Zlength in *; lia) HB ltac:(unfold FseNCount.Zlength in *; lia) E) as [[_ ->]|[_ [-> _]]]; auto.
Qed.

Lemma fse_read_ok_cor :
  forall (ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : fmem) (SPV NC MSVP TLP BUF : Z)
         (rt0 buf : list Z) (msv0 lo : Z) (tl0 : word) (rt : list Z) (msv tl n : Z),
  u8arr usegs m NC (u16s (map (Z_to_bv 64) rt0)) ->
  rw_cells usegs m MSVP [C4 (Z_to_bv 64 msv0)] ->
  rw_cells usegs m TLP [C4 tl0] ->
  bytes_at usegs m BUF (map (Z_to_bv 8) buf) -> Forall (fun c => 0 <= c < 256) buf ->
  0 <= msv0 <= 255 -> msv0 + 1 <= zlen rt0 -> zlen buf <= 1048576 ->
  0 < NC -> NC mod 2 = 0 -> 0 < MSVP -> MSVP mod 4 = 0 -> 0 < TLP -> TLP mod 4 = 0 ->
  0 < BUF -> BUF + zlen buf + 8 <= 2^64 ->
  stk usegs m lo SPV -> lo <= SPV - FSE_READ_STACK -> 0 <= SPV < 2^64 ->
  (NC + 2 * zlen rt0 <= lo \/ SPV <= NC) -> (MSVP + 4 <= lo \/ SPV <= MSVP) ->
  (TLP + 4 <= lo \/ SPV <= TLP) -> (BUF + zlen buf <= lo \/ SPV <= BUF) ->
  (NC + 2 * zlen rt0 <= MSVP \/ MSVP + 4 <= NC) -> (NC + 2 * zlen rt0 <= TLP \/ TLP + 4 <= NC) ->
  (NC + 2 * zlen rt0 <= BUF \/ BUF + zlen buf <= NC) ->
  (MSVP + 4 <= TLP \/ TLP + 4 <= MSVP) ->
  (MSVP + 4 <= BUF \/ BUF + zlen buf <= MSVP) -> (TLP + 4 <= BUF \/ BUF + zlen buf <= TLP) ->
  mem_inv usegs m ->
  a0 = Z_to_bv 64 NC -> a1 = Z_to_bv 64 MSVP -> a2 = Z_to_bv 64 TLP -> a3 = Z_to_bv 64 BUF -> a4 = Z_to_bv 64 (zlen buf) ->
  read_ncount rt0 msv0 buf = Ok (rt, msv, tl, n) ->
  evt usegs (fse_read_post ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV NC MSVP TLP rt0 rt msv tl n lo m)
    (MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 PFSE_READ) fc None m (seg_rom usegs)).
Proof.
  intros until n. intros H1 H2 H3 H4 H5 H6 H7 H8 N1 N2 N3 N4 N5 N6 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23 H24 E0 E1 E2 E3 E4 RN.
  eapply evt_mono.
  - pose proof fse_read_any_proof as ANY. unfold fse_read_any_stmt, fse_read_any_stmt_at in ANY.
    eapply (ANY ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m SPV NC MSVP TLP BUF rt0 buf msv0 lo tl0); eassumption.
  - intros ms' [(rt' & msv' & tl' & n' & RN' & P) | (e & RN' & _)]; [| congruence].
    rewrite RN in RN'. injection RN' as <- <- <- <-. exact P.
Qed.

Lemma fse_read_err_cor :
  forall (ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : fmem) (SPV NC MSVP TLP BUF : Z)
         (rt0 buf : list Z) (msv0 lo : Z) (tl0 : word) (e : Z),
  u8arr usegs m NC (u16s (map (Z_to_bv 64) rt0)) ->
  rw_cells usegs m MSVP [C4 (Z_to_bv 64 msv0)] ->
  rw_cells usegs m TLP [C4 tl0] ->
  bytes_at usegs m BUF (map (Z_to_bv 8) buf) -> Forall (fun c => 0 <= c < 256) buf ->
  0 <= msv0 <= 255 -> msv0 + 1 <= zlen rt0 -> zlen buf <= 1048576 ->
  0 < NC -> NC mod 2 = 0 -> 0 < MSVP -> MSVP mod 4 = 0 -> 0 < TLP -> TLP mod 4 = 0 ->
  0 < BUF -> BUF + zlen buf + 8 <= 2^64 ->
  stk usegs m lo SPV -> lo <= SPV - FSE_READ_STACK -> 0 <= SPV < 2^64 ->
  (NC + 2 * zlen rt0 <= lo \/ SPV <= NC) -> (MSVP + 4 <= lo \/ SPV <= MSVP) ->
  (TLP + 4 <= lo \/ SPV <= TLP) -> (BUF + zlen buf <= lo \/ SPV <= BUF) ->
  (NC + 2 * zlen rt0 <= MSVP \/ MSVP + 4 <= NC) -> (NC + 2 * zlen rt0 <= TLP \/ TLP + 4 <= NC) ->
  (NC + 2 * zlen rt0 <= BUF \/ BUF + zlen buf <= NC) ->
  (MSVP + 4 <= TLP \/ TLP + 4 <= MSVP) ->
  (MSVP + 4 <= BUF \/ BUF + zlen buf <= MSVP) -> (TLP + 4 <= BUF \/ BUF + zlen buf <= TLP) ->
  mem_inv usegs m ->
  a0 = Z_to_bv 64 NC -> a1 = Z_to_bv 64 MSVP -> a2 = Z_to_bv 64 TLP -> a3 = Z_to_bv 64 BUF -> a4 = Z_to_bv 64 (zlen buf) ->
  read_ncount rt0 msv0 buf = Err e ->
  evt usegs (fse_read_err_post ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV NC MSVP TLP rt0 lo m (2^64 - e))
    (MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 PFSE_READ) fc None m (seg_rom usegs)).
Proof.
  intros until e. intros H1 H2 H3 H4 H5 H6 H7 H8 N1 N2 N3 N4 N5 N6 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23 H24 E0 E1 E2 E3 E4 RN.
  eapply evt_mono.
  - pose proof fse_read_any_proof as ANY. unfold fse_read_any_stmt, fse_read_any_stmt_at in ANY.
    eapply (ANY ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m SPV NC MSVP TLP BUF rt0 buf msv0 lo tl0); eassumption.
  - intros ms' [(rt' & msv' & tl' & n' & RN' & _) | (e' & RN' & P)]; [congruence|].
    rewrite RN in RN'. injection RN' as <-. exact P.
Qed.

(* [comment removed for export] *)
Local Ltac transport_chunks segs m a bs ::= transport_chunks_hide segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_hide segs m a bs.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_hide segs m m' MU WM.

Section BST.
  Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : fmem)
            (SPV lo DTS DTP SRC W DFLT BASE BITS ty : Z) (k : seq_kind) (dt0 wb0 : list byte) (srcb : list Z) (oldp nbw frw : word).
  Hypothesis HY : bs_hyps SPV lo DTS DTP SRC W BASE BITS (Z.of_nat (length dt0)) (Z.of_nat (length wb0)) (Z.of_nat (length srcb)).
  Hypothesis DLEN : Z.of_nat (length dt0) = 8 + 8 * 2^(kind_maxLog k).
  Hypothesis ALDTS : DTS mod 4 = 0.
  Hypothesis ALDTP : DTP mod 8 = 0.
  Hypothesis ALBASE : BASE mod 4 = 0.
  Hypothesis ALW : W mod 2 = 0.
  Hypothesis ALSP : SPV mod 16 = 0.
  Hypothesis OLDP : frw <> Z_to_bv 64 0 -> 4096 <= bv_unsigned oldp < 2^47.
  Notation POST := (zd_buildseq_post ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV DTS DTP W DFLT k ty (Z.of_nat (length srcb)) frw oldp dt0
                                     (length wb0) lo m).
  Notation ST pc mm xra x5 x6 x7 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 x28 x29 x30 x31 :=
    (MS (mkR xra (Z_to_bv 64 (SPV + -192)) gp tp x5 x6 x7 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom usegs)).

  (* [comment removed for export] *)
  Definition BS (dt' wb' : list byte) (pv : word) (m1 : fmem) : Prop :=
    u8arr usegs m1 DTS dt' /\ length dt' = length dt0 /\ u8arr usegs m1 W wb' /\ length wb' = length wb0
    /\ rw_cells usegs m1 DTP [C8 pv] /\ stk usegs m1 lo (SPV + -192)
    /\ (exists fb, rw_cells usegs m1 (SPV + -192) [CB 136 fb; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])
    /\ mem_inv usegs m1
    /\ munch [(DTS, DTS + Z.of_nat (length dt0)); (DTP, DTP + 8); (W, W + Z.of_nat (length wb0)); (SPV - 448, SPV)] m m1
    /\ wmono usegs m m1.

  (* [comment removed for export] *)
  Lemma bs_ret : forall m1 dt' wb' pv r xra x5 x6 x7 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 x28 x29 x30 x31,
    BS dt' wb' pv m1 -> 0 <= r < 2^64 -> xa0 = Z_to_bv 64 r ->
    (zd_is_error r = true
     \/ (r <= Z.of_nat (length srcb) /\
         ((ty = 0 /\ pv = Z_to_bv 64 DFLT /\ dt' = dt0)
          \/ (ty = 3 /\ frw <> Z_to_bv 64 0 /\ pv = oldp /\ dt' = dt0)
          \/ ((ty = 1 \/ ty = 2) /\ pv = Z_to_bv 64 DTS /\
              exists t, seq_table_ok k t /\ firstn (length (seq_table_bytes t)) dt' = map (Z_to_bv 8) (seq_table_bytes t))))) ->
    evt usegs POST (ST 0x17774 m1 xra x5 x6 x7 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 x28 x29 x30 x31).
  Proof.
    intros until x31. intros (DTA & DTL' & WA & WL' & DTPC & STK & (fb & FR) & MI & MU & WM) HR -> RES. open_bsh HY. hide_all_disj.
    do 7 zstep. zstep.
    release_frame FR STK SPV.
    zstep. apply evt_done. unfold zd_buildseq_post.
    do 14 eexists. exists m1, r, dt', wb', pv.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact STK|].
    split; [exact DTA|]. split; [exact DTL'|]. split; [exact WA|]. split; [exact WL'|]. split; [exact DTPC|]. split; [exact HR| exact RES].
  Qed.

  (* [comment removed for export] *)
  Definition BS0 (m1 : fmem) : Prop :=
    u8arr usegs m1 DTS dt0 /\ rw_cells usegs m1 DTP [C8 oldp] /\ u8arr usegs m1 W wb0
    /\ bytes_at usegs m1 SRC (map (Z_to_bv 8) srcb)
    /\ bytes_at usegs m1 BASE (u32s (map (Z_to_bv 64) (kind_base k))) /\ bytes_at usegs m1 BITS (map (Z_to_bv 8) (kind_bits k))
    /\ rw_cells usegs m1 SPV [C8 nbw; C8 (Z_to_bv 64 W)]
    /\ stk usegs m1 lo (SPV + -192)
    /\ (exists j, rw_cells usegs m1 (SPV + -192) [CB 132 j; C4 (Z_to_bv 64 (kind_max k)); C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])
    /\ mem_inv usegs m1
    /\ munch [(DTS, DTS + Z.of_nat (length dt0)); (DTP, DTP + 8); (W, W + Z.of_nat (length wb0)); (SPV - 448, SPV)] m m1
    /\ wmono usegs m m1.
  Ltac open_bs0 I := destruct I as (DTA & DTPC & WA & SRCB & BASEB & BITSB & ARGS & STK & (j & FR) & MI & MU & WM).

  Lemma bs0_bs : forall m1, BS0 m1 -> BS dt0 wb0 oldp m1.
  Proof.
    intros m1 I. open_bs0 I.
    pose proof (rw_cells_merge usegs m1 (SPV + -192) [] [CB 132 j; C4 (Z_to_bv 64 (kind_max k))]
                  [C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] FR) as FM.
    cbn [app cells_size csize Nat.add] in FM.
    split; [exact DTA|]. split; [reflexivity|]. split; [exact WA|]. split; [reflexivity|]. split; [exact DTPC|]. split; [exact STK|].
    split; [eexists; exact FM|]. split; [exact MI|]. split; [exact MU| exact WM].
  Qed.

  (* [comment removed for export] *)
  Lemma bs_repeat : forall m1 xra x5 x6 x7 xs0 xs1 xa0 xa2 xa3 xa5 xa6 xa7 xs2 xs3 xs4 xs5 x28 x29 x31,
    BS0 m1 -> ty = 3 ->
    evt usegs POST (ST 0x17710 m1 xra x5 x6 x7 xs0 xs1 xa0 (Z_to_bv 64 DTP) xa2 xa3 (Z_to_bv 64 (kind_maxLog k)) xa5 xa6 xa7 xs2 xs3 xs4 xs5 x28 x29 frw x31).
  Proof.
    intros until x31. intros I TY3. pose proof (bs0_bs m1 I) as BSI. open_bs0 I. open_bsh HY. hide_all_disj.
    zstep. if_cases K3; zify_cond K3.
    - zstep. zstep.
      eapply (bs_ret m1 dt0 wb0 oldp (2^64 - 20)); [exact BSI | lia | apply bv_eq; reflexivity | left; reflexivity].
    - assert (FRNZ : frw <> Z_to_bv 64 0) by (intros E; apply K3; rewrite E; reflexivity).
      zstep. zstep. if_cases K4; zify_cond K4.
      + eapply (bs_ret m1 dt0 wb0 oldp 0); [exact BSI | lia | reflexivity | right; split; [lia|]; right; left; auto].
      + zstep. zstep. zstep. if_cases K5; zify_cond K5.
        * eapply (bs_ret m1 dt0 wb0 oldp 0); [exact BSI | lia | reflexivity | right; split; [lia|]; right; left; auto].
        * assert (ML : kind_maxLog k = 9 \/ kind_maxLog k = 8) by (destruct k; cbn; auto).
          pose proof (OLDP FRNZ) as OR.
          zstep. zstep. uck. rewrite land7_mod8, ALDTP. zstep.
          clear - BSI FRNZ TY3 HY DLEN ML ALDTP OR.
          destruct ML as [ML | ML]; rewrite ML.
          all: zstep; zstep; zstep; zstep; uckz_split.
          all: repeat (zstep; zstep; uck; zstep; zstep; zstep; uckz; zstep; zstep; if_true).
          all: zstep; zstep; uck; zstep; zstep; zstep; uckz; zstep; zstep; if_false; zstep; zstep.
          all: eapply (bs_ret m1 dt0 wb0 oldp 0); [exact BSI | lia | reflexivity | right; split; [lia|]; right; left; auto].
  Qed.

  (* [comment removed for export] *)
  Lemma bs_basic : forall m1 xra x5 x6 x7 xs0 xs1 xa0 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 x28 x30 x31,
    BS0 m1 -> ty = 0 ->
    evt usegs POST (ST 0x175e8 m1 xra x5 x6 x7 xs0 xs1 xa0 (Z_to_bv 64 DTP) xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 x28 (Z_to_bv 64 DFLT) x30 x31).
  Proof.
    intros until x31. intros I TY0. open_bs0 I. open_bsh HY. hide_all_disj.
    zstep. zstep. uck. rewrite land7_mod8, ALDTP. zstep. zstep.
    pose proof (rw_cells_merge usegs _ (SPV + -192) [] [CB 132 j; C4 (Z_to_bv 64 (kind_max k))]
                  [C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] FR) as FM.
    cbn [app cells_size csize Nat.add] in FM.
    eapply (bs_ret _ dt0 wb0 (Z_to_bv 64 DFLT) 0); [ | lia | reflexivity | right; split; [lia|]; left; auto].
    split; [exact DTA|]. split; [reflexivity|]. split; [exact WA|]. split; [reflexivity|]. split; [eassumption|]. split; [exact STK|].
    split; [eexists; exact FM|]. split; [exact MI|]. split; [exact MU| exact WM].
  Qed.

  (* [comment removed for export] *)
  Lemma bs_rle : forall m1 xra x5 x6 x7 xs0 xs1 xa2 xa4 xs2 xs3 xs4 xs5 x29 x30 x31,
    BS0 m1 -> ty = 1 -> Forall (fun c => 0 <= c < 256) srcb ->
    evt usegs POST (ST 0x17678 m1 xra x5 x6 x7 xs0 xs1 (Z_to_bv 64 DTS) (Z_to_bv 64 DTP) xa2 (Z_to_bv 64 (kind_max k)) xa4 (Z_to_bv 64 SRC)
                       (Z_to_bv 64 (Z.of_nat (length srcb))) (Z_to_bv 64 BASE) xs2 xs3 xs4 xs5 (Z_to_bv 64 BITS) x29 x30 x31).
  Proof.
    intros until x31. intros I TY1 FBY. pose proof (bs0_bs m1 I) as BSI. open_bs0 I. open_bsh HY. hide_all_disj.
    assert (KM : 0 <= kind_max k <= 52 /\ 8 <= kind_maxLog k <= 9) by (destruct k; cbn; lia).
    assert (LKB : Z.of_nat (length (kind_bits k)) = kind_max k + 1 /\ Z.of_nat (length (kind_base k)) = kind_max k + 1) by (destruct k; split; reflexivity).
    zstep. if_cases K1; zify_cond K1.
    - (* [comment removed for export] *)
      zstep.
      eapply (bs_ret m1 dt0 wb0 oldp (2^64 - 72)); [exact BSI | lia | apply bv_eq; reflexivity | left; reflexivity].
    - set (sym := Znth 0 srcb).
      pose proof (Forall_Znth _ _ 0 FBY ltac:(lia)) as SYMR. cbv beta in SYMR. fold sym in SYMR.
      pose proof (u8ro_read usegs m1 SRC _ 0 _ (wa SRC) SRCB (nth_error_map_Znth (Z_to_bv 8) srcb 0 ltac:(lia)) ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD0.
      fold sym in RD0.
      zstep. uck.
      zstep.
      cbv beta. rewrite (byte_lit sym) by lia.
      zstep. if_cases K2; zify_cond K2.
      { (* [comment removed for export] *)
        zstep. zstep.
        eapply (bs_ret m1 dt0 wb0 oldp (2^64 - 20)); [exact BSI | lia | apply bv_eq; reflexivity | left; reflexivity]. }
      zstep. zstep. zstep. rewrite (Z.shiftl_mul_pow2 sym 2) by lia. change (2^2) with 4. uck.
      zstep. zstep. zstep. zstep. uckz.
      zstep. uck.
      zstep. zstep. uck.
      zstep. zstep. uck.
      zstep. zstep. zstep. zstep. uckz.
      zstep. uck.
      zstep. zstep. uck.
      zstep. zstep. uck.
      assert (FBITS : Forall (fun v => 0 <= v < 256) (kind_bits k)) by (destruct k; repeat constructor; lia).
      assert (FBASE : Forall (fun v => 0 <= v < 2147483648) (kind_base k)) by (destruct k; repeat constructor; lia).
      pose proof (Forall_Znth _ _ sym FBITS ltac:(lia)) as RBITS. pose proof (Forall_Znth _ _ sym FBASE ltac:(lia)) as RBASE. cbv beta in RBITS, RBASE.
      destruct LKB as [LKB1 LKB2].
      lazymatch goal with |- _ => let a := cur_mem_addr in
        pose proof (u32ro_read usegs _ BASE _ sym _ a BASEB (nth_error_map_Znth (Z_to_bv 64) (kind_base k) sym ltac:(lia)) ltac:(lia) ltac:(unfold wa; f_equal; rewrite ?Z.shiftl_mul_pow2 by lia; lia)) as RD4 end.
      zstep.
      rewrite (sx32w_small (Znth sym (kind_base k))) by lia.
      lazymatch goal with |- _ => let a := cur_mem_addr in
        pose proof (u8ro_read usegs m1 BITS _ sym _ a BITSB (nth_error_map_Znth (Z_to_bv 8) (kind_bits k) sym ltac:(lia)) ltac:(lia) ltac:(addr_tac)) as RD3 end.
      zstep.
      cbv beta. rewrite (byte_lit (Znth sym (kind_bits k))) by lia.
      assert (P8 : 256 <= 2 ^ kind_maxLog k) by (change 256 with (2^8); apply Z.pow_le_mono_r; lia).
      rewrite <- (firstn_skipn 16 dt0) in DTA. apply u8arr_app in DTA. destruct DTA as [HDU RESTU].
      assert (LH : length (firstn 16 dt0) = 16%nat) by (rewrite firstn_length; lia).
      rewrite LH in RESTU. change (Z.of_nat 16) with 16 in RESTU.
      apply rw_cells_of_u8arr in HDU. rewrite LH in HDU.
      assert (DJP : DTP + 8 <= DTS + 16 \/ DTS + 16 + Z.of_nat (length (skipn 16 dt0)) <= DTP) by (unfold hidden in DTSDTP; rewrite skipn_length; lia).
      zstep. zstep. zstep.
      zstep. rewrite le1_lit. mem_after_store.
      zstep.
      zstep.
      zstep.
      zstep. uck.
      zstep. zstep. zstep.
      lazymatch type of HDU with rw_cells _ ?mx _ ?cs => pose proof (rw_cells_merge usegs mx DTS [] cs []) as HDM; rewrite app_nil_r in HDM; specialize (HDM HDU) end.
      cbn [app cells_size csize Nat.add] in HDM.
      apply u8arr_of_rw_cells in HDM.
      lazymatch type of HDM with u8arr _ _ _ ?bs => set (img := bs) in * end.
      assert (LIMG : length img = 16%nat) by reflexivity.
      assert (EIMG : img = map (Z_to_bv 8) (seq_table_bytes (rle_table k sym))).
      { subst img. unfold rle_table, seq_table_bytes. cbn [st_fast st_log st_cells flat_map seqsym_bytes ss_next ss_nbAdd ss_nbBits ss_base cells_bytes cbytes].
        rewrite !map_app. rewrite (le4_Z 0 0 eq_refl), (le2_Z 0 0 eq_refl), (le4_Z _ _ eq_refl). rewrite !app_nil_r. reflexivity. }
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => assert (DTA : u8arr usegs mx DTS (img ++ skipn 16 dt0)) end.
      { apply u8arr_app. split; [exact HDM|]. rewrite LIMG. exact RESTU. }
      pose proof (rw_cells_merge usegs _ (SPV + -192) [] [CB 132 j; C4 (Z_to_bv 64 (kind_max k))]
                    [C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] FR) as FM.
      cbn [app cells_size csize Nat.add] in FM.
      eapply (bs_ret _ (img ++ skipn 16 dt0) wb0 (Z_to_bv 64 DTS) 1); [ | lia | reflexivity | ].
      + split; [exact DTA|]. split; [rewrite length_app, skipn_length, LIMG; lia|]. split; [exact WA|]. split; [reflexivity|].
        split; [eassumption|]. split; [exact STK|]. split; [eexists; exact FM|]. split; [exact MI|]. split; [exact MU| exact WM].
      + right. split; [lia|]. right. right. split; [left; exact TY1|]. split; [reflexivity|].
        exists (rle_table k sym). split; [apply rle_table_ok; lia|].
        replace (length (seq_table_bytes (rle_table k sym))) with (length img) by (rewrite EIMG, length_map; reflexivity).
        rewrite firstn_app, Nat.sub_diag, firstn_O, app_nil_r, firstn_all. exact EIMG.
  Qed.

  (* [comment removed for export] *)
  Lemma bs_frame_merge : forall m2 c22 (nb : list byte) tlw msvw,
    rw_cells usegs m2 (SPV + -192) c22 -> cells_size c22 = 22%nat ->
    u8arr usegs m2 (SPV + -170) nb -> length nb = 106%nat ->
    rw_cells usegs m2 (SPV + -64) [C4 tlw] -> rw_cells usegs m2 (SPV + -60) [C4 msvw] ->
    rw_cells usegs m2 (SPV + -56) [C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    exists fb, rw_cells usegs m2 (SPV + -192) [CB 136 fb; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
  Proof.
    intros m2 c22 nb tlw msvw FA L22 NB LNB TL MSV REST.
    apply rw_cells_of_u8arr in NB. rewrite LNB in NB.
    assert (ALL : rw_cells usegs m2 (SPV + -192) ((c22 ++ [CB 106 nb; C4 tlw; C4 msvw]) ++ [C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])).
    { apply rw_cells_app. split.
      - apply rw_cells_app. split; [exact FA|]. rewrite L22. replace (SPV + -192 + Z.of_nat 22) with (SPV + -170) by lia.
        change [CB 106 nb; C4 tlw; C4 msvw] with ([CB 106 nb] ++ [C4 tlw] ++ [C4 msvw]).
        apply rw_cells_app. split; [exact NB|]. cbn [cells_size csize Nat.add]. replace (SPV + -170 + Z.of_nat _) with (SPV + -64) by lia.
        apply rw_cells_app. split; [exact TL|]. cbn [cells_size csize Nat.add]. replace (SPV + -64 + Z.of_nat _) with (SPV + -60) by lia. exact MSV.
      - rewrite cells_size_app, L22. cbn [cells_size csize Nat.add]. replace (SPV + -192 + Z.of_nat _) with (SPV + -56) by lia. exact REST. }
    pose proof (rw_cells_merge usegs m2 (SPV + -192) [] (c22 ++ [CB 106 nb; C4 tlw; C4 msvw]) [C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ALL) as M.
    rewrite cells_size_app, L22 in M. cbn [app cells_size csize Nat.add] in M.
    eexists. exact M.
  Qed.

  (* [comment removed for export] *)
  Lemma bs_comp : forall m1 xra x5 x6 x7 xs0 xs1 xa2 xa3 xs2 xs3 xs4 xs5 x29 x30 x31,
    BS0 m1 -> ty = 2 -> Forall (fun c => 0 <= c < 256) srcb ->
    evt usegs POST (ST 0x17600 m1 xra x5 x6 x7 xs0 xs1 (Z_to_bv 64 DTS) (Z_to_bv 64 DTP) xa2 xa3 (Z_to_bv 64 (kind_maxLog k)) (Z_to_bv 64 SRC)
                       (Z_to_bv 64 (Z.of_nat (length srcb))) (Z_to_bv 64 BASE) xs2 xs3 xs4 xs5 (Z_to_bv 64 BITS) x29 x30 x31).
  Proof.
    intros until x31. intros I TY2 FBY. pose proof (bs0_bs m1 I) as BSI. open_bs0 I. open_bsh HY. hide_all_disj.
    assert (KM : 0 <= kind_max k <= 52 /\ 8 <= kind_maxLog k <= 9) by (destruct k; cbn; lia).
    assert (LKB : Z.of_nat (length (kind_bits k)) = kind_max k + 1 /\ Z.of_nat (length (kind_base k)) = kind_max k + 1) by (destruct k; split; reflexivity).
    destruct LKB as [LKB1 LKB2].
    do 10 zstep.
    (* [comment removed for export] *)
    assert (LJ : length j = 132%nat) by (pose proof FR as [[Hwf _] _]; exact (proj1 Hwf)).
    pose proof (rw_cells_split_CB usegs m1 (SPV + -192) [] 132 j
                  [C4 (Z_to_bv 64 (kind_max k)); C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] [22; 106; 4]%nat FR eq_refl) as FS.
    cbn [app mk_CB_cells] in FS. clear FR.
    set (j22 := firstn 22 j) in FS. set (j106 := firstn 106 (skipn 22 j)) in FS. set (j4 := firstn 4 (skipn 106 (skipn 22 j))) in FS.
    assert (L106 : length j106 = 106%nat) by (subst j106; rewrite firstn_length, skipn_length; lia).
    assert (L4 : length j4 = 4%nat) by (subst j4; rewrite firstn_length, !skipn_length; lia).
    lazymatch type of FS with rw_cells _ _ _ (?c1 :: ?c2 :: ?c3 :: ?c4 :: ?rest) =>
      change (c1 :: c2 :: c3 :: c4 :: rest) with ([c1] ++ [c2] ++ [c3] ++ [c4] ++ rest) in FS end.
    apply rw_cells_app in FS. destruct FS as [FA FS]. cbn [cells_size csize Nat.add] in FS.
    apply rw_cells_app in FS. destruct FS as [FN FS]. cbn [cells_size csize Nat.add] in FS.
    apply rw_cells_app in FS. destruct FS as [FT FS]. cbn [cells_size csize Nat.add] in FS.
    apply rw_cells_app in FS. destruct FS as [FM FS]. cbn [cells_size csize Nat.add] in FS.
    replace (SPV + -192 + Z.of_nat 22) with (SPV + -170) in * by lia.
    replace (SPV + -170 + Z.of_nat 106) with (SPV + -64) in * by lia.
    replace (SPV + -64 + Z.of_nat 4) with (SPV + -60) in * by lia.
    replace (SPV + -60 + Z.of_nat 4) with (SPV + -56) in * by lia.
    apply u8arr_of_rw_cells in FN.
    destruct (u16s_of_bytes 53 j106 L106) as (rt0 & LRT0 & _ & ERT0). rewrite ERT0 in FN.
    rewrite <- (le4_of_bytes j4 L4) in FT.
    assert (FT' : rw_cells usegs m1 (SPV + -64) [C4 (le_bytes_to_word j4)]).
    { destruct FT as [[Wf B] R]. split; [split|]; [ split; [exact I | exact (proj2 Wf)] | exact B | exact R ]. }
    clear FT. rename FT' into FT.
    assert (NCL : Z.of_nat (length rt0) = 53) by lia.
    zstep.
    destruct (read_ncount_total rt0 (kind_max k) srcb (Forall_all_bytes _ FBY) ltac:(lia) ltac:(unfold FseNCount.Zlength; lia))
      as [(rt & msv & tl & n & RN & LRT & MSVR & TLR & NR & ZER & KEEP & SUMS) | (e & RN)].
    - (* [comment removed for export] *)
      assert (FRS : FSE_READ_STACK = 256) by reflexivity.
      unhide_mentioning SRC.
      eapply evt_cut; [ eapply (fse_read_ok_cor) with (SPV := SPV + -192) (NC := SPV + -170) (MSVP := SPV + -60) (TLP := SPV + -64) (BUF := SRC)
                          (rt0 := rt0) (buf := srcb) (msv0 := kind_max k) (lo := lo) (rt := rt) (msv := msv) (tl := tl) (n := n);
          [ exact FN | exact FM | exact FT | exact SRCB | exact FBY | lia | lia | lia | lia | lia | lia | lia | lia | lia | lia | lia | exact STK | unfold FSE_READ_STACK; lia | lia
          | right; lia | right; lia | right; lia | lia | lia | lia | lia | lia | lia | lia | exact MI
          | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | exact RN ]
        | hide_all_disj; post_call usegs m1 ].
      clear BSI. rename PC into STK. rename PC0 into FN. rename PC1 into FM. rename POST into FT. rename MI0 into MI.
      zstep. zstep. zstep. zstep. if_cases K1; zify_cond K1.
      { exfalso. unfold FseNCount.Zlength in NR. rewrite Z.mod_small in K1 by lia. lia. }
      zstep.
      rewrite (sx32w_small tl) by lia.
      zstep. if_cases K2; zify_cond K2.
      { (* [comment removed for export] *)
        destruct (bs_frame_merge _ _ _ _ _ FA eq_refl FN ltac:(rewrite u16s_length, length_map; lia) FT FM FS) as (fb & FRM).
        eapply (bs_ret _ dt0 wb0 oldp (2^64 - 20)); [ | lia | apply bv_eq; reflexivity | left; reflexivity].
        split; [exact DTA|]. split; [reflexivity|]. split; [exact WA|]. split; [reflexivity|]. split; [exact DTPC|]. split; [exact STK|].
        split; [eexists; exact FRM|]. split; [exact MI|]. split; [exact MU| exact WM]. }
      zstep. zstep. rewrite (sx32w_small msv) by lia.
      zstep. zstep. zstep. zstep. zstep. zstep.
      assert (P2 : 2^tl <= 2^(kind_maxLog k)) by (apply Z.pow_le_mono_r; lia).
      assert (P5 : 32 <= 2^tl) by (change 32 with (2^5); apply Z.pow_le_mono_r; lia).
      set (N := Z.to_nat (8 + 8 * 2^tl)).
      rewrite <- (firstn_skipn N dt0) in DTA. apply u8arr_app in DTA. destruct DTA as [DTA1 DTA2].
      assert (LN : Z.of_nat (length (firstn N dt0)) = 8 + 8 * 2^tl) by (rewrite firstn_length; subst N; lia).
      rewrite LN in DTA2.
      assert (LSK : Z.of_nat (length (skipn N dt0)) = Z.of_nat (length dt0) - (8 + 8 * 2^tl)) by (rewrite skipn_length; subst N; lia).
      destruct (SUMS ltac:(lia)) as [NGE NSUM].
      assert (ZRT : FseNCount.Zlength rt = 53) by (unfold FseNCount.Zlength; lia).
      pose proof zd_buildfse_proof as BF. unfold zd_buildfse_stmt, PZD_BUILDFSE, off_stack, apart in BF.
      eapply evt_cut; [ eapply BF with (SPV := SPV + -192) (lo := lo) (DT := DTS) (NC := SPV + -170) (BASE := BASE) (BITS := BITS) (W := W)
                          (maxSV := msv) (tl := tl) (k := k) (dt0 := firstn N dt0) (wb0 := wb0) (norm := rt);
          [ exact DTA1 | exact LN | exact WA | lia | exact (proj1 FN) | lia | lia | lia | exact NGE | exact NSUM | exact BASEB | exact BITSB
          | lia | lia | lia | lia | lia | lia | lia | lia | exact STK | lia | lia | lia
          | sep_solve | sep_solve | right; lia | sep_solve | sep_solve
          | sep_solve | sep_solve | sep_solve | sep_solve | sep_solve | sep_solve | sep_solve
          | exact ALDTS | exact ALW | lia | exact ALBASE
          | exact MI | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity ]
        | clear BF; hide_all_disj; post_call usegs m0 ].
      rename PC into STK. rename PC0 into TB. rename PC1 into TLOG. rename PC2 into TOK. rename PC3 into WA. rename POST into WLN.
      lazymatch type of TB with u8arr _ _ _ (map _ (seq_table_bytes ?t)) => set (tbl := t) in * end.
      assert (LTB : Z.of_nat (length (map (Z_to_bv 8) (seq_table_bytes tbl))) = 8 + 8 * 2^tl).
      { rewrite length_map. pose proof (seq_table_bytes_length tbl) as SL. unfold FseNCount.Zlength in SL.
        destruct TOK as (_ & TC & _). rewrite TLOG in TC. unfold FseNCount.Zlength in *. lia. }
      zstep. zstep. uck. zstep. zstep. zstep.
      assert (DTA : u8arr usegs m0 DTS (map (Z_to_bv 8) (seq_table_bytes tbl) ++ skipn N dt0)).
      { apply u8arr_app. split; [exact TB|]. rewrite LTB. exact DTA2. }
      destruct (bs_frame_merge _ _ _ _ _ FA eq_refl FN ltac:(rewrite u16s_length, length_map; lia) FT FM FS) as (fb & FRM).
      unfold FseNCount.Zlength in NR.
      eapply (bs_ret _ (map (Z_to_bv 8) (seq_table_bytes tbl) ++ skipn N dt0) _ (Z_to_bv 64 DTS) n); [ | lia | reflexivity | ].
      + split; [exact DTA|]. split; [apply Nat2Z.inj; rewrite length_app, Nat2Z.inj_add; lia|]. split; [exact WA|]. split; [exact WLN|].
        split; [eassumption|]. split; [exact STK|]. split; [eexists; exact FRM|]. split; [eassumption|]. split; [exact MU| exact WM].
      + right. split; [lia|]. right. right. split; [right; exact TY2|]. split; [reflexivity|].
        exists tbl. split; [exact TOK|].
        replace (length (seq_table_bytes tbl)) with (length (map (Z_to_bv 8) (seq_table_bytes tbl))) by apply length_map.
        rewrite firstn_app, Nat.sub_diag, firstn_O, app_nil_r, firstn_all. reflexivity.
    - (* [comment removed for export] *)
      assert (FRS : FSE_READ_STACK = 256) by reflexivity.
      assert (EV : e = 20 \/ e = 44) by (apply (read_ncount_err_val rt0 (kind_max k) srcb e (Forall_all_bytes _ FBY)); [lia | unfold FseNCount.Zlength; lia | exact RN]).
      assert (ER : 20 <= e <= 44) by lia. clear EV.
      unhide_mentioning SRC.
      eapply evt_cut; [ eapply (fse_read_err_cor) with (SPV := SPV + -192) (NC := SPV + -170) (MSVP := SPV + -60) (TLP := SPV + -64) (BUF := SRC)
                          (rt0 := rt0) (buf := srcb) (msv0 := kind_max k) (lo := lo) (e := e);
          [ exact FN | exact FM | exact FT | exact SRCB | exact FBY | lia | lia | lia | lia | lia | lia | lia | lia | lia | lia | lia | exact STK | lia | lia
          | right; lia | right; lia | right; lia | lia | lia | lia | lia | lia | lia | lia | exact MI
          | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | exact RN ]
        | hide_all_disj; post_call usegs m1 ].
      clear BSI. rename PC into STK. rename PC0 into FN. rename PC1 into LRT. rename PC2 into FM. rename POST into FT.
      zstep. zstep. zstep. zstep. if_cases K1; zify_cond K1.
      2:{ exfalso. lia. }
      destruct (bs_frame_merge _ _ _ _ _ FA eq_refl FN ltac:(rewrite u16s_length, length_map; lia) FT FM FS) as (fb & FRM).
      eapply (bs_ret _ dt0 wb0 oldp (2^64 - 20)); [ | lia | apply bv_eq; reflexivity | left; reflexivity].
      split; [exact DTA|]. split; [reflexivity|]. split; [exact WA|]. split; [reflexivity|]. split; [exact DTPC|]. split; [exact STK|].
      split; [eexists; exact FRM|]. split; [eassumption|]. split; [exact MU| exact WM].
  Qed.

  (* [comment removed for export] *)
  Lemma bs_main : forall (t0 t1 t2 t6 : word),
    u8arr usegs m DTS dt0 -> rw_cells usegs m DTP [C8 oldp] -> u8arr usegs m W wb0 ->
    bytes_at usegs m SRC (map (Z_to_bv 8) srcb) -> Forall (fun c => 0 <= c < 256) srcb ->
    bytes_at usegs m BASE (u32s (map (Z_to_bv 64) (kind_base k))) -> bytes_at usegs m BITS (map (Z_to_bv 8) (kind_bits k)) ->
    rw_cells usegs m SPV [C8 nbw; C8 (Z_to_bv 64 W)] -> 0 <= ty <= 3 ->
    stk usegs m lo SPV -> mem_inv usegs m ->
    evt usegs POST
      (MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 DTS) (Z_to_bv 64 DTP) (Z_to_bv 64 ty) (Z_to_bv 64 (kind_max k))
               (Z_to_bv 64 (kind_maxLog k)) (Z_to_bv 64 SRC) (Z_to_bv 64 (Z.of_nat (length srcb))) (Z_to_bv 64 BASE)
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 BITS) (Z_to_bv 64 DFLT) frw t6)
          F (Z_to_bv 64 0x175b8) fc None m (seg_rom usegs)).
  Proof.
    intros t0 t1 t2 t6 DTA DTPC WA SRCB FBY BASEB BITSB ARGS TYR STK MI. open_bsh HY. hide_all_disj.
    assert (MU : munch [(DTS, DTS + Z.of_nat (length dt0)); (DTP, DTP + 8); (W, W + Z.of_nat (length wb0)); (SPV - 448, SPV)] m m) by apply munch_refl.
    assert (WM : wmono usegs m m) by apply wmono_refl.
    assert (KM : 0 <= kind_max k <= 52 /\ 8 <= kind_maxLog k <= 9) by (destruct k; cbn; lia).
    assert (LKB : Z.of_nat (length (kind_bits k)) = kind_max k + 1 /\ Z.of_nat (length (kind_base k)) = kind_max k + 1) by (destruct k; split; reflexivity).
    destruct LKB as [LKB1 LKB2].
    zstep. carve_frame 192%nat STK.
    do 7 zstep. zstep. zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mp end.
    assert (I0 : BS0 mp).
    { split; [exact DTA|]. split; [exact DTPC|]. split; [exact WA|]. split; [exact SRCB|]. split; [exact BASEB|]. split; [exact BITSB|].
      split; [exact ARGS|]. split; [exact STK|]. split; [eexists; exact FR|]. split; [exact MI|]. split; [exact MU| exact WM]. }
    clear DTA DTPC WA SRCB BASEB BITSB ARGS STK FR MI MU WM.
    zstep. if_cases K; zify_cond K.
    - rewrite (signed_lit ty) in K by lia.
      zstep. zstep. if_cases K2; zify_cond K2.
      + eapply bs_repeat; [exact I0 | lia].
      + eapply bs_comp; [exact I0 | lia | exact FBY].
    - rewrite (signed_lit ty) in K by lia.
      zstep. if_cases K2; zify_cond K2.
      + eapply bs_rle; [exact I0 | lia | exact FBY].
      + eapply bs_basic; [exact I0 | lia].
  Qed.
End BST.

Theorem zd_buildseq_proof : zd_buildseq_stmt.
Proof.
  unfold zd_buildseq_stmt, PZD_BUILDSEQ, off_stack, apart. intros until nbw.
  intros DTA DLEN DTPC WA WLEN SRCB FBY SLEN BASEB BITSB ARGS TYR DTSL DTSH DTPL DTPH WL WH SRCL SRCH BASER BITSR STK LOS LO0 SPH
         OFFDTS OFFDTP OFFW OFFSRC OFFBASE OFFBITS DTSDTP DTSW DTSSRC DTSBASE DTSBITS DTSSP DTPW DTPSRC DTPBASE DTPBITS DTPSP WSRC WBASE WBITS WSP
         ALDTS ALDTP ALBASE ALW ALSP OLDP MI
         -> -> -> -> -> -> -> -> -> ->.
  eapply (bs_main ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DTS DTP SRC W DFLT BASE BITS ty k dt0 wb0 srcb oldp nbw t5);
    try eassumption.
  unfold bs_hyps. repeat split; try eassumption; try lia.
Qed.
