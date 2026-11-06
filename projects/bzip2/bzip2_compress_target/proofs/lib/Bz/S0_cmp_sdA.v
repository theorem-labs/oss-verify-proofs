(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Tac WalkLib.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require ZBridge.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require SegsS0 StoreFast.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.Tac OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.WalkLib OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.ZBridge.Bytes OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.SegsS0 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.StoreFast.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzTac BzTac2 BzArr BzCMem BzCStream BzCState BzCMtf BzArrD BzCLemmas1 CmpMem BzSepTac.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpCut CmpCut0 CmpCutSM CmpCutSmA CmpCutSmA0 CmpCutSD CmpCutSD0 CmpSdKit CmpSdTac CmpArith CmpArith2 BzCNumZ BzWalkArith4.
From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Open Scope bv_scope.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzParams.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpCut6.   (* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpLiaP.   (* [comment removed for export] *)
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac tlia ::= first [ Zify.zify; xlia zchecker
                         | sf_unhide; unhide_disj;
                           first [ zify_prune_neg; Zify.zify; xlia zchecker
                                 | zify_prune_plain; Zify.zify; xlia zchecker
                                 | Zify.zify; xlia zchecker ] ].
Local Ltac tslia ::= tslia_sep.
Local Ltac simpl_sizes_goal ::=
  literal_cell_sizes;
  try match goal with |- context [length (_ ++ _)] => rewrite !length_app end;
  cbn [cells_size csize length cbytes Nat.add Z.of_nat Pos.of_succ_nat Pos.succ];
  try match goal with |- context [length (le8 _)] => rewrite !length_le8 end;
  try match goal with |- context [length (le4 _)] => rewrite !length_le4 end;
  try match goal with |- context [length (le2 _)] => rewrite !length_le2 end;
  try match goal with |- context [length (le1 _)] => rewrite !length_le1 end;
  try match goal with |- context [length (u32s _)] => rewrite !u32s_length end;
  try match goal with |- context [length (u64s _)] => rewrite !u64s_length end;
  try match goal with |- context [length (upd _ _ _)] => rewrite !upd_length end;
  try match goal with |- context [length (zb8 _ _)] => rewrite !zb8_length_nat end;
  try match goal with |- context [length (ovb _ _ _)] => rewrite !ovb_length_nat end;
  try match goal with |- context [length (ovw _ _ _)] => rewrite !ovw_length_nat end;
  try match goal with |- context [length (zw32 _ _)] => rewrite !zw32_length_nat end.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpFast.   (* [comment removed for export] *)
Local Ltac BzTac.mlia ::= CmpFast.mlia_fast.   (* [comment removed for export] *)
Local Ltac Lib.ZBridge.mlia ::= CmpFast.mlia_fast.   (* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpLiaC.   (* [comment removed for export] *)
Local Ltac lia ::= CmpLiaC.lia_c.   (* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpSepV.   (* [comment removed for export] *)
Local Ltac Lib.Step.slia ::= CmpSepV.slia_v.   (* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpSepVS.   (* [comment removed for export] *)
Local Ltac Lib.StoreFast.tslia ::= CmpSepVS.tslia_vs.   (* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpSdStep.   (* [comment removed for export] *)
Local Ltac CmpSdKit.pstep_with SC p q n k ::= CmpSdStep.pstep_with_fast SC p q n k.   (* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpStEq.   (* [comment removed for export] *)
Local Ltac BzTac.st_eq ::= CmpStEq.st_eq_fast.   (* [comment removed for export] *)
Local Ltac simpl_arr_sizes ::= CmpFast.sas7.   (* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.
Section ACeilS1. Context {BZP : BzParams} {ACEIL__ : ACeil}.


Section SDA.
  Variables (cx : cctx) (g : eg) (e : est).
  Variables (sp gp tp : word) (F : bvmap 5 word) (fc : bv 32).
  Notation usp := (bv_unsigned sp). Notation E := (c_E cx). Notation A1 := (c_A1 cx). Notation A2 := (c_A2 cx). Notation J := (c_J cx).
  Notation nblock := (e_nblock e).
  Notation LENA := (e_len e). Notation CODA := (e_code e). Notation ARR1 := (e_arr1 e). Notation SELA := (e_selector e).
  Hypothesis CX : cctx_ok cx. Hypothesis SEP : cctx_sep cx.
  Hypothesis Gmtf : g_mtf g = true. Hypothesis Gbs : g_bs g = true. Hypothesis Gzb : g_zbits g = Z_to_bv 64 (A2 + nblock).
  Hypothesis Hnb : (0 <= nblock)%Z.
  Hypothesis USP1 : (CEIL <= usp)%Z. Hypothesis USP2 : (usp + 1008 <= 18446744073709551616)%Z.
  (* [comment removed for export] *)
  Variable LIM : Z. Hypothesis HLIM : (nblock + LIM <= ARR2_SIZE)%Z.

  (* [comment removed for export] *)
  Variables (nG nSel : Z) (sv : word) (W : s3w) (m0 : word -> option byte) (i16 : list byte).
  Notation MD := (MS3 cx g e nG nSel usp sv W m0 i16).
  Ltac openCX := openCX3 CX SEP USP1.
  Ltac openMD H := openMS3 Gmtf Gbs Gzb H.
  Ltac closeMD := closeMS3 Gmtf Gbs Gzb.

  (* [comment removed for export] *)
  Variables (sel gs A : Z).
  Hypothesis Hsel : (0 <= sel < 6)%Z. Hypothesis HA : (3 <= A <= 258)%Z.
  Hypothesis LENF : forall v, (0 <= v < A)%Z -> zdef LENA (258 * sel + v) = true /\ (1 <= zget LENA (258 * sel + v) <= 17)%Z.
  Hypothesis CODF : forall v, (0 <= v < A)%Z -> zdef CODA (258 * sel + v) = true /\ (0 <= zget CODA (258 * sel + v) < 4294967296)%Z.
  Notation MT := (A1 + 2 * gs)%Z. Notation CR := (E + 39256 + 1032 * sel)%Z. Notation LR := (E + 37708 + 258 * sel)%Z.
  Notation RD ra t0 t1 t2 s1 a0 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s9 s11 t3 t4 t5 t6 :=
    (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 E) s1 a0 (Z_to_bv 64 MT) (Z_to_bv 64 CR) (Z_to_bv 64 LR) a4 a5 a6 a7
         s2 s3 s4 s5 s6 s7 (Z_to_bv 64 8) s9 (Z_to_bv 64 15) s11 t3 t4 t5 t6).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma S0_itah_flush : forall (q : Z) (SC : same_code s0segs q 0x17b68 14) (Q : machine_state -> Prop)
      (f : nat) (b : bw) (N : Z) (m : word -> option byte)
      (ra t1 t2 s1 a0 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s9 s11 t3 t4 t5 t6 : word),
    bw_ok b -> (8 <= bw_live b)%Z -> (bw_live b < 8 * Z.of_nat f)%Z ->
    (bw_numZ (bs_needw f b) <= LIM)%Z ->
    (bv_unsigned a6 mod 4294967296 = bw_buff b)%Z ->
    MD b m ->
    (forall b1 m' (a6' t1' : word),
        b1 = bs_needw f b -> MD b1 m' -> (bv_unsigned a6' mod 4294967296 = bw_buff b1)%Z -> (0 <= bw_live b1 < 8)%Z ->
        evt s0segs Q (MS (RD ra (Z_to_bv 64 (bw_numZ b1)) t1' t2 s1 a0 a4 a5 a6' (Z_to_bv 64 (bw_live b1)) s2 s3 s4 s5 s6 s7 s9 s11 t3 t4 t5 t6)
                          F (Z_to_bv 64 (q + 56)) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (RD ra (Z_to_bv 64 (bw_numZ b)) t1 t2 s1 a0 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s9 s11 t3 t4 t5 t6)
                      F (Z_to_bv 64 q) fc None m (seg_rom s0segs)).
  Proof.
    intros q SC Q f. induction f as [|f IH]; intros b N m ra t1 t2 s1 a0 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s9 s11 t3 t4 t5 t6 OK L8 Lf NL X6 MEM K; [lia|].
    openCX. try clear ME MA1 MA2 MF Mb Mf. openMD MEM. bz_params.
    cps_destruct OK as (OKb & OKl & OKn).
    pose proof (needw_NZM f (bw_emit b)) as NZ1. unfold NZM in NZ1. cbn [bs_needw] in NL.
    replace (8 <=? bw_live b)%Z with true in NL by (symmetry; apply Z.leb_le; lia).
    cps_pose (bw_emit_shape b) as (Es1 & Es2 & Es3).
    pose proof (zb8_length (zbl (e_arr2 e) nblock b) ARR2_SIZE ltac:(lia)) as LA2.
    (* [comment removed for export] *)
    pstep SC. pstep SC. pstep SC.
    (* [comment removed for export] *)
    pose proof (u8arr_store_ok s0segs m A2 _ (nblock + bw_numZ b) _ AR2 ltac:(rewrite zb8_length_nat; lia) eq_refl) as SO.
    pstep SC.
    pose proof (zb8_write1 s0segs m A2 (zbl (e_arr2 e) nblock b) ARR2_SIZE (nblock + bw_numZ b) (Z_to_bv 64 (bv_unsigned a6 / 16777216)) AR2 ltac:(lia)) as AR2'.
    clear AR2. store_done. rename AR2' into AR2.
    (* [comment removed for export] *)
    pstep SC. pstep SC. pstep SC.
    (* [comment removed for export] *)
    pstep SC. pstep SC. pstep SC.
    (* [comment removed for export] *)
    pstep SC. pstep SC. pstep SC.
    reword_C4 EH2 0%nat ((Z.shiftl (bw_buff b) 8) mod 4294967296)%Z.
    { rewrite shiftl_mul256, low32_mod, low32_lit, low32_mul, low32_sx32, low32_lit, <- low32_mul. reflexivity. }
    replace (bw_live b + -8)%Z with (bw_live b - 8)%Z in EH2 by lia.
    replace (wr8 (zbl (e_arr2 e) nblock b) (nblock + bw_numZ b) (bv_unsigned (Z_to_bv 64 (bv_unsigned a6 / 16777216))))
      with (zbl (e_arr2 e) nblock (bw_emit b)) in AR2.
    2:{ rewrite zbl_emit by lia. unfold wr8. f_equal. rewrite shiftr_div24.
        rewrite unsigned_lit. 2:{ pose proof (word_urange a6). split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]. }
        rewrite (high_byte_of_low32 (bv_unsigned a6) (bw_buff b)); [| pose proof (word_urange a6); lia | exact X6 | lia].
        apply Z.mod_small. pose proof (bw_emit_byte b ltac:(lia)). rewrite shiftr_div24 in *. lia. }
    (* [comment removed for export] *)
    pstep SC; if_cases Kc; zify_cond_z Kc; pcnorm q.
    - (* [comment removed for export] *)
      enter_with (IH (bw_emit b) N m); [st_eq| unfold bw_ok; lia| lia| lia| exact NL| | |].
      + unfold bw_emit. cbn [bw_buff]. apply low32_shl8_sx32.
      + closeMD.
      + intros b1 m' a6' t1' Eb1 MEM' X6' L1. eapply K; [|exact MEM'| exact X6'| exact L1].
        rewrite Eb1. cbn [bs_needw]. replace (8 <=? bw_live b)%Z with true by (symmetry; apply Z.leb_le; lia). reflexivity.
    - (* [comment removed for export] *)
      enter_with (K (bw_emit b) m); [st_eq| | | | lia].
      + cbn [bs_needw]. replace (8 <=? bw_live b)%Z with true by (symmetry; apply Z.leb_le; lia).
        destruct f; cbn [bs_needw]; [reflexivity|]. replace (8 <=? bw_live (bw_emit b))%Z with false by (symmetry; apply Z.leb_gt; lia). reflexivity.
      + closeMD.
      + unfold bw_emit. cbn [bw_buff]. apply low32_shl8_sx32.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma S0_itah_tail : forall (r : Z) (SC : same_code s0segs r 0x17ba0 6) (Q : machine_state -> Prop)
      (b1 : bw) (n cv : Z) (m : word -> option byte)
      (ra t0 t1 t2 s1 a0 a6 s2 s3 s4 s5 s6 s7 s9 s11 t3 t4 t5 t6 : word),
    bw_ok b1 -> (0 <= bw_live b1 < 8)%Z -> (1 <= n <= 17)%Z -> (0 <= cv < 4294967296)%Z ->
    (bv_unsigned a6 mod 4294967296 = bw_buff b1)%Z ->
    MD b1 m ->
    (forall m' (a4' a5' a6' : word),
        let b' := BW (Z.lor (bw_buff b1) ((Z.shiftl cv (32 - bw_live b1 - n)) mod 4294967296)) (bw_live b1 + n) (bw_numZ b1) (bw_zb b1) in
        MD b' m' -> (bv_unsigned a6' mod 4294967296 = bw_buff b')%Z ->
        evt s0segs Q (MS (RD ra t0 t1 t2 s1 a0 a4' a5' a6' (Z_to_bv 64 (bw_live b1 + n)) s2 s3 s4 s5 s6 s7 s9 s11 t3 t4 t5 t6)
                          F (Z_to_bv 64 (r + 24)) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (RD ra t0 t1 t2 s1 a0 (sx32 (Z_to_bv 64 cv)) (Z_to_bv 64 n) a6 (Z_to_bv 64 (bw_live b1)) s2 s3 s4 s5 s6 s7 s9 s11 t3 t4 t5 t6)
                      F (Z_to_bv 64 r) fc None m (seg_rom s0segs)).
  Proof.
    intros r SC Q b1 n cv m ra t0 t1 t2 s1 a0 a6 s2 s3 s4 s5 s6 s7 s9 s11 t3 t4 t5 t6 OK L1 Hn Hcv X6 MEM K.
    openCX. try clear ME MA1 MA2 MF Mb Mf. openMD MEM. bz_params.
    cps_destruct OK as (OKb & OKl & OKn).
    (* [comment removed for export] *)
    pstep SC. pstep SC. pstep SC. pstep SC.
    rewrite (neg_shift_amount (bw_live b1) n) by lia.
    replace (bw_live b1 + n =? 32)%Z with false by (symmetry; apply Z.eqb_neq; lia).
    (* [comment removed for export] *)
    pstep SC. pstep SC.
    reword_C4 EH2 0%nat (Z.lor (bw_buff b1) ((Z.shiftl cv (32 - bw_live b1 - n)) mod 4294967296))%Z.
    { rewrite (low32_or_shifted _ _ a6 (bw_buff b1) X6) by lia.
      rewrite (shl_mod32_congr _ cv) by (first [lia| rewrite low32_sx32, low32_lit; reflexivity]).
      rewrite low32_small; [reflexivity|].
      change 4294967296%Z with (2^32)%Z. apply lor_lt_pow2; [lia| apply Z.mod_pos_bound; lia]. }
    eapply K.
    - closeMD.
    - cbn [bw_buff]. rewrite (low32_or_shifted _ _ a6 (bw_buff b1) X6) by lia.
      rewrite (shl_mod32_congr _ cv) by (first [lia| rewrite low32_sx32, low32_lit; reflexivity]).
      apply low32_small. change 4294967296%Z with (2^32)%Z. apply lor_lt_pow2; [lia| apply Z.mod_pos_bound; lia].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma S0_itah_head : forall (p : Z) (SC : same_code s0segs p 0x17b4c 21) (Q : machine_state -> Prop)
      (b : bw) (v : Z) (m : word -> option byte)
      (ra t0 t1 t2 s1 a0 a5 a6 s2 s3 s4 s5 s6 s7 s9 s11 t3 t4 t5 t6 : word),
    let n := zget LENA (258 * sel + v) in let cv := zget CODA (258 * sel + v) in
    bw_ok b -> (0 <= v < A)%Z -> (bw_numZ (bsW b n cv) <= LIM)%Z ->
    (bv_unsigned a6 mod 4294967296 = bw_buff b)%Z ->
    MD b m ->
    (forall b1 m' (t0' t1' a6' : word),
        b1 = bs_needw BS_FUEL b -> MD b1 m' -> (bv_unsigned a6' mod 4294967296 = bw_buff b1)%Z -> (0 <= bw_live b1 < 8)%Z ->
        evt s0segs Q (MS (RD ra t0' t1' t2 s1 a0 (sx32 (Z_to_bv 64 cv)) (Z_to_bv 64 n) a6' (Z_to_bv 64 (bw_live b1)) s2 s3 s4 s5 s6 s7 s9 s11 t3 t4 t5 t6)
                          F (Z_to_bv 64 (p + 84)) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (RD ra t0 t1 t2 s1 a0 (Z_to_bv 64 v) a5 a6 (Z_to_bv 64 (bw_live b)) s2 s3 s4 s5 s6 s7 s9 s11 t3 t4 t5 t6)
                      F (Z_to_bv 64 p) fc None m (seg_rom s0segs)).
  Proof.
    intros p SC Q b v m ra t0 t1 t2 s1 a0 a5 a6 s2 s3 s4 s5 s6 s7 s9 s11 t3 t4 t5 t6. cbv zeta. intros OK Hv NL X6 MEM K.
    openCX. try clear ME MA1 MA2 MF Mb Mf. openMD MEM. bz_params.
    cps_destruct OK as (OKb & OKl & OKn).
    destruct (LENF v Hv) as [LD LRG]. destruct (CODF v Hv) as [CD CRG].
    pose proof (bsW_NZM b (zget LENA (258 * sel + v)) (zget CODA (258 * sel + v))) as NZ0. unfold NZM in NZ0.
    (* [comment removed for export] *)
    pstep SC. pstep SC. pstep SC.
    (* [comment removed for export] *)
    pose proof (ovb_read1 s0segs m (E + 37708) LENA (jseg J 37708 1548) 1548 (258 * sel + v) _ LEN ltac:(lia) LD eq_refl) as RD1.
    pstep SC. clear RD1.
    (* [comment removed for export] *)
    pose proof (ovw_read s0segs m (E + 39256) CODA (jseg J 39256 6192) 1548 (258 * sel + v) _ COD ltac:(lia) CD eq_refl) as RD2.
    pstep SC. clear RD2.
    rewrite (unsigned_lit8 (zget LENA (258 * sel + v))) by lia.
    (* [comment removed for export] *)
    pstep SC; if_cases Kc; zify_cond_z Kc; pcnorm p.
    - (* [comment removed for export] *)
      eapply K; [| closeMD| exact X6| lia].
      unfold BS_FUEL. cbn [bs_needw]. replace (8 <=? bw_live b)%Z with false by (symmetry; apply Z.leb_gt; lia). reflexivity.
    - (* [comment removed for export] *)
      pstep SC.
      eapply (S0_itah_flush (p + 28) ltac:(exact (same_code_skip s0segs 7 p 0x17b4c 21 SC)) Q BS_FUEL b LIM m);
        [unfold bw_ok; lia| lia| unfold BS_FUEL; cbn; lia| | exact X6| closeMD|].
      { pose proof (bsW_bytes b (zget LENA (258 * sel + v)) (zget CODA (258 * sel + v))) as [BB _]. rewrite <- BB. exact NL. }
      intros b1 m' a6' t1' Eb1 MEM' X6' L1. pcnorm p. eapply K; [exact Eb1| exact MEM'| exact X6'| exact L1].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma S0_itah_blk : forall (p : Z) (SC : same_code s0segs p 0x17b4c 27) (Q : machine_state -> Prop)
      (b : bw) (v : Z) (m : word -> option byte)
      (ra t0 t1 t2 s1 a0 a5 a6 s2 s3 s4 s5 s6 s7 s9 s11 t3 t4 t5 t6 : word),
    let n := zget LENA (258 * sel + v) in let cv := zget CODA (258 * sel + v) in
    bw_ok b -> (0 <= v < A)%Z -> (bw_numZ (bsW b n cv) <= LIM)%Z ->
    (bv_unsigned a6 mod 4294967296 = bw_buff b)%Z ->
    MD b m ->
    (forall m' (t0' t1' a4' a5' a6' : word),
        MD (bsW b n cv) m' -> (bv_unsigned a6' mod 4294967296 = bw_buff (bsW b n cv))%Z ->
        evt s0segs Q (MS (RD ra t0' t1' t2 s1 a0 a4' a5' a6' (Z_to_bv 64 (bw_live (bsW b n cv))) s2 s3 s4 s5 s6 s7 s9 s11 t3 t4 t5 t6)
                          F (Z_to_bv 64 (p + 108)) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (RD ra t0 t1 t2 s1 a0 (Z_to_bv 64 v) a5 a6 (Z_to_bv 64 (bw_live b)) s2 s3 s4 s5 s6 s7 s9 s11 t3 t4 t5 t6)
                      F (Z_to_bv 64 p) fc None m (seg_rom s0segs)).
  Proof.
    intros p SC Q b v m ra t0 t1 t2 s1 a0 a5 a6 s2 s3 s4 s5 s6 s7 s9 s11 t3 t4 t5 t6. cbv zeta. intros OK Hv NL X6 MEM K.
    destruct (LENF v Hv) as [LD LRG]. destruct (CODF v Hv) as [CD CRG]. cps_pose OK as (OKb & OKl & OKn).
    eapply (S0_itah_head p (same_code_prefix s0segs 21 27 p 0x17b4c SC ltac:(lia)) Q b v m);
      [exact OK| exact Hv| exact NL| exact X6| exact MEM|].
    intros b1 m' t0' t1' a6' Eb1 MEM' X6' L1.
    cps_pose (bs_needw_post BS_FUEL b OK ltac:(unfold BS_FUEL; cbn; lia)) as (OK1 & M1 & N1). rewrite <- Eb1 in OK1, M1, N1.
    eapply (S0_itah_tail (p + 84) ltac:(exact (same_code_skip s0segs 21 p 0x17b4c 27 SC)) Q b1); [exact OK1| lia| lia| lia| exact X6'| exact MEM'|].
    intros m'' a4'' a5'' a6'' b' MEM'' X6''. subst b'. pcnorm p.
    replace (bsW b (zget LENA (258 * sel + v)) (zget CODA (258 * sel + v)))
      with (BW (Z.lor (bw_buff b1) ((Z.shiftl (zget CODA (258 * sel + v)) (32 - bw_live b1 - zget LENA (258 * sel + v))) mod 4294967296))
               (bw_live b1 + zget LENA (258 * sel + v)) (bw_numZ b1) (bw_zb b1)) in K by (unfold bsW; rewrite <- Eb1; reflexivity).
    exact (K _ _ _ _ _ _ MEM'' X6'').
  Qed.
End SDA.

End ACeilS1.
