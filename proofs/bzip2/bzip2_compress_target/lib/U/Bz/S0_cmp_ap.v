(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Tac WalkLib.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require ZBridge.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib Require SegsS0.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Tac OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.WalkLib OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.ZBridge.Bytes OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib.SegsS0.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzTables. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzTac BzTac2. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzArr BzCMem BzCStream BzCState BzArrD BzCLemmas1 CmpMem.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import CmpCut CmpCut0. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpArith.
From Stdlib Require Lia. Unset Lia Cache.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeilTac.
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
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.

(* [comment removed for export] *)
Ltac lin16 H := lazymatch type of H with (?x mod 16 = 0)%Z =>
  let E := fresh "E16" in pose proof (Z.div_mod x 16 ltac:(lia)) as E; rewrite H, Z.add_0_r in E; clear H;
  let q := fresh "qal" in set (q := (x / 16)%Z) in E; clearbody q; rename E into H end.

Import ListNotations. Open Scope bv_scope.
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
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpLiaC.   (* [comment removed for export] *)
Local Ltac lia ::= CmpLiaC.lia_c.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpSepV.   (* [comment removed for export] *)
Local Ltac Lib.Step.slia ::= CmpSepV.slia_v.   (* [comment removed for export] *)
Local Ltac Lib.StoreFast.tslia ::= CmpSepV.tslia_v.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require CmpStEq.   (* [comment removed for export] *)
Local Ltac BzTac.st_eq ::= CmpStEq.st_eq_fast.   (* [comment removed for export] *)
Local Ltac simpl_arr_sizes ::= CmpFast.sas7_all.   (* [comment removed for export] *)
Section ACeilS1. Context {BZP : BzParams} {ACEIL__ : ACeil}.


Section AP.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m0 : word -> option byte).
  Variables (cx : cctx) (g : eg) (e : est) (lo : Z) (sv : word).
  Notation usp := (bv_unsigned sp). Notation E := (c_E cx). Notation A2 := (c_A2 cx). Notation J := (c_J cx).
  Notation nblock := (e_nblock e). Notation ch := (e_state_in_ch e). Notation len := (e_state_in_len e). Notation crc0 := (e_blockCRC e).
  Hypothesis CX : cctx_ok cx. Hypothesis SEP2 : apart E ESTATE_SIZE A2 ARR2_SIZE. Hypothesis IME : img_apart (ci_hi S0C) E ESTATE_SIZE. Hypothesis IMA : img_apart (ci_hi S0C) A2 ARR2_SIZE.
  Hypothesis Hch : (0 <= ch < 256)%Z. Hypothesis Hlen : (1 <= len <= 255)%Z. Hypothesis Hcrc : (0 <= crc0 < 4294967296)%Z.
  Hypothesis Hnb : (0 <= nblock)%Z. Hypothesis ROOM : (nblock + 5 <= ARR2_SIZE)%Z.
  Hypothesis DEFI : zdefr (e_inUse e) 0 256. Hypothesis BOK : zbok (e_arr2 e).
  Hypothesis LO : (CEIL <= lo)%Z.
  Variables (t0 t1 t2 t3 t4 t5 t6 : word).

  Notation W := (add_pair_W cx e).
  Notation POST := (add_pair_post s0segs cx g e ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo W m0).
  (* [comment removed for export] *)
  Definition MEMp (nb : Z) (crcw : word) (inUse blk : zarr) (m : word -> option byte) : Prop :=
    rw_cells s0segs m E (EHEAD1 cx g (est_set_rl e (RL nb blk inUse (e_blockCRC e) ch len))) /\
    rw_cells s0segs m (E + 640) (cset 2 (C4 crcw) (EHEAD2 cx g e)) /\
    u8arr s0segs m (E + 128) (ovb inUse (jseg J 128 256) 256) /\
    u8arr s0segs m A2 (zb8 blk ARR2_SIZE) /\
    u32arr s0segs m (ci_crc S0C) crc_words /\ rw_cells s0segs m (ci_got S0C + 24) [C8 (Z_to_bv 64 (ci_crc S0C))] /\
    mem_inv s0segs m /\ munch W m0 m /\ wmono s0segs m0 m /\ stk s0segs m lo usp.

  Ltac prep :=
    let ALE := ident:(ALE) in let AL1 := ident:(AL1) in let AL2 := ident:(AL2) in let ALF := ident:(ALF) in let ALB := ident:(ALB) in let ALFb := ident:(ALFb) in pose proof CX as CX'; unfold cctx_ok in CX'; cbv zeta in CX';
    bz_ceil; bz_params; unfold ESTATE_SIZE, FTAB_WORDS, BZFILE_SIZE, IMG_HI3, CEIL in CX';
    cps_destruct CX' as (RE1 & RE2 & RA1 & RA1' & RA2 & RA2' & RFT & RFT' & RBZ & RBZ' & RFB & RFB' & ALE & AL1 & AL2 & ALF & ALB & ALFb & LJ & LJB); try lin16 ALE; try lin16 AL1; try lin16 AL2; try lin16 ALF; try lin16 ALB; try lin16 ALFb;
    pose proof SEP2 as SEP2'; pose proof IME as IME'; pose proof IMA as IMA'; unfold apart, img_apart, ESTATE_SIZE, IMG_LO3, IMG_HI3 in SEP2', IME', IMA'; cbn [ci_hi S0C] in IME', IMA';
    bz_ceil; bz_params; unfold ESTATE_SIZE, CEIL in *; pose proof crc_words_length as CWL.
  Ltac fin_tac :=
    bz_params; cbn [e_arr2 e_inUse est_set_rl rl_block rl_inUse rl_nblock rl_crc rl_ch rl_len];
    repeat match goal with H : u8arr _ _ _ _ |- _ => rewrite ?unsigned_lit in H by lia end;
    try assumption.
  Ltac blk_sb AR2 i :=
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
     lazymatch type of AR2 with u8arr _ _ ?A (zb8 ?a _) =>
      let SO := fresh "SO" in
      pose proof (u8arr_store_ok s0segs mm A _ i _ AR2 ltac:(rewrite zb8_length_nat; lia) eq_refl) as SO;
      wstep;
      match goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le1 ?w)) _) =>
        let H := fresh "AR" in pose proof (zb8_write1 s0segs mm A a ARR2_SIZE i w AR2 ltac:(lia)) as H;
        clear AR2; store_done; rename H into AR2 end end end.
  Ltac openp MEM := let EH1 := ident:(EH1) in let EH2 := ident:(EH2) in let CRC := ident:(CRC) in let GOTC := ident:(GOTC) in let MU := ident:(MU) in cps_destruct MEM as (EH1 & EH2 & INU & AR2 & CRC & GOTC & MI & MU & WM & STK); unfold EHEAD1, EHEAD2 in EH1, EH2;
    change (ci_got S0C + 24)%Z with 205056%Z in GOTC; change (ci_crc S0C) with 209272%Z in CRC, GOTC;
    cbn [e_mode e_state e_avail_in_expect e_arr1 e_arr2 e_ftab e_origPtr e_state_in_ch e_state_in_len e_nblock e_state_out_pos
         e_nInUse e_inUse e_unseqToSeq e_bw e_blockCRC e_combinedCRC e_blockNo e_nMTF e_mtfFreq e_selector e_selectorMtf
         e_len e_code e_rfreq e_len_pack est_set_rl rl_block rl_nblock rl_inUse rl_crc rl_ch rl_len cset ci_crc ci_got S0C Z.add] in EH1, EH2, CRC, GOTC;
    unfold add_pair_W in MU |- *.
  Ltac ap_chk := wstep; notrap.

  (* [comment removed for export] *)
  Lemma ap_crc : forall (k : nat) (crc : Z) (crcw x17 : word) (m : word -> option byte) x12 x11,
    (1 <= Z.of_nat k <= 255)%Z -> (bv_unsigned crcw mod 4294967296 = crc)%Z -> (0 <= crc < 4294967296)%Z ->
    MEMp nblock crcw (e_inUse e) (e_arr2 e) m ->
    (forall crcw' x17' m', (bv_unsigned crcw' mod 4294967296 = crc_update_n crc ch k)%Z -> MEMp nblock crcw' (e_inUse e) (e_arr2 e) m' ->
        evt s0segs POST (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 E) x11 x12 (Z_to_bv 64 ch) crcw' (Z_to_bv 64 (ci_crc S0C)) (Z_to_bv 64 0) x17'
                                  s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x16094) fc None m' (seg_rom s0segs))) ->
    evt s0segs POST (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 E) x11 x12 (Z_to_bv 64 ch) crcw (Z_to_bv 64 (ci_crc S0C)) (Z_to_bv 64 (Z.of_nat k)) x17
                              s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x1606c) fc None m (seg_rom s0segs)).
  Proof using BZP ACEIL__ ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 cx g e lo CX SEP2 IME IMA Hch Hnb ROOM t0 t1 t2 t3 t4 t5 t6.
    induction k as [|k IH]; intros crc crcw x17 m x12 x11 Hk XC Hc MEM K; [lia|].
    openp MEM. prep.
    (* [comment removed for export] *)
    wstep. wstep. wstep. wstep.
    rewrite XC. set (idx := Z.lxor (crc / 16777216) ch).
    assert (Hidx : (0 <= idx < 256)%Z).
    { subst idx. apply lxor_byte; [|lia]. split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]. }
    change (ci_crc S0C) with 209272%Z.
    u32_read CRC crc_words_length idx tw NTH RD.
    try replace (209272 + idx * 4)%Z with (209272 + 4 * idx)%Z by lia.
    try replace (idx * 4 + 209272)%Z with (209272 + 4 * idx)%Z by lia.
    wstep. clear RD.
    assert (Etw : tw = Z_to_bv 64 (crc32_tbl idx)).
    { pose proof (nth_error_wnth crc_words idx ltac:(lia) ltac:(rewrite crc_words_length; lia)) as N2.
      rewrite NTH in N2. injection N2 as N3. rewrite N3. apply wnth_crc_words. lia. }
    subst tw. pose proof (crc32_tbl_range idx Hidx) as TR.
    (* [comment removed for export] *)
    wstep. wstep. wstep. wstep.
    lazymatch goal with |- evt _ _ (MS (mkR _ _ _ _ _ _ _ _ _ _ _ _ _ ?w _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ _ _) =>
      assert (STEP : (bv_unsigned w mod 4294967296 = crc_update crc ch)%Z) end.
    { unfold crc_update. rewrite land255_mod, (Z.mod_small ch 256) by lia. rewrite shiftr_div24.
      first [ subst idx; apply low32_crc_step'; [exact XC| exact TR]
            | rewrite (Z.lxor_comm (bv_unsigned (sx32 (Z_to_bv 64 (crc32_tbl idx))))); subst idx; apply low32_crc_step'; [exact XC| exact TR] ]. }

    pose proof (crc_update_range crc ch ltac:(lia)) as CR'.
    (* [comment removed for export] *)
    wstep; if_cases Kc; zify_cond_z Kc.
    - (* [comment removed for export] *)
      enter_with (IH (crc_update crc ch) _ _ m1 x12 x11); [st_eq| lia| exact STEP | exact CR' | |].
      + split; [exact EH1|]. split; [exact EH2|]. split; [exact INU|]. split; [exact AR2|]. split; [exact CRC|]. split; [exact GOTC|].
        split; [exact MI|]. split; [exact MU|]. split; [exact WM| exact STK].
      + intros crcw' x17' m' XC' MEM'. eapply K; [|exact MEM']. rewrite XC'. rewrite crc_update_n_S. reflexivity.
    - (* [comment removed for export] *)
      assert (k = 0)%nat by lia. subst k.
      enter_with (K _ _ m1); [st_eq| exact STEP | ].
      + split; [exact EH1|]. split; [exact EH2|]. split; [exact INU|]. split; [exact AR2|]. split; [exact CRC|]. split; [exact GOTC|].
        split; [exact MI|]. split; [exact MU|]. split; [exact WM| exact STK].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma rl_put_eq : forall r b, 0 <= b -> rl_put r b = RL (rl_nblock r + 1) (wr8 (rl_block r) (rl_nblock r) b) (rl_inUse r) (rl_crc r) (rl_ch r) (rl_len r).
  Proof. intros r b Hb. unfold rl_put. rewrite wr8_zset_land by exact Hb. reflexivity. Qed.

  Lemma ap_tail : forall (crcw x13 x14 x15 x16 x17 : word) (m : word -> option byte),
    (bv_unsigned crcw mod 4294967296 = crc_update_n crc0 ch (Z.to_nat len))%Z ->
    MEMp nblock crcw (e_inUse e) (e_arr2 e) m ->
    evt s0segs POST (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 E) (Z_to_bv 64 ch) (Z_to_bv 64 len) x13 x14 x15 x16 x17
                              s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x16094) fc None m (seg_rom s0segs)).
  Proof.
    intros crcw x13 x14 x15 x16 x17 m XC MEM. openp MEM. prep.
    pose proof (ovb_length (e_inUse e) (jseg J 128 256) 256 ltac:(lia)) as LIU.
    pose proof (zb8_length (e_arr2 e) ARR2_SIZE ltac:(lia)) as LA2.
    (* [comment removed for export] *)
    wstep. ap_chk. wstep. wstep. ap_chk. wstep. wstep. wstep.
    pose proof (u8arr_store_ok s0segs m (E + 128) _ ch _ INU ltac:(rewrite ovb_length_nat; lia) eq_refl) as SO.
    wstep.
    match goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le1 ?w)) _) =>
      pose proof (ovb_write1 s0segs m (E + 128) (e_inUse e) (jseg J 128 256) 256 ch w INU ltac:(lia)) as INU' end.
    clear INU. store_done. rename INU' into INU.
    replace (wr8 (e_inUse e) ch (bv_unsigned (Z_to_bv 64 1))) with (zset (e_inUse e) ch 1) in INU by reflexivity.
    assert (CRN : (0 <= crc_update_n crc0 ch (Z.to_nat len) < 4294967296)%Z) by (apply crc_update_n_range; lia).
    reword_C4 EH2 2%nat (crc_update_n crc0 ch (Z.to_nat len)). { rewrite XC. symmetry. apply Z.mod_small. exact CRN. }
    (* [comment removed for export] *)
    wstep; if_cases K3; zify_cond_z K3.
    - (* [comment removed for export] *)
      wstep. wstep. wstep. fstep. fstep. ap_chk. fstep. fstep. wstep. wstep. ap_chk. ap_chk.
      blk_sb AR2 (e_nblock e).
      wstep. wstep. ap_chk. wstep. wstep. fstep. fstep. wstep. ap_chk. fstep. fstep. wstep. wstep. ap_chk. ap_chk.
      blk_sb AR2 (e_nblock e + 1)%Z.
      wstep. wstep. ap_chk. wstep. wstep. fstep. fstep. wstep. ap_chk. fstep. fstep. wstep. wstep. ap_chk. ap_chk.
      blk_sb AR2 (e_nblock e + 2)%Z.
      wstep. wstep. wstep. ap_chk. wstep. wstep.
      unfold add_pair_post. cbv zeta.
      replace (add_pair_to_block (est_rl e)) with
        (RL (nblock + 3) (wr8 (wr8 (wr8 (e_arr2 e) nblock ch) (nblock + 1) ch) (nblock + 2) ch) (zset (e_inUse e) ch 1) (crc_update_n crc0 ch (Z.to_nat len)) ch len).
      2:{ unfold add_pair_to_block, est_rl. cbn [rl_nblock rl_block rl_inUse rl_crc rl_ch rl_len].
          replace (len =? 1)%Z with false by (symmetry; apply Z.eqb_neq; lia). replace (len =? 2)%Z with false by (symmetry; apply Z.eqb_neq; lia).
          replace (len =? 3)%Z with true by (symmetry; apply Z.eqb_eq; lia).
          rewrite !rl_put_eq by (apply Z.land_nonneg; right; lia). cbn [rl_nblock rl_block rl_inUse rl_crc rl_ch rl_len].
          rewrite land255_mod, (Z.mod_small ch 256) by lia. CmpFast.rlf_sp. }
      finish. fin_tac.
    - wstep. wstep; if_cases K2; zify_cond_z K2.
      + (* [comment removed for export] *)
        wstep. wstep. wstep. fstep. fstep. ap_chk. fstep. fstep. wstep. wstep. wstep. ap_chk. ap_chk.
        blk_sb AR2 (e_nblock e).
        wstep. wstep. ap_chk. wstep. wstep. fstep. fstep. wstep. ap_chk. fstep. fstep. wstep. wstep. ap_chk. ap_chk.
        blk_sb AR2 (e_nblock e + 1)%Z.
        wstep. wstep. wstep. ap_chk. wstep. wstep.
        unfold add_pair_post. cbv zeta.
        replace (add_pair_to_block (est_rl e)) with
          (RL (nblock + 2) (wr8 (wr8 (e_arr2 e) nblock ch) (nblock + 1) ch) (zset (e_inUse e) ch 1) (crc_update_n crc0 ch (Z.to_nat len)) ch len).
        2:{ unfold add_pair_to_block, est_rl. cbn [rl_nblock rl_block rl_inUse rl_crc rl_ch rl_len].
            replace (len =? 1)%Z with false by (symmetry; apply Z.eqb_neq; lia). replace (len =? 2)%Z with true by (symmetry; apply Z.eqb_eq; lia).
            rewrite !rl_put_eq by (apply Z.land_nonneg; right; lia). cbn [rl_nblock rl_block rl_inUse rl_crc rl_ch rl_len].
            rewrite land255_mod, (Z.mod_small ch 256) by lia. CmpFast.rlf_sp. }
        finish. fin_tac.
      + wstep. wstep; if_cases K1; zify_cond_z K1.
        * (* [comment removed for export] *)
          wstep. ap_chk. wstep. ap_chk. ap_chk.
          wstep. wstep. wstep. wstep. wstep. fstep. fstep.
          pose proof (u8arr_store_ok s0segs _ (E + 128) _ (len - 4) _ INU ltac:(rewrite ovb_length_nat; lia) eq_refl) as SO2.
          wstep.
          lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mm _ (le1 ?w)) _) =>
            pose proof (ovb_write1 s0segs mm (E + 128) (zset (e_inUse e) ch 1) (jseg J 128 256) 256 (len - 4) w INU ltac:(lia)) as INU' end.
          clear INU. store_done. rename INU' into INU.
          replace (wr8 (zset (e_inUse e) ch 1) (len - 4) (bv_unsigned (Z_to_bv 64 1))) with (zset (zset (e_inUse e) ch 1) (len - 4) 1) in INU by reflexivity.
          (* [comment removed for export] *)
          ap_chk. fstep. fstep. wstep. wstep. ap_chk. ap_chk.
          blk_sb AR2 (e_nblock e).
          wstep. wstep. ap_chk. wstep. wstep. fstep. fstep. wstep. ap_chk. fstep. fstep. wstep. wstep. ap_chk. ap_chk.
          blk_sb AR2 (e_nblock e + 1)%Z.
          wstep. wstep. ap_chk. wstep. wstep. fstep. fstep. wstep. ap_chk. fstep. fstep. wstep. wstep. ap_chk. ap_chk.
          blk_sb AR2 (e_nblock e + 2)%Z.
          wstep. wstep. ap_chk. wstep. wstep. fstep. fstep. wstep. ap_chk. fstep. fstep. wstep. wstep. ap_chk. ap_chk.
          blk_sb AR2 (e_nblock e + 3)%Z.
          (* [comment removed for export] *)
          wstep. wstep. ap_chk. wstep. wstep. wstep. ap_chk.
          wstep. wstep. fstep. fstep. ap_chk. fstep. fstep. wstep. wstep. ap_chk. ap_chk.
          blk_sb AR2 (e_nblock e + 4)%Z.
          (* [comment removed for export] *)
          wstep. wstep. ap_chk. wstep. wstep.
          unfold add_pair_post. cbv zeta.
          replace (add_pair_to_block (est_rl e)) with
            (RL (nblock + 5) (wr8 (wr8 (wr8 (wr8 (wr8 (e_arr2 e) nblock ch) (nblock + 1) ch) (nblock + 2) ch) (nblock + 3) ch) (nblock + 4) (len - 4))
                (zset (zset (e_inUse e) ch 1) (len - 4) 1) (crc_update_n crc0 ch (Z.to_nat len)) ch len).
          2:{ unfold add_pair_to_block, est_rl. cbn [rl_nblock rl_block rl_inUse rl_crc rl_ch rl_len].
              replace (len =? 1)%Z with false by (symmetry; apply Z.eqb_neq; lia). replace (len =? 2)%Z with false by (symmetry; apply Z.eqb_neq; lia).
              replace (len =? 3)%Z with false by (symmetry; apply Z.eqb_neq; lia).
              rewrite !rl_put_eq by (try (apply Z.land_nonneg; right); lia). cbn [rl_nblock rl_block rl_inUse rl_crc rl_ch rl_len].
              rewrite land255_mod, (Z.mod_small ch 256) by lia. CmpFast.rlf_sp. }
          finish. fin_tac.
        * (* [comment removed for export] *)
          wstep. wstep. wstep. fstep. fstep. ap_chk. fstep. fstep. wstep. wstep. wstep. ap_chk. ap_chk.
          blk_sb AR2 (e_nblock e).
          wstep. wstep. wstep. ap_chk. wstep. wstep.
          unfold add_pair_post. cbv zeta.
          replace (add_pair_to_block (est_rl e)) with (RL (nblock + 1) (wr8 (e_arr2 e) nblock ch) (zset (e_inUse e) ch 1) (crc_update_n crc0 ch (Z.to_nat len)) ch len).
          2:{ unfold add_pair_to_block, est_rl. cbn [rl_nblock rl_block rl_inUse rl_crc rl_ch rl_len].
              replace (len =? 1)%Z with true by (symmetry; apply Z.eqb_eq; lia). rewrite rl_put_eq by (apply Z.land_nonneg; right; lia).
              cbn [rl_nblock rl_block rl_inUse rl_crc rl_ch rl_len]. rewrite land255_mod, (Z.mod_small ch 256) by lia. reflexivity. }
          finish. fin_tac.
  Qed.

  Lemma ap_entry : forall (x11 x12 x13 x14 x15 x16 x17 : word),
    MEMp nblock (Z_to_bv 64 crc0) (e_inUse e) (e_arr2 e) m0 ->
    evt s0segs POST (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 E) x11 x12 x13 x14 x15 x16 x17
                              s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x1603c) fc None m0 (seg_rom s0segs)).
  Proof.
    intros x11 x12 x13 x14 x15 x16 x17 MEM. pose proof MEM as MEM0. openp MEM. prep.
    (* [comment removed for export] *)
    wstep. ap_chk. wstep. wstep. wstep; if_cases K0; zify_cond_z K0; [exfalso; lia|].
    (* [comment removed for export] *)
    wstep. wstep. wstep. wstep. fstep. wstep. wstep.
    replace (Z.land 18446744073709551615 len) with (Z.of_nat (Z.to_nat len)).
    2:{ rewrite Z2Nat.id by lia. rewrite Z.land_comm. change 18446744073709551615%Z with (Z.ones 64). rewrite Z.land_ones by lia. symmetry. apply Z.mod_small. lia. }
    rewrite (Z.land_ones ch 8) || rewrite land255_mod. rewrite (Z.mod_small ch 256) by lia.
    change 209272%Z with (ci_crc S0C).
    unshelve (epose proof (rw_cells_C4_reword s0segs m0 (E + 640) _ 2 _ (sx32 (Z_to_bv 64 crc0)) EH2 eq_refl _) as EH2'); [rewrite low32_sx32; reflexivity|].
    cbn [cset] in EH2'.
    enter_with (ap_crc (Z.to_nat len) crc0 (sx32 (Z_to_bv 64 crc0)) _ m0 _ _); [st_eq| lia| rewrite low32_sx32, low32_lit; apply Z.mod_small; lia| lia| |].
    { split; [exact EH1|]. split; [cbn [cset]; exact EH2'|]. split; [exact INU|]. split; [exact AR2|]. split; [exact CRC|]. split; [exact GOTC|].
      split; [exact MI|]. split; [exact MU|]. split; [exact WM| exact STK]. }
    intros crcw' x17' m' XC' MEM'. eapply (ap_tail crcw'); [exact XC'| exact MEM'].
  Qed.
End AP.

Theorem S0_add_pair : add_pair_spec S0C.
Proof.
  unfold add_pair_spec. cbn [ci_segs ci_add_pair S0C]. intros until sv. intros -> EH1 EH2 INU AR2 CM MI ST LO16 LO CX SEP IMG Hch Hlen Hcrc Hnb ROOM DEFI BOK.
  pose proof CX as CX'. unfold cctx_ok in CX'. cbv zeta in CX'.
  unfold cctx_sep in SEP. cbv zeta in SEP. cps_destruct SEP as (_ & SEP2 & _).
  unfold cctx_img in IMG. cps_destruct IMG as (IME & _ & IMA & _).
  pose proof (cimg_crc_u32arr S0C m sv CM) as CRC. cps_destruct CM as (_ & GOTC & _ & _).
  eapply ap_entry; try eassumption.
  split; [exact EH1|]. split; [cbn [cset]; exact EH2|]. split; [exact INU|]. split; [exact AR2|]. split; [exact CRC|]. split; [exact GOTC|].
  split; [exact MI|]. split; [apply munch_refl|]. split; [apply wmono_refl| exact ST].
Qed.

End ACeilS1.
