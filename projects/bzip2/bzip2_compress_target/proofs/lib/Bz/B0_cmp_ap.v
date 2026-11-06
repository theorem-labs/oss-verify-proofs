(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Tac WalkLib.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require ZBridge.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require SegsA0 SegsB0.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.Tac OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.WalkLib OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.ZBridge.Bytes OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.SegsA0 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.SegsB0.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzTables BzTac BzTac2 BzArr BzCMem BzCStream BzCState BzArrD BzCLemmas1 CmpMem.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import AsanKit AsanCut AsanCutB0 AsanKitB0.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpCut CmpCut0 CmpArith.
From Stdlib Require Lia. Unset Lia Cache.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeilTac.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzParams.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpCut6.   (* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpLiaP.   (* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StepFast.
Local Ltac Lib.Step.step_core segs R F pc fc rv m ro ::= StepFast.sf_step_core.
Local Ltac Lib.Step.zstep ::= StepFast.sf_zstep.
#[local] Ltac2 Set StepFast.sf_foldgoal := Ltac2.Init.true.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StoreFast StoreFastZ StoreFastC.
Local Ltac Lib.Step.transport_chunks segs m a bs ::= StoreFast.transport_chunks_fast segs m a bs.
Local Ltac Lib.Tac.footprint_after_store segs m a bs ::= StoreFast.footprint_after_store_fast segs m a bs.
Local Ltac Lib.Step.mem_after_store ::= first [ StoreFastC.mem_after_store_fastzc | StoreFastZ.mem_after_store_fastz | StoreFast.mem_after_store_fast ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.

(* [comment removed for export] *)
Ltac lin16 H := lazymatch type of H with (?x mod 16 = 0)%Z =>
  let E := fresh "E16" in pose proof (Z.div_mod x 16 ltac:(lia)) as E; rewrite H, Z.add_0_r in E; clear H;
  let q := fresh "qal" in set (q := (x / 16)%Z) in E; clearbody q; rename E into H end.

Import ListNotations. Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpFast.   (* [comment removed for export] *)
Local Ltac BzTac.mlia ::= CmpFast.mlia_fast.   (* [comment removed for export] *)
Local Ltac Lib.ZBridge.mlia ::= CmpFast.mlia_fast.   (* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require RangeFast RangeFastEnv.
#[local] Ltac2 Set RangeFast.RF.rc_atom_facts := RangeFastEnv.env_atom_facts.
Local Ltac Lib.ZBridge.flia ::= RangeFast.rc_decide ltac:(first [ assumption | Lib.ZBridge.slim; lia | lia ]).
Local Ltac Lib.ZBridge.mlia ::= RangeFast.rc_decide ltac:(CmpFast.mlia_fast).
Local Ltac Bz.BzTac.mlia ::= RangeFast.rc_decide ltac:(CmpFast.mlia_fast).
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpLiaC.   (* [comment removed for export] *)
Local Ltac lia ::= CmpLiaC.lia_c.   (* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpSepV.   (* [comment removed for export] *)
Local Ltac Lib.Step.slia ::= CmpSepV.slia_v.   (* [comment removed for export] *)
Local Ltac Lib.StoreFast.tslia ::= CmpSepV.tslia_v.   (* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpStEq.   (* [comment removed for export] *)
Local Ltac BzTac.st_eq ::= CmpStEq.st_eq_fast.   (* [comment removed for export] *)
Local Ltac simpl_arr_sizes ::= CmpFast.sas7_all.   (* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac Lib.Step.solve_load ::= AsanKit.asan_solve_load.
Section ACeilS1. Context {BZP : BzParams} {ACEIL__ : ACeil}.


Section AP.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m0 : word -> option byte).
  Variables (cx : cctx) (g : eg) (e : est) (lo : Z) (sv : word).
  Notation usp := (bv_unsigned sp). Notation E := (c_E cx). Notation A2 := (c_A2 cx). Notation J := (c_J cx).
  Notation nblock := (e_nblock e). Notation ch := (e_state_in_ch e). Notation len := (e_state_in_len e). Notation crc0 := (e_blockCRC e).
  Hypothesis CX : cctx_ok cx. Hypothesis SEP2 : apart E ESTATE_SIZE A2 ARR2_SIZE. Hypothesis IME : img_apart (ci_hi (aci_c B0C)) E ESTATE_SIZE. Hypothesis IMA : img_apart (ci_hi (aci_c B0C)) A2 ARR2_SIZE.
  Hypothesis Hch : (0 <= ch < 256)%Z. Hypothesis Hlen : (1 <= len <= 255)%Z. Hypothesis Hcrc : (0 <= crc0 < 4294967296)%Z.
  Hypothesis Hnb : (0 <= nblock)%Z. Hypothesis ROOM : (nblock + 5 <= ARR2_SIZE)%Z.
  Hypothesis DEFI : zdefr (e_inUse e) 0 256. Hypothesis BOK : zbok (e_arr2 e).
  Hypothesis LO : (CEIL <= lo)%Z. Hypothesis LO16 : (lo + 16 <= usp)%Z.
  Variables (t0 t1 t2 t3 t4 t5 t6 : word).

  Notation W := (add_pair_W cx e ++ [(usp - 16, usp)])%Z.
  Variable SHE : Z. Hypothesis AE : sanchor E SHE.
  Hypothesis SHe : shzW b0segs W m0 E (E + ESTATE_SIZE).
  Hypothesis SHc : shzW b0segs W m0 (ci_crc (aci_c B0C)) (ci_crc (aci_c B0C) + 1024).
  Hypothesis SH2 : shzW b0segs W m0 A2 (A2 + ARR2_SIZE).
  Notation POST := (add_pair_post b0segs cx g e ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo W m0).
  (* [comment removed for export] *)
  Definition MEMp (nb : Z) (crcw : word) (inUse blk : zarr) (m : word -> option byte) : Prop :=
    rw_cells b0segs m E (EHEAD1 cx g (est_set_rl e (RL nb blk inUse (e_blockCRC e) ch len))) /\
    rw_cells b0segs m (E + 640) (cset 2 (C4 crcw) (EHEAD2 cx g e)) /\
    u8arr b0segs m (E + 128) (ovb inUse (jseg J 128 256) 256) /\
    u8arr b0segs m A2 (zb8 blk ARR2_SIZE) /\
    u32arr b0segs m (ci_crc (aci_c B0C)) crc_words /\ ro_cells b0segs m (ci_got (aci_c B0C) + 24) [C8 (Z_to_bv 64 (ci_crc (aci_c B0C)))] /\
    mem_inv b0segs m /\ munch W m0 m /\ wmono b0segs m0 m /\ stk b0segs m lo (usp + -16) /\ rw_cells b0segs m (usp + -16) [C8 s0; C8 ra].

  Ltac prep :=
    let ALE := ident:(ALE) in let AL1 := ident:(AL1) in let AL2 := ident:(AL2) in let ALF := ident:(ALF) in let ALB := ident:(ALB) in let ALFb := ident:(ALFb) in pose proof CX as CX'; unfold cctx_ok in CX'; cbv zeta in CX';
    bz_ceil; bz_params; unfold ESTATE_SIZE, FTAB_WORDS, BZFILE_SIZE, IMG_HI3, CEIL in CX';
    cps_destruct CX' as (RE1 & RE2 & RA1 & RA1' & RA2 & RA2' & RFT & RFT' & RBZ & RBZ' & RFB & RFB' & ALE & AL1 & AL2 & ALF & ALB & ALFb & LJ & LJB); try lin16 ALE; try lin16 AL1; try lin16 AL2; try lin16 ALF; try lin16 ALB; try lin16 ALFb;
    pose proof SEP2 as SEP2'; pose proof IME as IME'; pose proof IMA as IMA'; unfold apart, img_apart, ESTATE_SIZE, IMG_LO3, IMG_HI3 in SEP2', IME', IMA'; cbn [ci_hi aci_c B0C] in IME', IMA';
    bz_ceil; bz_params; unfold ESTATE_SIZE, CEIL in *; pose proof crc_words_length as CWL.
  Ltac fin_tac :=
    bz_params; cbn [e_arr2 e_inUse est_set_rl rl_block rl_inUse rl_nblock rl_crc rl_ch rl_len];
    repeat match goal with H : u8arr _ _ _ _ |- _ => rewrite ?unsigned_lit in H by lia end;
    try assumption.
  Ltac blk_sb AR2 i :=
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
     lazymatch type of AR2 with u8arr _ _ ?A (zb8 ?a _) =>
      let SO := fresh "SO" in
      pose proof (u8arr_store_ok b0segs mm A _ i _ AR2 ltac:(rewrite zb8_length_nat; lia) eq_refl) as SO;
      wstep;
      match goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le1 ?w)) _) =>
        let H := fresh "AR" in pose proof (zb8_write1 b0segs mm A a ARR2_SIZE i w AR2 ltac:(lia)) as H;
        clear AR2; store_done; rename H into AR2 end end end.
  Ltac openp MEM := let EH1 := ident:(EH1) in let EH2 := ident:(EH2) in let CRC := ident:(CRC) in let GOTC := ident:(GOTC) in let MU := ident:(MU) in cps_destruct MEM as (EH1 & EH2 & INU & AR2 & CRC & GOTC & MI & MU & WM & STK & FR); unfold EHEAD1, EHEAD2 in EH1, EH2;
    change (ci_got (aci_c B0C) + 24)%Z with 842416%Z in GOTC; change (ci_crc (aci_c B0C)) with 857056%Z in CRC, GOTC;
    cbn [e_mode e_state e_avail_in_expect e_arr1 e_arr2 e_ftab e_origPtr e_state_in_ch e_state_in_len e_nblock e_state_out_pos
         e_nInUse e_inUse e_unseqToSeq e_bw e_blockCRC e_combinedCRC e_blockNo e_nMTF e_mtfFreq e_selector e_selectorMtf
         e_len e_code e_rfreq e_len_pack est_set_rl rl_block rl_nblock rl_inUse rl_crc rl_ch rl_len cset ci_crc ci_got aci_c B0C Z.add] in EH1, EH2, CRC, GOTC;
    unfold add_pair_W in MU |- *; cbn [app] in MU |- *.

  (* [comment removed for export] *)
  Lemma ap_crc : forall (k : nat) (crc : Z) (crcw : word) (m : word -> option byte) (x10 x13 x16 x29 x31 : word),
    (1 <= Z.of_nat k <= 255)%Z -> (bv_unsigned crcw mod 4294967296 = crc)%Z -> (0 <= crc < 4294967296)%Z ->
    MEMp nblock crcw (e_inUse e) (e_arr2 e) m ->
    (forall crcw' x13' x31' m', (bv_unsigned crcw' mod 4294967296 = crc_update_n crc ch k)%Z -> MEMp nblock crcw' (e_inUse e) (e_arr2 e) m' ->
        evt b0segs POST (MS (mkR ra (Z_to_bv 64 (usp + -16)) gp tp (Z_to_bv 64 (SHE + 81)) (Z_to_bv 64 ch) crcw' s0 s1 x10 (Z_to_bv 64 E) (Z_to_bv 64 (E + 648)) x13'
                                  (Z_to_bv 64 2147450880) (Z_to_bv 64 ch) x16 (Z_to_bv 64 len)
                                  s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 857056) (Z_to_bv 64 0) x29 x31') F (Z_to_bv 64 0x89094) fc None m' (seg_rom b0segs))) ->
    evt b0segs POST (MS (mkR ra (Z_to_bv 64 (usp + -16)) gp tp (Z_to_bv 64 (SHE + 81)) (Z_to_bv 64 ch) crcw s0 s1 x10 (Z_to_bv 64 E) (Z_to_bv 64 (E + 648)) x13
                              (Z_to_bv 64 2147450880) (Z_to_bv 64 ch) x16 (Z_to_bv 64 len)
                              s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 857056) (Z_to_bv 64 (Z.of_nat k)) x29 x31) F (Z_to_bv 64 0x89034) fc None m (seg_rom b0segs)).
  Proof.
    induction k as [|k IH]; intros crc crcw m x10 x13 x16 x29 x31 Hk XC Hc MEM K; [lia|].
    openp MEM. prep. cbn [ci_crc aci_c B0C] in SHc. unfold add_pair_W in SHe, SHc. cbn [app] in SHe, SHc.
    (* [comment removed for export] *)
    brun_to 0x89044%Z.
    rewrite XC. set (idx := Z.lxor (crc / 16777216) ch).
    assert (Hidx : (0 <= idx < 256)%Z).
    { subst idx. apply lxor_byte; [|lia]. split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]. }
    (* [comment removed for export] *)
    brun.
    u32_read CRC crc_words_length idx tw NTH RD.
    replace (857056 + idx * 4)%Z with (857056 + 4 * idx)%Z by lia.
    wstep. clear RD.
    assert (Etw : tw = Z_to_bv 64 (crc32_tbl idx)).
    { pose proof (nth_error_wnth crc_words idx ltac:(lia) ltac:(rewrite crc_words_length; lia)) as N2.
      rewrite NTH in N2. injection N2 as N3. rewrite N3. apply wnth_crc_words. lia. }
    subst tw. pose proof (crc32_tbl_range idx Hidx) as TR.
    (* [comment removed for export] *)
    brun_to 0x89070%Z.
    assert (STEP : (bv_unsigned (Z_to_bv 64 (Z.lxor (bv_unsigned (sx32 (Z_to_bv 64 (crc32_tbl idx)))) ((bv_unsigned crcw * 256) mod 18446744073709551616))) mod 4294967296
                   = crc_update crc ch)%Z).      (* [comment removed for export] *)
    { rewrite Z.lxor_comm. unfold crc_update. rewrite land255_mod, (Z.mod_small ch 256) by lia. rewrite shiftr_div24. subst idx.
      apply low32_crc_step'; [exact XC| exact TR]. }
    pose proof (crc_update_range crc ch ltac:(lia)) as CR'.
    (* [comment removed for export] *)
    wstep; if_cases Kc; zify_cond_z Kc.
    - (* [comment removed for export] *)
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        enter_with (IH (crc_update crc ch) _ mm x10 _ x16 x29 _); [st_eq| lia| exact STEP | exact CR' | |] end.
      + split; [exact EH1|]. split; [exact EH2|]. split; [exact INU|]. split; [exact AR2|]. split; [exact CRC|]. split; [exact GOTC|].
        split; [exact MI|]. split; [exact MU|]. split; [exact WM|]. split; [exact STK| exact FR].
      + intros crcw' x13' x31' m' XC' MEM'. eapply K; [|exact MEM']. rewrite XC'. rewrite crc_update_n_S. reflexivity.
    - (* [comment removed for export] *)
      assert (k = 0)%nat by lia. subst k.
      wstep.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (K _ _ _ mm); [st_eq| exact STEP | ] end.
      split; [exact EH1|]. split; [exact EH2|]. split; [exact INU|]. split; [exact AR2|]. split; [exact CRC|]. split; [exact GOTC|].
      split; [exact MI|]. split; [exact MU|]. split; [exact WM|]. split; [exact STK| exact FR].
  Qed.

  (* [comment removed for export] *)
  Ltac ap_exit FR STK :=
    brun_to 0x89644%Z; wstep; wstep; wstep; release_frame FR STK (bv_unsigned sp);
    replace (Z_to_bv 64 (bv_unsigned sp + -16 + 16)) with sp by (rewrite <- (Z_to_bv_bv_unsigned sp) at 1; f_equal; lia);
    wstep.

  (* [comment removed for export] *)
  Lemma rl_put_eq : forall r b, 0 <= b -> rl_put r b = RL (rl_nblock r + 1) (wr8 (rl_block r) (rl_nblock r) b) (rl_inUse r) (rl_crc r) (rl_ch r) (rl_len r).
  Proof. intros r b Hb. unfold rl_put. rewrite wr8_zset_land by exact Hb. reflexivity. Qed.

  (* [comment removed for export] *)
  Lemma ap_tail : forall (crcw x13 x29 x31 : word) (m : word -> option byte),
    (bv_unsigned crcw mod 4294967296 = crc_update_n crc0 ch (Z.to_nat len))%Z ->
    MEMp nblock crcw (e_inUse e) (e_arr2 e) m ->
    evt b0segs POST (MS (mkR ra (Z_to_bv 64 (usp + -16)) gp tp (Z_to_bv 64 (SHE + 81)) (Z_to_bv 64 ch) crcw s0 s1 (Z_to_bv 64 (E + 96)) (Z_to_bv 64 E) (Z_to_bv 64 (E + 648)) x13
                              (Z_to_bv 64 2147450880) (Z_to_bv 64 ch) (Z_to_bv 64 (SHE + 12)) (Z_to_bv 64 len)
                              s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 857056) (Z_to_bv 64 0) x29 x31) F (Z_to_bv 64 0x89094) fc None m (seg_rom b0segs)).
  Proof.
    intros crcw x13 x29 x31 m XC MEM. openp MEM. prep.
    cbn [ci_crc aci_c B0C] in SHc. unfold add_pair_W in SHe, SHc, SH2. cbn [app] in SHe, SHc, SH2.
    pose proof (ovb_length (e_inUse e) (jseg J 128 256) 256 ltac:(lia)) as LIU.
    pose proof (zb8_length (e_arr2 e) ARR2_SIZE ltac:(lia)) as LA2.
    (* [comment removed for export] *)
    brun.
    pose proof (u8arr_store_ok b0segs m (E + 128) _ ch _ INU ltac:(rewrite ovb_length_nat; lia) eq_refl) as SO.
    wstep.
    match goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le1 ?w)) _) =>
      pose proof (ovb_write1 b0segs m (E + 128) (e_inUse e) (jseg J 128 256) 256 ch w INU ltac:(lia)) as INU' end.
    clear INU. store_done. rename INU' into INU.
    replace (wr8 (e_inUse e) ch (bv_unsigned (Z_to_bv 64 1))) with (zset (e_inUse e) ch 1) in INU by reflexivity.
    assert (CRN : (0 <= crc_update_n crc0 ch (Z.to_nat len) < 4294967296)%Z) by (apply crc_update_n_range; lia).
    reword_C4 EH2 2%nat (crc_update_n crc0 ch (Z.to_nat len)). { rewrite XC. symmetry. apply Z.mod_small. exact CRN. }
    (* [comment removed for export] *)
    brun; if_cases K3; zify_cond_z K3.
    - (* [comment removed for export] *)
      brun. blk_sb AR2 (e_nblock e).
      brun. blk_sb AR2 (e_nblock e + 1)%Z.
      brun. blk_sb AR2 (e_nblock e + 2)%Z.
      ap_exit FR STK.
      unfold add_pair_post. cbv zeta.
      replace (add_pair_to_block (est_rl e)) with
        (RL (nblock + 3) (wr8 (wr8 (wr8 (e_arr2 e) nblock ch) (nblock + 1) ch) (nblock + 2) ch) (zset (e_inUse e) ch 1) (crc_update_n crc0 ch (Z.to_nat len)) ch len).
      2:{ unfold add_pair_to_block, est_rl. cbn [rl_nblock rl_block rl_inUse rl_crc rl_ch rl_len].
          replace (len =? 1)%Z with false by (symmetry; apply Z.eqb_neq; lia). replace (len =? 2)%Z with false by (symmetry; apply Z.eqb_neq; lia).
          replace (len =? 3)%Z with true by (symmetry; apply Z.eqb_eq; lia).
          rewrite !rl_put_eq by (apply Z.land_nonneg; right; lia). cbn [rl_nblock rl_block rl_inUse rl_crc rl_ch rl_len].
          rewrite land255_mod, (Z.mod_small ch 256) by lia. CmpFast.rlf_sp. }
      finish. fin_tac.
    - brun; if_cases K2; zify_cond_z K2.
      + (* [comment removed for export] *)
        brun. blk_sb AR2 (e_nblock e).
        brun. blk_sb AR2 (e_nblock e + 1)%Z.
        ap_exit FR STK.
        unfold add_pair_post. cbv zeta.
        replace (add_pair_to_block (est_rl e)) with
          (RL (nblock + 2) (wr8 (wr8 (e_arr2 e) nblock ch) (nblock + 1) ch) (zset (e_inUse e) ch 1) (crc_update_n crc0 ch (Z.to_nat len)) ch len).
        2:{ unfold add_pair_to_block, est_rl. cbn [rl_nblock rl_block rl_inUse rl_crc rl_ch rl_len].
            replace (len =? 1)%Z with false by (symmetry; apply Z.eqb_neq; lia). replace (len =? 2)%Z with true by (symmetry; apply Z.eqb_eq; lia).
            rewrite !rl_put_eq by (apply Z.land_nonneg; right; lia). cbn [rl_nblock rl_block rl_inUse rl_crc rl_ch rl_len].
            rewrite land255_mod, (Z.mod_small ch 256) by lia. CmpFast.rlf_sp. }
        finish. fin_tac.
      + brun; if_cases K1; zify_cond_z K1.
        * (* [comment removed for export] *)
          brun_to 0x893ec%Z.
          replace (E + 128 + (len + -4))%Z with (E + 128 + (len - 4))%Z by lia.   (* [comment removed for export] *)
          brun.
          pose proof (u8arr_store_ok b0segs _ (E + 128) _ (len - 4) _ INU ltac:(rewrite ovb_length_nat; lia) eq_refl) as SO2.
          wstep.
          lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mm _ (le1 ?w)) _) =>
            pose proof (ovb_write1 b0segs mm (E + 128) (zset (e_inUse e) ch 1) (jseg J 128 256) 256 (len - 4) w INU ltac:(lia)) as INU' end.
          clear INU. store_done. rename INU' into INU.
          replace (wr8 (zset (e_inUse e) ch 1) (len - 4) (bv_unsigned (Z_to_bv 64 1))) with (zset (zset (e_inUse e) ch 1) (len - 4) 1) in INU by reflexivity.
          (* [comment removed for export] *)
          brun. blk_sb AR2 (e_nblock e).
          brun. blk_sb AR2 (e_nblock e + 1)%Z.
          brun. blk_sb AR2 (e_nblock e + 2)%Z.
          brun. blk_sb AR2 (e_nblock e + 3)%Z.
          (* [comment removed for export] *)
          (* [comment removed for export] *)
          brun. blk_sb AR2 (e_nblock e + 4)%Z.
          ap_exit FR STK.
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
          brun. blk_sb AR2 (e_nblock e).
          ap_exit FR STK.
          unfold add_pair_post. cbv zeta.
          replace (add_pair_to_block (est_rl e)) with (RL (nblock + 1) (wr8 (e_arr2 e) nblock ch) (zset (e_inUse e) ch 1) (crc_update_n crc0 ch (Z.to_nat len)) ch len).
          2:{ unfold add_pair_to_block, est_rl. cbn [rl_nblock rl_block rl_inUse rl_crc rl_ch rl_len].
              replace (len =? 1)%Z with true by (symmetry; apply Z.eqb_eq; lia). rewrite rl_put_eq by (apply Z.land_nonneg; right; lia).
              cbn [rl_nblock rl_block rl_inUse rl_crc rl_ch rl_len]. rewrite land255_mod, (Z.mod_small ch 256) by lia. reflexivity. }
          finish. fin_tac.
  Qed.

  (* [comment removed for export] *)
  Lemma ap_entry : forall (x11 x12 x13 x14 x15 x16 x17 : word),
    rw_cells b0segs m0 E (EHEAD1 cx g e) -> rw_cells b0segs m0 (E + 640) (EHEAD2 cx g e) ->
    u8arr b0segs m0 (E + 128) (ovb (e_inUse e) (jseg J 128 256) 256) -> u8arr b0segs m0 A2 (zb8 (e_arr2 e) ARR2_SIZE) ->
    u32arr b0segs m0 (ci_crc (aci_c B0C)) crc_words -> ro_cells b0segs m0 (ci_got (aci_c B0C) + 24) [C8 (Z_to_bv 64 (ci_crc (aci_c B0C)))] ->
    mem_inv b0segs m0 -> stk b0segs m0 lo usp -> aconsts B0C m0 ->
    evt b0segs POST (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 E) x11 x12 x13 x14 x15 x16 x17
                              s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x88fa4) fc None m0 (seg_rom b0segs)).
  Proof.
    intros x11 x12 x13 x14 x15 x16 x17 EH1 EH2 INU AR2 CRC GOTC MI STK AC.
    destruct AC as [GOT SBV]. cbn [aci_segs aci_c aci_got_sh aci_shvar B0C ci_segs] in GOT, SBV.
    pose proof (munch_refl W m0) as MU. pose proof (wmono_refl b0segs m0) as WM.
    unfold EHEAD1, EHEAD2 in EH1, EH2.
    change (ci_got (aci_c B0C) + 24)%Z with 842416%Z in GOTC; change (ci_crc (aci_c B0C)) with 857056%Z in CRC, GOTC.
    cbn [e_mode e_state e_avail_in_expect e_arr1 e_arr2 e_ftab e_origPtr e_state_in_ch e_state_in_len e_nblock e_state_out_pos
         e_nInUse e_inUse e_unseqToSeq e_bw e_blockCRC e_combinedCRC e_blockNo e_nMTF e_mtfFreq e_selector e_selectorMtf
         e_len e_code e_rfreq e_len_pack est_set_rl rl_block rl_nblock rl_inUse rl_crc rl_ch rl_len cset ci_crc ci_got aci_c B0C Z.add] in EH1, EH2, CRC, GOTC.
    unfold add_pair_W in MU |- *; cbn [app] in MU |- *.
    prep. cbn [ci_crc aci_c B0C] in SHc. unfold add_pair_W in SHe, SHc, SH2. cbn [app] in SHe, SHc, SH2.
    pose proof (ovb_length (e_inUse e) (jseg J 128 256) 256 ltac:(lia)) as LIU.
    pose proof (zb8_length (e_arr2 e) ARR2_SIZE ltac:(lia)) as LA2.
    carve_frame 16%nat STK.
    (* [comment removed for export] *)
    brun; if_cases K0; zify_cond_z K0; [exfalso; lia|].
    (* [comment removed for export] *)
    brun_to 0x89034%Z.
    change 18446744073709551615%Z with (Z.ones 64). rewrite (Z.land_comm (Z.ones 64) len), Z.land_ones, (Z.mod_small len) by lia.      (* [comment removed for export] *)
    rewrite (Z.land_ones ch 8) || rewrite land255_mod. rewrite (Z.mod_small ch 256) by lia.
    unshelve (epose proof (rw_cells_C4_reword b0segs _ (E + 640) _ 2 _ (sx32 (Z_to_bv 64 crc0)) EH2 eq_refl _) as EH2'); [rewrite low32_sx32; reflexivity|].
    cbn [cset] in EH2'.
    sh_norm.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      enter_with (ap_crc (Z.to_nat len) crc0 (sx32 (Z_to_bv 64 crc0)) mm _ _ _ _ _); [st_eq| lia| rewrite low32_sx32, low32_lit; apply Z.mod_small; lia| lia| |] end.
    { split; [exact EH1|]. split; [cbn [cset]; exact EH2'|]. split; [exact INU|]. split; [exact AR2|]. split; [exact CRC|]. split; [exact GOTC|].
      split; [exact MI|]. split; [exact MU|]. split; [exact WM|]. split; [exact STK| exact FR]. }
    intros crcw' x13' x31' m' XC' MEM'. eapply ap_tail; [exact XC'| exact MEM'].
  Qed.

End AP.

Theorem B0_add_pair : add_pair_aspecF B0C 16.
Proof.
  unfold add_pair_aspecF. cbn [aci_segs aci_c ci_segs ci_add_pair B0C]. intros until sv. intros -> EH1 EH2 INU AR2 CM MI ST LO16 LO CX SEP IMG Hch Hlen Hcrc Hnb ROOM DEFI BOK AC CSH ISH.
  pose proof CX as CX'. unfold cctx_ok in CX'. cbv zeta in CX'.
  unfold cctx_sep in SEP. cbv zeta in SEP. cps_destruct SEP as (_ & SEP2 & _).
  unfold cctx_img in IMG. cps_destruct IMG as (IME & _ & IMA & _).
  pose proof (acimg_crc_u32arr B0C m sv CM) as CRC. cps_destruct CM as (_ & GOTC & _ & _).
  destruct CSH as (SHe & _ & SH2 & _ & _). unfold cimg_sh in ISH.
  assert (AE : sanchor (c_E cx) (c_E cx / 8 + 2147450880)).
  { apply sanchor_intro. cps_destruct CX' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & ALE & _). clear - ALE. Z.div_mod_to_equations. lia. }
  eapply (ap_entry ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m cx g e lo); try eassumption.
Qed.

End ACeilS1.
