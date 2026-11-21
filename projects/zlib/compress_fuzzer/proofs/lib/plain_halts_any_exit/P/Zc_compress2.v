(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP MonadX Frame.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Malloc Require Import MallocBlocks Malloc_iface.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.MallocP Require Import RMallocRep RMallocTree RMalloc_iface.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec Require Import Prelim STree Malloc Monad Stdio ZApi ZHarness ZInst ZTarget ZApiL ZHarnessL ZApiC ZHarnessC ZInstC ZTargetC Target Prog.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require ZIface ZApiInst ZApiInstC ZApiOkC ZLoopFactsC.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.P Require Import Layout Exit Startup_glue F_stdio_exit Printf_lib Drv_kit Zlib_iface Zh_kit Z_deflate Zc_kit Zc_wkit Zc_drc Zc_c2facts Zc_iface.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.P Require Zc_zrd.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.P Require Z_dview.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Lib Require Import Ceiling.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.P Require Import Rnd.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Lib Require Import StoreFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Notation psegs := Image.psegs.
Notation mem := (word -> option byte).
Notation wz := MallocRep.wz.
Ltac rpc := apply ret_pc_even; [lia| reflexivity].
Ltac nm n t := first [t | fail 100 "premise" n].
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof alloc_ceiling_range as CEIL_RANGE__); std_lia__].

Local Transparent the_zapi the_zapiC.

(* 1.4 (zl14-cmp): compress2 (ZC_COMPRESS2) is a 32-byte wrapper that copies *destLen into a local (got), calls the
   new compress2_z (ZC_COMPRESS2Z, the old body with NULL checks and z_size_t lengths) with &got, and stores got back.
   Section C2 walks compress2_z; compress2_proof walks the wrapper. *)
Definition ZC_COMPRESS2Z : Z := 0x160f4.

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.
Notation za := the_zapi.
Notation zc := the_zapiC.

Section C2.
  Variable R : zreps.
  Hypothesis ZOK : zlib_okC R.
  Hypothesis HFRAME : RHEAP_frame_stmt.
  Hypothesis HBR : RHEAP_block_range_stmt.
  Hypothesis HND : RHEAP_blocks_nodup_stmt.
  Hypothesis HBD : RHEAP_blocks_disjoint_stmt.

  Variables (ra sp gp tp : word) (S0 S1 S2 S3 S4 S5 S6 S7 S8 S9 S10 S11 : word).
  Variables (LB : list block) (cp : bptr) (C N PL NI n lv : Z) (oldc src : list Z) (lo B : Z) (canary : word).
  Notation usp := (bv_unsigned sp).
  Notation SS := (usp + -160).
  Hypothesis INC : In (cp, C, N) LB.
  Hypothesis OLDL : zlength oldc = N.
  Hypothesis PLLO : usp <= PL.
  Hypothesis PLHI : PL + 8 <= B.
  Hypothesis PL8 : PL mod 8 = 0.
  Hypothesis SRCF : Forall (fun c => 0 <= c < 256) src.
  Hypothesis SRCL : zlength src = n.
  Hypothesis SRCB : exists b, In b LB /\ blk_addr b <= NI /\ NI + n <= blk_addr b + blk_size b.
  Hypothesis NEQ : NI + n <= C \/ C + N <= NI.
  Hypothesis NR : ZC_MIN - 3 <= n <= ZC_MAX - 3.
  Hypothesis ECL : N = zc_bound zc n.
  Hypothesis LV : 0 <= lv <= 9.
  Hypothesis SPB : usp <= B.
  Hypothesis B63 : B < 2^63.
  Hypothesis LOC : alloc_ceiling <= lo.
  Hypothesis LOG : GLOBALS_TOP <= lo.
  Hypothesis LOSP : lo <= usp - (ZC_WRAP_STACK - 32).
  Hypothesis TP : tp = wz RATP.
  Hypothesis SP16 : usp mod 16 = 0.
  Hypothesis CR : rblock_range C N.
  Hypothesis LBR : forall b, In b LB -> rblock_range (blk_addr b) (blk_size b).

  Lemma N_facts : n < N <= 2097152 /\ 7 <= n <= 1048573 /\ zlength src <= 2097152.
  Proof.
    pose proof (zo_boundC zc the_zapiC_ok n ltac:(unfold ZC_MIN, ZC_MAX in *; lia)) as HB. rewrite <- ECL in HB.
    unfold ZC_MIN, ZC_MAX, ZBC_MAX, ZC_MAX in *. lia.
  Qed.
  Lemma N_factsB : 0 <= N <= ZBC_MAX /\ zlength src <= ZBC_MAX.
  Proof. pose proof N_facts. unfold ZBC_MAX, ZC_MAX. lia. Qed.

  Notation XX := [(C, C + N); (PL, PL + 8)].

  Definition FRHI (mm : mem) : Prop := rw_cells psegs mm (usp + -48) [C8 S4; C8 S3; C8 S2; C8 S1; C8 S0; C8 ra].

  Lemma client_inner : forall a, lx_client LB usp XX a -> lx_client LB SS [(SS, SS + ZS_SIZEOF)] a.
  Proof.
    intros a [_ Hc]. split.
    - cbn [rin_ivs fst snd]. intros [Hi|[]]. unfold ZS_SIZEOF in Hi. destruct Hc as [Hc|[(b & Hb & Hr)|[Hc _]]]; [lia| |].
      + destruct (LBR b Hb) as (_ & _ & _ & BC & _). unfold ZC_WRAP_STACK, Z_INFLATE_STACK, RMALLOC_STACK in *. lia.
      + unfold ZC_WRAP_STACK, Z_INFLATE_STACK, RMALLOC_STACK, GLOBALS_TOP in *. lia.
    - destruct Hc as [Hc|[Hc|Hc]]; [left; lia| right; left; exact Hc| right; right; exact Hc].
  Qed.

  Lemma fr_lx : forall m m' (A : Z) cs, lx_pres LB SS [(SS, SS + ZS_SIZEOF)] m m' -> rw_cells psegs m A cs ->
    SS <= A -> (A + Z.of_nat (cells_size cs) <= SS \/ SS + ZS_SIZEOF <= A) -> rw_cells psegs m' A cs.
  Proof.
    intros m m' A cs LXP H HA HD. eapply rw_cells_agree; [exact (agree_of_lx_pres _ _ _ _ _ LXP)| exact H|].
    intros a Ha. apply stack_client; [lia|]. cbn [rin_ivs fst snd]. lia.
  Qed.

  Section Loop.
    Variables (m2 : mem) (LBz : list block) (F : bvmap 5 word) (fc : bv 32).
    Hypothesis LBZR : forall b, In b LBz -> rblock_range (blk_addr b) (blk_size b).
    Hypothesis LBZC : forall b, In b LBz -> blk_addr b + blk_size b <= C \/ C + N <= blk_addr b.
    Hypothesis LBZS : forall b, In b LBz -> blk_addr b + blk_size b <= NI \/ NI + n <= blk_addr b.
    Hypothesis ZLS2 : zl_statics m2.
    Hypothesis SRC2 : bytes_at psegs m2 NI (to_bytes src).

    Definition W0 : list (Z * Z) := [(lo, usp); (C, C + N)] ++ map (fun b => (blk_addr b, blk_addr b + blk_size b)) LBz.

    Lemma fp_call : forall n0 k, 0 <= n0 -> 0 <= k -> n0 + k <= N ->
      sub_fp ([(lo, SS); (SS, SS + ZS_SIZEOF); (C + n0, C + n0 + k)] ++ map (fun b => (blk_addr b, blk_addr b + blk_size b)) LBz) W0.
    Proof.
      intros n0 k H0 Hk H x Hx. unfold W0 in Hx. apply outside_app in Hx. destruct Hx as [Hx1 Hx2]. apply outside_app. split; [| exact Hx2].
      cbn [outside] in Hx1 |- *. unfold ZS_SIZEOF. unfold ZC_WRAP_STACK, Z_INFLATE_STACK, RMALLOC_STACK in LOSP. lia.
    Qed.
    Lemma fp_pub : sub_fp [(SS, SS + 48)] W0.
    Proof. intros x Hx. unfold W0 in Hx. cbn [app outside] in Hx |- *. unfold ZC_WRAP_STACK, Z_INFLATE_STACK, RMALLOC_STACK in LOSP. split; [lia| exact I]. Qed.

    Lemma W0_image : forall a, 0x29000 <= a < 0x5c000 -> outside W0 a.
    Proof.
      intros a Ha. unfold W0. apply outside_app. split.
      - cbn [outside]. unfold GLOBALS_TOP in *. destruct CR as (_ & _ & _ & _ & CI). lia.
      - apply outside_blocks. intros b Hb. destruct (LBZR b Hb) as (_ & _ & _ & _ & BI). lia.
    Qed.
    Lemma W0_high : forall a, usp <= a -> outside W0 a.
    Proof.
      intros a Ha. unfold W0. apply outside_app. split.
      - cbn [outside]. destruct CR as (_ & _ & _ & CC & _). unfold ZC_WRAP_STACK, Z_INFLATE_STACK, RMALLOC_STACK in *. lia.
      - apply outside_blocks. intros b Hb. destruct (LBZR b Hb) as (_ & _ & _ & BC & _). unfold ZC_WRAP_STACK, Z_INFLATE_STACK, RMALLOC_STACK in *. lia.
    Qed.
    Lemma W0_heap : forall a, a < lo -> ~ (C <= a < C + N) -> (a < 0x10000 \/ 0x5c000 <= a) ->
      (forall b, In b LBz -> ~ (blk_addr b <= a < blk_addr b + blk_size b)) -> outside W0 a.
    Proof.
      intros a Ha Hc Hi Hb. unfold W0. apply outside_app. split.
      - cbn [outside]. lia.
      - apply outside_blocks. exact Hb.
    Qed.

    Lemma zls_inv : forall m, munch W0 m2 m -> wmono psegs m2 m -> zl_statics m.
    Proof.
      intros m MU WM. eapply zl_statics_agree; [exact (agree_on_of_munch _ _ _ MU WM)| | exact ZLS2].
      intros a Ha. apply W0_image. unfold zls_addr, ZL_RELRO_LO, ZL_RELRO_HI, ZL_GOT_LO, ZL_GOT_HI, ZH_STATICS, ZL_MREPL in Ha. lia.
    Qed.
    Lemma src_inv : forall m, munch W0 m2 m -> wmono psegs m2 m -> bytes_at psegs m NI (to_bytes src).
    Proof.
      intros m MU WM. eapply bytes_at_agree; [exact (agree_on_of_munch _ _ _ MU WM)| exact SRC2|].
      intros a Ha. rewrite to_bytes_len in Ha. unfold zlength in SRCL. destruct SRCB as (b & Hb & B1 & B2). destruct (LBR b Hb) as (_ & _ & _ & BC & BI).
      apply W0_heap; [lia| lia| lia|]. intros b' Hb'. pose proof (LBZS b' Hb'). lia.
    Qed.

    Lemma zrd_own : forall m m' ds W, Zlib_iface.zr_d R m SS LBz ds -> munch W m m' -> wmono psegs m m' -> sub_fp W [(SS, SS + 48)] ->
      Zlib_iface.zr_d R m' SS LBz ds.
    Proof.
      intros m m' ds W ZR MU WM SUB. eapply (zr_d_frame R); [exact ZR|]. intros a Ha Hin.
      apply (agree_on_of_munch _ _ _ (munch_weaken _ _ _ _ SUB MU) WM a Ha). cbn [outside]. split; [| exact I].
      destruct Hin as [Hin|(b & Hb & Hr)]; [unfold ZS_PUB, ZS_SIZEOF in *; lia|].
      destruct (LBZR b Hb) as (_ & _ & _ & BC & _). unfold ZC_WRAP_STACK, Z_INFLATE_STACK, RMALLOC_STACK in *. lia.
    Qed.

    Definition CINV (m : mem) (x : c2L zc) (k : Z) : Prop :=
      (exists p1 p2, rw_cells psegs m SS (zs_pub (NI + (zlength src - zlength (c2_rest zc x))) (c2_ain zc x) (c2_tin x)
                                               (C + c2_tout x) (c2_aout zc x) (c2_tout x) p1 p2))
      /\ Zlib_iface.zr_d R m SS LBz (c2_ds zc x)
      /\ u8arr psegs m C (to_bytes (rev (c2_orev zc x) ++ skipn (length (c2_orev zc x)) oldc))
      /\ FRHI m /\ rw_cells psegs m PL [C8 (wz 0)]
      /\ munch W0 m2 m /\ wmono psegs m2 m /\ mem_inv psegs m /\ stk psegs m lo SS
      /\ 0 <= k /\ c2_tin x <= k * ZC_MAX /\ Forall (fun c => 0 <= c < 256) (c2_orev zc x).

    Definition head_pc (x : c2L zc) : Z := if c2_aout zc x =? 0 then 0x161b0 else 0x16190.

    (* 1.4 registers: s0 = destLen, s1 = dest (kept for next_out - dest), s2 = sourceLen, s3 = left, s4 = max *)
    Notation HDS pc x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 slen left m :=
      (MS (mkR x1 (wz SS) gp tp t0 t1 t2 (wz PL) (wz C) a0 a1 a2 a3 a4 a5 a6 a7 (wz slen) (wz left) (wz 4294967295) S5 S6 S7 S8 S9 S10 S11 t3 t4 t5 t6)
          F pc fc None m (seg_rom psegs)).

    Lemma c2_head_to_call : forall (Q : machine_state -> Prop) m x k (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
      C2I N src lv x -> CINV m x k ->
      (forall m1 (t0' t1' t2' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (ret : Z) (p1 p2 : list byte),
         (ret = 0x161a8 \/ ret = 0x161f0) ->
         munch [(SS, SS + 48)] m m1 -> wmono psegs m m1 -> mem_inv psegs m1 -> stk psegs m1 lo SS ->
         rw_cells psegs m1 SS (zs_pub (NI + (zlength src - zlength (c2_rest zc x))) (zlength (c2_rest zc x)) (c2_tin x)
                                      (C + c2_tout x) (N - c2_tout x) (c2_tout x) p1 p2) ->
         evt psegs Q (HDS (wz Z_DEFLATE) (wz ret) t0' t1' t2' (wz SS) (wz Z_FINISH) a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' 0 0 m1)) ->
      evt psegs Q (HDS (wz (head_pc x)) x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (c2_slen zc x) (c2_left zc x) m).
    Proof.
      intros until t6. intros CX (PUB & ZR & OUT & FRH & PLC & MU & WM & MI & ST & K0 & TIN & ORF) K.
      pose proof N_facts as (NF1 & NF2 & NF3).
      pose proof (C2I_shape N src lv x (proj1 N_factsB) CX) as SH. cbv zeta in SH.
      destruct SH as (TOUT & TOUT0 & SUM & AOUT0 & LEFT0 & AIN0 & SLEN0 & SUMI & RL & SLAI & LEAO & EREST & TINR & RESTF).
      destruct PUB as (p1 & p2 & PUB).
      pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
      unfold ZC_WRAP_STACK, Z_INFLATE_STACK, RMALLOC_STACK, GLOBALS_TOP in LOSP, LOG.
      assert (RL0 : 0 <= zlength (c2_rest zc x)) by (unfold zlength; lia).
      apply box in ZR. apply box in OUT. apply box in MU. apply box in WM.
      pose proof (munch_refl [(SS, SS + 48)] m) as MUp. pose proof (wmono_refl psegs m) as WMp.
      unfold zs_pub in PUB. cbv beta delta [MallocRep.wz] in PUB.
      unfold head_pc. cbv beta delta [MallocRep.wz].
      destruct (Z.eqb_spec (c2_aout zc x) 0) as [EA|EA].
      -
        rewrite EA in PUB.
        assert (HLT : bv_ltu (Z_to_bv 64 (c2_left zc x)) (Z_to_bv 64 4294967295) = true) by (unfold bv_ltu; rewrite !unsigned_lit by lia; apply Z.ltb_lt; lia).
        zstep. zstep. rewrite HLT; cbv_concl_iota. zstep. zstep. zstep. zstep.
        if_cases KAI; rewrite sx32_small in KAI by lia; zify_cond KAI; rewrite ?unsigned_lit in KAI by lia.
        +
          assert (ESL : c2_slen zc x = 0) by lia. rewrite ESL.
          zstep. zstep. zstep. zstep.
          lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
          replace (c2_left zc x + - c2_left zc x) with 0 by lia.
          eapply (K m1); [left; reflexivity| exact MUp| exact WMp| assumption| assumption|].
          unfold zs_pub. cbv beta delta [MallocRep.wz]. replace (c2_ain zc x) with (zlength (c2_rest zc x)) in PUB by lia.
          replace (c2_left zc x) with (N - c2_tout x) in PUB by lia. exact PUB.
        +
          assert (EAI : c2_ain zc x = 0) by lia. rewrite EAI in *.
          assert (HLT2 : bv_ltu (Z_to_bv 64 (c2_slen zc x)) (Z_to_bv 64 4294967295) = true) by (unfold bv_ltu; rewrite !unsigned_lit by lia; apply Z.ltb_lt; lia).
          zstep. zstep. rewrite HLT2; cbv_concl_iota. zstep. zstep.
          replace (c2_slen zc x + - c2_slen zc x) with 0 by lia. try replace (c2_left zc x + - c2_left zc x) with 0 by lia.
          zstep. zstep. zstep. zstep.
          lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
          eapply (K m1); [right; reflexivity| exact MUp| exact WMp| assumption| assumption|].
          unfold zs_pub. cbv beta delta [MallocRep.wz]. replace (c2_slen zc x) with (zlength (c2_rest zc x)) in PUB by lia.
          replace (c2_left zc x) with (N - c2_tout x) in PUB by lia. exact PUB.
      -
        assert (EL : c2_left zc x = 0) by lia. rewrite EL.
        zstep. zstep. if_cases KAI; rewrite sx32_small in KAI by lia; zify_cond KAI; rewrite ?unsigned_lit in KAI by lia.
        +
          assert (EAI : c2_ain zc x = 0) by lia. rewrite EAI in *.
          assert (HLT2 : bv_ltu (Z_to_bv 64 (c2_slen zc x)) (Z_to_bv 64 4294967295) = true) by (unfold bv_ltu; rewrite !unsigned_lit by lia; apply Z.ltb_lt; lia).
          zstep. zstep. rewrite HLT2; cbv_concl_iota. zstep. zstep.
          replace (c2_slen zc x + - c2_slen zc x) with 0 by lia. try replace (c2_left zc x + - c2_left zc x) with 0 by lia.
          zstep. zstep. zstep. zstep.
          lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
          eapply (K m1); [right; reflexivity| exact MUp| exact WMp| assumption| assumption|].
          unfold zs_pub. cbv beta delta [MallocRep.wz]. replace (c2_slen zc x) with (zlength (c2_rest zc x)) in PUB by lia.
          replace (c2_aout zc x) with (N - c2_tout x) in PUB by lia. exact PUB.
        +
          assert (ESL : c2_slen zc x = 0) by lia. rewrite ESL.
          zstep. zstep. zstep. zstep.
          lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
          eapply (K m1); [left; reflexivity| exact MUp| exact WMp| assumption| assumption|].
          unfold zs_pub. cbv beta delta [MallocRep.wz]. replace (c2_ain zc x) with (zlength (c2_rest zc x)) in PUB by lia.
          replace (c2_aout zc x) with (N - c2_tout x) in PUB by lia. exact PUB.
    Qed.

    Definition KMAX : Z := 4194304.

    Lemma c2_call : forall (Q : machine_state -> Prop) m m1 x k n0 r (t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (ret : Z) (p1 p2 : list byte),
      C2I N src lv x -> CINV m x k -> c2_after zc (S n0) x = Some r -> k < KMAX ->
      (ret = 0x161a8 \/ ret = 0x161f0) ->
      munch [(SS, SS + 48)] m m1 -> wmono psegs m m1 -> mem_inv psegs m1 -> stk psegs m1 lo SS ->
      rw_cells psegs m1 SS (zs_pub (NI + (zlength src - zlength (c2_rest zc x))) (zlength (c2_rest zc x)) (c2_tin x)
                                   (C + c2_tout x) (N - c2_tout x) (c2_tout x) p1 p2) ->
      (forall m' (x' : c2L zc) (rc : Z) (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
         CINV m' x' (k + 1) -> c2_slen zc x' = 0 -> c2_left zc x' = 0 ->
         (rc = Z_OK -> C2I N src lv x' /\ c2_after zc n0 x' = Some r) ->
         (rc <> Z_OK -> r = (x', rc)) ->
         - 2^31 <= rc < 2^31 ->
         evt psegs Q (HDS (ret_pc (wz ret)) (wz ret) t0' t1' t2' (wint rc) a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' 0 0 m')) ->
      evt psegs Q (HDS (wz Z_DEFLATE) (wz ret) t0 t1 t2 (wz SS) (wz Z_FINISH) a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 0 0 m1).
    Proof.
      intros until p2. intros CX CI AF KB RET MUp WMp MI1 ST1 PUB1 K.
      destruct ZOK as (_ & DEFL & _).
      pose proof N_facts as (NF1 & NF2 & NF3). pose proof N_factsB as [NB SB].
      pose proof (C2I_shape N src lv x NB CX) as SH. cbv zeta in SH.
      destruct SH as (TOUT & TOUT0 & SUM & AOUT0 & LEFT0 & AIN0 & SLEN0 & SUMI & RL & SLAI & LEAO & EREST & TINR & RESTF).
      destruct CI as (_ & ZR & OUT & FRH & PLC & MU & WM & MI & ST & K0 & TIN & ORF).
      pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
      unfold ZC_WRAP_STACK, Z_INFLATE_STACK, RMALLOC_STACK, GLOBALS_TOP in LOSP, LOG. unfold KMAX in KB. unfold ZC_MAX in TIN.
      pose proof CR as (C0 & _ & _ & CC & CI). destruct SRCB as (bS & HbS & BS1 & BS2). destruct (LBR bS HbS) as (S0' & _ & _ & SC & SI).
      assert (RL0 : 0 <= zlength (c2_rest zc x)) by (unfold zlength; lia).
      set (rest := c2_rest zc x) in *. set (tout := c2_tout x) in *. set (k0 := zlength src - zlength rest) in *.

      pose proof (c2_trip N src lv x n0 r NB SB CX AF) as TR. cbv zeta in TR. fold rest tout in TR.
      destruct (dc_deflate zc rest (c2_ds zc x) (N - tout) Z_FINISH) as [[[ds' consumed] bs] rc] eqn:ED.
      destruct TR as (CONS & BSR & TOUT' & KOK & KNZ).

      pose proof (agree_on_of_munch _ _ _ MUp WMp) as AGp.
      assert (ZR1 : Zlib_iface.zr_d R m1 SS LBz (c2_ds zc x)) by (eapply zrd_own; [exact ZR| exact MUp| exact WMp| intros a Ha; exact Ha]).
      assert (MU1 : munch W0 m2 m1) by (eapply munch_trans; [exact MU| eapply munch_weaken; [apply fp_pub| exact MUp]]).
      assert (WM1 : wmono psegs m2 m1) by (eapply wmono_trans; [exact WM| exact WMp]).
      pose proof (src_inv m1 MU1 WM1) as SRC1. pose proof (zls_inv m1 MU1 WM1) as ZLS1.
      assert (LOREV : Z.of_nat (length (c2_orev zc x)) = tout) by (unfold zlength in TOUT; lia).
      assert (LOLD : Z.of_nat (length oldc) = N) by (unfold zlength in OLDL; lia).
      assert (LDEST : Z.of_nat (length (to_bytes (rev (c2_orev zc x) ++ skipn (length (c2_orev zc x)) oldc))) = N).
      { rewrite to_bytes_len, length_app, length_rev, length_skipn. lia. }
      assert (OUT1 : u8arr psegs m1 C (to_bytes (rev (c2_orev zc x) ++ skipn (length (c2_orev zc x)) oldc))).
      { eapply u8arr_agree; [exact AGp| exact OUT|]. intros a Ha. rewrite LDEST in Ha. cbn [outside]. lia. }
      assert (FRH1 : FRHI m1) by (unfold FRHI in *; eapply rw_cells_agree; [exact AGp| exact FRH| intros a Ha; cbn in Ha; cbn [outside]; lia]).
      assert (PLC1 : rw_cells psegs m1 PL [C8 (wz 0)]) by (eapply rw_cells_agree; [exact AGp| exact PLC| intros a Ha; cbn in Ha; cbn [outside]; lia]).
      clear ZR OUT FRH PLC MU WM MI ST AGp.

      assert (INP1 : bytes_at psegs m1 (NI + k0) (to_bytes rest)).
      { rewrite EREST. unfold zdrop. rewrite to_bytes_skipn. fold k0.
        pose proof SRC1 as SBY. rewrite <- (firstn_skipn (Z.to_nat k0) (to_bytes src)) in SBY. apply bytes_at_app in SBY. destruct SBY as [_ SBY].
        rewrite length_firstn, to_bytes_len, Nat.min_l in SBY by (unfold zlength in *; lia). rewrite Z2Nat.id in SBY by lia. exact SBY. }
      pose proof OUT1 as ROOM1. rewrite to_bytes_app in ROOM1. apply Z_dview.u8arr_app in ROOM1. destruct ROOM1 as [OPRE1 ROOM1].
      rewrite to_bytes_len, length_rev, LOREV in ROOM1.
      assert (LROOM : zlength (skipn (length (c2_orev zc x)) oldc) = N - tout) by (unfold zlength; rewrite length_skipn; lia).
      assert (E160 : bv_unsigned (Z_to_bv 64 SS) = SS) by (apply unsigned_lit; lia).
      assert (SPM : SS mod 16 = 0) by (clear - SP16 RSP; Z.div_mod_to_equations; lia).
      eapply evt_cut.
      { eapply DEFL with (S := SS) (NI := NI + k0) (NO := C + tout) (LBz := LBz) (inp := rest) (oldc := skipn (length (c2_orev zc x)) oldc) (ds := c2_ds zc x)
                         (ao := N - tout) (flush := Z_FINISH) (p1 := p1) (p2 := p2) (lo := lo) (B := B);
          unfold Z_DEFLATE_STACK; cbv delta [MallocRep.wz]; rewrite ?E160;
          [ nm 1 ltac:(exact PUB1) | nm 2 ltac:(exact ZR1) | nm 3 ltac:(exact INP1) | nm 4 ltac:(exact RESTF) | nm 5 ltac:(lia) | nm 6 ltac:(lia)
          | nm 7 ltac:(exact ROOM1) | nm 8 ltac:(exact LROOM) | nm 9 ltac:(lia) | nm 10 ltac:(lia)
          | nm 11 ltac:(lia) | nm 12 ltac:(lia) | nm 13 ltac:(unfold dsc_tin; fold (c2_tin x); lia) | nm 14 ltac:(unfold dsc_tin; fold (c2_tin x); lia)
          | nm 15 ltac:(unfold dsc_tout; fold (c2_tout x); fold tout; lia) | nm 16 ltac:(unfold dsc_tout; fold (c2_tout x); fold tout; lia)
          | nm 17 ltac:(right; reflexivity) | nm 18 ltac:(lia) | nm 19 ltac:(lia) | nm 20 ltac:(lia)
          | nm 21 ltac:(intros b Hb; pose proof (LBZC b Hb); lia) | nm 22 ltac:(intros b Hb; pose proof (LBZS b Hb); lia) | nm 23 ltac:(lia)
          | nm 24 ltac:(exact ZLS1) | nm 25 ltac:(unfold strm_in_frame, ZS_SIZEOF; lia)
          | nm 26 ltac:(exact ST1) | nm 27 ltac:(exact LOC) | nm 28 ltac:(unfold GLOBALS_TOP; lia) | nm 29 ltac:(lia) | nm 30 ltac:(exact SPM)
          | nm 31 ltac:(lia) | nm 32 ltac:(exact B63) | nm 33 ltac:(exact MI1) | nm 34 ltac:(reflexivity) | nm 35 ltac:(reflexivity) ]. }
      cbv beta. intros ms' PO. unfold deflate_postC in PO. rewrite ED in PO.
      destruct PO as (u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m' & p1' & p2' & -> & MU' & WM' & MI' & ST' & -> &
                      CRG & BSR' & BSF & TIN' & TOUT2 & PUB' & ZR' & OUT').
      rewrite ?E160 in MU', ST'.
      pose proof (zdc_rc rest (c2_ds zc x) (N - tout) Z_FINISH) as RCR. cbn [dc_deflate zc ZApiInstC.zinstC] in ED. rewrite ED in RCR. cbn [snd] in RCR. unfold cint in RCR.

      set (x' := c2_next x N ds' consumed bs) in *.
      pose proof (agree_on_of_munch _ _ _ MU' WM') as AG'.
      assert (BS0 : 0 <= zlength bs) by (unfold zlength; lia).
      assert (OUTw : forall a, SS + ZS_SIZEOF <= a \/ (C <= a < C + tout) \/ (NI <= a < NI + n) ->
                outside ([(lo, SS); (SS, SS + ZS_SIZEOF); (C + tout, C + tout + zlength bs)] ++ map (fun b => (blk_addr b, blk_addr b + blk_size b)) LBz) a).
      { intros a Ha. apply outside_app. split.
        - cbn [outside]. unfold ZS_SIZEOF in *. clear - Ha LOSP LOC RSP CC C0 BSR BS0 TOUT0 NEQ BS1 BS2 SC NF1 NF2 SUM AOUT0 LEFT0. lia.
        - apply outside_blocks. intros b Hb. pose proof (LBZC b Hb) as X1. pose proof (LBZS b Hb) as X2. destruct (LBZR b Hb) as (_ & _ & _ & BC & _).
          clear - Ha X1 X2 BC LOC LOSP RSP TOUT0 BS0 BSR NF2 SUM AOUT0 LEFT0. unfold ZS_SIZEOF in Ha. lia. }
      assert (CINV' : CINV m' x' (k + 1)).
      { unfold CINV. subst x'. unfold c2_next. cbn [c2_rest c2_ain c2_aout c2_orev c2_ds c2_left c2_slen].
        unfold c2_next in TOUT'. fold tout. rewrite TOUT'.
        rewrite (zlength_zdrop' rest consumed) by lia.
        split. { exists p1', p2'. replace (NI + (zlength src - (zlength rest - consumed))) with (NI + k0 + consumed) by lia.
                 replace (C + (tout + zlength bs)) with (C + tout + zlength bs) by lia.
                 unfold c2_tin. cbn [c2_ds]. unfold dsc_tin, dsc_tout in PUB'. unfold c2_tout in TOUT'. cbn [c2_ds] in TOUT'.
                 rewrite TOUT' in PUB'. replace (C + (tout + zlength bs)) with (C + tout + zlength bs) in PUB' by lia. exact PUB'. }
        split; [exact ZR'|].
        split. { rewrite rev_append_rev', rev_app_distr, rev_involutive, <- app_assoc, to_bytes_app. apply (proj2 (Z_dview.u8arr_app _ _ _ _)). split.
                 - eapply u8arr_agree; [exact AG'| exact OPRE1|]. intros a Ha. rewrite to_bytes_len, length_rev in Ha. apply OUTw. lia.
                 - rewrite to_bytes_len, length_rev, LOREV, length_app, length_rev.
                   rewrite (zstore0_app bs) in OUT' by (rewrite length_skipn; unfold zlength in *; lia). rewrite skipn_skipn in OUT'.
                   replace (length (c2_orev zc x) + length bs)%nat with (length bs + length (c2_orev zc x))%nat by lia. exact OUT'. }
        split; [unfold FRHI in *; eapply rw_cells_agree; [exact AG'| exact FRH1| intros a Ha; cbn in Ha; apply OUTw; unfold ZS_SIZEOF; lia]|].
        split; [eapply rw_cells_agree; [exact AG'| exact PLC1| intros a Ha; cbn in Ha; apply OUTw; unfold ZS_SIZEOF; lia]|].
        split; [eapply munch_trans; [exact MU1| eapply munch_weaken; [| exact MU']; apply fp_call; lia]|].
        split; [eapply wmono_trans; [exact WM1| exact WM']|]. split; [exact MI'|]. split; [exact ST'|].
        split; [lia|]. split; [unfold c2_tin; cbn [c2_ds]; unfold dsc_tin in TIN'; fold (c2_tin x) in TIN'; unfold ZC_MAX; lia|].
        rewrite rev_append_rev'. apply Forall_app. split; [apply Forall_rev; exact BSF| exact ORF]. }
      eapply (K m' x' rc); [exact CINV'| reflexivity| reflexivity| exact KOK| exact KNZ| exact RCR].
    Qed.

    Lemma c2_loop : forall n0 (Q : machine_state -> Prop) m x k r (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
      C2I N src lv x -> CINV m x k -> c2_after zc n0 x = Some r -> k + Z.of_nat n0 <= KMAX ->
      (forall m' k' (x1' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
         CINV m' (fst r) k' -> - 2^31 <= snd r < 2^31 -> snd r <> Z_OK ->
         evt psegs Q (HDS (wz 0x16200) x1' t0' t1' t2' (wint (snd r)) a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' 0 0 m')) ->
      evt psegs Q (HDS (wz (head_pc x)) x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (c2_slen zc x) (c2_left zc x) m).
    Proof.
      induction n0 as [|n0 IH]; intros until t6; intros CX CI AF KB K.
      { rewrite c2_after_O in AF. discriminate AF. }
      pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
      eapply c2_head_to_call; [exact CX| exact CI|].
      intros m1 t0' t1' t2' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' ret p1 p2 RET MUp WMp MI1 ST1 PUB1.
      eapply c2_call; [exact CX| exact CI| exact AF| unfold KMAX in *; lia| exact RET| exact MUp| exact WMp| exact MI1| exact ST1| exact PUB1|].
      intros m' x' rc u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 CI' ESL' EL' KOK KNZ RCR.
      pose proof CI' as (_ & _ & _ & _ & _ & _ & _ & MI' & ST' & _).
      pose proof N_factsB as [NB SB]. pose proof N_facts as (NF1 & NF2 & NF3).

      assert (A0Z : bv_unsigned (wint rc) = 0 <-> rc = 0).
      { unfold wint, MallocRep.wz. rewrite unsigned_lit by (pose proof (Z.mod_pos_bound rc (2^64)); lia). split; intros Hz; [| subst rc; reflexivity].
        destruct (Z.eq_dec rc 0) as [E|E]; [exact E|]. exfalso.
        destruct (Z.lt_ge_cases rc 0); [| rewrite Z.mod_small in Hz by lia; lia].
        replace (rc mod 2^64) with (rc + 2^64) in Hz by (apply (Z.mod_unique_pos _ _ (-1)); lia). lia. }
      pose proof (munch_refl ([] : list (Z * Z)) m') as MU0. pose proof (wmono_refl psegs m') as WM0.
      cbv beta delta [MallocRep.wz]. unfold ZC_WRAP_STACK, Z_INFLATE_STACK, RMALLOC_STACK, GLOBALS_TOP in LOSP, LOG.
      destruct (Z.eq_dec rc Z_OK) as [RC0|RCNZ].
      -
        destruct (KOK RC0) as [CX' AF']. subst rc. change (wint Z_OK) with (Z_to_bv 64 0).
        destruct CI' as ((q1 & q2 & PUB') & REST'). unfold zs_pub in PUB'. cbv beta delta [MallocRep.wz] in PUB'.
        pose proof (C2I_shape N src lv x' NB CX') as SH'. cbv zeta in SH'. destruct SH' as (_ & TOUT0' & SUM' & AOUT0' & LEFT0' & _).
        assert (AGN : forall (y1 z0 z1 z2 w0 w1 w2 w3 w4 w5 w6 w7 z3 z4 z5 z6 : word),
                  evt psegs Q (MS (mkR y1 (Z_to_bv 64 SS) gp tp z0 z1 z2 (Z_to_bv 64 PL) (Z_to_bv 64 C) w0 w1 w2 w3 w4 w5 w6 w7
                                        (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 4294967295) S5 S6 S7 S8 S9 S10 S11 z3 z4 z5 z6)
                                   F (Z_to_bv 64 0x161f4) fc None m' (seg_rom psegs))).
        { intros. zstep. zstep. if_cases KAO; rewrite sx32_small in KAO by lia; zify_cond KAO; rewrite ?unsigned_lit in KAO by lia.
          *
            eapply evt_eq; [| eapply (IH Q m' x' (k + 1) r); [exact CX'| split; [exists q1, q2; exact PUB'| exact REST']| exact AF'| lia| exact K]].
            unfold head_pc. replace (c2_aout zc x' =? 0) with false by (symmetry; apply Z.eqb_neq; lia). rewrite ESL', EL'. reflexivity.
          *
            zstep.
            eapply evt_eq; [| eapply (IH Q m' x' (k + 1) r); [exact CX'| split; [exists q1, q2; exact PUB'| exact REST']| exact AF'| lia| exact K]].
            unfold head_pc. replace (c2_aout zc x' =? 0) with true by (symmetry; apply Z.eqb_eq; lia). rewrite ESL', EL'. reflexivity. }
        destruct RET as [-> | ->].
        + replace (ret_pc (Z_to_bv 64 0x161a8)) with (Z_to_bv 64 0x161a8) by (symmetry; rpc). zstep. apply AGN.
        + replace (ret_pc (Z_to_bv 64 0x161f0)) with (Z_to_bv 64 0x161f0) by (symmetry; rpc). zstep. apply AGN.
      -
        pose proof (KNZ RCNZ) as ER. subst r. cbn [fst snd] in K.
        assert (NZ : bv_unsigned (wint rc) <> 0) by (intros Hz; apply RCNZ; apply A0Z; exact Hz).
        destruct RET as [-> | ->].
        + replace (ret_pc (Z_to_bv 64 0x161a8)) with (Z_to_bv 64 0x161a8) by (symmetry; rpc).
          zstep. if_cases KRC; zify_cond KRC; [exfalso; apply NZ; exact KRC|]. zstep.
          eapply (K m' (k + 1)); [exact CI'| exact RCR| exact RCNZ].
        + replace (ret_pc (Z_to_bv 64 0x161f0)) with (Z_to_bv 64 0x161f0) by (symmetry; rpc).
          zstep. if_cases KRC; zify_cond KRC; [| exfalso; apply NZ; exact KRC].
          eapply (K m' (k + 1)); [exact CI'| exact RCR| exact RCNZ].
    Qed.
  End Loop.

  Lemma frame_split : forall m (jp jm js jr : list byte),
    rw_cells psegs m SS [CB 48 jp; CB 8 jm; CB 8 js; C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); CB 24 jr;
                        C8 S4; C8 S3; C8 S2; C8 S1; C8 S0; C8 ra] ->
    FRHI m
    /\ exists ni ai ti no ao to p1 p2 (jmsg jstate : word),
         rw_cells psegs m SS (zs_pub ni ai ti no ao to p1 p2 ++ [C8 jmsg; C8 jstate; C8 (wz 0); C8 (wz 0); C8 (wz 0); CB 24 jr]).
  Proof.
    intros m jp jm js jr FR.
    apply (proj1 (rw_cells_app psegs _ _ [_;_;_;_;_;_;_] _)) in FR. destruct FR as [FRS FRH].
    cbn [cells_size csize Nat.add] in FRS, FRH. replace (SS + Z.of_nat 112) with (usp + -48) in FRH by lia.
    split; [exact FRH|].
    pose proof FRS as [[WFS _] _]. cbn [cells_wf cell_wf] in WFS. destruct WFS as (L1 & L2 & L3 & _ & _ & _ & L4 & _).
    destruct (zs_pub_of_bytes _ L1) as (ni & ai & ti & no & ao & to & p1 & p2 & EB & WFP & _).
    destruct (le8_of_bytes _ L2) as (zmsg & _ & Emsg). destruct (le8_of_bytes _ L3) as (zst & _ & Est).
    exists ni, ai, ti, no, ao, to, p1, p2, (Z_to_bv 64 zmsg), (Z_to_bv 64 zst).
    eapply rw_cells_recast; [exact FRS| |].
    - apply cells_wf_app. split; [exact WFP|]. cbn [cells_wf cell_wf]. repeat split. exact L4.
    - rewrite cells_bytes_app, EB. cbn [cells_bytes cbytes]. rewrite Emsg, Est. reflexivity.
  Qed.

  Lemma frame_join : forall m (js : list byte), rw_cells psegs m SS [CB 112 js] -> FRHI m ->
    rw_cells psegs m SS [CB 112 js; C8 S4; C8 S3; C8 S2; C8 S1; C8 S0; C8 ra].
  Proof.
    intros m js FS FH. change [CB 112 js; C8 S4; C8 S3; C8 S2; C8 S1; C8 S0; C8 ra] with ([CB 112 js] ++ [C8 S4; C8 S3; C8 S2; C8 S1; C8 S0; C8 ra]).
    apply (proj2 (rw_cells_app psegs _ _ _ _)). split; [exact FS|]. cbn [cells_size csize Nat.add]. eapply rw_cells_addr_eq; [exact FH| lia].
  Qed.

  Notation POSTC := (rcompress2_post ra sp gp tp S0 S1 S2 S3 S4 S5 S6 S7 S8 S9 S10 S11).

  Lemma c2_epilogue : forall (Q : machine_state -> Prop) m (js : list byte) (x1 t0 t1 t2 x8 x9 a0v a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
    rw_cells psegs m SS [CB 112 js] -> FRHI m -> stk psegs m lo SS -> mem_inv psegs m ->
    (forall (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word), stk psegs m lo usp ->
       Q (MS (mkR ra sp gp tp t0' t1' t2' S0 S1 a0v a1' a2' a3' a4' a5' a6' a7' S2 S3 S4 S5 S6 S7 S8 S9 S10 S11 t3' t4' t5' t6') F (ret_pc ra) fc None m (seg_rom psegs))) ->
    evt psegs Q (MS (mkR x1 (Z_to_bv 64 SS) gp tp t0 t1 t2 x8 x9 a0v a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 S5 S6 S7 S8 S9 S10 S11 t3 t4 t5 t6)
                    F (Z_to_bv 64 0x16228) fc None m (seg_rom psegs)).
  Proof.
    intros until fc. intros FS FH ST MI KK.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    unfold ZC_WRAP_STACK, Z_INFLATE_STACK, RMALLOC_STACK, GLOBALS_TOP in LOSP, LOG.
    pose proof (frame_join m js FS FH) as FR. unfold FRHI in FH.
    pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl psegs m) as WM.
    do 6 zstep. release_frame FR ST (bv_unsigned sp). zstep. zstep.
    apply evt_done. apply KK. exact ST.
  Qed.

  Theorem c2_main : forall (t0 t1 t2 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m0 : mem) (s : PState) (errv : word),
    lx_env m0 s [] LB sp tp B lo errv canary ->
    u8arr psegs m0 C (to_bytes oldc) -> rw_cells psegs m0 PL [C8 (wz N)] -> bytes_at psegs m0 NI (to_bytes src) -> frm0 fc ->
    implM psegs (compress2M lops zc N src lv) s (POSTC s LB C N PL oldc lo B canary m0)
      (MS (mkR ra sp gp tp t0 t1 t2 S0 S1 (wz C) (wz PL) (wz NI) (wz n) (wz lv) a5 a6 a7 S2 S3 S4 S5 S6 S7 S8 S9 S10 S11 t3 t4 t5 t6)
          F (wz ZC_COMPRESS2Z) fc None m0 (seg_rom psegs)).
  Proof.
    intros until errv. intros ENV0 CARR0 PLC0 SRC0 FRM.
    pose proof ENV0 as (HP0 & _ & ZLS0 & _ & _ & _ & _ & _ & ST0 & _ & _ & _ & _ & MI0).
    pose proof N_facts as (NF1 & NF2 & NF3). pose proof N_factsB as [NB SB].
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    pose proof CR as (C0 & C16 & _ & CC & CI).
    destruct SRCB as (bS & HbS & BS1 & BS2). destruct (LBR bS HbS) as (S0' & _ & _ & SC & SI). cbn [blk_addr blk_size] in S0', SC, SI.
    unfold ZC_WRAP_STACK, Z_INFLATE_STACK, RMALLOC_STACK, GLOBALS_TOP in LOSP, LOG.
    destruct ZOK as (DINIT & DEFL & DEND & _).
    unfold compress2M. cbn [bind ret lops Target.ops unreachable].
    unfold ZC_COMPRESS2Z. cbv beta delta [MallocRep.wz] in PLC0 |- *.
    assert (LC0 : Z.of_nat (length (to_bytes oldc)) = N) by (rewrite to_bytes_len; unfold zlength in OLDL; lia).
    assert (LS0 : Z.of_nat (length (to_bytes src)) = n) by (rewrite to_bytes_len; unfold zlength in SRCL; lia).
    apply box in CARR0. apply box in SRC0.
    pose proof (munch_refl [(SS, usp); (PL, PL + 8)] m0) as MU. pose proof (wmono_refl psegs m0) as WM.
    unfold implM. iprefix.
    zstep. carve_frame 160%nat ST0.
    apply (rw_cells_split_CB psegs _ _ [] 160 junk [] [48; 8; 8; 8; 8; 8; 24; 8; 8; 8; 8; 8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
    do 6 zstep.
    (* 1.4: mv s1,a0; li a0,-2; beqz a1 (destLen = PL is not NULL) *)
    zstep. zstep. zstep. if_cases KN1; zify_cond KN1; rewrite ?unsigned_lit in KN1 by lia; [exfalso; lia|].
    (* mv s2,a3; mv s0,a1; snez a1,a3; seqz a3,a2; and a1,a3,a1; bnez a1 (sourceLen > 0 and source = NI is not NULL) *)
    do 5 zstep.
    replace (NI <? 1) with false by (symmetry; apply Z.ltb_ge; lia).
    replace (0 <? n) with true by (symmetry; apply Z.ltb_lt; lia).
    cbn [Z.b2z Z.land].
    zstep. if_cases KN2; zify_cond KN2; rewrite ?unsigned_lit in KN2 by lia; [exfalso; lia|].
    (* ld s3,0(s0) (left := *destLen); bnez s1 (dest = C is not NULL) *)
    zstep. zstep. if_cases KN3; zify_cond KN3; rewrite ?unsigned_lit in KN3 by lia; [|exfalso; lia].
    (* sd zero,0(s0); sd zero,64/72/80(sp) *)
    zs. do 3 zs.
    (* auipc a1; mv a0,sp; add a5,a1,754; li a3,112; mv a1,a4; mv s4,a2; mv a2,a5; jal deflateInit_ *)
    do 8 zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
    destruct (frame_split m1 _ _ _ _ FR) as (FRH1 & (ni & ai & ti & no & ao & to & p1 & p2 & jmsg & jstate & FRS1)). clear FR.
    assert (SPM : SS mod 16 = 0) by (clear - SP16 RSP; Z.div_mod_to_equations; lia).
    assert (E160 : bv_unsigned (Z_to_bv 64 SS) = SS) by (apply unsigned_lit; lia).

    assert (ENV1 : lx_env m1 s [] LB (Z_to_bv 64 SS) tp B lo errv canary).
    { eapply (lx_env_munch [(SS, usp); (PL, PL + 8)] m0 m1); [exact HFRAME| exact ENV0| exact MU| exact WM| assumption| rewrite E160; assumption| rewrite E160; lia| |].
      - constructor; [left; cbn [fst]; lia|]. constructor; [left; cbn [fst]; lia| constructor].
      - intros a Ha. cbn [outside]. lia. }
    assert (PRES1 : lx_pres LB usp XX m0 m1).
    { eapply lx_pres_of_munch; [exact MU| exact WM|]. intros a [HX [Ha|[(b & Hb & Hr)|[Ha _]]]]; cbn [outside].
      - split; [lia|]. split; [| exact I]. intros Hz. apply HX. cbn [rin_ivs fst snd]. right; left. lia.
      - destruct (LBR b Hb) as (_ & _ & _ & BC & _). lia.
      - lia. }
    pose proof (agree_on_of_munch _ _ _ MU WM) as AG1.
    assert (CARR1 : u8arr psegs m1 C (to_bytes oldc)) by (eapply u8arr_agree; [exact AG1| exact (unbox _ CARR0)| intros a Ha; rewrite LC0 in Ha; cbn [outside]; lia]).
    assert (SRC1 : bytes_at psegs m1 NI (to_bytes src)) by (eapply bytes_at_agree; [exact AG1| exact (unbox _ SRC0)| intros a Ha; rewrite LS0 in Ha; cbn [outside]; lia]).
    rename PLC0 into PLC1.
    clear AG1 MU WM CARR0 SRC0.
    apply evt_done.
    lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM psegs tm s (POSTC s LB C N PL oldc lo B canary m0) msx) end.
    eapply implM_bind.
    { eapply (DINIT lv LV) with (S := SS) (lo := lo) (B := B) (errv := errv) (canary := canary);
        [ exact ENV1 | exact FRS1
        | unfold strm_in_frame, ZS_SIZEOF; rewrite E160; repeat split; try lia; clear - SP16 RSP; Z.div_mod_to_equations; lia
        | rewrite E160; unfold Z_DEFLATEINIT_STACK, RMALLOC_STACK; lia | rewrite E160; exact SPM | exact FRM
        | reflexivity | unfold wint, MallocRep.wz; f_equal; rewrite Z.mod_small by lia; reflexivity | reflexivity | reflexivity ]. }
    cbv beta. intros r s2 ms2 PO. unfold deflateInit_postC in PO.
    destruct PO as (u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F2 & fc2 & m2 & -> & PO).
    replace (ret_pc (Z_to_bv 64 0x16170)) with (Z_to_bv 64 0x16170) by (symmetry; rpc).
    destruct r as [blk|].
    2:{
      destruct PO as (((errv2 & ENV2) & FRM2 & LXP2 & ESO2 & EFA2) & -> & (js & STR2)).
      rewrite E160 in LXP2. pose proof (agree_of_lx_pres _ _ _ _ _ LXP2) as AG2.
      pose proof (fr_lx _ _ _ _ LXP2 FRH1 ltac:(lia) ltac:(cbn; unfold ZS_SIZEOF; lia)) as FRH2.
      pose proof (fr_lx _ _ _ _ LXP2 PLC1 ltac:(lia) ltac:(cbn; unfold ZS_SIZEOF; lia)) as PLC2.
      assert (CARR2 : u8arr psegs m2 C (to_bytes oldc)).
      { eapply u8arr_agree; [exact AG2| exact CARR1|]. intros a Ha.
        eapply block_client; [exact INC| cbn [blk_addr blk_size fst snd]; lia| cbn [rin_ivs fst snd]; unfold ZS_SIZEOF; lia]. }
      pose proof ENV2 as (_ & _ & _ & _ & _ & _ & _ & _ & ST2 & _ & _ & _ & _ & MI2). rewrite E160 in ST2.
      change (wint Z_MEM_ERROR) with (Z_to_bv 64 18446744073709551612).
      apply implM_ret.
      pose proof (munch_refl ([] : list (Z * Z)) m2) as MU. pose proof (wmono_refl psegs m2) as WM.
      zstep.
      eapply c2_epilogue; [exact STR2| exact FRH2| exact ST2| exact MI2|]. intros. unfold rcompress2_post.
      do 15 eexists. exists F2, fc2, m2, Z_MEM_ERROR. split; [reflexivity|].
      split.
      { unfold lx_post_env. split; [exists errv2; eapply lx_env_sp; [exact ENV2| assumption| exact SPB]|]. split; [exact FRM2|].
        split; [| split; [exact ESO2| exact EFA2]].
        eapply lx_pres_trans; [exact PRES1|]. eapply lx_pres_sub; [exact LXP2| apply client_inner]. }
      split; [reflexivity|]. split; [reflexivity|]. split; [change Z_MEM_ERROR with (-4); lia|].
      split; [cbn [fst]; rewrite zstore_nil; exact CARR2|]. cbn [fst snd].
      split; [reflexivity|]. split; [change (zlength (@nil Z)) with 0; lia|]. split; [constructor| exact PLC2]. }

    destruct PO as (As & Aw & Ap & Ah & Ab & ((errv2 & ENV2) & FRM2 & LXP2 & ESO2 & EFA2) & -> & PUB2 & TI0 & TO0 & ZR2).
    rewrite E160 in LXP2.
    set (LBz := blk5_blocks blk As Aw Ap Ah Ab) in *.
    pose proof ENV2 as (HP2 & _ & ZLS2 & _ & _ & _ & _ & _ & ST2 & _ & _ & _ & _ & MI2). rewrite E160 in ST2. cbn [app] in HP2.
    pose proof (fr_lx _ _ _ _ LXP2 FRH1 ltac:(lia) ltac:(cbn; unfold ZS_SIZEOF; lia)) as FRH2.
    pose proof (fr_lx _ _ _ _ LXP2 PLC1 ltac:(lia) ltac:(cbn; unfold ZS_SIZEOF; lia)) as PLC2.
    pose proof (agree_of_lx_pres _ _ _ _ _ LXP2) as AG2.
    assert (CARR2 : u8arr psegs m2 C (to_bytes oldc)).
    { eapply u8arr_agree; [exact AG2| exact CARR1|]. intros a Ha.
      eapply block_client; [exact INC| cbn [blk_addr blk_size fst snd]; lia| cbn [rin_ivs fst snd]; unfold ZS_SIZEOF; lia]. }
    assert (SRC2 : bytes_at psegs m2 NI (to_bytes src)).
    { eapply bytes_at_agree; [exact AG2| exact SRC1|]. intros a Ha.
      eapply block_client; [exact HbS| cbn [blk_addr blk_size fst snd]; lia| cbn [rin_ivs fst snd]; unfold ZS_SIZEOF; lia]. }
    assert (PRES2 : lx_pres LB usp XX m0 m2) by (eapply lx_pres_trans; [exact PRES1| eapply lx_pres_sub; [exact LXP2| apply client_inner]]).
    assert (LBZR : forall b, In b LBz -> rblock_range (blk_addr b) (blk_size b)).
    { intros b Hb. apply (HBR _ _ _ _ HP2). apply in_or_app. left. exact Hb. }
    assert (LBZC : forall b, In b LBz -> blk_addr b + blk_size b <= C \/ C + N <= blk_addr b).
    { intros b Hb. exact (heap_sep _ _ _ _ b (cp, C, N) HND HBD HP2 Hb INC). }
    assert (LBZS : forall b, In b LBz -> blk_addr b + blk_size b <= NI \/ NI + n <= blk_addr b).
    { intros b Hb. pose proof (heap_sep _ _ _ _ b bS HND HBD HP2 Hb HbS) as X. lia. }
    assert (LBZL : forall b b', In b LBz -> In b' LB -> blk_addr b + blk_size b <= blk_addr b' \/ blk_addr b' + blk_size b' <= blk_addr b).
    { intros b b' Hb Hb'. exact (heap_sep _ _ _ _ b b' HND HBD HP2 Hb Hb'). }
    clear FRH1 PLC1 CARR1 SRC1.

    change (wint Z_OK) with (Z_to_bv 64 0).
    destruct (c2_pure zc N src lv) as [[[out tout] rc2]|] eqn:CP.
    2:{
      apply implM_unr. }

    unfold zs_pub in PUB2. cbv beta delta [MallocRep.wz] in PUB2.
    pose proof (munch_refl [(SS, SS + 48)] m2) as MUz. pose proof (wmono_refl psegs m2) as WMz.
    apply box in CARR2. apply box in SRC2. apply box in ZR2.
    unfold implM. iprefix.
    zstep. if_false. zs. zs. zs. zs. zstep. zstep. zstep. if_true.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m3 end.

    pose proof CP as CP0. unfold c2_pure in CP. rewrite c2_loop_after in CP.
    destruct (c2_after zc (Z.to_nat (C2_FUEL N (zlength src))) (c2_x0 zc N src lv)) as [[xf err]|] eqn:AF; [| discriminate CP].
    destruct (Z.eqb_spec (dc_total_out zc (c2_ds zc xf)) (zlength (rev_append (c2_orev zc xf) []))) as [GT1|GT1]; [| cbn [andb] in CP; discriminate CP].
    destruct (Z.leb_spec (dc_total_out zc (c2_ds zc xf)) N) as [GT2|GT2]; [| cbn [andb] in CP; discriminate CP].
    cbn [andb] in CP. injection CP as EOUT ETOUT ERC2.

    pose proof (Zc_zrd.dzC_init_scalars lv LV) as DZ0.
    assert (TIN0 : c2_tin (c2_x0 zc N src lv) = 0) by (unfold c2_tin, c2_x0; cbn [c2_ds dc_init the_zapiC ZApiInstC.zinstC]; rewrite DZ0; reflexivity).
    assert (TOUT00 : c2_tout (c2_x0 zc N src lv) = 0) by (unfold c2_tout, c2_x0; cbn [c2_ds dc_init the_zapiC ZApiInstC.zinstC]; rewrite DZ0; reflexivity).
    assert (CI3 : CINV m2 LBz m3 (c2_x0 zc N src lv) 0).
    { unfold CINV. rewrite TIN0, TOUT00. unfold c2_x0. cbn [c2_rest c2_ain c2_aout c2_orev c2_ds c2_left c2_slen].
      rewrite Z.sub_diag, !Z.add_0_r. cbn [rev length skipn app].
      split; [exists p1, p2; unfold zs_pub; cbv beta delta [MallocRep.wz]; exact PUB2|].
      split; [eapply (zrd_own LBz LBZR); [exact (unbox _ ZR2)| exact MUz| exact WMz| intros a Ha; exact Ha]|].
      split; [eapply u8arr_agree; [exact (agree_on_of_munch _ _ _ MUz WMz)| exact (unbox _ CARR2)| intros a Ha; rewrite LC0 in Ha; cbn [outside]; lia]|].
      split; [exact FRH2|]. split; [exact PLC2|].
      split; [eapply munch_weaken; [apply (fp_pub LBz)| exact MUz]|]. split; [exact WMz|]. split; [assumption|]. split; [assumption|].
      split; [lia|]. split; [lia| constructor]. }
    eapply evt_eq; [| eapply (c2_loop m2 LBz F2 fc2 LBZR LBZC LBZS ZLS2 (unbox _ SRC2) (Z.to_nat (C2_FUEL N (zlength src))) _ m3 (c2_x0 zc N src lv) 0 (xf, err));
      [ apply C2I_init; [exact NB| exact SB| exact SRCF| exact LV] | exact CI3 | exact AF
      | unfold KMAX, C2_FUEL; rewrite Z2Nat.id by lia; lia | ]].
    { unfold head_pc, c2_x0. cbn [c2_aout c2_slen c2_left Z.eqb]. rewrite SRCL. reflexivity. }

    cbn [fst snd]. intros m4 k4 y1 z0 z1 z2 w1 w2 w3 w4 w5 w6 w7 z3 z4 z5 z6 CI4 RCR4 NZ4.
    destruct CI4 as ((q1 & q2 & PUB4) & ZR4 & OUT4 & FRH4 & PLC4 & MU4 & WM4 & MI4 & ST4 & _ & _ & ORF4).
    clear CI3 MUz WMz PUB2 FRH2 PLC2.

    assert (ETO : c2_tout xf = tout) by (unfold c2_tout; cbn [dc_total_out the_zapiC ZApiInstC.zinstC] in ETOUT; exact ETOUT).
    rewrite rev_append_rev', app_nil_r in EOUT, GT1.
    assert (LOUT : zlength out = tout) by (rewrite <- EOUT, <- ETO; unfold c2_tout; cbn [dc_total_out the_zapiC ZApiInstC.zinstC] in GT1; symmetry; exact GT1).
    assert (TOUTN : tout <= N) by (rewrite <- ETO; unfold c2_tout; cbn [dc_total_out the_zapiC ZApiInstC.zinstC] in GT2; exact GT2).
    assert (OUT0 : 0 <= zlength out) by (unfold zlength; lia).
    pose proof (bv_unsigned_in_range 64 sp) as RSP'.

    unfold zs_pub in PUB4. cbv beta delta [MallocRep.wz] in PUB4. rewrite ETO in PUB4.
    apply box in OUT4. apply box in ZR4. apply box in MU4. apply box in WM4.
    pose proof (munch_refl [(PL, PL + 8)] m4) as MU5. pose proof (wmono_refl psegs m4) as WM5.
    (* 1.4: ld a1,24(sp) (next_out); sub a1,a1,s1 (- dest); sd a1,0(s0); mv s0,a0; mv a0,sp; jal deflateEnd *)
    cbv beta delta [MallocRep.wz]. zstep. zstep. zs. zstep. zstep. zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m5 end.
    pose proof (agree_on_of_munch _ _ _ MU5 WM5) as AG5.
    assert (FRH5 : FRHI m5) by (unfold FRHI in *; eapply rw_cells_agree; [exact AG5| exact FRH4| intros a Ha; cbn in Ha; cbn [outside]; lia]).
    assert (ZR5 : Zlib_iface.zr_d R m5 SS LBz (c2_ds zc xf)).
    { eapply (zr_d_frame R); [exact (unbox _ ZR4)|]. intros a Ha Hin. apply (AG5 a Ha). cbn [outside]. split; [| exact I].
      destruct Hin as [Hin|(b & Hb & Hr)]; [unfold ZS_PUB, ZS_SIZEOF in *; lia|]. destruct (LBZR b Hb) as (_ & _ & _ & BC & _). lia. }
    assert (OUT5 : u8arr psegs m5 C (to_bytes (rev (c2_orev zc xf) ++ skipn (length (c2_orev zc xf)) oldc))).
    { eapply u8arr_agree; [exact AG5| exact (unbox _ OUT4)|]. intros a Ha. rewrite to_bytes_len, length_app, length_rev, length_skipn in Ha.
      cbn [outside]. unfold zlength in LOUT, OLDL. rewrite <- EOUT in LOUT. rewrite length_rev in LOUT. lia. }
    assert (ENV5 : lx_env m5 s2 LBz LB (Z_to_bv 64 SS) tp B lo errv2 canary).
    { eapply (lx_env_munch (W0 LBz ++ [(PL, PL + 8)]) m2 m5); [exact HFRAME| exact ENV2| | | assumption| rewrite E160; assumption| rewrite E160; lia| |].
      - eapply munch_trans; [eapply munch_weaken; [| exact (unbox _ MU4)]| eapply munch_weaken; [| exact MU5]];
          intros a Ha; apply outside_app in Ha; [exact (proj1 Ha)| exact (proj2 Ha)].
      - eapply wmono_trans; [exact (unbox _ WM4)| exact WM5].
      - unfold W0. apply Forall_app. split; [apply Forall_app; split|].
        + constructor; [left; cbn [fst]; lia|]. constructor; [| constructor]. right; right. exists (cp, C, N). split; [apply in_or_app; right; exact INC| cbn; lia].
        + apply Forall_forall. intros iv Hiv. apply in_map_iff in Hiv. destruct Hiv as (b & <- & Hb). right; right. exists b.
          split; [apply in_or_app; left; exact Hb| cbn [fst snd]; lia].
        + constructor; [left; cbn [fst]; lia| constructor].
      - intros a Ha. apply outside_app. split; [| cbn [outside]; lia].
        destruct Ha as [Ha|Ha]; [apply W0_high; [exact LBZR| lia]| apply W0_image; [exact LBZR| exact Ha]]. }
    apply evt_done.
    lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM psegs tm s2 (POSTC s LB C N PL oldc lo B canary m0) msx) end.
    eapply implM_bind.
    { eapply (DEND) with (S := SS) (b := blk) (ds := c2_ds zc xf) (lo := lo) (B := B) (errv := errv2) (canary := canary);
        [ exact ENV5 | exact PUB4 | exact ZR5
        | unfold strm_in_frame, ZS_SIZEOF; rewrite E160; repeat split; try lia; clear - SP16 RSP; Z.div_mod_to_equations; lia
        | rewrite E160; unfold Z_DEFLATEEND_STACK, RFREE_STACK; lia | rewrite E160; exact SPM | exact FRM2 | reflexivity ]. }
    cbv beta. intros [] s3 ms3 PO. unfold deflateEnd_postC in PO.
    destruct PO as (v0 & v1 & v2 & c0 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & v3 & v4 & v5 & v6 & F3 & fc3 & m6 & -> & ((errv3 & ENV6) & FRM3 & LXP6 & ESO6 & EFA6) & _ & (js & STR6)).
    replace (ret_pc (Z_to_bv 64 0x16218)) with (Z_to_bv 64 0x16218) by (symmetry; rpc).
    rewrite E160 in LXP6. pose proof (agree_of_lx_pres _ _ _ _ _ LXP6) as AG6.
    pose proof ENV6 as (_ & _ & _ & _ & _ & _ & _ & _ & ST6 & _ & _ & _ & _ & MI6). rewrite E160 in ST6.
    pose proof (fr_lx _ _ _ _ LXP6 FRH5 ltac:(lia) ltac:(cbn; unfold ZS_SIZEOF; lia)) as FRH6.
    lazymatch goal with PLC5 : rw_cells psegs m5 PL _ |- _ => pose proof (fr_lx _ _ _ _ LXP6 PLC5 ltac:(lia) ltac:(cbn; unfold ZS_SIZEOF; lia)) as PLC6 end.
    assert (OUT6 : u8arr psegs m6 C (to_bytes (zstore oldc 0 out))).
    { assert (LD5 : Z.of_nat (length (to_bytes (rev (c2_orev zc xf) ++ skipn (length (c2_orev zc xf)) oldc))) = N).
      { rewrite to_bytes_len, length_app, length_rev, length_skipn. unfold zlength in LOUT, OLDL. rewrite <- EOUT, length_rev in LOUT. lia. }
      assert (OUT6' : u8arr psegs m6 C (to_bytes (rev (c2_orev zc xf) ++ skipn (length (c2_orev zc xf)) oldc))).
      { eapply u8arr_agree; [exact AG6| exact OUT5|]. intros a Ha. rewrite LD5 in Ha.
        eapply block_client; [exact INC| cbn [blk_addr blk_size fst snd]; lia| cbn [rin_ivs fst snd]; unfold ZS_SIZEOF; lia]. }
      rewrite zstore0_app by (unfold zlength in LOUT, OLDL; lia). rewrite <- EOUT. rewrite length_rev. exact OUT6'. }
    apply implM_ret.
    pose proof (munch_refl ([] : list (Z * Z)) m6) as MU6. pose proof (wmono_refl psegs m6) as WM6.
    zstep. zstep. zstep. zstep.
    eapply c2_epilogue; [exact STR6| exact FRH6| exact ST6| exact MI6|]. intros. unfold rcompress2_post.
    (* road (ii): the return code is c2_pure's (rc2); k3: its a0 goal is the second bullet below (k1's probe goal closed). *)
    lazymatch goal with |- context [mkR ra sp gp tp _ _ _ S0 S1 ?av _ _ _ _ _ _ _ S2] =>
      do 15 eexists; exists F3, fc3, m6, rc2;
      split; [reflexivity|];
      split; [| split; [idtac
                       | split; [reflexivity| split; [subst rc2; destruct (err =? Z_STREAM_END); [change Z_OK with 0; lia| lia]|]]]] end.
    - unfold lx_post_env. split; [exists errv3; eapply lx_env_sp; [exact ENV6| assumption| exact SPB]|]. split; [exact FRM3|].
      split; [| split; [rewrite ESO6; exact ESO2| rewrite EFA6; exact EFA2]].
      eapply lx_pres_trans; [exact PRES2|]. eapply lx_pres_trans; [| eapply lx_pres_sub; [exact LXP6| apply client_inner]].
      eapply lx_pres_trans.
      + eapply lx_pres_of_munch; [exact (unbox _ MU4)| exact (unbox _ WM4)|]. intros a [HX [Ha|[(b & Hb & Hr)|[Ha _]]]].
        * apply W0_high; [exact LBZR| lia].
        * destruct (LBR b Hb) as (_ & _ & _ & BC & BI). apply W0_heap; [lia| | lia|].
          -- intros Hc. apply HX. cbn [rin_ivs fst snd]. left. exact Hc.
          -- intros b' Hb'. pose proof (LBZL b' b Hb' Hb). lia.
        * apply W0_image; [exact LBZR| exact Ha].
      + eapply lx_pres_of_munch; [exact MU5| exact WM5|]. intros a [HX _]. cbn [outside]. split; [| exact I].
        assert (~ (PL <= a < PL + 8)) by (intros Hp; apply HX; cbn [rin_ivs fst snd]; right; left; exact Hp). lia.
    - (* k3: a0 = wint rc2: the 1.4 code maps Z_STREAM_END to Z_OK and returns every other code as it is *)
      subst rc2. unfold wint, MallocRep.wz.
      rewrite unsigned_lit by (pose proof (Z.mod_pos_bound err (2^64)); lia).
      destruct (Z.eq_dec err Z_STREAM_END) as [E1|E1].
      + subst err. apply bv_eq. vm_compute. reflexivity.
      + rewrite (proj2 (Z.eqb_neq err Z_STREAM_END) E1).
        assert (U1 : err mod 2^64 <> 1).
        { unfold Z_STREAM_END in E1. intros H1. destruct (Z.lt_ge_cases err 0).
          - replace (err mod 2^64) with (err + 2^64) in H1 by (apply (Z.mod_unique_pos _ _ (-1)); lia). lia.
          - rewrite Z.mod_small in H1 by lia. lia. }
        assert (UR2 : 0 <= err mod 2^64 < 2^64) by (apply Z.mod_pos_bound; lia).
        set (u := err mod 2^64) in *.
        replace (Z.land (u + -1) 18446744073709551615 <? 1) with false
          by (symmetry; apply Z.ltb_ge; change 18446744073709551615 with (Z.ones 64); rewrite Z.land_ones by lia;
              Z.div_mod_to_equations; lia).
        replace (Z.land (bv_swrap 32 (Z.b2z false + -1)) 18446744073709551615) with 18446744073709551615
          by (vm_compute; reflexivity).
        replace (Z.land 18446744073709551615 u) with u
          by (symmetry; rewrite Z.land_comm; change 18446744073709551615 with (Z.ones 64); rewrite Z.land_ones by lia;
              apply Z.mod_small; lia).
        reflexivity.
    - cbn [fst snd]. split; [exact OUT6|]. split; [lia|]. split; [lia|]. split; [rewrite <- EOUT; apply Forall_rev; exact ORF4|].
      (* 1.4 stores next_out - dest (1.3.1: total_out); its value is C + tout - C *)
      lazymatch type of PLC6 with rw_cells _ _ _ [C8 ?v] =>
        first [exact PLC6
              | replace (wz tout) with v; [exact PLC6| first [reflexivity | (cbv beta delta [MallocRep.wz]; f_equal; lia)
                                                          | (idtac "PLC6 value:" v; fail 100 "PLC6")]]] end.
  Qed.
End C2.

(* compress2_z's own statement: rcompress2_stmt at ZC_COMPRESS2Z, with 32 bytes less stack (the wrapper's frame). *)
Definition rcompress2z_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem)
         (s : PState) (LB : list block) (cp : bptr) (C cl PL NI n lv : Z) (oldc src : list Z) (lo B : Z) (errv canary : word),
  lx_env m s [] LB sp tp B lo errv canary ->
  In (cp, C, cl) LB -> u8arr psegs m C (to_bytes oldc) -> zlength oldc = cl ->
  rw_cells psegs m PL [C8 (wz cl)] -> bv_unsigned sp <= PL -> PL + 8 <= B -> PL mod 8 = 0 ->
  bytes_at psegs m NI (to_bytes src) -> Forall (fun c => 0 <= c < 256) src -> zlength src = n ->
  (exists b, In b LB /\ blk_addr b <= NI /\ NI + n <= blk_addr b + blk_size b) ->
  (NI + n <= C \/ C + cl <= NI) ->
  ZC_MIN - 3 <= n <= ZC_MAX - 3 -> cl = zc_bound zc n -> 0 <= lv <= 9 ->
  lo <= bv_unsigned sp - (ZC_WRAP_STACK - 32) -> bv_unsigned sp mod 16 = 0 ->
  frm0 fc ->
  a0 = wz C -> a1 = wz PL -> a2 = wz NI -> a3 = wz n -> a4 = wz lv ->
  implM psegs (compress2M lops zc cl src lv) s
        (rcompress2_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s LB C cl PL oldc lo B canary m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (wz ZC_COMPRESS2Z) fc None m (seg_rom psegs)).

Theorem compress2z_proof : forall R : zreps, zlib_okC R ->
  RHEAP_frame_stmt -> RHEAP_block_range_stmt -> RHEAP_blocks_nodup_stmt -> RHEAP_blocks_disjoint_stmt ->
  rcompress2z_stmt.
Proof.
  intros R ZOK HFRAME HBR HND HBD. unfold rcompress2z_stmt. intros until canary.
  intros ENV INC UC UCL PLC PLLO PLHI PL8 SB SF SL SRCB NEQ NR ECL LV LOSP SP16 FRM -> -> -> -> ->.
  pose proof ENV as (HP & _ & _ & _ & _ & _ & SPB & B63 & _ & LOC & LOG & _ & TP & _). cbn [app] in HP.
  pose proof (HBR _ _ _ _ HP INC) as CR. cbn [blk_addr blk_size fst snd] in CR.
  assert (LBR : forall b, In b LB -> rblock_range (blk_addr b) (blk_size b)) by (intros b Hb; exact (HBR _ _ _ _ HP Hb)).
  eapply (c2_main R) with (cp := cp) (errv := errv); eassumption.
Qed.

Section C2W.
  Hypothesis C2Z : rcompress2z_stmt.
  Hypothesis HFRAME : RHEAP_frame_stmt.
  Hypothesis HBR : RHEAP_block_range_stmt.

  (* 1.4 compress2 (0x161d4): add sp,sp,-32; sd ra,24(sp); sd s0,16(sp); mv s0,a1; ld a1,0(a1); sd a1,8(sp);
     add a1,sp,8; jal compress2_z; ld a1,8(sp); sd a1,0(s0); ld ra,24(sp); ld s0,16(sp); add sp,sp,32; ret.
     sp+0 is junk; got = sp+8. *)
  Theorem compress2_wrap : rcompress2_stmt.
  Proof.
    unfold rcompress2_stmt. intros until canary.
    intros ENV INC UC UCL PLC PLLO PLHI PL8 SB SF SL SRCB NEQ NR ECL LV LOSP SP16 FRM -> -> -> -> ->.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    pose proof ENV as (HP0 & LXS0 & ZLS0 & SEW0 & SSP0 & AUX0 & SPB & B63 & ST0 & LOC & LOG & ERR0 & TP & MI0).
    pose proof LOSP as LOSP0. unfold ZC_WRAP_STACK, Z_INFLATE_STACK, RMALLOC_STACK, GLOBALS_TOP in LOSP, LOG.
    pose proof (HBR _ _ _ _ HP0 INC) as (C0 & _ & _ & CCEIL & CIMG). cbn [blk_addr blk_size fst snd] in C0, CCEIL, CIMG.
    pose proof SRCB as (bS & HbS & BS1 & BS2). pose proof (HBR _ _ _ _ HP0 HbS) as (S0' & _ & _ & SCEIL & SIMG).
    assert (LC : Z.of_nat (length (to_bytes oldc)) = cl) by (rewrite to_bytes_len; unfold zlength in UCL; lia).
    assert (LS : Z.of_nat (length (to_bytes src)) = n) by (rewrite to_bytes_len; unfold zlength in SL; lia).
    apply box in UC. apply box in SB.
    pose proof (munch_refl [(bv_unsigned sp + -32, bv_unsigned sp)] m) as MU. pose proof (wmono_refl psegs m) as WM.
    unfold implM. iprefix. unfold ZC_COMPRESS2. cbv beta delta [MallocRep.wz].
    zstep. carve_frame 32%nat ST0.
    apply (rw_cells_split_CB psegs _ _ [] 32 junk [] [8; 8; 8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
    do 7 zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
    assert (E32 : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -32)) = bv_unsigned sp + -32) by (apply unsigned_lit; lia).
    assert (ENV1 : lx_env m1 s [] LB (Z_to_bv 64 (bv_unsigned sp + -32)) tp B lo errv canary).
    { eapply (lx_env_munch _ m m1); [exact HFRAME| exact ENV| exact MU| exact WM| assumption| rewrite E32; assumption| rewrite E32; lia| |].
      - constructor; [| constructor]. left. cbn [fst]. lia.
      - intros a Ha. cbn [outside]. lia. }
    pose proof (agree_on_of_munch _ _ _ MU WM) as AG1.
    assert (UC1 : u8arr psegs m1 C (to_bytes oldc)).
    { eapply u8arr_agree; [exact AG1| exact (unbox _ UC)|]. intros a Ha. cbn [outside]. lia. }
    assert (SB1 : bytes_at psegs m1 NI (to_bytes src)).
    { eapply bytes_at_agree; [exact AG1| exact (unbox _ SB)|]. intros a Ha. cbn [outside]. lia. }
    rename PLC into PLC1.
    assert (PRES1 : lx_pres LB (bv_unsigned sp) [(C, C + cl); (PL, PL + 8)] m m1).
    { eapply lx_pres_of_munch; [exact MU| exact WM|]. intros a [HX [Ha|[(b & Hb & Hr)|[Ha _]]]]; cbn [outside].
      - lia.
      - pose proof (HBR _ _ _ _ HP0 Hb) as (_ & _ & _ & BC & _). lia.
      - lia. }
    apply evt_done.
    lazymatch goal with |- impl _ _ (?tm _) _ ?msx =>
      change (implM psegs tm s (rcompress2_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s LB C cl PL oldc lo B canary m) msx) end.
    lazymatch goal with FRx : rw_cells psegs m1 (bv_unsigned sp + -32) [CB 8 ?j; C8 ?vdl; C8 ?vs0; C8 ?vra] |- _ =>
      apply (rw_cells_app psegs m1 (bv_unsigned sp + -32) [CB 8 j] [C8 vdl; C8 vs0; C8 vra]) in FRx; destruct FRx as [FJ1 FRx];
      cbn [cells_size csize Nat.add] in FRx;
      apply (rw_cells_app psegs m1 (bv_unsigned sp + -32 + 8) [C8 vdl] [C8 vs0; C8 vra]) in FRx; destruct FRx as [FL1 FRA1];
      cbn [cells_size csize Nat.add] in FRA1 end.
    eapply implM_post_evt'.
    { eapply (C2Z _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m1 s LB cp C cl (bv_unsigned sp + -32 + 8) NI n lv oldc src lo B errv canary);
        rewrite ?E32;
        [ exact ENV1 | exact INC | exact UC1 | exact UCL | exact FL1 | lia | lia | clear - SP16 RSP; Z.div_mod_to_equations; lia
        | exact SB1 | exact SF | exact SL | exact SRCB | exact NEQ | exact NR | exact ECL | exact LV
        | unfold ZC_WRAP_STACK, Z_INFLATE_STACK, RMALLOC_STACK; lia | clear - SP16 RSP; Z.div_mod_to_equations; lia | exact FRM
        | reflexivity | first [reflexivity | f_equal; rewrite ?E32; lia] | reflexivity | reflexivity | reflexivity ]. }
    cbv beta. intros r s' ms' PO. unfold rcompress2_post in PO.
    destruct PO as (x0 & x1 & x2 & e0 & e1 & e2 & e3 & e4 & e5 & e6 & e7 & x3 & x4 & x5 & x6 & F' & fc' & m' & rc & -> & LPE & HA0 & HRC & HRR & UC' & LEN' & LEN2 & FA' & PLC').
    replace (ret_pc (Z_to_bv 64 0x16268)) with (Z_to_bv 64 0x16268) by (symmetry; rpc).
    destruct LPE as ((errv' & ENV') & FRM' & PRES' & ESO' & EFA').
    pose proof ENV' as (HP' & _ & _ & _ & _ & _ & _ & _ & ST' & _ & _ & _ & _ & MI').
    rewrite E32 in ST', PRES'.
    assert (FRA' : rw_cells psegs m' (bv_unsigned sp + -32 + 8 + 8) [C8 s0; C8 ra]).
    { eapply rw_cells_agree; [exact (agree_of_lx_pres _ _ _ _ _ PRES')| exact FRA1|].
      intros a Ha. cbn in Ha. split; [| left; lia]. cbn [rin_ivs fst snd]. lia. }
    lazymatch type of FJ1 with rw_cells _ _ _ [CB 8 ?j] =>
      assert (FJ' : rw_cells psegs m' (bv_unsigned sp + -32) [CB 8 j])
        by (eapply rw_cells_agree; [exact (agree_of_lx_pres _ _ _ _ _ PRES')| exact FJ1|];
            intros a Ha; cbn in Ha; split; [| left; lia]; cbn [rin_ivs fst snd]; lia);
      assert (PLC2 : rw_cells psegs m' PL [C8 (Z_to_bv 64 cl)])
        by (eapply rw_cells_agree; [exact (agree_of_lx_pres _ _ _ _ _ PRES')| exact PLC1|];
            intros a Ha; cbn in Ha; split; [| left; lia]; cbn [rin_ivs fst snd]; lia);
      assert (FR2 : rw_cells psegs m' (bv_unsigned sp + -32) [CB 8 j; C8 (Z_to_bv 64 (snd (fst r))); C8 s0; C8 ra])
        by (apply (proj2 (rw_cells_app psegs m' (bv_unsigned sp + -32) [CB 8 j] [C8 (Z_to_bv 64 (snd (fst r))); C8 s0; C8 ra]));
            split; [exact FJ'|]; cbn [cells_size csize Nat.add];
            apply (proj2 (rw_cells_app psegs m' (bv_unsigned sp + -32 + 8) [C8 (Z_to_bv 64 (snd (fst r)))] [C8 s0; C8 ra]));
            split; [exact PLC'| cbn [cells_size csize Nat.add]; exact FRA']) end.
    clear FRA' FJ' PLC'.
    pose proof (munch_refl [(bv_unsigned sp + -32, bv_unsigned sp); (PL, PL + 8)] m') as MU'. pose proof (wmono_refl psegs m') as WM'.
    apply box in UC'.
    (* ld a1,8(sp); sd a1,0(s0): *destLen := got *)
    zstep. zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m2 end.
    assert (ENV2 : lx_env m2 s' [] LB (Z_to_bv 64 (bv_unsigned sp + -32)) tp B lo errv' canary).
    { eapply (lx_env_munch _ m' m2); [exact HFRAME| exact ENV'| exact MU'| exact WM'| assumption| rewrite E32; assumption| rewrite E32; lia| |].
      - constructor; [| constructor; [| constructor]]; left; cbn [fst]; lia.
      - intros a Ha. cbn [outside]. lia. }
    assert (UC2 : u8arr psegs m2 C (to_bytes (zstore oldc 0 (fst (fst r))))).
    { eapply u8arr_agree; [exact (agree_on_of_munch _ _ _ MU' WM')| exact (unbox _ UC')|]. intros a Ha. cbn [outside].
      rewrite to_bytes_len in Ha. pose proof (zstore_length (fst (fst r)) oldc 0) as ZL. unfold zlength in ZL, UCL. lia. }
    assert (PRESst : lx_pres LB (bv_unsigned sp) [(C, C + cl); (PL, PL + 8)] m' m2).
    { eapply lx_pres_of_munch; [exact MU'| exact WM'|]. intros a [HX [Ha|[(b & Hb & Hr)|[Ha _]]]]; cbn [outside].
      - cbn [rin_ivs fst snd] in HX. lia.
      - pose proof (HBR _ _ _ _ HP0 Hb) as (_ & _ & _ & BC & _). cbn [rin_ivs fst snd] in HX. lia.
      - cbn [rin_ivs fst snd] in HX. lia. }
    (* ld ra,24(sp); ld s0,16(sp); add sp,sp,32 *)
    zstep. zstep. zstep.
    release_frame FR2 ST' (bv_unsigned sp).
    zstep.
    apply evt_done. unfold rcompress2_post.
    do 15 eexists. exists F', fc', m2, rc. split; [reflexivity|].
    split.
    { unfold lx_post_env. split; [exists errv'; eapply lx_env_sp; [exact ENV2| exact ST'| exact SPB]|].
      split; [exact FRM'|]. split; [| split; [exact ESO'| exact EFA']].
      eapply lx_pres_trans; [exact PRES1|]. eapply lx_pres_trans; [| exact PRESst].
      eapply lx_pres_sub; [exact PRES'|]. intros a [HX Hc]. split.
      - cbn [rin_ivs fst snd] in HX |- *. intros [H1|[H2|[]]]; [apply HX; left; exact H1|].
        destruct Hc as [Hc|[(b & Hb & Hr)|[Hc _]]]; [lia| | lia].
        pose proof (HBR _ _ _ _ HP0 Hb) as (_ & _ & _ & BC & _); lia.
      - destruct Hc as [Hc|Hc]; [left; lia| right; exact Hc]. }
    split; [exact HA0|]. split; [exact HRC|]. split; [exact HRR|]. split; [exact UC2|]. split; [exact LEN'|]. split; [exact LEN2|]. split; [exact FA'| exact PLC2].
  Qed.
End C2W.

Theorem compress2_proof : forall R : zreps, zlib_okC R ->
  RHEAP_frame_stmt -> RHEAP_block_range_stmt -> RHEAP_blocks_nodup_stmt -> RHEAP_blocks_disjoint_stmt ->
  rcompress2_stmt.
Proof.
  intros R ZOK HFRAME HBR HND HBD.
  exact (compress2_wrap (compress2z_proof R ZOK HFRAME HBR HND HBD) HFRAME HBR).
Qed.
End WithCeiling0.
