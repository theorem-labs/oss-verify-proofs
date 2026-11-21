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
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.P Require Import Layout Exit Startup_glue Printf_lib Drv_kit Zlib_iface Zh_kit Zg_zlib_iface Zc_kit Zc_wkit Zc_drc Zc_u2facts Zc_ibridge Zc_iface.
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

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.
Notation za := the_zapi.
Notation zc := the_zapiC.

Section U2.
  Variable R : zreps.
  Hypothesis ZOK : zlib_okC R.
  Hypothesis HFRAME : RHEAP_frame_stmt.
  Hypothesis HBR : RHEAP_block_range_stmt.
  Hypothesis HND : RHEAP_blocks_nodup_stmt.
  Hypothesis HBD : RHEAP_blocks_disjoint_stmt.

  Variables (ra sp gp tp : word) (S0 S1 S2 S3 S4 S5 S6 S7 S8 S9 S10 S11 : word).
  Variables (LB : list block) (up cpS : bptr) (U dlen PL C cl slen PS : Z) (uc comprc src : list Z) (lo B : Z) (canary : word).
  Notation usp := (bv_unsigned sp).
  (* 1.4 uncompress2_z: a 160-byte frame, the z_stream at sp+0 (no junk slot below it), s4..s0 / ra at sp+112.. *)
  Notation SP_ := (usp + -160).
  Notation SS := (usp + -160).
  Hypothesis INU : In (up, U, dlen) LB.
  Hypothesis UCL : zlength uc = dlen.
  Hypothesis PLLO : usp <= PL.
  Hypothesis PLHI : PL + 8 <= B.
  Hypothesis PL8 : PL mod 8 = 0.
  Hypothesis INC : In (cpS, C, cl) LB.
  Hypothesis CCL : zlength comprc = cl.
  Hypothesis CCF : Forall (fun c => 0 <= c < 256) comprc.
  Hypothesis SLEN : 0 <= slen <= cl.
  Hypothesis ESRC : ztake slen comprc = src.
  Hypothesis PSLO : usp <= PS.
  Hypothesis PSHI : PS + 8 <= B.
  Hypothesis PS8 : PS mod 8 = 0.
  Hypothesis PLPS : PL + 8 <= PS \/ PS + 8 <= PL.
  Hypothesis NEQB : up <> cpS.
  Hypothesis DL : 0 < dlen <= zc_bound zc (ZC_MAX - 3).
  Hypothesis CLB : cl <= zc_bound zc (ZC_MAX - 3).
  Hypothesis SPB : usp <= B.
  Hypothesis B63 : B < 2^63.
  Hypothesis LOC : alloc_ceiling <= lo.
  Hypothesis LOG : GLOBALS_TOP <= lo.
  Hypothesis LOSP : lo <= usp - ZC_WRAP_STACK.
  Hypothesis TP : tp = wz RATP.
  Hypothesis SP16 : usp mod 16 = 0.
  Hypothesis UR : rblock_range U dlen.
  Hypothesis CR : rblock_range C cl.
  Hypothesis CU : U + dlen <= C \/ C + cl <= U.
  Hypothesis LBR : forall b, In b LB -> rblock_range (blk_addr b) (blk_size b).

  Lemma N_facts : dlen <= 2097152 /\ cl <= 2097152 /\ zlength src = slen /\ Forall (fun c => 0 <= c < 256) src /\ 0 <= slen <= 2097152.
  Proof.
    pose proof (zo_boundC zc the_zapiC_ok (ZC_MAX - 3) ltac:(unfold ZC_MAX; lia)) as HB.
    unfold ZBC_MAX, ZC_MAX in *.
    split; [lia|]. split; [lia|]. split; [| split; [| lia]].
    - rewrite <- ESRC. unfold ztake, zlength in *. rewrite length_firstn. lia.
    - rewrite <- ESRC. unfold ztake. rewrite <- (firstn_skipn (Z.to_nat slen) comprc) in CCF. apply Forall_app in CCF. exact (proj1 CCF).
  Qed.
  Lemma N_factsB : 0 < dlen <= ZBC_MAX /\ zlength src <= ZBC_MAX.
  Proof. pose proof N_facts. unfold ZBC_MAX, ZC_MAX. lia. Qed.

  Notation XX := [(U, U + dlen); (PL, PL + 8); (PS, PS + 8)].

  Definition FRLO (mm : mem) : Prop := True.
  Definition FRHI (mm : mem) : Prop := rw_cells psegs mm (usp + -48) [C8 S4; C8 S3; C8 S2; C8 S1; C8 S0; C8 ra].

  Lemma client_inner : forall X a, (forall a', rin_ivs X a' -> (SS <= a' < SS + ZS_SIZEOF) \/ (U <= a' < U + dlen)) ->
    lx_client LB usp XX a -> lx_client LB SP_ X a.
  Proof.
    intros X a HX [Hn Hc]. split.
    - intros Hi. destruct (HX a Hi) as [Ha|Ha].
      + unfold ZS_SIZEOF in Ha. destruct Hc as [Hc|[(b & Hb & Hr)|[Hc _]]]; [lia| |].
        * destruct (LBR b Hb) as (_ & _ & _ & BC & _). unfold ZC_WRAP_STACK, Z_INFLATE_STACK, RMALLOC_STACK in *. lia.
        * unfold ZC_WRAP_STACK, Z_INFLATE_STACK, RMALLOC_STACK, GLOBALS_TOP in *. lia.
      + apply Hn. cbn [rin_ivs fst snd]. left. exact Ha.
    - destruct Hc as [Hc|[Hc|Hc]]; [left; lia| right; left; exact Hc| right; right; exact Hc].
  Qed.

  Lemma pres_munch : forall W m m', munch W m m' -> wmono psegs m m' ->
    (forall a, usp <= a \/ in_block LB a \/ (0x29000 <= a < 0x5c000) -> ~ rin_ivs XX a -> outside W a) -> lx_pres LB usp XX m m'.
  Proof.
    intros W m m' MU WM HW. eapply lx_pres_of_munch; [exact MU| exact WM|]. intros a [HX Hc]. apply HW; [| exact HX].
    destruct Hc as [Hc|[Hc|[Hc _]]]; [left; exact Hc| right; left; exact Hc| right; right; exact Hc].
  Qed.

  Section Inv.
    Variables (m0 : mem) (s0 : PState) (pst : bptr) (As : Z).

    Definition EINV (m : mem) (s : PState) (fc : bv 32) (OW : list block) : Prop :=
      (exists errv, lx_env m s OW LB (Z_to_bv 64 SP_) tp B lo errv canary)
      /\ FRLO m /\ FRHI m /\ u8arr psegs m C (to_bytes comprc)
      /\ rw_cells psegs m PL [C8 (Z_to_bv 64 dlen)] /\ rw_cells psegs m PS [C8 (Z_to_bv 64 slen)]
      /\ lx_pres LB usp XX m0 m /\ ps_so s = ps_so s0 /\ ps_fa s = ps_fa s0 /\ frm0 fc.

    Definition destc (orev : list Z) : list Z := rev orev ++ skipn (length orev) uc.
    Lemma destc_len : forall orev, zlength orev <= dlen -> Z.of_nat (length (to_bytes (destc orev))) = dlen /\ zlength (destc orev) = dlen.
    Proof. intros orev H. unfold destc, zlength in *. rewrite to_bytes_len, length_app, length_rev, length_skipn. lia. Qed.

    Definition IINV (m : mem) (s : PState) (fc : bv 32) (x : u2L zc) (w : option bptr) (Aw : Z) : Prop :=
      EINV m s fc (iblocks w Aw pst As)
      /\ (exists p1 p2, rw_cells psegs m SS (zs_pub (C + u2_tin x) (u2_ain zc x) (u2_tin x) (U + u2_tout x) (u2_aout zc x) (u2_tout x) p1 p2))
      /\ zr_i R m SS (iblocks w Aw pst As) (u2_is zc x)
      /\ u8arr psegs m U (to_bytes (destc (u2_orev zc x))).

    Definition IINVw (m : mem) (s : PState) (fc : bv 32) (x : u2L zc) (w : option bptr) (Aw : Z) : Prop :=
      EINV m s fc (iblocks w Aw pst As)
      /\ (exists ni no p1 p2, rw_cells psegs m SS (zs_pub ni (u2_ain zc x) (u2_tin x) no (u2_aout zc x) (u2_tout x) p1 p2))
      /\ zr_i R m SS (iblocks w Aw pst As) (u2_is zc x)
      /\ u8arr psegs m U (to_bytes (destc (u2_orev zc x))).

    Lemma wint_cases : forall rc, - 2^31 <= rc < 2^31 -> (0 <= rc /\ bv_unsigned (wint rc) = rc) \/ (rc < 0 /\ bv_unsigned (wint rc) = rc + 2^64).
    Proof.
      intros rc Hrc. unfold wint, wz. rewrite unsigned_lit by (apply Z.mod_pos_bound; lia).
      destruct (Z.lt_ge_cases rc 0) as [Ng|Ng]; [right| left]; (split; [lia|]).
      - symmetry. apply (Z.mod_unique_pos _ _ (-1)); lia.
      - apply Z.mod_small. lia.
    Qed.
    Lemma wint_zero : forall rc, - 2^31 <= rc < 2^31 -> (bv_unsigned (wint rc) = 0 <-> rc = 0).
    Proof. intros rc Hrc. destruct (wint_cases rc Hrc) as [[R0 E]|[R0 E]]; rewrite E; lia. Qed.

    Lemma cells_lx : forall X m m' (A : Z) cs, lx_pres LB SP_ X m m' -> rw_cells psegs m A cs ->
      (forall a, A <= a < A + Z.of_nat (cells_size cs) -> lx_client LB SP_ X a) -> rw_cells psegs m' A cs.
    Proof. intros X m m' A cs LXP H HC. eapply rw_cells_agree; [exact (agree_of_lx_pres _ _ _ _ _ LXP)| exact H| exact HC]. Qed.

    Lemma einv_step : forall m m' s s' fc fc' OW OW' X,
      EINV m s fc OW -> (forall a', rin_ivs X a' -> (SS <= a' < SS + ZS_SIZEOF) \/ (U <= a' < U + dlen)) ->
      lx_post_env m m' s s' OW' LB (Z_to_bv 64 SP_) tp B lo canary X fc' ->
      EINV m' s' fc' OW'.
    Proof.
      intros m m' s s' fc fc' OW OW' X ((errv & ENV) & FRL & FRH & CARR & PLC & PSC & PRES & ESO & EFA & FRM) HX (ENV' & FRM' & LXP & ESO' & EFA').
      pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
      unfold ZC_WRAP_STACK, Z_INFLATE_STACK, RMALLOC_STACK, GLOBALS_TOP in LOSP, LOG. pose proof N_facts as (NF1 & NF2 & _).
      rewrite unsigned_lit in LXP by lia.
      pose proof CR as (C0 & _ & _ & CC & CI). pose proof UR as (U0 & _ & _ & UC & UI).
      assert (NX : forall a, ~ ((SS <= a < SS + ZS_SIZEOF) \/ (U <= a < U + dlen)) -> ~ rin_ivs X a) by (intros a Ha Hi; apply Ha; exact (HX a Hi)).
      unfold EINV. split; [exact ENV'|].
      split; [exact I|].
      split. { unfold FRHI in *. eapply cells_lx; [exact LXP| exact FRH|]. intros a Ha. cbn in Ha. apply stack_client; [lia| apply NX; unfold ZS_SIZEOF; lia]. }
      split. { eapply u8arr_agree; [exact (agree_of_lx_pres _ _ _ _ _ LXP)| exact CARR|]. intros a Ha. rewrite to_bytes_len in Ha. unfold zlength in CCL.
               eapply block_client; [exact INC| cbn [blk_addr blk_size fst snd]; lia| apply NX; unfold ZS_SIZEOF; lia]. }
      split. { eapply cells_lx; [exact LXP| exact PLC|]. intros a Ha. cbn in Ha. apply stack_client; [lia| apply NX; unfold ZS_SIZEOF; lia]. }
      split. { eapply cells_lx; [exact LXP| exact PSC|]. intros a Ha. cbn in Ha. apply stack_client; [lia| apply NX; unfold ZS_SIZEOF; lia]. }
      split. { eapply lx_pres_trans; [exact PRES|]. eapply lx_pres_sub; [exact LXP|]. intros a Ha. apply (client_inner X a HX Ha). }
      split; [rewrite ESO'; exact ESO|]. split; [rewrite EFA'; exact EFA| exact FRM'].
    Qed.

    Lemma zri_pub : forall m m' LBz is, (forall b, In b LBz -> rblock_range (blk_addr b) (blk_size b)) ->
      zr_i R m SS LBz is -> munch [(SS, SS + 48)] m m' -> wmono psegs m m' -> zr_i R m' SS LBz is.
    Proof.
      intros m m' LBz is LBZR ZR MU WM. eapply (zr_i_frame R); [exact ZR|]. intros a Ha Hin.
      apply (agree_on_of_munch _ _ _ MU WM a Ha). cbn [outside]. split; [| exact I].
      destruct Hin as [Hin|(b & Hb & Hr)]; [unfold ZS_PUB, ZS_SIZEOF in *; lia|].
      destruct (LBZR b Hb) as (_ & _ & _ & BC & _). unfold ZC_WRAP_STACK, Z_INFLATE_STACK, RMALLOC_STACK, ZS_PUB in *. lia.
    Qed.

    Definition head_pc (x : u2L zc) : Z := if u2_aout zc x =? 0 then 0x1cde4 else 0x1cdc8.

    (* 1.4 registers in the loop: s0 = destLen, s1 = sourceLen, s2 = max, s3 = len, s4 = left (s5 untouched) *)
    Notation HDS pc x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 left len F fc m :=
      (MS (mkR x1 (wz SP_) gp tp t0 t1 t2 (wz PL) (wz PS) a0 a1 a2 a3 a4 a5 a6 a7 (wz 4294967295) (wz len) (wz left) S5 S6 S7 S8 S9 S10 S11 t3 t4 t5 t6)
          F pc fc None m (seg_rom psegs)).

    Lemma u2_head_to_call : forall (Q : machine_state -> Prop) m x (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) F fc (p1 p2 : list byte),
      U2I dlen src x ->
      rw_cells psegs m SS (zs_pub (C + u2_tin x) (u2_ain zc x) (u2_tin x) (U + u2_tout x) (u2_aout zc x) (u2_tout x) p1 p2) ->
      mem_inv psegs m -> stk psegs m lo SP_ ->
      (forall m1 (ret : Z),
         (ret = 0x1cddc \/ ret = 0x1ce20) ->
         munch [(SS, SS + 48)] m m1 -> wmono psegs m m1 -> mem_inv psegs m1 -> stk psegs m1 lo SP_ ->
         rw_cells psegs m1 SS (zs_pub (C + u2_tin x) (zlength (u2_rest zc x)) (u2_tin x) (U + u2_tout x) (dlen - u2_tout x) (u2_tout x) p1 p2) ->
         evt psegs Q (HDS (wz Z_INFLATE) (wz ret) t0 t1 t2 (wz SS) (wz Z_NO_FLUSH) a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 0 0 F fc m1)) ->
      evt psegs Q (HDS (wz (head_pc x)) x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (u2_left zc x) (u2_len zc x) F fc m).
    Proof.
      intros until p2. intros UX PUB MI ST K.
      pose proof N_facts as (NF1 & NF2 & NF3 & NF4 & NF5). pose proof N_factsB as [NB SB].
      pose proof (U2I_shape dlen src x UX) as SH. cbv zeta in SH.
      destruct SH as (TIN0 & TINS & EREST & TOUT & SUM & LA & LO & AIN0 & LEN0 & SUMI & AOUT0 & LEFT0 & RESTF & TO64).
      pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
      unfold ZC_WRAP_STACK, Z_INFLATE_STACK, RMALLOC_STACK, GLOBALS_TOP in LOSP, LOG.
      assert (RL0 : 0 <= zlength (u2_rest zc x)) by (unfold zlength; lia).
      pose proof (munch_refl [(SS, SS + 48)] m) as MUp. pose proof (wmono_refl psegs m) as WMp.
      unfold zs_pub in PUB. cbv beta delta [MallocRep.wz] in PUB.
      unfold head_pc. cbv beta delta [MallocRep.wz].
      destruct (Z.eqb_spec (u2_aout zc x) 0) as [EA|EA].
      -
        rewrite EA in PUB.
        assert (HLT : bv_ltu (Z_to_bv 64 (u2_left zc x)) (Z_to_bv 64 4294967295) = true) by (unfold bv_ltu; rewrite !unsigned_lit by lia; apply Z.ltb_lt; lia).
        zstep. zstep. rewrite HLT; cbv_concl_iota. zstep. zstep. zstep. zstep.
        if_cases KAI; rewrite sx32_small in KAI by lia; zify_cond KAI; rewrite ?unsigned_lit in KAI by lia.
        +
          assert (ELN : u2_len zc x = 0) by lia. rewrite ELN.
          replace (u2_left zc x + - u2_left zc x) with 0 by lia.
          zstep. zstep. zstep.
          lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
          eapply (K m1); [left; reflexivity| exact MUp| exact WMp| assumption| assumption|].
          unfold zs_pub. cbv beta delta [MallocRep.wz]. replace (u2_ain zc x) with (zlength (u2_rest zc x)) in PUB by lia.
          replace (u2_left zc x) with (dlen - u2_tout x) in PUB by lia. exact PUB.
        +
          assert (EAI : u2_ain zc x = 0) by lia. rewrite EAI in *.
          assert (HLT2 : bv_ltu (Z_to_bv 64 (u2_len zc x)) (Z_to_bv 64 4294967295) = true) by (unfold bv_ltu; rewrite !unsigned_lit by lia; apply Z.ltb_lt; lia).
          zstep. zstep. rewrite HLT2; cbv_concl_iota. zstep. zstep.
          replace (u2_len zc x + - u2_len zc x) with 0 by lia. try replace (u2_left zc x + - u2_left zc x) with 0 by lia.
          zstep. zstep. zstep.
          lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
          eapply (K m1); [right; reflexivity| exact MUp| exact WMp| assumption| assumption|].
          unfold zs_pub. cbv beta delta [MallocRep.wz]. replace (u2_len zc x) with (zlength (u2_rest zc x)) in PUB by lia.
          replace (u2_left zc x) with (dlen - u2_tout x) in PUB by lia. exact PUB.
      -
        assert (EL : u2_left zc x = 0) by lia. rewrite EL.
        zstep. zstep. if_cases KAI; rewrite sx32_small in KAI by lia; zify_cond KAI; rewrite ?unsigned_lit in KAI by lia.
        +
          assert (EAI : u2_ain zc x = 0) by lia. rewrite EAI in *.
          assert (HLT2 : bv_ltu (Z_to_bv 64 (u2_len zc x)) (Z_to_bv 64 4294967295) = true) by (unfold bv_ltu; rewrite !unsigned_lit by lia; apply Z.ltb_lt; lia).
          zstep. zstep. rewrite HLT2; cbv_concl_iota. zstep. zstep.
          replace (u2_len zc x + - u2_len zc x) with 0 by lia.
          zstep. zstep. zstep.
          lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
          eapply (K m1); [right; reflexivity| exact MUp| exact WMp| assumption| assumption|].
          unfold zs_pub. cbv beta delta [MallocRep.wz]. replace (u2_len zc x) with (zlength (u2_rest zc x)) in PUB by lia.
          replace (u2_aout zc x) with (dlen - u2_tout x) in PUB by lia. exact PUB.
        +
          assert (ELN : u2_len zc x = 0) by lia. rewrite ELN.
          zstep. zstep. zstep.
          lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
          eapply (K m1); [left; reflexivity| exact MUp| exact WMp| assumption| assumption|].
          unfold zs_pub. cbv beta delta [MallocRep.wz]. replace (u2_ain zc x) with (zlength (u2_rest zc x)) in PUB by lia.
          replace (u2_aout zc x) with (dlen - u2_tout x) in PUB by lia. exact PUB.
    Qed.

    Lemma destc_step : forall orev bs, (length orev + length bs <= length uc)%nat ->
      destc (rev_append bs orev) = zstore (destc orev) (zlength orev) bs.
    Proof.
      intros orev bs HL. unfold destc. rewrite rev_append_rev', rev_app_distr, rev_involutive, length_app, length_rev.
      replace (zlength orev) with (Z.of_nat (length (rev orev))) by (rewrite length_rev; reflexivity).
      rewrite (Z_deflate.zstore_split bs (rev orev)) by (rewrite length_skipn; lia).
      rewrite skipn_skipn, <- app_assoc. repeat f_equal; lia.
    Qed.

    Lemma iblocks_LBZR : forall s w Aw m, RHEAP s (iblocks w Aw pst As ++ LB) m ->
      forall b, In b (iblocks w Aw pst As) -> rblock_range (blk_addr b) (blk_size b).
    Proof. intros s w Aw m HP b Hb. apply (HBR _ _ _ _ HP). apply in_or_app. left. exact Hb. Qed.

    Lemma u2_loop : forall (A : Type) (K : u2L zc * Z * option bptr -> M PState A) (POSTQ : A -> PState -> machine_state -> Prop),
      (forall x' err w Aw s (x1 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) F fc m,
         IINVw m s fc x' w Aw -> zlength (u2_orev zc x') <= dlen -> 0 <= u2_tout x' < 2^64 ->
         - 2^31 <= err < 2^31 -> err <> Z_OK ->
         u2_left zc x' = 0 -> 0 <= u2_aout zc x' <= dlen ->
         u2_len zc x' = 0 -> (err = Z_BUF_ERROR -> 0 <= u2_ain zc x' < 2^32) ->
         implM psegs (K (x', err, w)) s POSTQ (HDS (wz 0x1ce30) x1 t0 t1 t2 (wint err) a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 0 0 F fc m)) ->
      forall (fuel : nat) x w Aw s (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) F fc m,
      U2I dlen src x -> IINV m s fc x w Aw ->
      implM psegs (mbind (u2_loopM lops zc fuel x w) K) s POSTQ
            (HDS (wz (head_pc x)) x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (u2_left zc x) (u2_len zc x) F fc m).
    Proof.
      destruct ZOK as (_ & _ & _ & _ & INFL & _).
      intros A K POSTQ KEND. induction fuel as [|f IH]; intros until m; intros UX INV.
      { cbn [u2_loopM unreachable lops Target.ops]. unfold implM. rewrite mbind_munr. apply impl_ret_unr. }
      cbn [u2_loopM]. cbn [bind ret unreachable lib_malloc lops Target.ops].
      pose proof INV as (EI & (p1 & p2 & PUB) & ZR & UARR).
      pose proof EI as ((errv & ENV) & FRL & FRH & CARR & PLC & PSC & PRES & ESO & EFA & FRM).
      pose proof ENV as (HP & _ & _ & _ & _ & _ & _ & _ & ST & _ & _ & _ & _ & MI).
      pose proof N_facts as (NF1 & NF2 & NF3 & NF4 & NF5). pose proof N_factsB as [NB SB].
      pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
      pose proof CR as (C0 & _ & _ & CC & CI). pose proof UR as (U0 & _ & _ & UC & UI).
      unfold ZC_WRAP_STACK, Z_INFLATE_STACK, RMALLOC_STACK, GLOBALS_TOP in LOSP, LOG.
      assert (E176 : bv_unsigned (Z_to_bv 64 SP_) = SP_) by (apply unsigned_lit; lia). rewrite E176 in ST.
      pose proof (U2I_shape dlen src x UX) as SH. cbv zeta in SH.
      destruct SH as (TIN0 & TINS & EREST & TOUT & SUM & LA & LO & AIN0 & LEN0 & SUMI & AOUT0 & LEFT0 & RESTF & TO64).
      assert (RL0 : 0 <= zlength (u2_rest zc x)) by (unfold zlength; lia).
      pose proof (iblocks_LBZR _ _ _ _ HP) as LBZR.

      rewrite (u2_wants_bridge dlen src x comprc slen w NB SB UX ESRC NF3 ltac:(lia)).
      rewrite <- bridge_wsize.
      set (WG := i_wantsG comprc (u2_is zc x) (zlength (u2_rest zc x)) (dlen - u2_tout x) w).

      unfold implM. iprefix.
      eapply (u2_head_to_call _ m x); [exact UX| exact PUB| exact MI| exact ST|].
      intros m1 ret RET MUp WMp MI1 ST1 PUB1.
      assert (ZR1 : zr_i R m1 SS (iblocks w Aw pst As) (u2_is zc x)) by (eapply zri_pub; [exact LBZR| exact ZR| exact MUp| exact WMp]).
      assert (ENV1 : lx_env m1 s (iblocks w Aw pst As) LB (Z_to_bv 64 SP_) tp B lo errv canary).
      { eapply (lx_env_munch [(SS, SS + 48)] m m1); [exact HFRAME| exact ENV| exact MUp| exact WMp| exact MI1| rewrite E176; exact ST1| rewrite E176; lia| |].
        - constructor; [left; cbn [fst]; lia| constructor].
        - intros a Ha. cbn [outside]. clear - Ha SPB LOG LOSP RSP. lia. }
      pose proof (agree_on_of_munch _ _ _ MUp WMp) as AG1.
      assert (EI1 : EINV m1 s fc (iblocks w Aw pst As)).
      { unfold EINV. split; [exists errv; exact ENV1|].
        split; [exact I|].
        split. { unfold FRHI in *. eapply rw_cells_agree; [exact AG1| exact FRH| intros a Ha; cbn in Ha; cbn [outside]; lia]. }
        split. { eapply u8arr_agree; [exact AG1| exact CARR|]. intros a Ha. rewrite to_bytes_len in Ha. unfold zlength in CCL. cbn [outside]. lia. }
        split. { eapply rw_cells_agree; [exact AG1| exact PLC| intros a Ha; cbn in Ha; cbn [outside]; lia]. }
        split. { eapply rw_cells_agree; [exact AG1| exact PSC| intros a Ha; cbn in Ha; cbn [outside]; lia]. }
        split. { eapply lx_pres_trans; [exact PRES|]. eapply pres_munch; [exact MUp| exact WMp|]. intros a Ha HX. cbn [outside]. split; [| exact I].
                 destruct Ha as [Ha|[(b & Hb & Hr)|Ha]]; [lia| destruct (LBR b Hb) as (_ & _ & _ & BC & _); lia| lia]. }
        split; [exact ESO|]. split; [exact EFA| exact FRM]. }
      pose proof (destc_len (u2_orev zc x) ltac:(lia)) as [LD LDZ].
      assert (UARR1 : u8arr psegs m1 U (to_bytes (destc (u2_orev zc x)))).
      { eapply u8arr_agree; [exact AG1| exact UARR|]. intros a Ha. rewrite LD in Ha. cbn [outside]. lia. }
      clear AG1 ZR UARR CARR PLC PSC FRL FRH.
      apply evt_done.
      lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM psegs tm s POSTQ msx) end.
      apply implM_bind_assoc. eapply implM_bind.
      { assert (SPM : SP_ mod 16 = 0) by (clear - SP16 RSP; Z.div_mod_to_equations; lia).
        eapply INFL with (S := SS) (C := C) (U := U) (cl := cl) (size := dlen) (comprc := comprc) (uc := destc (u2_orev zc x)) (is := u2_is zc x)
                         (ain := zlength (u2_rest zc x)) (no := u2_tout x) (aout := dlen - u2_tout x) (w := w) (Aw := Aw) (sp_ := pst) (As := As)
                         (p1 := p1) (p2 := p2) (lo := lo) (B := B) (errv := errv) (canary := canary);
          unfold strm_in_frame, Z_INFLATE_STACK, RMALLOC_STACK, ZS_SIZEOF; rewrite ?E176;
          [ nm 1 ltac:(exact ENV1)
          | nm 2 ltac:(exact PUB1)
          | nm 3 ltac:(exact ZR1)
          | nm 4 ltac:(exists (cpS, C, cl); split; [exact INC| split; reflexivity])
          | nm 5 ltac:(destruct EI1 as (_ & _ & _ & CARR1 & _); exact CARR1) | nm 6 ltac:(exact CCL) | nm 7 ltac:(exact CCF)
          | nm 8 ltac:(exists (up, U, dlen); split; [exact INU| split; reflexivity])
          | nm 9 ltac:(exact UARR1) | nm 10 ltac:(exact LDZ)
          | nm 11 ltac:(rewrite bridge_tin; lia) | nm 12 ltac:(lia) | nm 13 ltac:(rewrite bridge_tin; lia) | nm 14 ltac:(lia)
          | nm 15 ltac:(lia) | nm 16 ltac:(lia) | nm 17 ltac:(lia) | nm 18 ltac:(lia)
          | nm 19 ltac:(rewrite bridge_tout; lia) | nm 20 ltac:(rewrite bridge_tout; lia) | nm 21 ltac:(exact CU)
          | nm 22 ltac:(repeat split; try lia; clear - SP16 RSP; Z.div_mod_to_equations; lia)
          | nm 23 ltac:(lia) | nm 24 ltac:(exact SPM) | nm 25 ltac:(exact FRM) | nm 26 ltac:(reflexivity) | nm 27 ltac:(reflexivity) ]. }
      cbv beta. intros r s' ms' PO. unfold inflate_postG in PO.
      destruct PO as (u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F' & fc' & m' & p1' & p2' & Aw' & ni' & PO).
      unfold i_okG, i_windowG in PO. fold WG in PO.
      set (ok := if WG then match r with Some _ => true | None => false end else true) in *.
      set (w' := if WG then r else w) in *.
      replace (zlength (u2_rest zc x)) with (slen - u2_tin x) in PO by lia.
      rewrite (bridge_inflate comprc slen x (dlen - u2_tout x) ok) in PO by lia. rewrite ESRC in PO.
      pose proof (u2_trip dlen src x ok NB SB UX) as TR. cbv zeta in TR.
      pose proof (u2_trip_buf dlen src x ok NB SB UX) as TRB.
      destruct (ic_inflate zc (zdrop (u2_tin x) src) (u2_is zc x) (dlen - u2_tout x) ok) as [[[is' consumed] bs] rc] eqn:EINF.
      cbv zeta in PO. destruct PO as (-> & LPE & AWE & -> & PUB' & NIE & ZR' & UARR').
      destruct TR as (BSR & TO64' & RCR & KOK & KNZ & _).
      assert (BS0 : 0 <= zlength bs) by (unfold zlength; lia).
      assert (HX2 : forall a', rin_ivs [(SS, SS + ZS_SIZEOF); (U + u2_tout x, U + u2_tout x + (dlen - u2_tout x))] a' ->
                               (SS <= a' < SS + ZS_SIZEOF) \/ (U <= a' < U + dlen)) by (clear - TO64; intros a' Ha'; cbn [rin_ivs fst snd] in Ha'; unfold ZS_SIZEOF in *; lia).
      pose proof (einv_step _ _ _ _ _ _ _ _ _ EI1 HX2 LPE) as EI'.
      pose proof EI' as ((errv' & ENV') & _). pose proof ENV' as (HP' & _ & _ & _ & _ & _ & _ & _ & ST' & _ & _ & _ & _ & MI'). rewrite E176 in ST'.
      set (x' := u2_next x src dlen is' consumed bs) in *.
      assert (DST' : destc (u2_orev zc x') = zstore (destc (u2_orev zc x)) (u2_tout x) bs).
      { subst x'. unfold u2_next. cbn [u2_orev]. rewrite TOUT. apply destc_step. unfold zlength in *. lia. }
      assert (INVw : IINVw m' s' fc' x' w' Aw').
      { unfold IINVw. split; [exact EI'|].
        split. { exists ni', (U + u2_tout x + zlength bs), p1', p2'.
                 subst x'. unfold u2_next, u2_tin, u2_tout. cbn [u2_is u2_aout u2_ain]. unfold u2_tout in PUB'.
                 first [ exact PUB' | (rewrite NF3; exact PUB')
                       | (replace slen with (zlength src) in PUB' by exact NF3; exact PUB') ]. }
        split; [subst x'; unfold u2_next; cbn [u2_is]; exact ZR'|].
        rewrite DST'. exact UARR'. }
      assert (OREV' : zlength (u2_orev zc x') <= dlen) by (subst x'; unfold u2_next; cbn [u2_orev]; rewrite rev_append_rev', zlength_app', zlength_rev'; lia).
      pose proof (munch_refl ([] : list (Z * Z)) m') as MU0. pose proof (wmono_refl psegs m') as WM0.
      cbv beta delta [MallocRep.wz].
      destruct (u2_stepP zc ok x) as [x1'|[[x1' err]|]] eqn:EST.
      -
        destruct (KOK x1' eq_refl) as (EX1 & RC0 & CONS & UI'). subst rc.
        assert (OKT : ok = true).
        { subst ok. destruct WG eqn:EWG; [| reflexivity]. destruct r; [reflexivity|]. exfalso.
          pose proof (u2_wants_bridge dlen src x comprc slen w NB SB UX ESRC NF3 ltac:(lia)) as EWB. fold WG in EWB. rewrite EWG in EWB.
          apply andb_true_iff in EWB. destruct EWB as [HW _].
          destruct (u2_refused dlen src x NB SB NF4 UX HW) as [x2 E2].
          lazymatch type of EST with ?lhs = _ => change lhs with (u2_stepP zc false x) in EST end. rewrite E2 in EST. discriminate EST. }
        pose proof (UI' OKT) as UX'. rewrite EX1 in *. clear EX1.
        pose proof (U2I_shape dlen src x' UX') as SH'. cbv zeta in SH'. destruct SH' as (_ & _ & _ & TOUT' & SUM' & _ & _ & _ & _ & _ & AOUT0' & LEFT0' & _).
        assert (ETO' : u2_tout x' = u2_tout x + zlength bs).
        { rewrite TOUT'. subst x'. unfold u2_next. cbn [u2_orev]. rewrite rev_append_rev', zlength_app', zlength_rev'. lia. }
        assert (INV' : IINV m' s' fc' x' w' Aw').
        { unfold IINV. split; [exact EI'|].
          split. { exists p1', p2'. rewrite (NIE eq_refl) in PUB'.
                   replace (U + u2_tout x') with (U + u2_tout x + zlength bs) by lia.
                   subst x'. unfold u2_next, u2_tin, u2_tout in PUB' |- *. cbn [u2_is u2_aout u2_ain] in PUB' |- *. rewrite NF3. exact PUB'. }
          split; [subst x'; unfold u2_next; cbn [u2_is]; exact ZR'|].
          rewrite DST'. exact UARR'. }
        change (wint Z_OK) with (Z_to_bv 64 0).
        unfold zs_pub in PUB'. cbv beta delta [MallocRep.wz] in PUB'.
        assert (AGN : forall (y1 z0 z1 z2 w0 w1 w2 w3 w4 w5 w6 w7 z3 z4 z5 z6 : word),
                  implM psegs (mbind (u2_loopM lops zc f x' w') K) s' POSTQ
                        (MS (mkR y1 (Z_to_bv 64 SP_) gp tp z0 z1 z2 (Z_to_bv 64 PL) (Z_to_bv 64 PS) w0 w1 w2 w3 w4 w5 w6 w7
                                 (Z_to_bv 64 4294967295) (Z_to_bv 64 0) (Z_to_bv 64 0) S5 S6 S7 S8 S9 S10 S11 z3 z4 z5 z6)
                            F' (Z_to_bv 64 0x1ce24) fc' None m' (seg_rom psegs))).
        { intros. unfold implM. iprefix. zstep. zstep. if_cases KAO; rewrite sx32_small in KAO by lia; zify_cond KAO; rewrite ?unsigned_lit in KAO by lia.
          *
            eapply evt_eq; [| apply evt_done; apply (IH x' w' Aw' s'); [exact UX'| exact INV']].
            unfold head_pc. replace (u2_aout zc x' =? 0) with false by (symmetry; apply Z.eqb_neq; subst x'; unfold u2_next; cbn [u2_aout]; lia).
            subst x'. unfold u2_next. cbn [u2_left u2_len]. reflexivity.
          *
            zstep.
            eapply evt_eq; [| apply evt_done; apply (IH x' w' Aw' s'); [exact UX'| exact INV']].
            unfold head_pc. replace (u2_aout zc x' =? 0) with true by (symmetry; apply Z.eqb_eq; subst x'; unfold u2_next; cbn [u2_aout]; lia).
            subst x'. unfold u2_next. cbn [u2_left u2_len]. reflexivity. }
        destruct RET as [-> | ->].
        + replace (ret_pc (Z_to_bv 64 0x1cddc)) with (Z_to_bv 64 0x1cddc) by (symmetry; rpc). unfold implM. iprefix. zstep. apply evt_done. apply AGN.
        + replace (ret_pc (Z_to_bv 64 0x1ce20)) with (Z_to_bv 64 0x1ce20) by (symmetry; rpc). unfold implM. iprefix. zstep. apply evt_done. apply AGN.
      -
        destruct (KNZ x1' err eq_refl) as (EX1 & -> & RCNZ). rewrite EX1 in *. clear EX1.
        assert (NZ : bv_unsigned (wint rc) <> 0) by (intros Hz; apply RCNZ; apply (wint_zero rc RCR); exact Hz).
        (* 1.4's *destLen is dlen - (left + avail_out): u2_next leaves left 0 and avail_out = dlen - tout - |bs| *)
        assert (EL' : u2_left zc x' = 0) by (subst x'; unfold u2_next; cbn [u2_left]; reflexivity).
        assert (EA' : 0 <= u2_aout zc x' <= dlen) by (subst x'; unfold u2_next; cbn [u2_aout]; unfold zlength in *; lia).
        assert (EN' : u2_len zc x' = 0) by (subst x'; unfold u2_next; cbn [u2_len]; reflexivity).
        assert (AIR' : rc = Z_BUF_ERROR -> 0 <= u2_ain zc x' < 2^32).
        { intros EB. pose proof (TRB EB) as CB. pose proof (U2I_shape dlen src x UX) as SH0. cbv zeta in SH0.
          destruct SH0 as (TINX & _). subst x'. unfold u2_next. cbn [u2_ain]. lia. }
        apply implM_retb.
        destruct RET as [-> | ->].
        + replace (ret_pc (Z_to_bv 64 0x1cddc)) with (Z_to_bv 64 0x1cddc) by (symmetry; rpc).
          unfold implM. iprefix. zstep. if_cases KRC; zify_cond KRC; [exfalso; apply NZ; exact KRC|]. zstep. apply evt_done.
          apply (KEND x' rc w' Aw' s'); [exact INVw| exact OREV'| exact TO64'| exact RCR| exact RCNZ| exact EL'| exact EA'| exact EN'| exact AIR'].
        + replace (ret_pc (Z_to_bv 64 0x1ce20)) with (Z_to_bv 64 0x1ce20) by (symmetry; rpc).
          unfold implM. iprefix. zstep. if_cases KRC; zify_cond KRC; [| exfalso; apply NZ; exact KRC]. apply evt_done.
          apply (KEND x' rc w' Aw' s'); [exact INVw| exact OREV'| exact TO64'| exact RCR| exact RCNZ| exact EL'| exact EA'| exact EN'| exact AIR'].
      -
        unfold implM. rewrite mbind_munr. apply impl_ret_unr.
    Qed.

    Lemma stream_raw : forall m cs, rw_cells psegs m SS cs -> cells_size cs = 112%nat -> exists js, rw_cells psegs m SS [CB 112 js].
    Proof.
      intros m cs H Hs. exists (cells_bytes cs). pose proof H as [[WF _] _].
      eapply rw_cells_recast; [exact H| |]. { cbn [cells_wf cell_wf]. split; [| exact I]. rewrite (cells_bytes_length cs WF). exact Hs. }
      cbn [cells_bytes cbytes]. rewrite app_nil_r. reflexivity.
    Qed.

    Lemma frame_join : forall m (js : list byte), rw_cells psegs m SS [CB 112 js] -> FRHI m ->
      rw_cells psegs m SP_ [CB 112 js; C8 S4; C8 S3; C8 S2; C8 S1; C8 S0; C8 ra].
    Proof.
      intros m js FS FH.
      change [CB 112 js; C8 S4; C8 S3; C8 S2; C8 S1; C8 S0; C8 ra] with ([CB 112 js] ++ [C8 S4; C8 S3; C8 S2; C8 S1; C8 S0; C8 ra]).
      apply (proj2 (rw_cells_app psegs _ _ _ _)). split; [exact FS|]. cbn [cells_size csize Nat.add].
      eapply rw_cells_addr_eq; [exact FH| lia].
    Qed.

    (* 1.4 epilogue at 0x1ce1c: 6 loads (ra, s0..s4), add sp, ret; s5 is not saved, so it is S5 already *)
    Lemma u2_epilogue : forall (Q : machine_state -> Prop) m (js : list byte) (x1 t0 t1 t2 x8 x9 a0v a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
      FRLO m -> rw_cells psegs m SS [CB 112 js] -> FRHI m -> stk psegs m lo SP_ -> mem_inv psegs m ->
      (forall (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word), stk psegs m lo usp ->
         Q (MS (mkR ra sp gp tp t0' t1' t2' S0 S1 a0v a1' a2' a3' a4' a5' a6' a7' S2 S3 S4 S5 S6 S7 S8 S9 S10 S11 t3' t4' t5' t6') F (ret_pc ra) fc None m (seg_rom psegs))) ->
      evt psegs Q (MS (mkR x1 (Z_to_bv 64 SP_) gp tp t0 t1 t2 x8 x9 a0v a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 S5 S6 S7 S8 S9 S10 S11 t3 t4 t5 t6)
                      F (Z_to_bv 64 0x1ce90) fc None m (seg_rom psegs)).
    Proof.
      intros until fc. intros _ FS FH ST MI KK.
      pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
      unfold ZC_WRAP_STACK, Z_INFLATE_STACK, RMALLOC_STACK, GLOBALS_TOP in LOSP, LOG.
      pose proof (frame_join m js FS FH) as FR. unfold FRHI in FH.
      pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl psegs m) as WM.
      do 6 zstep. release_frame FR ST (bv_unsigned sp). zstep. zstep.
      apply evt_done. apply KK. exact ST.
    Qed.

    Definition KONT (r : u2L zc * Z * option bptr) : M PState (list Z * Z * Z) :=
      let '(xe, w) := r in let '(x, err) := xe in let '(out, tout, rc) := u2_result zc dlen x err in
      mbind (Target.lib_free_opt raw_free w) (fun _ => mbind (Target.lib_free_opt raw_free (Some pst)) (fun _ => mret (out, tout, rc))).

    Notation POST := (runcompress2_post ra sp gp tp S0 S1 S2 S3 S4 S5 S6 S7 S8 S9 S10 S11 s0 LB U dlen PL PS uc lo B canary m0).

    Lemma u2_end : forall x' err w Aw s (x1 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) F fc m,
      IINVw m s fc x' w Aw -> zlength (u2_orev zc x') <= dlen -> 0 <= u2_tout x' < 2^64 ->
      - 2^31 <= err < 2^31 -> err <> Z_OK ->
      u2_left zc x' = 0 -> 0 <= u2_aout zc x' <= dlen ->
      u2_len zc x' = 0 -> (err = Z_BUF_ERROR -> 0 <= u2_ain zc x' < 2^32) ->
      implM psegs (KONT (x', err, w)) s POST (HDS (wz 0x1ce30) x1 t0 t1 t2 (wint err) a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 0 0 F fc m).
    Proof.
      destruct ZOK as (_ & _ & _ & _ & _ & IEND).
      intros until m. intros (EI & (ni & no & p1 & p2 & PUB) & ZR & UARR) OREV TO64 RCR RCNZ EL' EA' EN' AIR'.
      pose proof EI as ((errv & ENV) & FRL & FRH & CARR & PLC & PSC & PRES & ESO & EFA & FRM).
      pose proof ENV as (HP & _ & _ & _ & _ & _ & _ & _ & ST & _ & _ & _ & _ & MI).
      pose proof N_facts as (NF1 & NF2 & NF3 & NF4 & NF5).
      pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
      pose proof CR as (C0 & _ & _ & CC & CI). pose proof UR as (U0 & _ & _ & UC & UI).
      unfold ZC_WRAP_STACK, Z_INFLATE_STACK, RMALLOC_STACK, GLOBALS_TOP in LOSP, LOG.
      assert (E176 : bv_unsigned (Z_to_bv 64 SP_) = SP_) by (apply unsigned_lit; lia). rewrite E176 in ST.
      assert (SPM : SP_ mod 16 = 0) by (clear - SP16 RSP; Z.div_mod_to_equations; lia).
      pose proof (iblocks_LBZR _ _ _ _ HP) as LBZR.
      pose proof (destc_len (u2_orev zc x') OREV) as [LD LDZ].
      cbn [KONT]. unfold u2_result.
      unfold zs_pub in PUB. cbv beta delta [MallocRep.wz] in PUB, PLC, PSC |- *.
      apply box in ZR. apply box in UARR. apply box in CARR. apply box in PRES.
      pose proof (munch_refl [(PS, PS + 8); (PL, PL + 8)] m) as MU. pose proof (wmono_refl psegs m) as WM.
      unfold implM. iprefix.

      (* 1.4 tail at 0x1ce1c: lwu a1,8(sp); ld a2,0(s1); lwu a3,32(sp); add s3,s3,a1; sub a1,a2,s3; sd a1,0(s1)
         [ *sourceLen -= len + avail_in ]; ld a1,0(s0); add a3,s4,a3; sub a1,a1,a3; sd a1,0(s0) [ *destLen -= left +
         avail_out ]; mv s0,a0; mv a0,sp; jal inflateEnd *)
      zstep. zstep. zstep. zstep. zstep. zs.
      zstep. zstep. zstep. zs.
      zstep. zstep. zstep.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m5 end.
      pose proof (agree_on_of_munch _ _ _ MU WM) as AG5.
      assert (OUTW : forall a, ~ (PS <= a < PS + 8) -> ~ (PL <= a < PL + 8) -> outside [(PS, PS + 8); (PL, PL + 8)] a) by (intros a H1 H2; cbn [outside]; lia).
      assert (ENV5 : lx_env m5 s (iblocks w Aw pst As) LB (Z_to_bv 64 SP_) tp B lo errv canary).
      { eapply (lx_env_munch [(PS, PS + 8); (PL, PL + 8)] m m5); [exact HFRAME| exact ENV| exact MU| exact WM| assumption| rewrite E176; assumption| rewrite E176; lia| |].
        - constructor; [left; cbn [fst]; lia|]. constructor; [left; cbn [fst]; lia| constructor].
        - intros a Ha. apply OUTW; clear - Ha PLHI PSHI PLLO PSLO LOG LOSP RSP; lia. }
      assert (ZR5 : zr_i R m5 SS (iblocks w Aw pst As) (u2_is zc x')).
      { eapply (zr_i_frame R); [exact (unbox _ ZR)|]. intros a Ha Hin. apply (AG5 a Ha). apply OUTW.
        - destruct Hin as [Hin|(b & Hb & Hr)]; [unfold ZS_PUB, ZS_SIZEOF in *; lia|]. destruct (LBZR b Hb) as (_ & _ & _ & BC & _). lia.
        - destruct Hin as [Hin|(b & Hb & Hr)]; [unfold ZS_PUB, ZS_SIZEOF in *; lia|]. destruct (LBZR b Hb) as (_ & _ & _ & BC & _). lia. }
      lazymatch goal with H : rw_cells psegs m5 SS _ |- _ => rename H into PUB5 end.
      lazymatch goal with H : rw_cells psegs m5 PL _ |- _ => rename H into PLC5 end.
      lazymatch goal with H : rw_cells psegs m5 PS _ |- _ => rename H into PSC5 end.
      assert (FRH5 : FRHI m5) by (unfold FRHI in *; eapply rw_cells_agree; [exact AG5| exact FRH| intros a Ha; cbn in Ha; apply OUTW; lia]).
      assert (UARR5 : u8arr psegs m5 U (to_bytes (destc (u2_orev zc x')))).
      { eapply u8arr_agree; [exact AG5| exact (unbox _ UARR)|]. intros a Ha. rewrite LD in Ha. apply OUTW; lia. }
      assert (PRES5 : lx_pres LB usp XX m0 m5).
      { eapply lx_pres_trans; [exact (unbox _ PRES)|]. eapply pres_munch; [exact MU| exact WM|]. intros a _ HX. apply OUTW; intros Hc; apply HX; cbn [rin_ivs fst snd]; lia. }
      clear AG5 MU WM.
      apply evt_done.
      lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM psegs tm s POST msx) end.
      eapply implM_bind2.
      { eapply IEND with (S := SS) (is := u2_is zc x') (w := w) (Aw := Aw) (sp_ := pst) (As := As) (lo := lo) (B := B) (errv := errv) (canary := canary);
          unfold strm_in_frame, Z_INFLATEEND_STACK, RFREE_STACK, ZS_SIZEOF; rewrite ?E176;
          [ exact ENV5 | unfold zs_pub; cbv beta delta [MallocRep.wz]; exact PUB5 | exact ZR5
          | repeat split; try lia; clear - SP16 RSP; Z.div_mod_to_equations; lia
          | lia | exact SPM | exact FRM | reflexivity ]. }
      cbv beta. intros [] s6 ms6 PO6. unfold inflateEnd_postX in PO6.
      destruct PO6 as (v0 & v1 & v2 & c0 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & v3 & v4 & v5 & v6 & F6 & fc6 & m6 & -> & ((errv6 & ENV6) & FRM6 & LXP6 & ESO6 & EFA6) & -> & (js & STR6)).
      replace (ret_pc (Z_to_bv 64 0x1ce64)) with (Z_to_bv 64 0x1ce64) by (symmetry; rpc).
      rewrite E176 in LXP6. pose proof (agree_of_lx_pres _ _ _ _ _ LXP6) as AG6.
      pose proof ENV6 as (_ & _ & _ & _ & _ & _ & _ & _ & ST6 & _ & _ & _ & _ & MI6). rewrite E176 in ST6.
      assert (NX6 : forall a, ~ (SS <= a < SS + ZS_SIZEOF) -> ~ rin_ivs [(SS, SS + ZS_SIZEOF)] a) by (clear; intros a Ha Hi; cbn [rin_ivs fst snd] in Hi; tauto).
      assert (FRH6 : FRHI m6) by (unfold FRHI in *; eapply (cells_lx _ _ _ _ _ LXP6 FRH5); intros a Ha; cbn in Ha; apply stack_client; [lia| apply NX6; unfold ZS_SIZEOF; lia]).
      lazymatch type of PLC5 with rw_cells _ _ _ [C8 ?v] =>
        assert (PLC6 : rw_cells psegs m6 PL [C8 v]) by (eapply (cells_lx _ _ _ _ _ LXP6 PLC5); intros a Ha; cbn in Ha; apply stack_client; [lia| apply NX6; unfold ZS_SIZEOF; lia]) end.
      lazymatch type of PSC5 with rw_cells _ _ _ [C8 ?v] =>
        assert (PSC6 : rw_cells psegs m6 PS [C8 v]) by (eapply (cells_lx _ _ _ _ _ LXP6 PSC5); intros a Ha; cbn in Ha; apply stack_client; [lia| apply NX6; unfold ZS_SIZEOF; lia]) end.
      assert (UARR6 : u8arr psegs m6 U (to_bytes (destc (u2_orev zc x')))).
      { eapply u8arr_agree; [exact AG6| exact UARR5|]. intros a Ha. rewrite LD in Ha.
        eapply block_client; [exact INU| cbn [blk_addr blk_size fst snd]; lia| apply NX6; unfold ZS_SIZEOF; lia]. }
      assert (PRES6 : lx_pres LB usp XX m0 m6).
      { eapply lx_pres_trans; [exact PRES5|]. eapply lx_pres_sub; [exact LXP6|]. intros a Ha. apply (client_inner _ a); [| exact Ha].
        intros a' Ha'. cbn [rin_ivs fst snd] in Ha'. left. lia. }
      destruct (stream_raw m6 _ STR6 ltac:(reflexivity)) as [js6 STR6r].

      (* road (ii), C1: KONT returns u2_result's triple, so the machine's a0 is wint (u2_rc zc err x'). *)
      assert (FIN : forall (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word), stk psegs m6 lo usp ->
                POST (rev_append (u2_orev zc x') [], dlen - (u2_left zc x' + u2_aout zc x'), u2_rc zc err x') s6
                     (MS (mkR ra sp gp tp t0' t1' t2' S0 S1 (wint (u2_rc zc err x')) a1' a2' a3' a4' a5' a6' a7' S2 S3 S4 S5 S6 S7 S8 S9 S10 S11 t3' t4' t5' t6') F6 (ret_pc ra) fc6 None m6 (seg_rom psegs))).
      { intros. unfold runcompress2_post.
        lazymatch type of PSC6 with rw_cells _ _ _ [C8 ?v] =>
          do 15 eexists; exists F6, fc6, m6, (u2_rc zc err x'), (bv_unsigned v) end.
        split; [reflexivity|].
        split. { unfold lx_post_env. split; [exists errv6; eapply lx_env_sp; [exact ENV6| assumption| exact SPB]|]. split; [exact FRM6|].
                 split; [exact PRES6|]. split; [rewrite ESO6; exact ESO| rewrite EFA6; exact EFA]. }
        split; [reflexivity|]. split; [reflexivity|].
        split; [unfold u2_rc; repeat match goal with |- context [if ?b then _ else _] => destruct b end;
                first [change Z_OK with 0; lia | change Z_DATA_ERROR with (-3); lia | lia]|].
        cbn [fst snd]. split. { rewrite rev_append_rev', app_nil_r. rewrite zstore0_app by (rewrite length_rev; unfold zlength in *; lia). rewrite length_rev.
                                unfold destc in UARR6. exact UARR6. }
        split; [rewrite rev_append_rev', app_nil_r, zlength_rev'; exact OREV|]. split; [lia|].
        (* 1.4 stores dlen - (left + avail_out) (zl14cmp-r2's u2_result length); the loaded avail_out is a 32-bit read *)
        split; [| unfold MallocRep.wz; rewrite Z_to_bv_bv_unsigned; exact PSC6].
        (* the 64-bit mask is already gone from PLC6 here: only avail_out's 32-bit read is left *)
        rewrite !Z.mod_small in PLC6 by lia. rewrite EL'.
        replace (dlen - (0 + u2_aout zc x')) with (dlen + - (0 + u2_aout zc x')) by lia. exact PLC6. }
      unfold zs_pub in STR6. cbn [app] in STR6. cbv beta delta [MallocRep.wz] in STR6.
      pose proof (munch_refl ([] : list (Z * Z)) m6) as MU6. pose proof (wmono_refl psegs m6) as WM6.
      change (wint Z_OK) with (Z_to_bv 64 0).
      apply implM_ret.

      (* 1.4 at 0x1ce50: li a1,1; beq s0,a1 -> 0x1ce18 (li a0,0); mv a0,s0; li a1,2; beq s0,a1 -> 0x1ce10;
         xor a1,a0,-5; or a1,a1,s3; bnez a1 -> 0x1ce1c (return err); 0x1ce10: li a0,-3; j 0x1ce1c. The post leaves the
         return code free, so every branch ends in the epilogue with FIN. *)
      (* road (ii), k3: each branch's a0 is rewritten to wint (u2_rc zc err x'); the side goal closes from the branch
         condition (K1 / K2 / K3), the int range of err (wint_cases) and the two KEND facts EN' (u2_len = 0) and AIR'
         (on Z_BUF_ERROR the avail_in cell, u2_ain zc x', is in [0, 2^32): u2_trip_buf). *)
      pose proof (wint_cases err RCR) as WC.
      zstep. zstep. if_cases K1.
      - zstep. eapply u2_epilogue; [exact I| exact STR6r| exact FRH6| exact ST6| exact MI6|]. intros.
        lazymatch goal with |- context [mkR ra sp gp tp _ _ _ S0 S1 ?av _ _ _ _ _ _ _ S2] =>
          replace av with (wint (u2_rc zc err x')); [apply FIN; assumption|] end.
        unfold bv_eqb in K1. apply Z.eqb_eq in K1. rewrite (unsigned_lit 1) in K1 by lia.
        assert (E1 : err = Z_STREAM_END) by (unfold Z_STREAM_END; destruct WC as [[WS WQ]|[WS WQ]]; lia).
        subst err. apply bv_eq. vm_compute. reflexivity.
      - zstep. zstep. zstep. if_cases K2.
        + zstep. zstep. eapply u2_epilogue; [exact I| exact STR6r| exact FRH6| exact ST6| exact MI6|]. intros.
          lazymatch goal with |- context [mkR ra sp gp tp _ _ _ S0 S1 ?av _ _ _ _ _ _ _ S2] =>
            replace av with (wint (u2_rc zc err x')); [apply FIN; assumption|] end.
          unfold bv_eqb in K1, K2. apply Z.eqb_neq in K1. apply Z.eqb_eq in K2.
          rewrite (unsigned_lit 1) in K1 by lia. rewrite (unsigned_lit 2) in K2 by lia.
          assert (E2 : err = Z_NEED_DICT) by (unfold Z_NEED_DICT; destruct WC as [[WS WQ]|[WS WQ]]; lia).
          subst err. apply bv_eq. vm_compute. reflexivity.
        + zstep. zstep. zstep. if_cases K3.
          * eapply u2_epilogue; [exact I| exact STR6r| exact FRH6| exact ST6| exact MI6|]. intros.
            lazymatch goal with |- context [mkR ra sp gp tp _ _ _ S0 S1 ?av _ _ _ _ _ _ _ S2] =>
              replace av with (wint (u2_rc zc err x')); [apply FIN; assumption|] end.
            unfold bv_eqb in K1, K2. apply Z.eqb_neq in K1. apply Z.eqb_neq in K2.
            rewrite (unsigned_lit 1) in K1 by lia. rewrite (unsigned_lit 2) in K2 by lia.
            f_equal. unfold u2_rc.
            match goal with |- context [if ?b then _ else _] => destruct b eqn:Q1 end.
            { exfalso. apply Z.eqb_eq in Q1. vm_compute in Q1. destruct WC as [[WS WQ]|[WS WQ]]; lia. }
            match goal with |- context [if ?b then _ else _] => destruct b eqn:Q2 end.
            { exfalso. apply Z.eqb_eq in Q2. vm_compute in Q2. destruct WC as [[WS WQ]|[WS WQ]]; lia. }
            match goal with |- context [if ?b then _ else _] => destruct b eqn:Q3 end; [| reflexivity].
            exfalso. apply andb_true_iff in Q3. destruct Q3 as [Q3a Q3b]. apply Z.eqb_eq in Q3a. apply Z.eqb_eq in Q3b.
            assert (AZ : u2_ain zc x' = 0) by lia.
            subst err.
            lazymatch type of K3 with context [Z.land ?a 18446744073709551615] =>
              replace a with 0 in K3 by (symmetry; exact AZ) end.
            vm_compute in K3. discriminate K3.
          * zstep. zstep. eapply u2_epilogue; [exact I| exact STR6r| exact FRH6| exact ST6| exact MI6|]. intros.
            lazymatch goal with |- context [mkR ra sp gp tp _ _ _ S0 S1 ?av _ _ _ _ _ _ _ S2] =>
              replace av with (wint (u2_rc zc err x')); [apply FIN; assumption|] end.
            unfold bv_eqb in K1, K2. apply Z.eqb_neq in K1. apply Z.eqb_neq in K2.
            rewrite (unsigned_lit 1) in K1 by lia. rewrite (unsigned_lit 2) in K2 by lia.
            apply Bool.negb_false_iff in K3. unfold bv_eqb in K3. apply Z.eqb_eq in K3.
            replace (bv_unsigned z64) with 0 in K3 by (vm_compute; reflexivity).
            lazymatch type of K3 with
            | bv_unsigned (Z_to_bv 64 (Z.lor (Z.lxor ?u ?c) (0 + Z.land ?a 18446744073709551615 mod 4294967296))) = 0 =>
                assert (UR6 : 0 <= u < 2^64) by (destruct WC as [[WS WQ]|[WS WQ]]; lia);
                assert (YR6 : 0 <= Z.land a 18446744073709551615 mod 4294967296 < 4294967296) by (apply Z.mod_pos_bound; lia);
                rewrite (unsigned_lit (Z.lor (Z.lxor u c) (0 + Z.land a 18446744073709551615 mod 4294967296))) in K3
                  by (first [ (apply zr_lor; [apply zr_lxor; unfold inr64; lia| unfold inr64; lia]) | zrange ]);
                apply zb_lor_eq0 in K3; destruct K3 as [KX KY]; apply zb_lxor_eq0 in KX;
                assert (EB : err = Z_BUF_ERROR) by (unfold Z_BUF_ERROR; destruct WC as [[WS WQ]|[WS WQ]];
                  rewrite ?Z.lxor_0_r in KX; rewrite ?zb_lxor_eq0 in KX;
                  first [ lia | (match type of KX with ?t => idtac "K3-B4 SHAPE: EB KX" t end; fail) ]);
                destruct (AIR' EB) as [AI0 AI1];
                assert (LA6 : Z.land a 18446744073709551615 = a)
                  by (change 18446744073709551615 with (Z.ones 64); rewrite Z.land_ones by lia; apply Z.mod_small; lia);
                rewrite LA6, Z.mod_small in KY by lia;
                assert (AZ : u2_ain zc x' = 0) by lia;
                subst err; unfold u2_rc; rewrite EN', AZ; apply bv_eq; vm_compute; reflexivity
            | _ => let t := type of K3 in idtac "K3-B4 SHAPE:" t; fail 100 "B4 shape"
            end.
    Qed.
  End Inv.

  Lemma frame_recast : forall m (jp jm js ja jf jo jr j4 j3 j2 j1 jz jra : list byte),
    rw_cells psegs m SP_ [CB 48 jp; CB 8 jm; CB 8 js; CB 8 ja; CB 8 jf; CB 8 jo; CB 24 jr; CB 8 j4; CB 8 j3; CB 8 j2; CB 8 j1; CB 8 jz; CB 8 jra] ->
    exists ni ai ti no ao to q1 q2 (jmsg jstate : word),
      rw_cells psegs m SP_ [C8 (Z_to_bv 64 ni); C4 (Z_to_bv 64 ai); CB 4 q1; C8 (Z_to_bv 64 ti); C8 (Z_to_bv 64 no); C4 (Z_to_bv 64 ao); CB 4 q2; C8 (Z_to_bv 64 to);
                           C8 jmsg; C8 jstate; CB 8 ja; CB 8 jf; CB 8 jo; CB 24 jr; CB 8 j4; CB 8 j3; CB 8 j2; CB 8 j1; CB 8 jz; CB 8 jra].
  Proof.
    intros until jra. intros FR.
    pose proof FR as [[WF _] _]. cbn [cells_wf cell_wf] in WF. destruct WF as (L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8 & L9 & L10 & L11 & L12 & L13 & _).
    destruct (zs_pub_of_bytes _ L1) as (ni & ai & ti & no & ao & to & q1 & q2 & EB & WFP & _).
    destruct (le8_of_bytes _ L2) as (zmsg & _ & Emsg). destruct (le8_of_bytes _ L3) as (zst & _ & Est).
    exists ni, ai, ti, no, ao, to, q1, q2, (Z_to_bv 64 zmsg), (Z_to_bv 64 zst).
    unfold zs_pub, MallocRep.wz in EB, WFP. cbn [cells_wf cell_wf] in WFP. destruct WFP as (_ & _ & Q1 & _ & _ & _ & Q2 & _).
    eapply rw_cells_recast; [exact FR| |].
    - cbn [cells_wf cell_wf]. repeat split; assumption.
    - cbn [cells_bytes cbytes] in EB |- *. rewrite <- EB, Emsg, Est. rewrite <- !app_assoc. reflexivity.
  Qed.

  Lemma frame_split3 : forall m (q1 q2 jr : list byte) (ti no ao to : Z) (jmsg jstate : word),
    rw_cells psegs m SP_ [C8 (Z_to_bv 64 C); C4 (Z_to_bv 64 0); CB 4 q1; C8 (Z_to_bv 64 ti); C8 (Z_to_bv 64 no); C4 (Z_to_bv 64 ao); CB 4 q2; C8 (Z_to_bv 64 to);
                         C8 jmsg; C8 jstate; C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); CB 24 jr; C8 S4; C8 S3; C8 S2; C8 S1; C8 S0; C8 ra] ->
    rw_cells psegs m SS (zs_pub C 0 ti no ao to q1 q2 ++ [C8 jmsg; C8 jstate; C8 (wz 0); C8 (wz 0); C8 (wz 0); CB 24 jr])
    /\ FRHI m.
  Proof.
    intros until jstate. intros FR.
    apply (proj1 (rw_cells_app psegs _ _ [_;_;_;_;_;_;_;_;_;_;_;_;_;_] _)) in FR. destruct FR as [FRS FRH]. cbn [cells_size csize Nat.add] in FRH.
    split.
    - unfold zs_pub. cbn [app]. eapply rw_cells_addr_eq; [exact FRS| lia].
    - unfold FRHI. eapply rw_cells_addr_eq; [exact FRH| lia].
  Qed.

  Notation POSTC := (runcompress2_post ra sp gp tp S0 S1 S2 S3 S4 S5 S6 S7 S8 S9 S10 S11).

  Theorem u2_main : forall (t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m0 : mem) (s : PState) (errv : word),
    lx_env m0 s [] LB sp tp B lo errv canary ->
    u8arr psegs m0 U (to_bytes uc) -> rw_cells psegs m0 PL [C8 (wz dlen)] -> u8arr psegs m0 C (to_bytes comprc) -> rw_cells psegs m0 PS [C8 (wz slen)] -> frm0 fc ->
    implM psegs (uncompress2M lops zc dlen src) s (POSTC s LB U dlen PL PS uc lo B canary m0)
      (MS (mkR ra sp gp tp t0 t1 t2 S0 S1 (wz U) (wz PL) (wz C) (wz PS) a4 a5 a6 a7 S2 S3 S4 S5 S6 S7 S8 S9 S10 S11 t3 t4 t5 t6)
          F (wz ZC_UNCOMPRESS2) fc None m0 (seg_rom psegs)).
  Proof.
    intros until errv. intros ENV0 UARR0 PLC0 CARR0 PSC0 FRM.
    pose proof ENV0 as (HP0 & _ & _ & _ & _ & _ & _ & _ & ST0 & _ & _ & _ & _ & MI0). cbn [app] in HP0.
    pose proof N_facts as (NF1 & NF2 & NF3 & NF4 & NF5). pose proof N_factsB as [NB SB].
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    pose proof CR as (C0 & _ & _ & CC & CI). pose proof UR as (U0 & _ & _ & UC & UI).
    unfold ZC_WRAP_STACK, Z_INFLATE_STACK, RMALLOC_STACK, GLOBALS_TOP in LOSP, LOG.
    destruct ZOK as (_ & _ & _ & IINIT & _ & _).
    unfold uncompress2M. cbn [bind ret unreachable lib_malloc lib_free lops Target.ops]. rewrite <- bridge_isize.
    unfold ZC_UNCOMPRESS2. cbv beta delta [MallocRep.wz] in PLC0, PSC0 |- *.
    assert (LU0 : Z.of_nat (length (to_bytes uc)) = dlen) by (rewrite to_bytes_len; unfold zlength in UCL; lia).
    assert (LC0 : Z.of_nat (length (to_bytes comprc)) = cl) by (rewrite to_bytes_len; unfold zlength in CCL; lia).
    apply box in UARR0. apply box in CARR0.
    pose proof (munch_refl [(SP_, usp)] m0) as MU. pose proof (wmono_refl psegs m0) as WM.
    unfold implM. iprefix.
    zstep. carve_frame 160%nat ST0.
    apply (rw_cells_split_CB psegs _ _ [] 160 junk [] [48; 8; 8; 8; 8; 8; 24; 8; 8; 8; 8; 8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => destruct (frame_recast mx _ _ _ _ _ _ _ _ _ _ _ _ _ FR) as (ni & ai & ti & no & ao & to & q1 & q2 & jmsg & jstate & FR') end.
    clear FR. rename FR' into FR.

    (* 1.4: 6 saves; mv s2,a0; li a0,-2; beqz a3 (sourceLen = PS is not NULL); mv s0,a1; beqz a1 (destLen = PL is not NULL) *)
    do 6 zstep. zstep. zstep.
    zstep. if_cases KN1; zify_cond KN1; rewrite ?unsigned_lit in KN1 by lia; [exfalso; lia|].
    zstep.
    zstep. if_cases KN2; zify_cond KN2; rewrite ?unsigned_lit in KN2 by lia; [exfalso; lia|].
    (* mv s1,a3; ld s3,0(a3) (len := slen); snez a1,s3; seqz a3,a2; and a1,a3,a1; bnez a1 (source = C is not NULL) *)
    zstep. zstep. zstep. zstep. zstep.
    replace (C <? 1) with false by (symmetry; apply Z.ltb_ge; lia). cbn [Z.b2z Z.land].
    zstep. if_cases KN3; zify_cond KN3; rewrite ?unsigned_lit in KN3 by lia; [exfalso; lia|].
    (* ld s4,0(s0) (left := dlen; 1.4 does not zero *destLen); bnez s2 (dest = U is not NULL) *)
    zstep.
    zstep. if_cases KN4; zify_cond KN4; rewrite ?unsigned_lit in KN4 by lia; [|exfalso; lia].
    (* sd a2,0(sp); sw zero,8(sp); sd zero,64/72/80(sp); auipc; mv a0,sp; add a1; li a2,112; jal inflateInit_ *)
    zs. zs. zs. zs. zs.
    zstep. zstep. zstep. zstep. zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
    destruct (frame_split3 m1 _ _ _ _ _ _ _ _ _ FR) as (FRS1 & FRH1). clear FR.
    assert (SPM : SP_ mod 16 = 0) by (clear - SP16 RSP; Z.div_mod_to_equations; lia).
    assert (E176 : bv_unsigned (Z_to_bv 64 SP_) = SP_) by (apply unsigned_lit; lia).

    assert (ENV1 : lx_env m1 s [] LB (Z_to_bv 64 SP_) tp B lo errv canary).
    { eapply (lx_env_munch [(SP_, usp)] m0 m1); [exact HFRAME| exact ENV0| exact MU| exact WM| assumption| rewrite E176; assumption| rewrite E176; lia| |].
      - constructor; [left; cbn [fst]; lia| constructor].
      - intros a Ha. cbn [outside]. clear - Ha SPB PLHI PLLO LOG LOSP RSP. lia. }
    assert (PRES1 : lx_pres LB usp XX m0 m1).
    { eapply pres_munch; [exact MU| exact WM|]. intros a Ha HX. cbn [outside].
      split; [| exact I].
      destruct Ha as [Ha|[(b & Hb & Hr)|Ha]]; [lia| destruct (LBR b Hb) as (_ & _ & _ & BC & _); lia| lia]. }
    pose proof (agree_on_of_munch _ _ _ MU WM) as AG1.
    assert (UARR1 : u8arr psegs m1 U (to_bytes uc)) by (eapply u8arr_agree; [exact AG1| exact (unbox _ UARR0)| intros a Ha; rewrite LU0 in Ha; cbn [outside]; lia]).
    assert (CARR1 : u8arr psegs m1 C (to_bytes comprc)) by (eapply u8arr_agree; [exact AG1| exact (unbox _ CARR0)| intros a Ha; rewrite LC0 in Ha; cbn [outside]; lia]).
    first [ lazymatch goal with H : rw_cells psegs m1 PL _ |- _ => rename H into PLC1 end
          | assert (PLC1 : rw_cells psegs m1 PL [C8 (Z_to_bv 64 dlen)]) by (eapply rw_cells_agree; [exact AG1| exact PLC0| intros a Ha; cbn in Ha; cbn [outside]; lia]) ].
    first [ lazymatch goal with H : rw_cells psegs m1 PS _ |- _ => rename H into PSC1 end
          | assert (PSC1 : rw_cells psegs m1 PS [C8 (Z_to_bv 64 slen)]) by (eapply rw_cells_agree; [exact AG1| exact PSC0| intros a Ha; cbn in Ha; cbn [outside]; lia]) ].
    clear AG1 MU WM UARR0 CARR0.
    apply evt_done.
    lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM psegs tm s (POSTC s LB U dlen PL PS uc lo B canary m0) msx) end.
    eapply implM_bind.
    { eapply IINIT with (S := SS) (lo := lo) (B := B) (errv := errv) (canary := canary);
        [ exact ENV1 | exact FRS1
        | unfold strm_in_frame, ZS_SIZEOF; rewrite E176; repeat split; try lia; clear - SP16 RSP; Z.div_mod_to_equations; lia
        | rewrite E176; unfold Z_INFLATEINIT_STACK, RMALLOC_STACK; lia | rewrite E176; exact SPM | exact FRM
        | reflexivity | unfold A_ZVERSION; reflexivity | reflexivity ]. }
    cbv beta. intros r s2 ms2 PO. unfold inflateInit_post in PO.
    destruct PO as (u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F2 & fc2 & m2 & -> & PO).
    replace (ret_pc (Z_to_bv 64 0x1cda4)) with (Z_to_bv 64 0x1cda4) by (symmetry; rpc).
    assert (NX : forall a, ~ (SS <= a < SS + ZS_SIZEOF) -> ~ rin_ivs [(SS, SS + ZS_SIZEOF)] a) by (clear; intros a Ha Hi; cbn [rin_ivs fst snd] in Hi; tauto).
    destruct r as [p|].
    2:{
      destruct PO as (((errv2 & ENV2) & FRM2 & LXP2 & ESO2 & EFA2) & -> & (js & STR2)).
      rewrite E176 in LXP2. pose proof (agree_of_lx_pres _ _ _ _ _ LXP2) as AG2.
      pose proof ENV2 as (_ & _ & _ & _ & _ & _ & _ & _ & ST2 & _ & _ & _ & _ & MI2). rewrite E176 in ST2.
      assert (FRH2 : FRHI m2) by (unfold FRHI in *; eapply rw_cells_agree; [exact AG2| exact FRH1| intros a Ha; cbn in Ha; apply stack_client; [lia| apply NX; unfold ZS_SIZEOF; lia]]).
      assert (PLC2 : rw_cells psegs m2 PL [C8 (Z_to_bv 64 dlen)]) by (eapply rw_cells_agree; [exact AG2| exact PLC1| intros a Ha; cbn in Ha; apply stack_client; [lia| apply NX; unfold ZS_SIZEOF; lia]]).
      assert (PSC2 : rw_cells psegs m2 PS [C8 (Z_to_bv 64 slen)]) by (eapply rw_cells_agree; [exact AG2| exact PSC1| intros a Ha; cbn in Ha; apply stack_client; [lia| apply NX; unfold ZS_SIZEOF; lia]]).
      assert (UARR2 : u8arr psegs m2 U (to_bytes uc)).
      { eapply u8arr_agree; [exact AG2| exact UARR1|]. intros a Ha. rewrite LU0 in Ha.
        eapply block_client; [exact INU| cbn [blk_addr blk_size fst snd]; lia| apply NX; unfold ZS_SIZEOF; lia]. }
      change (wint Z_MEM_ERROR) with (Z_to_bv 64 18446744073709551612).
      apply implM_ret.
      pose proof (munch_refl ([] : list (Z * Z)) m2) as MU. pose proof (wmono_refl psegs m2) as WM.
      (* 1.4: bnez a0 -> 0x1ce1c (the epilogue) *)
      zstep.
      eapply u2_epilogue; [exact I| exact STR2| exact FRH2| exact ST2| exact MI2|]. intros. unfold runcompress2_post.
      do 15 eexists. exists F2, fc2, m2, Z_MEM_ERROR, slen. split; [reflexivity|].
      split.
      { unfold lx_post_env. split; [exists errv2; eapply lx_env_sp; [exact ENV2| assumption| exact SPB]|]. split; [exact FRM2|].
        split; [| split; [exact ESO2| exact EFA2]].
        eapply lx_pres_trans; [exact PRES1|]. eapply lx_pres_sub; [exact LXP2|]. intros a Ha. apply (client_inner _ a); [| exact Ha].
        intros a' Ha'. cbn [rin_ivs fst snd] in Ha'. left. lia. }
      split; [reflexivity|]. split; [reflexivity|].
      split; [first [ (unfold Z_MEM_ERROR; lia) | lia
                    | (match goal with |- ?g => idtac "K3-B4 SHAPE: K8 range" g end; fail) ]|].
      cbn [fst snd]. split; [rewrite zstore_nil; exact UARR2|].
      split; [change (zlength (@nil Z)) with 0; lia|].
      split; [first [ lia | (match goal with |- ?g => idtac "K3-B4 SHAPE: K8 dlen" g end; fail) ]|].
      (* 1.4 leaves *destLen = dlen when inflateInit fails (zl14cmp-r2's uncompress2M returns ([], dlen) there) *)
      split; [exact PLC2| exact PSC2]. }

    destruct PO as (As & ((errv2 & ENV2) & FRM2 & LXP2 & ESO2 & EFA2) & -> & PUB2 & ZR2).
    rewrite E176 in LXP2. pose proof (agree_of_lx_pres _ _ _ _ _ LXP2) as AG2.
    pose proof ENV2 as (HP2 & _ & _ & _ & _ & _ & _ & _ & ST2 & _ & _ & _ & _ & MI2). rewrite E176 in ST2.
    assert (FRH2 : FRHI m2) by (unfold FRHI in *; eapply rw_cells_agree; [exact AG2| exact FRH1| intros a Ha; cbn in Ha; apply stack_client; [lia| apply NX; unfold ZS_SIZEOF; lia]]).
    assert (PLC2 : rw_cells psegs m2 PL [C8 (Z_to_bv 64 dlen)]) by (eapply rw_cells_agree; [exact AG2| exact PLC1| intros a Ha; cbn in Ha; apply stack_client; [lia| apply NX; unfold ZS_SIZEOF; lia]]).
    assert (PSC2 : rw_cells psegs m2 PS [C8 (Z_to_bv 64 slen)]) by (eapply rw_cells_agree; [exact AG2| exact PSC1| intros a Ha; cbn in Ha; apply stack_client; [lia| apply NX; unfold ZS_SIZEOF; lia]]).
    assert (UARR2 : u8arr psegs m2 U (to_bytes uc)).
    { eapply u8arr_agree; [exact AG2| exact UARR1|]. intros a Ha. rewrite LU0 in Ha.
      eapply block_client; [exact INU| cbn [blk_addr blk_size fst snd]; lia| apply NX; unfold ZS_SIZEOF; lia]. }
    assert (CARR2 : u8arr psegs m2 C (to_bytes comprc)).
    { eapply u8arr_agree; [exact AG2| exact CARR1|]. intros a Ha. rewrite LC0 in Ha.
      eapply block_client; [exact INC| cbn [blk_addr blk_size fst snd]; lia| apply NX; unfold ZS_SIZEOF; lia]. }
    assert (PRES2 : lx_pres LB usp XX m0 m2).
    { eapply lx_pres_trans; [exact PRES1|]. eapply lx_pres_sub; [exact LXP2|]. intros a Ha. apply (client_inner _ a); [| exact Ha].
      intros a' Ha'. cbn [rin_ivs fst snd] in Ha'. left. lia. }
    pose proof (iblocks_LBZR p As _ _ _ _ HP2) as LBZR.
    clear FRH1 PLC1 PSC1 UARR1 CARR1 AG2 FRS1.
    change (wint Z_OK) with (Z_to_bv 64 0).

    unfold zs_pub in PUB2. cbv beta delta [MallocRep.wz] in PUB2.
    pose proof (munch_refl [(SS, SS + 48)] m2) as MUz. pose proof (wmono_refl psegs m2) as WMz.
    apply box in UARR2. apply box in CARR2. apply box in ZR2. apply box in PRES2.
    unfold implM. iprefix.
    (* 1.4 at 0x1cd90: bnez a0 (not taken); or a0,s2,s4; bnez a0 (dest | left is not 0: taken, dest stays);
       sd s2,24(sp) (next_out); sw zero,32(sp); li a1,-1; srl s2,a1,32 (max); beqz zero -> 0x1cd70 *)
    zstep. if_false.
    zstep. zstep. if_cases KN5; zify_cond KN5; rewrite ?unsigned_lit in KN5 by (first [apply lor_lt_pow2 | apply Z_lor_lt_pow2 | lia]; lia);
      [| exfalso; first [apply Z.lor_eq_0_iff in KN5; lia | lia]].
    zs. zs. zstep. zstep. zstep. first [if_true | idtac].
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m3 end.
    pose proof (agree_on_of_munch _ _ _ MUz WMz) as AG3.
    pose proof (u2_x0_totals dlen src) as [TIN0 TOUT0].

    assert (INV3 : IINV m0 s p As m3 s2 fc2 (u2_x0 zc dlen src) None 0).
    { unfold IINV, EINV. rewrite TIN0, TOUT0. unfold u2_x0. cbn [u2_ain u2_aout u2_orev u2_is]. rewrite !Z.add_0_r.
      split.
      { split. { exists errv2. eapply (lx_env_munch [(SS, SS + 48)] m2 m3); [exact HFRAME| exact ENV2| exact MUz| exact WMz| assumption| rewrite E176; assumption| rewrite E176; lia| |].
                 - constructor; [left; cbn [fst]; lia| constructor].
                 - intros a Ha. cbn [outside]. clear - Ha SPB LOG LOSP RSP. lia. }
        split; [exact I|].
        split; [unfold FRHI in *; eapply rw_cells_agree; [exact AG3| exact FRH2| intros a Ha; cbn in Ha; cbn [outside]; lia]|].
        split; [eapply u8arr_agree; [exact AG3| exact (unbox _ CARR2)| intros a Ha; rewrite LC0 in Ha; cbn [outside]; lia]|].
        split; [exact PLC2|].
        split; [exact PSC2|].
        split. { eapply lx_pres_trans; [exact (unbox _ PRES2)|]. eapply pres_munch; [exact MUz| exact WMz|]. intros a Ha HX. cbn [outside]. split; [| exact I].
                 destruct Ha as [Ha|[(b & Hb & Hr)|Ha]]; [lia| destruct (LBR b Hb) as (_ & _ & _ & BC & _); lia| lia]. }
        split; [exact ESO2|]. split; [exact EFA2| exact FRM2]. }
      split; [do 2 eexists; unfold zs_pub; cbv beta delta [MallocRep.wz]; eassumption|].
      split; [eapply zri_pub; [exact LBZR| rewrite <- bridge_iinit; exact (unbox _ ZR2)| exact MUz| exact WMz]|].
      unfold destc. cbn [rev length skipn app]. eapply u8arr_agree; [exact AG3| exact (unbox _ UARR2)| intros a Ha; rewrite LU0 in Ha; cbn [outside]; lia]. }
    eapply evt_eq.
    2:{ apply evt_done.
        lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM psegs tm s2 (POSTC s LB U dlen PL PS uc lo B canary m0) msx) end.
        lazymatch goal with |- implM _ (mbind ?MM _) ?ss ?Q ?msx => change (implM psegs (mbind MM (KONT p)) ss Q msx) end.
        first [ eapply (u2_loop m0 s p As); [intros; eapply (u2_end m0 s p As); eassumption| apply U2I_init; [exact NB| exact SB| exact NF4]| exact INV3]
              | fail 100 "u2_loop application" ]. }
    unfold head_pc, u2_x0. cbn [u2_aout u2_left u2_len Z.eqb]. rewrite NF3. reflexivity.
  Qed.
End U2.

Theorem uncompress2_proof : forall R : zreps, zlib_okC R ->
  RHEAP_frame_stmt -> RHEAP_block_range_stmt -> RHEAP_blocks_nodup_stmt -> RHEAP_blocks_disjoint_stmt ->
  runcompress2_stmt.
Proof.
  intros R ZOK HFRAME HBR HND HBD. unfold runcompress2_stmt. intros until canary.
  intros ENV INU UC UCL PLC PLLO PLHI PL8 INC CARR CCL CCF SLEN ESRC PSC PSLO PSHI PS8 PLPS NEQB DL CLB LOSP SP16 FRM -> -> -> ->.
  pose proof ENV as (HP & _ & _ & _ & _ & _ & SPB & B63 & _ & LOC & LOG & _ & TP & _). cbn [app] in HP.
  pose proof (HBR _ _ _ _ HP INU) as UR. cbn [blk_addr blk_size fst snd] in UR.
  pose proof (HBR _ _ _ _ HP INC) as CR. cbn [blk_addr blk_size fst snd] in CR.
  assert (CU : U + dlen <= C \/ C + cl <= U).
  { pose proof (HBD _ _ _ _ _ HP INU INC ltac:(cbn; exact NEQB)) as X. cbn [blk_addr blk_size fst snd] in X. lia. }
  assert (LBR : forall b, In b LB -> rblock_range (blk_addr b) (blk_size b)) by (intros b Hb; exact (HBR _ _ _ _ HP Hb)).
  eapply (u2_main R) with (up := up) (cpS := cpS) (errv := errv); eassumption.
Qed.
End WithCeiling0.
