(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PropExec CatSim SymExec3 SymExec3Sound SymRun3.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HLib.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BMState BMem BCells BExec BLFrame BStep BSysStep BacX BellsX.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsIface BsCXXHeap BsStack0 BsWalk BXXRep RtB_Iface RtB_Annot BakeStackRep.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LibIface.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require Import CRep ContStmts StrLib.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LbB_Kit LbB_Bridge LbB_Call LbB_Conv LbB_SR LbB_MILB LbB_Own LbB_ContStmt LbB_ContV4R LbB_ContV4 LbB_ContVotR LbB_ContVot LbB_SegKit LbB_StrPbR.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition SPB_DEL_RA : Z := 0x1200e8.
Definition SPB_STACK : Z := 64 + AOPNEW_STACK.

Definition strA (LB : list block) (m : mem) (p : Z) (sb : sbuf) (cs : list Z) : Prop := @str_rep AC_A ASEGS LY_A MI_A (lbl LB) m p sb cs.

Definition spb_in_ff (LF : list fframe) (O n : Z) : Prop :=
  exists f, In f LF /\ ff_addr f <= O /\ O + n <= ff_addr f + fsz (ff_class f).

Section SPBS.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.

  Definition spb_blk (LB : list block) (m : mem) (sb : sbuf) (pid : bptr) : Prop :=
    match sb with SShort => True | SLong d asz => In (pid, d, asz) LB /\ SHAD m d (shadow_of asz) end.

  Definition spb_own (sb : sbuf) (pid : bptr) : list block :=
    match sb with SShort => [] | SLong d asz => [(pid, d, asz)] end.

  Definition spb_lbo (LB LBo : list block) (sb : sbuf) (pid : bptr) : Prop :=
    (forall b, In b LBo -> In b LB) /\ List.NoDup (map blk_id LBo)
    /\ match sb with SShort => True | SLong d asz => In (pid, d, asz) LBo end.

  Definition spb_x (sb : sbuf) : list (Z * Z) :=
    match sb with SShort => [] | SLong d asz => [(d, d + asz); (sh d, sh d + nsh asz)] end.

  Definition spb_old (sb : sbuf) : Z := match sb with SShort => 0 | SLong _ asz => asz end.

  Definition spb_cost (sb : sbuf) (cs : list Z) : Z :=
    if Zlen cs =? str_cap sb then as_Cm H (str_grow sb) + as_Cf H (spb_old sb) else 0.

  Definition spb_LB (LB : list block) (sb : sbuf) (pid pid' : bptr) (d' : Z) : list block :=
    (pid', d', str_grow sb) :: (match sb with SShort => LB | SLong _ _ => as_lb_remove H pid LB end).

  Definition spb_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (s : as_St H) (LB LBo : list block) (LF : list fframe) (p c : Z) (sb : sbuf) (cs : list Z) (pid : bptr) (lo B shi : Z)
      (m : mem) (mo : Model) : config -> Prop :=
    fun cf => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (errv' : word) (s' : as_St H) (LB' LBo' : list block)
                     (sb' : sbuf) (pid' : bptr),
      as_VIS H s' (cfg_ms cf) = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                   F (ret_pc ra) fc None m' (seg_rom asegs)
      /\ as_AKREL H s' cf /\ as_MPRES H mo (cfg_model cf)
      /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
      /\ rw_cells asegs m' (errno_addr tp) [C4 errv'] /\ as_rauxv_ok H m' B
      /\ xpres H LB (bv_unsigned sp) ((p, p + 24) :: spb_x sb) m m'
      /\ as_RHEAP H s' LB' m' /\ strA LB' m' p sb' (cs ++ [c]) /\ spb_blk LB' m' sb' pid'
      /\ ((Zlen cs < str_cap sb /\ sb' = sb /\ LB' = LB /\ pid' = pid /\ LBo' = LBo)
          \/ (Zlen cs = str_cap sb /\ ~ In pid' (map blk_id LB)
              /\ exists d', sb' = SLong d' (str_grow sb) /\ LB' = spb_LB LB sb pid pid' d' /\ ablock_range H d' (str_grow sb)
                           /\ LBo' = spb_LB LBo sb pid pid' d'))
      /\ addressable m' p 24 /\ wr_at asegs m' p 24 /\ lb_own LBo' m'
      /\ as_RFS H LF m' /\ ACONST m' /\ stack0 m' lo shi
      /\ as_AL H s' >= as_AL H s - spb_cost sb cs.

  Definition spb_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (msF : machine_state) (m : mem) (mo : Model)
           (s : as_St H) (LB LBo : list block) (LF : list fframe) (p c : Z) (sb : sbuf) (cs : list Z) (pid : bptr)
           (lo B shi : Z) (errv : word),
      as_VIS H s msF = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                          F (Z_to_bv 64 SPB_ENTRY) fc None m (seg_rom asegs) ->
      a0 = Z_to_bv 64 p -> a1 = Z_to_bv 64 c -> 0 <= c <= 255 ->
      strA LB m p sb cs -> spb_blk LB m sb pid ->
      p mod 8 = 0 -> addressable m p 24 -> spb_in_ff LF p 24 -> obj_win H LB LF (bv_unsigned sp) lo p 24 ->
      ((0x6e8000 <= p /\ p + 24 <= 0x7fff7000) \/ (0x10007fff8000 <= p /\ p + 24 <= 2 ^ 47)) ->
      wr_at asegs m p 24 -> lb_own LBo m -> spb_lbo LB LBo sb pid ->
      str_grow sb <= 2 ^ 28 ->
      (Zlen cs = str_cap sb -> as_alloc_ok H s LB (str_grow sb) /\ spb_cost sb cs <= as_AL H s) ->
      trace_ok (as_TR H) APC0_FREE [SPB_DEL_RA] ->
      as_RHEAP H s LB m -> as_AKREL H s (mkCfg msF mo) ->
      as_rauxv_ok H m B -> bv_unsigned sp <= B ->
      bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= 2 ^ 47 ->
      stk asegs m lo (bv_unsigned sp) -> aceil <= lo -> lo <= bv_unsigned sp - SPB_STACK ->
      rw_cells asegs m (errno_addr tp) [C4 errv] -> mem_inv asegs m -> tp = Z_to_bv 64 ATP ->
      ACONST m -> as_RFS H LF m ->
      stack0 m lo shi -> bv_unsigned sp <= shi ->
      as_SR H (spb_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB LBo LF p c sb cs pid lo B shi m mo)
        (mkCfg msF mo).
End SPBS.

Lemma fldA_munch : forall W m m' a k v, munch W m m' -> 0 <= a -> a + Z.of_nat k < 2 ^ 64 ->
  (forall x, a <= x < a + Z.of_nat k -> outside W x) -> fldA m a k v -> fldA m' a k v.
Proof.
  intros W m m' a k v MU H0 H1 HO HF. unfold fldA. eapply fld_agree; [exact H0 | exact H1 | exact HF |].
  intros x Hx. unfold zwin in Hx. apply MU. rewrite Z_to_bv_unsigned, bv_wrap64_mod, Z.mod_small by lia. apply HO. lia.
Qed.

Lemma mdef_dmono : forall m m' a n, mdef m a n -> (forall x, m x <> None -> m' x <> None) -> mdef m' a n.
Proof. intros m m' a n HD DM i Hi. apply DM, HD, Hi. Qed.

Lemma strA_short_push : forall LB m m1 p cs c,
  strA LB m p SShort cs -> Zlen cs < SSO_CAP -> 0 <= c <= 255 -> (forall x, m x <> None -> m1 x <> None) ->
  (forall i, 0 <= i < Zlen cs -> fldA m (p + 1 + i) 1 (Znth i cs) -> fldA m1 (p + 1 + i) 1 (Znth i cs)) ->
  fldA m1 p 1 (2 * Zlen cs + 2) -> fldA m1 (p + 1 + Zlen cs) 1 c -> fldA m1 (p + 2 + Zlen cs) 1 0 ->
  strA LB m1 p SShort (cs ++ [c]).
Proof.
  intros LB m m1 p cs c (Hs & Hs' & HD & Hlen & HM & HC & HZ) HL CR DM HK F0 FC FZ.
  unfold strA, str_rep. cbn [str_data str_cap] in *. rewrite Zlen_app1.
  split; [exact Hs|]. split; [exact Hs'|]. split; [exact (mdef_dmono _ _ _ _ HD DM)|]. split; [unfold SSO_CAP in *; lia|].
  split; [replace (2 * (Zlen cs + 1)) with (2 * Zlen cs + 2) by lia; exact F0|].
  split.
  - intros i Hi. destruct (Z.eq_dec i (Zlen cs)) as [->|Hne].
    + rewrite Znth_app1_eq. split; [lia|]. exact FC.
    + rewrite Znth_app1_lt by lia. destruct (HC i ltac:(lia)) as [Hr Hf]. split; [exact Hr|].
      replace (p + 1 + i) with (p + 1 + i) by lia. apply HK; [lia | exact Hf].
  - replace (p + 1 + (Zlen cs + 1)) with (p + 2 + Zlen cs) by lia. exact FZ.
Qed.

Lemma strA_long_push : forall LB LB' m m1 p d asz cs c,
  strA LB m p (SLong d asz) cs -> Zlen cs < asz - 1 -> 0 <= c <= 255 -> (forall x, m x <> None -> m1 x <> None) ->
  (forall q k, In (q, k) (lbl LB) -> In (q, k) (lbl LB')) ->
  fldA m1 p 8 (asz + 1) -> fldA m1 (p + 16) 8 d ->
  (forall i, 0 <= i < Zlen cs -> fldA m (d + i) 1 (Znth i cs) -> fldA m1 (d + i) 1 (Znth i cs)) ->
  fldA m1 (p + 8) 8 (Zlen cs + 1) -> fldA m1 (d + Zlen cs) 1 c -> fldA m1 (d + Zlen cs + 1) 1 0 ->
  strA LB' m1 p (SLong d asz) (cs ++ [c]).
Proof.
  intros LB LB' m m1 p d asz cs c (Hs & Hs' & HD & Hlen & HM & HC & HZ) HL CR DM INC F0 F16 HK F8 FC FZ.
  destruct HM as (Hd & Hd16 & Hd' & Hal & Hmin & HIn & Hdj & G0 & G8 & G16).
  unfold strA, str_rep. cbn [str_data str_cap] in *. rewrite Zlen_app1.
  split; [exact Hs|]. split; [exact Hs'|]. split; [exact (mdef_dmono _ _ _ _ HD DM)|]. split; [lia|].
  split; [repeat (split; [assumption|]); split; [apply INC; exact HIn|]; split; [exact Hdj|];
          split; [exact F0|]; split; [exact F8 | exact F16]|].
  split.
  - intros i Hi. destruct (Z.eq_dec i (Zlen cs)) as [->|Hne].
    + rewrite Znth_app1_eq. split; [lia|]. exact FC.
    + rewrite Znth_app1_lt by lia. destruct (HC i ltac:(lia)) as [Hr Hf]. split; [exact Hr|]. apply HK; [lia | exact Hf].
  - replace (d + (Zlen cs + 1)) with (d + Zlen cs + 1) by lia. exact FZ.
Qed.

Lemma strA_short_facts : forall LB m p cs, strA LB m p SShort cs ->
  0 <= Zlen cs <= SSO_CAP /\ fldA m p 1 (2 * Zlen cs) /\ mdef m p 24.
Proof. intros LB m p cs (Hs & Hs' & HD & Hlen & HM & HC & HZ). cbn [str_cap] in Hlen. split; [exact Hlen|]. split; [exact HM | exact HD]. Qed.

Lemma strA_long_facts : forall LB m p d asz cs, strA LB m p (SLong d asz) cs ->
  0 <= Zlen cs <= asz - 1 /\ 0 < d /\ d mod 16 = 0 /\ asz mod 8 = 0 /\ 46 <= asz /\ (p + 24 <= d \/ d + asz <= p)
  /\ fldA m p 8 (asz + 1) /\ fldA m (p + 8) 8 (Zlen cs) /\ fldA m (p + 16) 8 d.
Proof.
  intros LB m p d asz cs (Hs & Hs' & HD & Hlen & HM & HC & HZ). cbn [str_cap] in Hlen.
  destruct HM as (Hd & Hd16 & Hd' & Hal & Hmin & HIn & Hdj & G0 & G8 & G16). unfold SSO_CAP in Hmin.
  repeat (split; [assumption || lia|]). exact G16.
Qed.

Lemma sp_wr_sub : forall mk a n a' n', wr_at asegs mk a n -> a <= a' -> a' + n' <= a + n -> 0 <= n' -> wr_at asegs mk a' n'.
Proof.
  intros mk a n a' n' (W0 & W1 & W) H1 H2 H3. split; [lia|]. split; [lia|].
  intros i Hi. replace (a' + i) with (a + (a' - a + i)) by lia. apply W. lia.
Qed.

Lemma vo_band_of_aapp' {HCEIL : HeapCeil} : forall A n, aapp A n -> (0 <= A /\ A + n <= 0x7fff7000) \/ 0x10007fff8000 <= A.
Proof. intros A n HA. unfold aapp, aapp_lo, aapp_hi, AIMG_TOP, ALOWSH_LO, AHI_LO in HA. destruct HA; [left|right]; lia. Qed.

Lemma firstn1_skipn_map : forall (f : Z -> byte) (cs : list Z) k, (k < length cs)%nat ->
  firstn 1 (skipn k (map f cs)) = [f (nth k cs 0)].
Proof.
  intros f cs. induction cs as [|x cs IH]; intros k Hk; [cbn in Hk; lia|].
  destruct k as [|k]; [reflexivity|]. cbn [map skipn nth]. apply IH. cbn in Hk. lia.
Qed.

Lemma sbuf_cases : forall sb : sbuf, sb = SShort \/ exists d asz, sb = SLong d asz.
Proof. intros [|d asz]; [left; reflexivity | right; exists d, asz; reflexivity]. Qed.

Lemma munch_sub : forall W W' (m m' : mem), munch W m m' -> (forall x, outside W' x -> outside W x) -> munch W' m m'.
Proof. intros W W' m m' MU HO x Hx. apply MU. apply HO. exact Hx. Qed.

Section SPP.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HH : asan_rt_hyps H.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
            (m : mem) (mo : Model) (s : as_St H) (LB LBo : list block) (LF : list fframe)
            (p c : Z) (sb : sbuf) (cs : list Z) (pid : bptr) (lo B shi spz : Z).
  Hypothesis SPZ : bv_unsigned sp = spz.
  Hypothesis SPR : 2 ^ 45 <= spz - SPB_STACK /\ spz <= 2 ^ 47 /\ spz mod 16 = 0.
  Hypothesis CR : 0 <= c <= 255.
  Hypothesis REP : strA LB m p sb cs.
  Hypothesis BLK : spb_blk LB m sb pid.
  Hypothesis P8 : p mod 8 = 0.
  Hypothesis ADV0 : addressable m p 24.
  Hypothesis PFF : spb_in_ff LF p 24.
  Hypothesis OBJ : obj_win H LB LF spz lo p 24.
  Hypothesis PBAND : (0x6e8000 <= p /\ p + 24 <= 0x7fff7000) \/ (0x10007fff8000 <= p /\ p + 24 <= 2 ^ 47).
  Hypothesis PWR : wr_at asegs m p 24.
  Hypothesis OWN : lb_own LBo m.
  Hypothesis LBO : spb_lbo LB LBo sb pid.
  Hypothesis GROW : str_grow sb <= 2 ^ 28.
  Hypothesis AOK : Zlen cs = str_cap sb -> as_alloc_ok H s LB (str_grow sb) /\ spb_cost H sb cs <= as_AL H s.
  Hypothesis TRO : trace_ok (as_TR H) APC0_FREE [SPB_DEL_RA].
  Hypothesis RH0 : as_RHEAP H s LB m.
  Hypothesis RA0 : as_rauxv_ok H m B.
  Hypothesis SPB : spz <= B.
  Hypothesis ST0 : stk asegs m lo spz.
  Hypothesis LOR : aceil <= lo /\ lo <= spz - SPB_STACK.
  Hypothesis MI0 : mem_inv asegs m.
  Hypothesis TPV : tp = Z_to_bv 64 ATP.
  Hypothesis AC0 : ACONST m.
  Hypothesis RF0 : as_RFS H LF m.
  Hypothesis S00 : stack0 m lo shi.
  Hypothesis SHI : spz <= shi.

  Let Q := spb_post H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB LBo LF p c sb cs pid lo B shi m mo.
  Let FRAME : list cell := map (fun w => C8 w) [s6; s5; s4; s3; s2; s1; s0; ra].

  Lemma spz_sp : sp = Z_to_bv 64 spz.
  Proof. rewrite <- SPZ. symmetry. apply Z_to_bv_bv_unsigned. Qed.

  Lemma spb_rm_ne : forall q LB1 b, List.NoDup (map blk_id LB1) -> In b (as_lb_remove H q LB1) -> blk_id b <> q.
  Proof.
    intros q LB1 b ND. pose proof (ah_lb_remove H HH) as (L1 & L2 & L3).
    induction LB1 as [|b' LB1 IH]; intros Hin; [destruct (L3 _ _ _ Hin)|].
    cbn [map] in ND. apply NoDup_cons_iff in ND as [ND1 ND2].
    destruct (Z.eq_dec (blk_id b') q) as [Eq|Ne].
    - destruct b' as [[q' A'] n']. cbn [blk_id fst] in Eq. subst q'. rewrite (L1 _ _ _ _ ND1) in Hin.
      intros Eb. apply ND1. rewrite <- Eb. exact (List.in_map blk_id LB1 b Hin).
    - rewrite (L2 _ _ _ Ne) in Hin. destruct Hin as [<-|Hin]; [exact Ne | exact (IH ND2 Hin)].
  Qed.
  Lemma spb_rm_keep : forall q LB1 b, List.NoDup (map blk_id LB1) -> In b LB1 -> blk_id b <> q -> In b (as_lb_remove H q LB1).
  Proof.
    intros q LB1 b ND IN NE. pose proof (ah_lb_remove H HH) as (L1 & L2 & L3).
    induction LB1 as [|b' LB1 IH]; [destruct IN|]. cbn [map] in ND. apply NoDup_cons_iff in ND as [ND1 ND2].
    destruct (Z.eq_dec (blk_id b') q) as [E|E].
    - destruct b' as [[q' A'] n']. cbn in E. subst q'. rewrite L1 by exact ND1.
      destruct IN as [<-|IN]; [cbn in NE; congruence | exact IN].
    - rewrite L2 by exact E. destruct IN as [<-|IN]; [left; reflexivity | right; exact (IH ND2 IN)].
  Qed.
  Lemma spb_rm_incl : forall q LB1 LB2, (forall b, In b LB1 -> In b LB2) -> List.NoDup (map blk_id LB1) -> List.NoDup (map blk_id LB2) ->
    forall b, In b (as_lb_remove H q LB1) -> In b (as_lb_remove H q LB2).
  Proof.
    intros q LB1 LB2 INC ND1 ND2 b Hb. pose proof (ah_lb_remove H HH) as (L1 & L2 & L3).
    apply spb_rm_keep; [exact ND2 | apply INC; exact (L3 _ _ _ Hb) | exact (spb_rm_ne q LB1 b ND1 Hb)].
  Qed.

  Lemma sp_end : forall (msF1 : machine_state) (mo1 : Model) (s1' : as_St H) (m1 : mem) (R1 : bvmap 5 word)
                        (LB' LBo' : list block) (sb' : sbuf) (pid' : bptr) (e1 : word),
    as_VIS H s1' msF1 = MS R1 F (Z_to_bv 64 SPB_RET) fc None m1 (seg_rom asegs) -> rfull R1 ->
    getr R1 1 = ra -> getr R1 2 = sp -> getr R1 3 = gp -> getr R1 4 = tp -> getr R1 8 = s0 -> getr R1 9 = s1 ->
    getr R1 18 = s2 -> getr R1 19 = s3 -> getr R1 20 = s4 -> getr R1 21 = s5 -> getr R1 22 = s6 -> getr R1 23 = s7 ->
    getr R1 24 = s8 -> getr R1 25 = s9 -> getr R1 26 = s10 -> getr R1 27 = s11 ->
    as_AKREL H s1' (mkCfg msF1 mo1) -> as_MPRES H mo mo1 ->
    mem_inv asegs m1 -> stk asegs m1 lo spz -> rw_cells asegs m1 (errno_addr tp) [C4 e1] -> as_rauxv_ok H m1 B ->
    xpres H LB spz ((p, p + 24) :: spb_x sb) m m1 ->
    as_RHEAP H s1' LB' m1 -> strA LB' m1 p sb' (cs ++ [c]) -> spb_blk LB' m1 sb' pid' ->
    ((Zlen cs < str_cap sb /\ sb' = sb /\ LB' = LB /\ pid' = pid /\ LBo' = LBo)
     \/ (Zlen cs = str_cap sb /\ ~ In pid' (map blk_id LB)
         /\ exists d', sb' = SLong d' (str_grow sb) /\ LB' = spb_LB H LB sb pid pid' d' /\ ablock_range H d' (str_grow sb)
                      /\ LBo' = spb_LB H LBo sb pid pid' d')) ->
    addressable m1 p 24 -> wr_at asegs m1 p 24 -> lb_own LBo' m1 ->
    as_RFS H LF m1 -> ACONST m1 -> stack0 m1 lo shi ->
    as_AL H s1' >= as_AL H s - spb_cost H sb cs ->
    as_SR H Q (mkCfg msF1 mo1).
  Proof.
    intros msF1 mo1 s1' m1 R1 LB' LBo' sb' pid' e1 VIS1 HF1 G1 G2 G3 G4 G8 G9 G18 G19 G20 G21 G22 G23 G24 G25 G26 G27 KR1 MP1
      MI1 ST1 ERR1 RA1 XP1 RH1 REP1 BLK1 CASE ADV1 WP1 OW1 RF1 AC1 S01 AL1.
    eapply (sr_evt H HH) with
      (P := fun ms => ms = MS (mkR ra sp gp tp (getr R1 5) (getr R1 6) (getr R1 7) s0 s1 (getr R1 10)
                                   (getr R1 11) (getr R1 12) (getr R1 13) (getr R1 14) (getr R1 15) (getr R1 16) (getr R1 17)
                                   s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (getr R1 28) (getr R1 29) (getr R1 30) (getr R1 31))
                              F (ret_pc ra) fc None m1 (seg_rom asegs));
      [exact KR1 | exact VIS1 | |].
    { rewrite (rfull_eq R1 HF1). apply sp_ret_ok.
      rewrite G1, G2, G3, G4, G8, G9, G18, G19, G20, G21, G22, G23, G24, G25, G26, G27. reflexivity. }
    intros msF2 mo2 KR2 MP2 HP. cbv beta in HP.
    exists (getr R1 5), (getr R1 6), (getr R1 7), (getr R1 10), (getr R1 11), (getr R1 12), (getr R1 13), (getr R1 14),
      (getr R1 15), (getr R1 16), (getr R1 17), (getr R1 28), (getr R1 29), (getr R1 30), (getr R1 31), m1, e1, s1', LB', LBo', sb', pid'.
    cbn [cfg_ms cfg_model]. rewrite SPZ.
    split; [exact HP|]. split; [exact KR2|]. split; [eapply (ah_mpres_trans H HH); eassumption|].
    split; [exact MI1|]. split; [exact ST1|]. split; [exact ERR1|]. split; [exact RA1|]. split; [exact XP1|].
    split; [exact RH1|]. split; [exact REP1|]. split; [exact BLK1|]. split; [exact CASE|].
    split; [exact ADV1|]. split; [exact WP1|]. split; [exact OW1|].
    split; [exact RF1|]. split; [exact AC1|]. split; [exact S01|]. exact AL1.
  Qed.

  Lemma sp_pband : 0x6e8000 <= p /\ p + 24 <= 2 ^ 47.
  Proof. destruct PBAND; lia. Qed.

  Lemma sp_pfar : p + 24 <= spz - SPB_STACK \/ spz <= p.
  Proof.
    destruct OBJ as (_ & _ & _ & _ & _ & SD). destruct LOR as [LO1 LO2]. lia.
  Qed.

  Lemma sp_frame_store : forall (m1 : mem) (W : list (Z * Z)),
    munch ((spz - 64, spz) :: W) m m1 -> wmono asegs m m1 -> mem_inv asegs m1 ->
    Forall (fun iv : Z * Z => p <= fst iv /\ snd iv <= p + 24) W ->
    as_RHEAP H s LB m1 /\ as_RFS H LF m1 /\ ACONST m1 /\ as_rauxv_ok H m1 B
    /\ stk asegs m1 lo spz /\ stack0 m1 lo shi /\ lb_own LBo m1 /\ wr_at asegs m1 p 24.
  Proof.
    intros m1 W MU WM MI1 FW.
    pose proof SPR as (SPL & SPH & SP16). pose proof LOR as [LO1 LO2].
    unfold SPB_STACK, AOPNEW_STACK, AMALLOC_STACK in LO2, SPL.
    pose proof aceil_facts as ((ACF1 & ACF2) & ACF3 & ACF4).
    pose proof (ah_fsb H HH _ _ _ RH0) as (FS1 & FS2 & FS3 & FS4).
    assert (SWL : aceil <= spz - 64) by lia.
    destruct (stack_window_ok H LB LF (spz - 64) spz SWL FS2) as (SW1 & SW2 & SW3).
    pose proof OBJ as (OC1 & OC2 & OW1 & OW2 & OW3 & OW4).
    pose proof sp_pband as PB.
    assert (MU' : munch [(spz - 64, spz); (p, p + 24)] m m1).
    { eapply munch_sub; [exact MU|]. intros x (Hx1 & Hx2 & _).
      cbn [outside]. split; [exact Hx1|]. clear - FW Hx2. induction W as [|[l h] W IH]; [exact I|].
      cbn. pose proof (Forall_inv FW) as F1. cbn in F1. split; [lia|]. apply IH. exact (Forall_inv_tail FW). }
    destruct (client_frame H HH s LB LF B [(spz - 64, spz); (p, p + 24)] m m1 RH0 RF0 AC0 RA0 MU' WM
                ltac:(apply Forall_cons; [exact SW1 | apply Forall_cons; [exact OW1 | apply Forall_nil]])
                ltac:(apply Forall_cons; [exact SW2 | apply Forall_cons; [exact OW2 | apply Forall_nil]])
                ltac:(apply Forall_cons; [exact SW3 | apply Forall_cons; [exact OW3 | apply Forall_nil]]))
      as (RH1 & RF1 & AC1 & RA1).
    split; [exact RH1|]. split; [exact RF1|]. split; [exact AC1|]. split; [exact RA1|].
    split; [eapply BakeStackRep.stk_high_transport; [exact ST0 | exact WM | unfold AIMG_TOP; lia]|].
    split.
    { eapply stack0_transport; [exact S00 | exact MU' | exact WM |].
      apply Forall_cons; [left; cbn [fst]; unfold AHI_LO; lia|]. apply Forall_cons; [|apply Forall_nil].
      assert (SHC : 0x7fff7000 < sh aceil) by (unfold sh, ASHADOW_BASE; Z.div_mod_to_equations; lia).
      unfold stack0_ok; cbn [fst snd]. destruct PBAND; [right | left]; unfold AHI_LO; lia. }
    split; [exact (lb_own_wmono _ _ _ OWN WM)|].
    exact (wr_at_wmono _ _ _ _ PWR WM).
  Qed.

  Lemma sp_psh : forall a n, 0 <= n -> ((0 <= a /\ a + n <= 0x7fff7000) \/ 0x10007fff8000 <= a) ->
    a + n <= sh p \/ sh p + nsh 24 <= a.
  Proof. intros a n Hn Ha. pose proof sp_pband as PB. apply v4_app_sh; [lia | lia | lia | exact Ha]. Qed.

  Lemma sp_pband2 : (0 <= p /\ p + 24 <= 0x7fff7000) \/ 0x10007fff8000 <= p.
  Proof. destruct PBAND; [left|right]; lia. Qed.

  Lemma spp_S : forall (msF : machine_state) (t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 errv : word),
    sb = SShort -> Zlen cs < SSO_CAP ->
    as_VIS H s msF = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 p) (Z_to_bv 64 c) a2 a3 a4 a5 a6 a7
                             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 SPB_ENTRY) fc None m (seg_rom asegs) ->
    as_AKREL H s (mkCfg msF mo) -> rw_cells asegs m (errno_addr tp) [C4 errv] ->
    as_SR H Q (mkCfg msF mo).
  Proof.
    intros msF t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 errv E HL VIS KR ERR.
    pose proof SPR as (SPL & SPH & SP16). pose proof LOR as [LO1 LO2].
    unfold SPB_STACK, AOPNEW_STACK, AMALLOC_STACK in LO2, SPL.
    pose proof aceil_facts as ((ACF1 & ACF2) & ACF3 & ACF4).
    pose proof REP as REP'. rewrite E in REP'.
    destruct (strA_short_facts _ _ _ _ REP') as (ZL & F0 & MD). unfold SSO_CAP in ZL, HL.
    pose proof sp_pband as PB. pose proof sp_pfar as PD. unfold SPB_STACK, AOPNEW_STACK, AMALLOC_STACK in PD.
    remember (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 p) (Z_to_bv 64 c) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
      as R0 eqn:HR0.
    assert (HF0 : rfull R0) by (rewrite HR0; apply rfull_mkR).
    destruct (spb_BS_ok R0 F fc m p c (Zlen cs) spz lo ltac:(rewrite HR0; reflexivity) ltac:(rewrite HR0; reflexivity)
                 ltac:(rewrite HR0; exact spz_sp) F0 ltac:(lia) CR PWR ST0 ltac:(lia) ltac:(lia) SPH
                 (proj1 PB) (proj2 PB) ltac:(lia))
      as (R1 & M1 & Hms & MU1 & WM1 & DM1 & G0 & GC & GZ & KK).
    pose proof (msteps_full asegs _ _ Hms HF0) as HF1. cbn [ms_regs] in HF1.
    assert (MI1 : mem_inv asegs M1) by exact (msteps_mem_inv asegs _ _ Hms MI0).
    destruct (sp_frame_store M1 [(p, p + 1); (p + 1 + Zlen cs, p + 3 + Zlen cs)] MU1 WM1 MI1
                ltac:(apply Forall_cons; [cbn; lia | apply Forall_cons; [cbn; lia | apply Forall_nil]]))
      as (RH1 & RF1 & AC1 & RA1 & ST1 & S01 & OW1 & WP1).
    eapply (sr_blk H HH); [exact KR | exact VIS | exact HF0 | exact Hms |].
    intros msF1 mo1 KR1 MP1 VIS1. rewrite <- (rfull_eq R1 HF1) in VIS1.
    eapply (sp_end msF1 mo1 s M1 R1 LB LBo SShort pid errv VIS1 HF1).
    all: try (rewrite (KK _ ltac:(inb)), HR0; reflexivity).
    - exact KR1.
    - exact MP1.
    - exact MI1.
    - exact ST1.
    - eapply rw_cells_transport; [exact ERR | exact MU1 | exact WM1 |]. rewrite TPV. rewrite u64_of_Z by (unfold ATP; lia).
      cbn. unfold ATP. split; [lia|]. split; [lia|]. split; [lia | exact I].
    - exact RA1.
    - eapply (xpres_of_munch H s LB spz _ _ m m M1); [exact HH | exact RH0 | exact MU1 | exact WM1 |].
      apply Forall_cons; [left; cbn [fst snd]; lia|].
      apply Forall_cons; [right; intros a Ha; left; cbn [fst snd] in *; lia|].
      apply Forall_cons; [right; intros a Ha; left; cbn [fst snd] in *; lia | apply Forall_nil].
    - exact RH1.
    - eapply (strA_short_push LB m M1 p cs c REP' ltac:(unfold SSO_CAP; lia) CR DM1); [| exact G0 | exact GC |].
      + intros i Hi Hf. eapply fldA_munch; [exact MU1 | lia | cbn; lia | | exact Hf]. intros x Hx. cbn in Hx |- *. lia.
      + replace (p + 2 + Zlen cs) with (p + 2 + Zlen cs) by lia. exact GZ.
    - exact I.
    - left. rewrite E. cbn [str_cap]. unfold SSO_CAP. repeat split; lia.
    - eapply addressable_transport; [exact ADV0 | exact MU1 | exact WM1 |].
      pose proof sp_pband2 as PB2.
      pose proof (sp_psh (spz - 64) 64 ltac:(lia) ltac:(right; lia)) as D1.
      pose proof (sp_psh p 1 ltac:(lia) ltac:(destruct PB2; [left|right]; lia)) as D2.
      pose proof (sp_psh (p + 1 + Zlen cs) 2 ltac:(lia) ltac:(destruct PB2; [left|right]; lia)) as D3.
      rewrite v4_nsh24 in *. cbn [disjoint_from]. repeat split; lia.
    - exact WP1.
    - exact OW1.
    - exact RF1.
    - exact AC1.
    - exact S01.
    - unfold spb_cost. destruct (Z.eqb_spec (Zlen cs) (str_cap sb)) as [EQ|NE]; [rewrite E in EQ; cbn in EQ; unfold SSO_CAP in EQ; lia | lia].
  Qed.

  Lemma spp_L : forall (msF : machine_state) (t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 errv : word) (d asz : Z),
    sb = SLong d asz -> Zlen cs < asz - 1 ->
    as_VIS H s msF = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 p) (Z_to_bv 64 c) a2 a3 a4 a5 a6 a7
                             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 SPB_ENTRY) fc None m (seg_rom asegs) ->
    as_AKREL H s (mkCfg msF mo) -> rw_cells asegs m (errno_addr tp) [C4 errv] ->
    as_SR H Q (mkCfg msF mo).
  Proof.
    intros msF t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 errv d asz E HL VIS KR ERR.
    pose proof SPR as (SPL & SPH & SP16). pose proof LOR as [LO1 LO2].
    unfold SPB_STACK, AOPNEW_STACK, AMALLOC_STACK in LO2, SPL.
    pose proof aceil_facts as ((ACF1 & ACF2) & ACF3 & ACF4).
    pose proof REP as REP'. rewrite E in REP'.
    pose proof BLK as BLK'. rewrite E in BLK'. destruct BLK' as [HIn SHD].
    destruct (strA_long_facts _ _ _ _ _ _ REP') as (ZL & D0 & D16 & AM & AMIN & DJ & F0 & F8 & F16).
    pose proof (ah_blocks H HH _ _ _ _ RH0 HIn) as (B0 & B16 & Bn & BI & BC & BF & BAPP).
    cbn [blk_addr blk_size fst snd] in B0, B16, Bn, BI, BC, BF, BAPP. unfold AIMG_TOP in BI.
    assert (AR : 48 <= asz <= 2 ^ 28) by (rewrite E in GROW; cbn [str_grow] in GROW; Z.div_mod_to_equations; lia).
    pose proof LBO as (_ & _ & HOb). rewrite E in HOb.
    pose proof (lb_own_In LBo m _ OWN HOb) as WB. cbn [blk_addr blk_size fst snd] in WB.
    pose proof sp_pband as PB. pose proof sp_pfar as PD. unfold SPB_STACK, AOPNEW_STACK, AMALLOC_STACK in PD.
    remember (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 p) (Z_to_bv 64 c) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
      as R0 eqn:HR0.
    assert (HF0 : rfull R0) by (rewrite HR0; apply rfull_mkR).
    destruct (spb_BL_ok R0 F fc m p c asz (Zlen cs) d spz lo ltac:(rewrite HR0; reflexivity) ltac:(rewrite HR0; reflexivity)
                 ltac:(rewrite HR0; exact spz_sp) F0 F8 F16 AM AR ltac:(lia) CR ltac:(lia) ltac:(lia)
                 ltac:(eapply sp_wr_sub; [exact WB | lia | lia | lia]) ltac:(lia) ltac:(lia) PWR ST0 ltac:(lia) ltac:(lia) SPH
                 (proj1 PB) (proj2 PB) ltac:(lia))
      as (R1 & M1 & Hms & MU1 & WM1 & DM1 & G8 & GC & GZ & KK).
    pose proof (msteps_full asegs _ _ Hms HF0) as HF1. cbn [ms_regs] in HF1.
    assert (MI1 : mem_inv asegs M1) by exact (msteps_mem_inv asegs _ _ Hms MI0).

    pose proof (ah_fsb H HH _ _ _ RH0) as (FS1 & FS2 & FS3 & FS4).
    assert (SWL : aceil <= spz - 64) by lia.
    destruct (stack_window_ok H LB LF (spz - 64) spz SWL FS2) as (SW1 & SW2 & SW3).
    pose proof OBJ as (OC1 & OC2 & OW1 & OW2 & OW3 & OW4).
    set (WD := (d + Zlen cs, d + Zlen cs + 2)).
    assert (WD1 : aclient_write_ok H LB WD). { right; right; left. exists (pid, d, asz). split; [exact HIn | unfold WD; cbn [fst snd blk_addr blk_size]; lia]. }
    assert (WD2 : afs_write_ok H LF WD).
    { unfold aapp, aapp_lo, aapp_hi, ALOWSH_LO, AHI_LO in FS4, BAPP. unfold AFS_SIZE, ATLS_PRIV_LO, ATLS_PRIV_HI, ATP in *.
      left. unfold WD; cbn [fst snd]. unfold AFS_SIZE, ATLS_PRIV_LO, ATLS_PRIV_HI, ATP. split; [destruct BF; lia | lia]. }
    assert (WD3 : aconst_ok WD) by (eapply (aconst_ok_app d asz); [exact BAPP | unfold WD; cbn [fst snd]; lia | unfold WD; cbn [fst snd]; lia]).
    assert (WD4 : stack0_ok WD) by (eapply (stack0_ok_aapp d asz); [exact BAPP | unfold WD; cbn [fst snd]; lia | unfold WD; cbn [fst snd]; lia]).
    assert (WP8 : aclient_write_ok H LB (p + 8, p + 16) /\ afs_write_ok H LF (p + 8, p + 16) /\ aconst_ok (p + 8, p + 16)).
    { split; [eapply aclient_write_ok_sub; [exact OW1 | lia | lia]|].
      split; [eapply afs_write_ok_sub; [exact OW2 | lia | lia] | eapply aconst_ok_sub; [exact OW3 | lia | lia]]. }
    destruct WP8 as (WP81 & WP82 & WP83).
    destruct (client_frame H HH s LB LF B [(spz - 64, spz); (p + 8, p + 16); WD] m M1 RH0 RF0 AC0 RA0 MU1 WM1
                ltac:(apply Forall_cons; [exact SW1 | apply Forall_cons; [exact WP81 | apply Forall_cons; [exact WD1 | apply Forall_nil]]])
                ltac:(apply Forall_cons; [exact SW2 | apply Forall_cons; [exact WP82 | apply Forall_cons; [exact WD2 | apply Forall_nil]]])
                ltac:(apply Forall_cons; [exact SW3 | apply Forall_cons; [exact WP83 | apply Forall_cons; [exact WD3 | apply Forall_nil]]]))
      as (RH1 & RF1 & AC1 & RA1).
    assert (SHC : 0x7fff7000 < sh aceil) by (unfold sh, ASHADOW_BASE; Z.div_mod_to_equations; lia).
    pose proof sp_pband2 as PB2.
    eapply (sr_blk H HH); [exact KR | exact VIS | exact HF0 | exact Hms |].
    intros msF1 mo1 KR1 MP1 VIS1. rewrite <- (rfull_eq R1 HF1) in VIS1.
    eapply (sp_end msF1 mo1 s M1 R1 LB LBo (SLong d asz) pid errv VIS1 HF1).
    all: try (rewrite (KK _ ltac:(inb)), HR0; reflexivity).
    - exact KR1.
    - exact MP1.
    - exact MI1.
    - eapply BakeStackRep.stk_high_transport; [exact ST0 | exact WM1 | unfold AIMG_TOP; lia].
    - eapply rw_cells_transport; [exact ERR | exact MU1 | exact WM1 |]. rewrite TPV. rewrite u64_of_Z by (unfold ATP; lia).
      cbn. unfold ATP. split; [lia|]. split; [lia|]. split; [lia | exact I].
    - exact RA1.
    - eapply (xpres_of_munch H s LB spz _ _ m m M1); [exact HH | exact RH0 | exact MU1 | exact WM1 |].
      rewrite E. cbn [spb_x].
      apply Forall_cons; [left; cbn [fst snd]; lia|].
      apply Forall_cons; [right; intros a Ha; left; cbn [fst snd] in *; lia|].
      apply Forall_cons; [right; intros a Ha; right; left; cbn [fst snd] in *; lia | apply Forall_nil].
    - exact RH1.
    - eapply (strA_long_push LB LB m M1 p d asz cs c REP' HL CR DM1 (fun q k H0 => H0)); [| | | exact G8 | exact GC |].
      + eapply fldA_munch; [exact MU1 | lia | cbn; lia | | exact F0]. intros x Hx. cbn in Hx |- *. lia.
      + eapply fldA_munch; [exact MU1 | lia | cbn; lia | | exact F16]. intros x Hx. cbn in Hx |- *. lia.
      + intros i Hi Hf. eapply fldA_munch; [exact MU1 | lia | cbn; lia | | exact Hf]. intros x Hx. cbn in Hx |- *. lia.
      + exact GZ.
    - split; [exact HIn|]. eapply SHAD_transport; [exact SHD | exact MU1 | exact WM1 |]. rewrite shadow_of_length by lia.
      pose proof (v4_app_sh (spz - 64) 64 d asz ltac:(lia) ltac:(lia) ltac:(lia) ltac:(right; lia)) as D1.
      pose proof (v4_app_sh (p + 8) 8 d asz ltac:(lia) ltac:(lia) ltac:(lia) ltac:(destruct PB2; [left|right]; lia)) as D2.
      pose proof (vo_band_of_aapp' d asz BAPP) as DB.
      pose proof (v4_app_sh (d + Zlen cs) 2 d asz ltac:(lia) ltac:(lia) ltac:(lia) ltac:(destruct DB; [left|right]; lia)) as D3.
      cbn [disjoint_from]. repeat split; lia.
    - left. rewrite E. cbn [str_cap]. repeat split; lia.
    - eapply addressable_transport; [exact ADV0 | exact MU1 | exact WM1 |].
      pose proof (vo_band_of_aapp' d asz BAPP) as DB.
      pose proof (sp_psh (spz - 64) 64 ltac:(lia) ltac:(right; lia)) as D1.
      pose proof (sp_psh (p + 8) 8 ltac:(lia) ltac:(destruct PB2; [left|right]; lia)) as D2.
      pose proof (sp_psh (d + Zlen cs) 2 ltac:(lia) ltac:(destruct DB; [left|right]; lia)) as D3.
      rewrite v4_nsh24 in *. cbn [disjoint_from]. repeat split; lia.
    - exact (wr_at_wmono _ _ _ _ PWR WM1).
    - exact (lb_own_wmono _ _ _ OWN WM1).
    - exact RF1.
    - exact AC1.
    - eapply stack0_transport; [exact S00 | exact MU1 | exact WM1 |].
      apply Forall_cons; [left; cbn [fst]; unfold AHI_LO; lia|].
      apply Forall_cons; [unfold stack0_ok; cbn [fst snd]; destruct PBAND; [right | left]; unfold AHI_LO; lia|].
      apply Forall_cons; [exact WD4 | apply Forall_nil].
    - unfold spb_cost. destruct (Z.eqb_spec (Zlen cs) (str_cap sb)) as [EQ|NE]; [rewrite E in EQ; cbn in EQ; lia | lia].
  Qed.

  Lemma sp_pff_range : forall mk, as_RFS H LF mk -> as_FSB H <= p /\ p + 24 <= as_FSB H + AFS_SIZE.
  Proof.
    intros mk RF. destruct PFF as (f & Hf & F1 & F2).
    destruct (ah_RFS_range H HH LF mk RF) as [_ RR]. destruct (RR f Hf) as (K0 & K1 & K2 & _).
    unfold AFS_HDR in K1. lia.
  Qed.

  Lemma sp_pcl : forall LBx SPx mk, as_RFS H LF mk ->
    aclient_range H LBx SPx p 24 /\ aclient_range H LBx SPx (sh p) (nsh 24).
  Proof.
    intros LBx SPx mk RF. destruct (sp_pff_range mk RF) as [F1 F2]. split.
    - right; right; right; right; left. lia.
    - right; right; right; right; right; left. split; [apply sh_mono; lia|].
      pose proof (sh_mono (p + 24) (as_FSB H + AFS_SIZE) F2) as K. rewrite v4_nsh24.
      assert (E : sh (p + 24) = sh p + 3) by (unfold sh; Z.div_mod_to_equations; lia). lia.
  Qed.

  Lemma sp_pwok : forall LBx mk, as_RFS H LF mk ->
    aclient_write_ok H LBx (p, p + 24) /\ afs_write_ok H LF (p, p + 24) /\ aconst_ok (p, p + 24).
  Proof.
    intros LBx mk RF. destruct (sp_pff_range mk RF) as [F1 F2].
    split; [right; right; right; right; left; cbn [fst snd]; lia|].
    split; [right; destruct PFF as (f & Hf & K1 & K2); exists f; cbn [fst snd]; split; [exact Hf | lia]|].
    destruct OBJ as (_ & _ & _ & _ & K & _). exact K.
  Qed.

  Lemma sp_pkeep : forall LBx SPx X mk mk', as_RFS H LF mk -> xpres H LBx SPx X mk mk' ->
    Forall (fun iv : Z * Z => p + 24 <= fst iv \/ snd iv <= p) X ->
    Forall (fun iv : Z * Z => sh p + 3 <= fst iv \/ snd iv <= sh p) X ->
    (forall a, p <= a < p + 24 -> mk' (Z_to_bv 64 a) = mk (Z_to_bv 64 a))
    /\ (addressable mk p 24 -> addressable mk' p 24) /\ (wr_at asegs mk p 24 -> wr_at asegs mk' p 24).
  Proof.
    intros LBx SPx X mk mk' RF XP FX FS.
    destruct (sp_pcl LBx SPx mk RF) as [C1 C2].
    assert (XC1 : xclient_range H LBx SPx X p 24) by (split; [exact C1 | exact FX]).
    assert (XC2 : xclient_range H LBx SPx X (sh p) 3) by (split; [rewrite v4_nsh24 in C2; exact C2 | exact FS]).
    pose proof sp_pband as PB.
    split; [|split].
    - intros a Ha. destruct (XP a ltac:(lia) (xclient_range_addr H LBx SPx X p 24 a XC1 Ha)) as [E _]. unfold wa in E. exact E.
    - intros [AN (SA0 & SA8 & [UB UW])]. split; [exact AN|]. split; [exact SA0|]. split; [exact SA8|].
      assert (XCS : xclient_range H LBx SPx X (sh p) (Z.of_nat (length (shadow_of 24)))) by (rewrite shadow_of_length by lia; rewrite v4_nsh24; exact XC2).
      split; [eapply (xpres_bytes_at H); [exact XP | exact UB | exact XCS] | eapply (xpres_wr_at H); [exact XP | exact UW | exact XCS]].
    - intros W. eapply (xpres_wr_at H); [exact XP | exact W | exact XC1].
  Qed.

  Definition spb_od (sb0 : sbuf) : Z := match sb0 with SShort => p + 1 | SLong d _ => d end.
  Definition spb_s5 (sb0 : sbuf) : Z := match sb0 with SShort => 23 | SLong _ asz => asz end.

  Lemma sp_chars_bytes : forall LBx mk, strA LBx mk p sb cs ->
    bytes_at asegs mk (spb_od sb) (str_bytes cs).
  Proof.
    intros LBx mk RP. pose proof RP as (Hs & Hs' & HD & Hlen & HM & HC & HZ).
    pose proof sp_pband as PB.
    assert (DR : 0 <= spb_od sb /\ spb_od sb + Zlen cs < 2 ^ 63).
    { destruct sb as [|d asz]; cbn [spb_od str_cap] in *; unfold SSO_CAP in *; [lia|].
      destruct HM as (Hd & _ & Hd' & _). lia. }
    apply bytes_at_of_rdn; [lia | rewrite str_bytes_length; unfold Zlen in DR; lia |].
    rewrite str_bytes_length. apply (fld_str_rdn ASEGS); [lia | lia |].
    intros i Hi. destruct (HC i Hi) as [Hr Hf]. split; [exact Hr|].
    destruct sb as [|d asz]; cbn [str_data spb_od] in *; exact Hf.
  Qed.

  Lemma sp_chars_back : forall mk A, bytes_at asegs mk A (str_bytes cs) ->
    (forall i, 0 <= i < Zlen cs -> 0 <= Znth i cs < 256) ->
    forall i, 0 <= i < Zlen cs -> fldA mk (A + i) 1 (Znth i cs).
  Proof.
    intros mk A BA CR0 i Hi. unfold fldA, fld.
    pose proof (bytes_at_rdn asegs mk A (str_bytes cs) (Z.to_nat i) 1 BA) as R.
    rewrite str_bytes_length in R. unfold Zlen in Hi. specialize (R ltac:(lia)).
    rewrite Z2Nat.id in R by lia. unfold wa in R.
    transitivity (Some (firstn 1 (skipn (Z.to_nat i) (str_bytes cs)))); [exact R|]. f_equal.
    rewrite w1_bytes_small by (apply CR0; unfold Zlen; lia).
    unfold str_bytes. rewrite firstn1_skipn_map by lia. reflexivity.
  Qed.

  Lemma sp_grow_facts : Zlen cs = str_cap sb ->
    48 <= str_grow sb <= 2 ^ 28 /\ str_grow sb mod 8 = 0 /\ Zlen cs + 2 <= str_grow sb
    /\ (forall d asz, sb = SLong d asz -> asz mod 8 = 0 /\ 48 <= asz /\ Zlen cs = asz - 1 /\ str_grow sb = 2 * asz)
    /\ (sb = SShort -> Zlen cs = 22 /\ str_grow sb = 48).
  Proof.
    intros FULL. pose proof REP as RP. destruct sb as [|d asz]; cbn [str_grow str_cap] in *; unfold SSO_CAP in *.
    - split; [lia|]. split; [reflexivity|]. split; [lia|]. split; [intros d asz E; discriminate E | intros _; split; reflexivity || lia].
    - destruct (strA_long_facts _ _ _ _ _ _ RP) as (ZL & D0 & D16 & AM & AMIN & _).
      assert (A48 : 48 <= asz) by (Z.div_mod_to_equations; lia).
      split; [lia|]. split; [Z.div_mod_to_equations; lia|]. split; [lia|].
      split; [intros d' asz' E; injection E as <- <-; repeat split; lia | intros E; discriminate E].
  Qed.

  Lemma sp_x_apart : Forall (fun iv : Z * Z => p + 24 <= fst iv \/ snd iv <= p) (spb_x sb)
    /\ Forall (fun iv : Z * Z => sh p + 3 <= fst iv \/ snd iv <= sh p) (spb_x sb).
  Proof.
    pose proof REP as RP. destruct sb as [|d asz]; cbn [spb_x]; [split; apply Forall_nil|].
    destruct (strA_long_facts _ _ _ _ _ _ RP) as (ZL & D0 & D16 & AM & AMIN & DJ & _).
    pose proof BLK as [HIn _].
    pose proof (ah_blocks H HH _ _ _ _ RH0 HIn) as (B0 & B16 & Bn & BI & BC & BF & BAPP).
    cbn [blk_addr blk_size fst snd] in B0, B16, Bn, BI, BC, BF, BAPP.
    pose proof aceil_facts as ((ACF1 & ACF2) & _ & _).
    pose proof sp_pband as PB. pose proof sp_pband2 as PB2.
    pose proof (v4_app_sh p 24 d asz ltac:(lia) ltac:(lia) ltac:(lia) PB2) as D1.
    pose proof (v4_app_sh d asz p 24 ltac:(lia) ltac:(lia) ltac:(lia) (vo_band_of_aapp' d asz BAPP)) as D2.
    pose proof (v4_sh_apart p 24 d asz ltac:(lia) ltac:(lia) P8 (v4_mod16_8 d B16) ltac:(lia) ltac:(lia) DJ) as D3.
    rewrite v4_nsh24 in D2, D3.
    split; (apply Forall_cons; [cbn [fst snd]; lia | apply Forall_cons; [cbn [fst snd]; lia | apply Forall_nil]]).
  Qed.

  Lemma sp_g4 : forall (msF4 : machine_state) (mo4 : Model) (sk4 : as_St H) (m4 : mem) (R4 : bvmap 5 word) (pid' : bptr) (A : Z)
                       (e4 : word) (sk2 : as_St H) (m2 : mem),
    Zlen cs = str_cap sb ->
    as_VIS H sk4 msF4 = MS R4 F (Z_to_bv 64 0x1200e8) fc None m4 (seg_rom asegs) -> rfull R4 ->
    getr R4 2 = Z_to_bv 64 (spz - 64) -> getr R4 3 = gp -> getr R4 4 = tp -> getr R4 8 = Z_to_bv 64 c -> getr R4 9 = Z_to_bv 64 p ->
    getr R4 19 = Z_to_bv 64 (str_grow sb) -> getr R4 20 = Z_to_bv 64 (Zlen cs) -> getr R4 22 = Z_to_bv 64 A ->
    getr R4 23 = s7 -> getr R4 24 = s8 -> getr R4 25 = s9 -> getr R4 26 = s10 -> getr R4 27 = s11 ->
    as_AKREL H sk4 (mkCfg msF4 mo4) -> as_MPRES H mo mo4 ->
    mem_inv asegs m4 -> stk asegs m4 lo spz -> rw_cells asegs m4 (errno_addr tp) [C4 e4] -> as_rauxv_ok H m4 B ->
    ACONST m4 -> as_RFS H LF m4 -> stack0 m4 lo shi ->
    as_RHEAP H sk4 (spb_LB H LB sb pid pid' A) m4 -> ~ In pid' (map blk_id LB) ->
    as_RHEAP H sk2 ((pid', A, str_grow sb) :: LB) m2 ->
    rw_cells asegs m4 (spz - 64) FRAME ->
    xpres H LB spz (spb_x sb) m m4 ->
    as_AL H sk4 >= as_AL H s - spb_cost H sb cs ->
    lb_own (spb_LB H LBo sb pid pid' A) m4 ->
    ablock_range H A (str_grow sb) -> SHAD m4 A (shadow_of (str_grow sb)) ->
    bytes_at asegs m4 A (str_bytes cs) -> (p + 24 <= A \/ A + str_grow sb <= p) ->
    as_SR H Q (mkCfg msF4 mo4).
  Proof.
    intros msF4 mo4 sk4 m4 R4 pid' A e4 sk2 m2 FULL VIS4 HF4 G2 G3 G4 G8 G9 G19 G20 G22 G23 G24 G25 G26 G27 KR4 MP4
      MI4 ST4 ERR4 RA4 AC4 RF4 S04 RH4 NI RHN FR4 XP4 AL4 OW4 ABR SHA BYA PAD.
    pose proof SPR as (SPL & SPH & SP16). pose proof LOR as [LO1 LO2].
    unfold SPB_STACK, AOPNEW_STACK, AMALLOC_STACK in LO2, SPL.
    pose proof aceil_facts as ((ACF1 & ACF2) & ACF3 & ACF4).
    pose proof ABR as (A0 & A16 & An & AI & ACE & AFS & AAP). unfold AIMG_TOP in AI.
    destruct (sp_grow_facts FULL) as (GR & GM & GS & _ & _).
    set (n' := str_grow sb) in *.
    pose proof sp_pband as PB. pose proof sp_pband2 as PB2. pose proof sp_pfar as PD.
    unfold SPB_STACK, AOPNEW_STACK, AMALLOC_STACK in PD.
    pose proof REP as (Hs & Hs' & HD & Hlen & HM & HC & HZ).
    destruct sp_x_apart as [XA1 XA2].
    destruct (sp_pkeep LB spz (spb_x sb) m m4 RF0 XP4 XA1 XA2) as (PEQ & PAD4 & PWR4).
    pose proof (PAD4 ADV0) as ADV4. pose proof (PWR4 PWR) as WP4.
    assert (HIN4o : In (pid', A, n') (spb_LB H LBo sb pid pid' A)) by (left; reflexivity).
    assert (HIN4 : In (pid', A, n') (spb_LB H LB sb pid pid' A)) by (left; reflexivity).
    pose proof (lb_own_In _ _ _ OW4 HIN4o) as WA. cbn [blk_addr blk_size fst snd] in WA.
    assert (WD : wr_at asegs m4 (A + Zlen cs) 2) by (eapply sp_wr_sub; [exact WA | lia | lia | lia]).
    cbn [map] in FR4.
    destruct (spb_B4_ok R4 F fc m4 p n' A (Zlen cs) c spz s6 s5 s4 s3 s2 s1 s0 ra G9 G19 G22 G20 G8 G2 FR4 WP4 WD
                 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) SPH (proj1 PB) (proj2 PB) AI ltac:(lia)
                 ltac:(Z.div_mod_to_equations; lia) ltac:(lia) ltac:(lia) ltac:(lia) CR)
      as (R5 & M5 & Hms & MU5 & WM5 & DM5 & H0 & H8 & H16 & HCc & HZz & K1 & K2 & K8 & K9 & K18 & K19 & K20 & K21 & K22 & KK).
    pose proof (msteps_full asegs _ _ Hms HF4) as HF5. cbn [ms_regs] in HF5.
    assert (MI5 : mem_inv asegs M5) by exact (msteps_mem_inv asegs _ _ Hms MI4).

    set (W5 := [(p, p + 24); (A + Zlen cs, A + Zlen cs + 2)]).
    destruct (sp_pwok (spb_LB H LB sb pid pid' A) m4 RF4) as (PW1 & PW2 & PW3).
    assert (WD1 : aclient_write_ok H (spb_LB H LB sb pid pid' A) (A + Zlen cs, A + Zlen cs + 2)).
    { right; right; left. exists (pid', A, n'). split; [exact HIN4 | cbn [fst snd blk_addr blk_size]; lia]. }
    pose proof (ah_fsb H HH _ _ _ RH4) as (FS1 & FS2 & FS3 & FS4).
    assert (WD2 : afs_write_ok H LF (A + Zlen cs, A + Zlen cs + 2)).
    { unfold aapp, aapp_lo, aapp_hi, ALOWSH_LO, AHI_LO in FS4, AAP.
      left. cbn [fst snd]. unfold AFS_SIZE, ATLS_PRIV_LO, ATLS_PRIV_HI, ATP in *. split; [destruct AFS; lia | lia]. }
    assert (WD3 : aconst_ok (A + Zlen cs, A + Zlen cs + 2)) by (eapply (aconst_ok_app A n'); [exact AAP | cbn; lia | cbn; lia]).
    assert (WD4 : stack0_ok (A + Zlen cs, A + Zlen cs + 2)) by (eapply (stack0_ok_aapp A n'); [exact AAP | cbn; lia | cbn; lia]).
    destruct (client_frame H HH sk4 _ LF B W5 m4 M5 RH4 RF4 AC4 RA4 MU5 WM5
                ltac:(apply Forall_cons; [exact PW1 | apply Forall_cons; [exact WD1 | apply Forall_nil]])
                ltac:(apply Forall_cons; [exact PW2 | apply Forall_cons; [exact WD2 | apply Forall_nil]])
                ltac:(apply Forall_cons; [exact PW3 | apply Forall_cons; [exact WD3 | apply Forall_nil]]))
      as (RH5 & RF5 & AC5 & RA5).
    assert (SHC : 0x7fff7000 < sh aceil) by (unfold sh, ASHADOW_BASE; Z.div_mod_to_equations; lia).
    pose proof (vo_band_of_aapp' A n' AAP) as AB.
    eapply (sr_blk H HH); [exact KR4 | exact VIS4 | exact HF4 | exact Hms |].
    intros msF5 mo5 KR5 MP5 VIS5. rewrite <- (rfull_eq R5 HF5) in VIS5.
    eapply (sp_end msF5 mo5 sk4 M5 R5 (spb_LB H LB sb pid pid' A) (spb_LB H LBo sb pid pid' A) (SLong A n') pid' e4 VIS5 HF5).
    - exact K1.
    - rewrite K2. symmetry. exact spz_sp.
    - rewrite (KK 3%bv ltac:(inb)). exact G3.
    - rewrite (KK 4%bv ltac:(inb)). exact G4.
    - exact K8.
    - exact K9.
    - exact K18.
    - exact K19.
    - exact K20.
    - exact K21.
    - exact K22.
    - rewrite (KK 23%bv ltac:(inb)). exact G23.
    - rewrite (KK 24%bv ltac:(inb)). exact G24.
    - rewrite (KK 25%bv ltac:(inb)). exact G25.
    - rewrite (KK 26%bv ltac:(inb)). exact G26.
    - rewrite (KK 27%bv ltac:(inb)). exact G27.
    - exact KR5.
    - eapply (ah_mpres_trans H HH); [exact MP4 | exact MP5].
    - exact MI5.
    - eapply BakeStackRep.stk_high_transport; [exact ST4 | exact WM5 | unfold AIMG_TOP; lia].
    - eapply rw_cells_transport; [exact ERR4 | exact MU5 | exact WM5 |]. rewrite TPV. rewrite u64_of_Z by (unfold ATP; lia).
      cbn. unfold ATP. split; [lia|]. split; [lia | exact I].
    - exact RA5.
    - eapply (xpres_trans H); [eapply (xpres_weaken H); [exact XP4 | lia | intros bb Hb; exact Hb | intros a Ha; right; exact Ha]|].
      eapply (sk_xpres_mixed H HH LB sk2 pid' A n' spz _ m2 m4 M5 W5 RHN NI ltac:(lia) MU5 WM5).
      apply Forall_cons; [right; right; right; intros a Ha; left; cbn [fst snd] in *; lia|].
      apply Forall_cons; [left; cbn [fst snd]; lia | apply Forall_nil].
    - exact RH5.
    - unfold strA, str_rep. cbn [str_data str_cap]. rewrite Zlen_app1.
      split; [exact Hs|]. split; [exact Hs'|].
      split; [intros i Hi; apply DM5; rewrite (PEQ (p + i) ltac:(lia)); exact (HD i Hi)|].
      split; [lia|].
      split; [split; [lia|]; split; [exact A16|]; split; [lia|]; split; [exact GM|]; split; [unfold SSO_CAP; lia|];
              split; [apply (lbl_in _ pid'); exact HIN4|]; split; [exact PAD|]; split; [exact H0|];
              split; [replace (Zlen cs + 1) with (Zlen cs + 1) by lia; exact H8 | exact H16]|].
      split.
      + intros i Hi. destruct (Z.eq_dec i (Zlen cs)) as [->|Hne].
        * rewrite Znth_app1_eq. split; [lia|]. exact HCc.
        * rewrite Znth_app1_lt by lia. destruct (HC i ltac:(lia)) as [Hr _]. split; [exact Hr|].
          eapply fldA_munch; [exact MU5 | lia | cbn; lia | |].
          -- intros x Hx. cbn in Hx |- *. lia.
          -- apply (sp_chars_back m4 A BYA); [intros j Hj; exact (proj1 (HC j Hj)) | lia].
      + replace (A + (Zlen cs + 1)) with (A + Zlen cs + 1) by lia. exact HZz.
    - split; [exact HIN4|]. eapply SHAD_transport; [exact SHA | exact MU5 | exact WM5 |]. rewrite shadow_of_length by lia.
      pose proof (v4_app_sh p 24 A n' ltac:(lia) ltac:(lia) ltac:(lia) PB2) as D1.
      pose proof (v4_app_sh (A + Zlen cs) 2 A n' ltac:(lia) ltac:(lia) ltac:(lia) ltac:(destruct AB; [left|right]; lia)) as D2.
      cbn [disjoint_from]. repeat split; lia.
    - right. split; [exact FULL|]. split; [exact NI|]. exists A. split; [reflexivity|]. split; [reflexivity|]. split; [exact ABR | reflexivity].
    - eapply addressable_transport; [exact ADV4 | exact MU5 | exact WM5 |].
      pose proof (sp_psh p 24 ltac:(lia) PB2) as D1.
      pose proof (sp_psh (A + Zlen cs) 2 ltac:(lia) ltac:(destruct AB; [left|right]; lia)) as D2.
      rewrite v4_nsh24 in *. cbn [disjoint_from]. repeat split; lia.
    - exact (wr_at_wmono _ _ _ _ WP4 WM5).
    - exact (lb_own_wmono _ _ _ OW4 WM5).
    - exact RF5.
    - exact AC5.
    - eapply stack0_transport; [exact S04 | exact MU5 | exact WM5 |].
      apply Forall_cons; [unfold stack0_ok; cbn [fst snd]; destruct PBAND; [right | left]; unfold AHI_LO; lia|].
      apply Forall_cons; [exact WD4 | apply Forall_nil].
    - exact AL4.
  Qed.

  Lemma sp_gdel : forall (msF3 : machine_state) (mo3 : Model) (sk3 : as_St H) (m3 : mem) (R3 : bvmap 5 word) (pid' : bptr) (A : Z)
                         (sk2 : as_St H) (m2 : mem) (d asz : Z),
    sb = SLong d asz -> Zlen cs = str_cap sb ->
    as_VIS H sk3 msF3 = MS R3 F (Z_to_bv 64 AOPDEL2) fc None m3 (seg_rom asegs) -> rfull R3 ->
    getr R3 1 = Z_to_bv 64 0x1200e8 -> getr R3 10 = Z_to_bv 64 d ->
    getr R3 2 = Z_to_bv 64 (spz - 64) -> getr R3 3 = gp -> getr R3 4 = tp -> getr R3 8 = Z_to_bv 64 c -> getr R3 9 = Z_to_bv 64 p ->
    getr R3 19 = Z_to_bv 64 (str_grow sb) -> getr R3 20 = Z_to_bv 64 (Zlen cs) -> getr R3 22 = Z_to_bv 64 A ->
    getr R3 23 = s7 -> getr R3 24 = s8 -> getr R3 25 = s9 -> getr R3 26 = s10 -> getr R3 27 = s11 ->
    as_AKREL H sk3 (mkCfg msF3 mo3) -> as_MPRES H mo mo3 ->
    smid H LB LBo LF lo spz shi B tp (spz - 64) FRAME s m (str_grow sb) sk3 m3 pid' A [] ->
    ablock_range H A (str_grow sb) -> ~ In pid' (map blk_id LB) ->
    as_RHEAP H sk2 ((pid', A, str_grow sb) :: LB) m2 ->
    SHAD m3 A (shadow_of (str_grow sb)) -> bytes_at asegs m3 A (str_bytes cs) -> (p + 24 <= A \/ A + str_grow sb <= p) ->
    as_SR H Q (mkCfg msF3 mo3).
  Proof.
    intros msF3 mo3 sk3 m3 R3 pid' A sk2 m2 d asz E FULL VIS3 HF3 G1 G10 G2 G3 G4 G8 G9 G19 G20 G22 G23 G24 G25 G26 G27 KR3 MP3
      MID ABR NI RHN SHA BYA PAD.
    pose proof MID as (MI3 & ST3 & (e3 & ERR3) & RA3 & AC3 & RF3 & S03 & RH3 & FR3 & XP3 & AL3 & OW3).
    pose proof SPR as (SPL & SPH & SP16). pose proof LOR as [LO1 LO2].
    unfold SPB_STACK, AOPNEW_STACK, AMALLOC_STACK in LO2, SPL.
    pose proof aceil_facts as ((ACF1 & ACF2) & ACF3 & ACF4).
    pose proof ABR as (A0 & A16 & An & AI & ACE & AFS & AAP). unfold AIMG_TOP in AI.
    destruct (sp_grow_facts FULL) as (GR & GM & GS & GL & _). destruct (GL d asz E) as (AM & A48 & ZC & GE).
    assert (COST : spb_cost H sb cs = as_Cm H (str_grow sb) + as_Cf H asz).
    { unfold spb_cost. rewrite (proj2 (Z.eqb_eq _ _) FULL). rewrite E. reflexivity. }
    set (n' := str_grow sb) in *.
    pose proof BLK as BLK'. rewrite E in BLK'. destruct BLK' as [HIn _].
    pose proof (ah_blocks H HH _ _ _ _ RH0 HIn) as (O0 & O16 & On & OI & OC & OF & OAP).
    cbn [blk_addr blk_size fst snd] in O0, O16, On, OI, OC, OF, OAP.
    assert (HINx : In (pid, d, asz) ((pid', A, n') :: LB)) by (right; exact HIn).
    assert (HINo : In (pid, d, asz) ((pid', A, n') :: LBo)) by (right; pose proof LBO as (_ & _ & X); rewrite E in X; exact X).
    destruct (rw_cells_of_own _ m3 (pid, d, asz) OW3 HINo ltac:(cbn [blk_addr blk_size fst snd]; exact OI)
                ltac:(cbn [blk_addr blk_size fst snd]; lia)) as (obs & OC3).
    cbn [blk_addr blk_size fst snd] in OC3.
    destruct (sk_blk_shad H HH sk3 m3 _ pid d asz RH3 HINx) as (sbs & SHB & SHL).
    assert (CFB : as_Cf H asz <= as_AL H sk3) by (destruct (AOK FULL) as [_ CK]; lia).
    assert (SP64 : (spz - 64) mod 16 = 0) by (Z.div_mod_to_equations; lia).
    rewrite (rfull_eq R3 HF3) in VIS3.
    eapply (ah_seq H HH).
    { eapply (ah_opdel2 H HH) with (p := pid) (A := d) (n := asz) (LB := (pid', A, n') :: LB) (lo := lo) (B := B)
          (errv := e3) (CH := []) (bs := obs) (sbs := sbs);
          [ exact VIS3 | exact RH3 | exact KR3 | exact HINx | exact CFB | exact OC3 | exact SHB | exact SHL
          | exact RA3 | rewrite G2, u64_of_Z by lia; lia
          | rewrite G2, u64_of_Z by lia; exact (proj1 (stk_split asegs m3 lo (spz - 64) spz ST3 ltac:(lia)))
          | exact LO1 | rewrite G2, u64_of_Z by lia; unfold AFREE_STACK; lia
          | rewrite G4; exact ERR3 | exact MI3 | rewrite G4; exact TPV | rewrite G2, u64_of_Z by lia; exact SP64 | exact AC3
          | rewrite G8; unfold wz; rewrite u64_of_Z by lia; apply (ah_chain_nil H HH); left; lia
          | rewrite G1; cbn [map]; unfold wz; rewrite u64_of_Z by lia; exact TRO
          | exact G10 ]. }
    intros c2 POST. destruct c2 as [msF4 mo4].
    destruct POST as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m4 & s4'
                      & VIS4 & KR4 & MP4 & MI4 & ST4 & ERR4 & RA4 & AP4 & RH4 & AC4 & AL4).
    cbn [cfg_ms cfg_model] in VIS4, KR4, MP4.
    rewrite G1 in VIS4. rewrite (ret_pc_even 0x1200e8 ltac:(lia) eq_refl) in VIS4.
    rewrite G2, u64_of_Z in ST4, AP4 by lia. rewrite G4 in ERR4.
    assert (NEQ : pid' <> pid) by (intros EQ; apply NI; rewrite EQ; apply in_map_iff; exists (pid, d, asz); split; [reflexivity | exact HIn]).
    pose proof (ah_lb_remove H HH) as (L1 & L2 & L3).
    assert (RMx : as_lb_remove H pid ((pid', A, n') :: LB) = (pid', A, n') :: as_lb_remove H pid LB).
    { apply L2. cbn [blk_id fst]. exact NEQ. }
    rewrite RMx in AP4, RH4.
    assert (LB4 : spb_LB H LB sb pid pid' A = (pid', A, n') :: as_lb_remove H pid LB) by (unfold spb_LB, n'; rewrite E; reflexivity).
    assert (XPF0 : xpres H LB (spz - 64) (spb_x sb) m3 m4).
    { eapply (xpres_of_apres_rm H HH sk3 LB ((pid', A, n') :: LB) (spz - 64) _ m3 m3 m4 pid d asz RH3 HINx);
        [intros bb Hb; right; exact Hb | rewrite RMx; exact AP4 | |].
      - intros a Ha. rewrite E. cbn [spb_x]. left. cbn [fst snd]. lia.
      - intros a Ha. rewrite E. cbn [spb_x]. right. left. cbn [fst snd]. lia. }
    assert (XPF : xpres H LB spz (spb_x sb) m3 m4)
      by (eapply (xpres_weaken H); [exact XPF0 | lia | intros bb Hb; exact Hb | intros a Ha; exact Ha]).
    assert (INA : In (pid', A, n') ((pid', A, n') :: as_lb_remove H pid LB)) by (left; reflexivity).
    eapply (sp_g4 msF4 mo4 s4' m4 _ pid' A e3 sk2 m2 FULL VIS4 (rfull_mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)).
    - exact G2.
    - exact G3.
    - exact G4.
    - exact G8.
    - exact G9.
    - exact G19.
    - exact G20.
    - exact G22.
    - exact G23.
    - exact G24.
    - exact G25.
    - exact G26.
    - exact G27.
    - exact KR4.
    - eapply (ah_mpres_trans H HH); [exact MP3 | exact MP4].
    - exact MI4.
    - eapply (stk_merge asegs); [exact ST4 | | lia].
      eapply (apres_stk H); [exact AP4 | exact (proj2 (stk_split asegs m3 lo (spz - 64) spz ST3 ltac:(lia))) | lia].
    - exact ERR4.
    - exact RA4.
    - exact AC4.
    - exact (RFS_via_apres H HH LF _ _ m3 m4 RF3 AP4).
    - eapply (stack0_xpres H); [exact (xpres_of_apres H _ _ [] _ _ AP4) | exact S03 | apply Forall_nil].
    - rewrite LB4. exact RH4.
    - exact NI.
    - exact RHN.
    - eapply (apres_rw_cells H); [exact AP4 | exact FR3 | left; lia].
    - eapply (xpres_trans H); [eapply (xpres_weaken H); [exact XP3 | lia | intros bb Hb; exact Hb | intros a Ha; destruct Ha] | exact XPF].
    - rewrite COST. lia.
    - assert (LB4o : spb_LB H LBo sb pid pid' A = (pid', A, n') :: as_lb_remove H pid LBo) by (unfold spb_LB, n'; rewrite E; reflexivity).
      rewrite LB4o. eapply (lb_own_apres H); [| exact AP4 |].
      + eapply lb_own_incl; [| exact OW3]. intros bb [Hb|Hb]; [left; exact Hb | right; exact (L3 _ _ _ Hb)].
      + pose proof LBO as (LBI & LBND & _). pose proof (ah_nodup H HH _ _ _ RH0) as NDL.
        intros bb [<-|Hb]; [left; reflexivity | right; exact (spb_rm_incl pid LBo LB LBI LBND NDL bb Hb)].
    - exact ABR.
    - eapply (apres_SHAD H); [exact AP4 | exact SHA |]. rewrite shadow_of_length by lia. eapply (aclient_range_block_sh H). exact INA.
    - eapply (apres_bytes_at H); [exact AP4 | exact BYA |]. rewrite str_bytes_length.
      eapply (aclient_range_block H); [exact INA | lia | unfold Zlen in GS; lia].
    - exact PAD.
  Qed.

  Lemma sp_g3 : forall (msF3 : machine_state) (mo3 : Model) (sk3 : as_St H) (m3 : mem) (R3 : bvmap 5 word) (pid' : bptr) (A : Z)
                       (sk2 : as_St H) (m2 : mem),
    Zlen cs = str_cap sb ->
    as_VIS H sk3 msF3 = MS R3 F (Z_to_bv 64 0x1200d4) fc None m3 (seg_rom asegs) -> rfull R3 ->
    getr R3 2 = Z_to_bv 64 (spz - 64) -> getr R3 3 = gp -> getr R3 4 = tp -> getr R3 8 = Z_to_bv 64 c -> getr R3 9 = Z_to_bv 64 p ->
    getr R3 18 = Z_to_bv 64 (spb_od sb) -> getr R3 19 = Z_to_bv 64 (str_grow sb) -> getr R3 20 = Z_to_bv 64 (Zlen cs) ->
    getr R3 21 = Z_to_bv 64 (spb_s5 sb) -> getr R3 22 = Z_to_bv 64 A ->
    getr R3 23 = s7 -> getr R3 24 = s8 -> getr R3 25 = s9 -> getr R3 26 = s10 -> getr R3 27 = s11 ->
    as_AKREL H sk3 (mkCfg msF3 mo3) -> as_MPRES H mo mo3 ->
    smid H LB LBo LF lo spz shi B tp (spz - 64) FRAME s m (str_grow sb) sk3 m3 pid' A [] ->
    ablock_range H A (str_grow sb) -> ~ In pid' (map blk_id LB) ->
    as_RHEAP H sk2 ((pid', A, str_grow sb) :: LB) m2 ->
    SHAD m3 A (shadow_of (str_grow sb)) -> bytes_at asegs m3 A (str_bytes cs) -> (p + 24 <= A \/ A + str_grow sb <= p) ->
    as_SR H Q (mkCfg msF3 mo3).
  Proof.
    intros msF3 mo3 sk3 m3 R3 pid' A sk2 m2 FULL VIS3 HF3 G2 G3 G4 G8 G9 G18 G19 G20 G21 G22 G23 G24 G25 G26 G27 KR3 MP3
      MID ABR NI RHN SHA BYA PAD.
    destruct (sp_grow_facts FULL) as (GR & GM & GS & GL & GSh).
    destruct (sbuf_cases sb) as [E|(d & asz & E)].
    -
      assert (G21' : getr R3 21 = wz 23) by (rewrite G21, E; reflexivity).
      destruct (spb_B3S_ok R3 F fc m3 G21') as (R4 & Hms & KK).
      pose proof (msteps_full asegs _ _ Hms HF3) as HF4. cbn [ms_regs] in HF4.
      pose proof MID as (MI3 & ST3 & (e3 & ERR3) & RA3 & AC3 & RF3 & S03 & RH3 & FR3 & XP3 & AL3 & OW3).
      eapply (sr_blk H HH); [exact KR3 | exact VIS3 | exact HF3 | exact Hms |].
      intros msF4 mo4 KR4 MP4 VIS4. rewrite <- (rfull_eq R4 HF4) in VIS4.
      assert (LB4 : spb_LB H LB sb pid pid' A = (pid', A, str_grow sb) :: LB) by (unfold spb_LB; rewrite E; reflexivity).
      assert (LB4o : spb_LB H LBo sb pid pid' A = (pid', A, str_grow sb) :: LBo) by (unfold spb_LB; rewrite E; reflexivity).
      eapply (sp_g4 msF4 mo4 sk3 m3 R4 pid' A e3 sk2 m2 FULL VIS4 HF4).
      + rewrite (KK 2%bv ltac:(inb)). exact G2.
      + rewrite (KK 3%bv ltac:(inb)). exact G3.
      + rewrite (KK 4%bv ltac:(inb)). exact G4.
      + rewrite (KK 8%bv ltac:(inb)). exact G8.
      + rewrite (KK 9%bv ltac:(inb)). exact G9.
      + rewrite (KK 19%bv ltac:(inb)). exact G19.
      + rewrite (KK 20%bv ltac:(inb)). exact G20.
      + rewrite (KK 22%bv ltac:(inb)). exact G22.
      + rewrite (KK 23%bv ltac:(inb)). exact G23.
      + rewrite (KK 24%bv ltac:(inb)). exact G24.
      + rewrite (KK 25%bv ltac:(inb)). exact G25.
      + rewrite (KK 26%bv ltac:(inb)). exact G26.
      + rewrite (KK 27%bv ltac:(inb)). exact G27.
      + exact KR4.
      + eapply (ah_mpres_trans H HH); [exact MP3 | exact MP4].
      + exact MI3.
      + exact ST3.
      + exact ERR3.
      + exact RA3.
      + exact AC3.
      + exact RF3.
      + exact S03.
      + rewrite LB4. exact RH3.
      + exact NI.
      + exact RHN.
      + exact FR3.
      + eapply (xpres_weaken H); [exact XP3 | lia | intros bb Hb; exact Hb | intros a Ha; destruct Ha].
      + unfold spb_cost. rewrite (proj2 (Z.eqb_eq _ _) FULL). replace (spb_old sb) with 0 by (rewrite E; reflexivity).
        pose proof (ah_costs H HH) as (_ & _ & CF & _). pose proof (CF 0 ltac:(lia)). lia.
      + rewrite LB4o. exact OW3.
      + exact ABR.
      + exact SHA.
      + exact BYA.
      + exact PAD.
    -
      destruct (GL d asz E) as (AM & A48 & ZC & GE).
      assert (G21' : getr R3 21 = wz asz) by (rewrite G21, E; reflexivity).
      destruct (spb_B3L_ok R3 F fc m3 asz G21' ltac:(lia)) as (R4 & Hms & K1 & K10 & K11 & KK).
      pose proof (msteps_full asegs _ _ Hms HF3) as HF4. cbn [ms_regs] in HF4.
      eapply (sr_blk H HH); [exact KR3 | exact VIS3 | exact HF3 | exact Hms |].
      intros msF4 mo4 KR4 MP4 VIS4. rewrite <- (rfull_eq R4 HF4) in VIS4.
      eapply (sp_gdel msF4 mo4 sk3 m3 R4 pid' A sk2 m2 d asz E FULL VIS4 HF4).
      + exact K1.
      + rewrite K10, G18, E. reflexivity.
      + rewrite (KK 2%bv ltac:(inb)). exact G2.
      + rewrite (KK 3%bv ltac:(inb)). exact G3.
      + rewrite (KK 4%bv ltac:(inb)). exact G4.
      + rewrite (KK 8%bv ltac:(inb)). exact G8.
      + rewrite (KK 9%bv ltac:(inb)). exact G9.
      + rewrite (KK 19%bv ltac:(inb)). exact G19.
      + rewrite (KK 20%bv ltac:(inb)). exact G20.
      + rewrite (KK 22%bv ltac:(inb)). exact G22.
      + rewrite (KK 23%bv ltac:(inb)). exact G23.
      + rewrite (KK 24%bv ltac:(inb)). exact G24.
      + rewrite (KK 25%bv ltac:(inb)). exact G25.
      + rewrite (KK 26%bv ltac:(inb)). exact G26.
      + rewrite (KK 27%bv ltac:(inb)). exact G27.
      + exact KR4.
      + eapply (ah_mpres_trans H HH); [exact MP3 | exact MP4].
      + exact MID.
      + exact ABR.
      + exact NI.
      + exact RHN.
      + exact SHA.
      + exact BYA.
      + exact PAD.
  Qed.

  Definition sp_srcf (mk : mem) : Prop :=
    bytes_at asegs mk (spb_od sb) (str_bytes cs) /\ accessible mk (spb_od sb) (Zlen cs) /\ shvis mk (spb_od sb) (spb_od sb + Zlen cs).

  Lemma sp_od_facts : Zlen cs = str_cap sb ->
    in_app_mem (spb_od sb) (spb_od sb + Zlen cs) /\ (spb_od sb + Zlen cs <= lo \/ spz <= spb_od sb)
    /\ 0 <= spb_od sb /\ spb_od sb + Zlen cs <= 2 ^ 47
    /\ (forall s' mk pid' A n, as_RHEAP H s' ((pid', A, n) :: LB) mk -> ~ In pid' (map blk_id LB) ->
          spb_od sb + Zlen cs <= A \/ A + n <= spb_od sb).
  Proof.
    intros FULL. destruct (sp_grow_facts FULL) as (GR & GM & GS & GL & GSh).
    pose proof aceil_facts as ((ACF1 & ACF2) & ACF3 & ACF4). pose proof LOR as [LO1 LO2].
    unfold SPB_STACK, AOPNEW_STACK, AMALLOC_STACK in LO2.
    destruct (sbuf_cases sb) as [E|(d & asz & E)].
    - destruct (GSh E) as [ZC GE]. rewrite E. cbn [spb_od]. rewrite ZC.
      pose proof sp_pband as PB. destruct (sp_pff_range m RF0) as [FF1 FF2].
      pose proof (ah_fsb H HH _ _ _ RH0) as (FS1 & FS2 & FS3 & FS4).
      destruct OBJ as (_ & _ & _ & _ & _ & SD).
      split; [unfold in_app_mem; destruct PBAND; [left | right]; unfold ASHADOW_BASE, AHI_LO, AAPP_HI; lia|].
      split; [lia|]. split; [lia|]. split; [lia|].
      intros s' mk pid' A n RH NI.
      pose proof (ah_blocks H HH _ _ _ (pid', A, n) RH (or_introl eq_refl)) as (R0 & R16 & Rn & RI & RC & RF & RAPP).
      cbn [blk_addr blk_size fst snd] in R0, R16, Rn, RI, RC, RF, RAPP. unfold AFS_SIZE in *. destruct RF; lia.
    - destruct (GL d asz E) as (AM & A48 & ZC & GE). rewrite E. cbn [spb_od].
      pose proof BLK as BLK'. rewrite E in BLK'. destruct BLK' as [HIn _].
      pose proof (ah_blocks H HH _ _ _ _ RH0 HIn) as (O0 & O16 & On & OI & OC & OF & OAP).
      cbn [blk_addr blk_size fst snd] in O0, O16, On, OI, OC, OF, OAP.
      split; [unfold in_app_mem; destruct (vo_band_of_aapp' d asz OAP) as [K|K]; [left | right]; unfold ASHADOW_BASE, AHI_LO, AAPP_HI; lia|].
      split; [left; lia|]. split; [lia|]. split; [lia|].
      intros s' mk pid' A n RH NI.
      assert (NEQ : pid' <> pid) by (intros EQ; apply NI; rewrite EQ; apply in_map_iff; exists (pid, d, asz); split; [reflexivity | exact HIn]).
      pose proof (ah_disj H HH _ _ _ (pid', A, n) (pid, d, asz) RH (or_introl eq_refl) (or_intror HIn) NEQ) as D.
      cbn [blk_addr blk_size fst snd] in D. lia.
  Qed.

  Lemma sp_gmm : forall (msF2 : machine_state) (mo2 : Model) (sk2 : as_St H) (m2 : mem) (R2 : bvmap 5 word) (pid' : bptr) (A : Z)
                        (junk : list byte),
    Zlen cs = str_cap sb ->
    as_VIS H sk2 msF2 = MS R2 F (Z_to_bv 64 AMEMMOVE_STUB) fc None m2 (seg_rom asegs) -> rfull R2 ->
    getr R2 1 = Z_to_bv 64 0x1200d4 -> getr R2 10 = Z_to_bv 64 A -> getr R2 11 = Z_to_bv 64 (spb_od sb) ->
    getr R2 12 = Z_to_bv 64 (Zlen cs) ->
    getr R2 2 = Z_to_bv 64 (spz - 64) -> getr R2 3 = gp -> getr R2 4 = tp -> getr R2 8 = Z_to_bv 64 c -> getr R2 9 = Z_to_bv 64 p ->
    getr R2 18 = Z_to_bv 64 (spb_od sb) -> getr R2 19 = Z_to_bv 64 (str_grow sb) -> getr R2 20 = Z_to_bv 64 (Zlen cs) ->
    getr R2 21 = Z_to_bv 64 (spb_s5 sb) -> getr R2 22 = Z_to_bv 64 A ->
    getr R2 23 = s7 -> getr R2 24 = s8 -> getr R2 25 = s9 -> getr R2 26 = s10 -> getr R2 27 = s11 ->
    as_AKREL H sk2 (mkCfg msF2 mo2) -> as_MPRES H mo mo2 ->
    smid H LB LBo LF lo spz shi B tp (spz - 64) FRAME s m (str_grow sb) sk2 m2 pid' A [] ->
    ablock_range H A (str_grow sb) -> ~ In pid' (map blk_id LB) ->
    rw_cells asegs m2 A [CB (Z.to_nat (str_grow sb)) junk] -> addressable m2 A (str_grow sb) ->
    sp_srcf m2 -> (p + 24 <= A \/ A + str_grow sb <= p) ->
    as_SR H Q (mkCfg msF2 mo2).
  Proof.
    intros msF2 mo2 sk2 m2 R2 pid' A junk FULL VIS2 HF2 G1 G10 G11 G12 G2 G3 G4 G8 G9 G18 G19 G20 G21 G22 G23 G24 G25 G26 G27
      KR2 MP2 MID ABR NI CBall ADDR SRCF PAD.
    pose proof MID as (MI2 & ST2 & (e2 & ERR2) & RA2 & AC2 & RF2 & S02 & RH2 & FR2 & XP2 & AL2 & OW2).
    pose proof SPR as (SPL & SPH & SP16). pose proof LOR as [LO1 LO2].
    unfold SPB_STACK, AOPNEW_STACK, AMALLOC_STACK in LO2, SPL.
    pose proof aceil_facts as ((ACF1 & ACF2) & ACF3 & ACF4).
    pose proof ABR as (A0 & A16 & An & AI & ACE & AFS & AAP). unfold AIMG_TOP in AI.
    destruct (sp_grow_facts FULL) as (GR & GM & GS & _ & _).
    destruct (sp_od_facts FULL) as (OAM & OFAR & OD0 & ODH & ODJ).
    pose proof (ODJ sk2 m2 pid' A (str_grow sb) RH2 NI) as DJA.
    assert (ZL0 : 0 <= Zlen cs) by (unfold Zlen; lia).
    destruct SRCF as (SB & SACC & SSV).
    set (n' := str_grow sb) in *. set (od := spb_od sb) in *.
    destruct (rw_cells_CB_split asegs m2 A (Z.to_nat n') (Z.to_nat (Zlen cs)) junk CBall ltac:(lia)) as [CBA _].
    rewrite (rfull_eq R2 HF2) in VIS2.
    eapply (ahh_evt_then H HH); [exact KR2 | exact VIS2 | |].
    { eapply (ah_memmove_icpt H HH) with (src := str_bytes cs) (junk := firstn (Z.to_nat (Zlen cs)) junk) (lo := lo);
        rewrite ?G10, ?G11, ?G12, ?G2; rewrite ?u64_of_Z by lia.
      - exact SB.
      - rewrite str_bytes_length. unfold Zlen. lia.
      - exact CBA.
      - lia.
      - exact SACC.
      - eapply addressable_accessible; [exact ADDR | lia | lia | unfold AAPP_HI; lia].
      - exact SSV.
      - eapply shvis_sub; [exact (ah_blk_shvis H HH _ _ _ _ _ _ RH2 (or_introl eq_refl)) | lia | lia | lia | lia | lia].
      - exact (proj1 (stk_split asegs m2 lo (spz - 64) spz ST2 ltac:(lia))).
      - exact LO1.
      - unfold AINTRIN_STACK; lia.
      - exact MI2.
      - exact AC2.
      - lia.
      - exact OAM.
      - unfold in_app_mem. destruct (vo_band_of_aapp' _ _ AAP) as [K|K]; [left | right]; unfold ASHADOW_BASE, AHI_LO, AAPP_HI; lia.
      - eapply aconst_ok_app; [exact AAP | lia | lia].
      - left; lia.
      - destruct OFAR as [K|K]; [left | right]; lia. }
    intros msF3 mo3 KR3 MP3 POST.
    destruct POST as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m3
                      & VIS3 & MU3 & WM3 & MI3 & ST3 & CB3 & AC3).
    rewrite G10, G12, G2, ?u64_of_Z in MU3 by lia. rewrite G10, G12, ?u64_of_Z in CB3 by lia. rewrite G2, u64_of_Z in ST3 by lia.
    unfold AINTRIN_STACK in MU3.
    rewrite G1 in VIS3. rewrite (ret_pc_even 0x1200d4 ltac:(lia) eq_refl) in VIS3.
    assert (W3 : Forall (swk H LB LF spz (spz - 64) A n' []) [(A, A + Zlen cs); (spz - 64 - 4096, spz - 64)]).
    { apply Forall_cons; [right; left; cbn [fst snd]; lia|]. apply Forall_cons; [left; cbn [fst snd]; lia | apply Forall_nil]. }
    assert (FRS : spz - 64 + Z.of_nat (cells_size FRAME) <= spz) by (unfold FRAME; rewrite v4_cells_size_map_C8'; cbn [length]; lia).
    eapply (sp_g3 msF3 mo3 sk2 m3 _ pid' A sk2 m2 FULL VIS3 (rfull_mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)).
    - exact G2.
    - exact G3.
    - exact G4.
    - exact G8.
    - exact G9.
    - exact G18.
    - exact G19.
    - exact G20.
    - exact G21.
    - exact G22.
    - exact G23.
    - exact G24.
    - exact G25.
    - exact G26.
    - exact G27.
    - exact KR3.
    - eapply (ah_mpres_trans H HH); [exact MP2 | exact MP3].
    - eapply (smid_munch H HH) with (fb := spz - 64); [exact MID | exact ABR | exact NI | exact LO1 | lia | lia | exact FRS | lia | exact TPV
                               | exact MU3 | exact WM3 | exact MI3 | exact W3].
    - exact ABR.
    - exact NI.
    - exact RH2.
    - eapply SHAD_transport; [exact (proj2 ADDR) | exact MU3 | exact WM3 |]. rewrite shadow_of_length by lia.
      pose proof (v4_app_sh A (Zlen cs) A n' ltac:(lia) ltac:(lia) ltac:(lia) ltac:(destruct (vo_band_of_aapp' _ _ AAP); [left|right]; lia)) as D.
      pose proof (sh_nsh_high A n' ltac:(lia) ltac:(lia) ltac:(unfold AAPP_HI; lia)) as D2. unfold AHI_LO in D2.
      change (str_grow sb) with n'. cbn [disjoint_from fst snd]. split; [lia | split; [lia | exact I]].
    - exact (bytes_of_CB _ _ _ _ CB3).
    - exact PAD.
  Qed.

  Lemma sp_g2 : forall (msF2 : machine_state) (mo2 : Model) (sk2 : as_St H) (m2 : mem) (R2 : bvmap 5 word) (pid' : bptr) (A : Z)
                       (junk : list byte),
    Zlen cs = str_cap sb ->
    as_VIS H sk2 msF2 = MS R2 F (Z_to_bv 64 0x1200c4) fc None m2 (seg_rom asegs) -> rfull R2 ->
    getr R2 2 = Z_to_bv 64 (spz - 64) -> getr R2 3 = gp -> getr R2 4 = tp -> getr R2 8 = Z_to_bv 64 c -> getr R2 9 = Z_to_bv 64 p ->
    getr R2 10 = Z_to_bv 64 A ->
    getr R2 18 = Z_to_bv 64 (spb_od sb) -> getr R2 19 = Z_to_bv 64 (str_grow sb) -> getr R2 20 = Z_to_bv 64 (Zlen cs) ->
    getr R2 21 = Z_to_bv 64 (spb_s5 sb) ->
    getr R2 23 = s7 -> getr R2 24 = s8 -> getr R2 25 = s9 -> getr R2 26 = s10 -> getr R2 27 = s11 ->
    as_AKREL H sk2 (mkCfg msF2 mo2) -> as_MPRES H mo mo2 ->
    smid H LB LBo LF lo spz shi B tp (spz - 64) FRAME s m (str_grow sb) sk2 m2 pid' A [] ->
    ablock_range H A (str_grow sb) -> ~ In pid' (map blk_id LB) ->
    rw_cells asegs m2 A [CB (Z.to_nat (str_grow sb)) junk] -> addressable m2 A (str_grow sb) ->
    sp_srcf m2 -> (p + 24 <= A \/ A + str_grow sb <= p) ->
    as_SR H Q (mkCfg msF2 mo2).
  Proof.
    intros msF2 mo2 sk2 m2 R2 pid' A junk FULL VIS2 HF2 G2 G3 G4 G8 G9 G10 G18 G19 G20 G21 G23 G24 G25 G26 G27
      KR2 MP2 MID ABR NI CBall ADDR SRCF PAD.
    destruct (spb_B2_ok R2 F fc m2) as (R3 & Hms & K1 & K10 & K11 & K12 & K22 & KK).
    pose proof (msteps_full asegs _ _ Hms HF2) as HF3. cbn [ms_regs] in HF3.
    eapply (sr_blk H HH); [exact KR2 | exact VIS2 | exact HF2 | exact Hms |].
    intros msF3 mo3 KR3 MP3 VIS3. rewrite <- (rfull_eq R3 HF3) in VIS3.
    eapply (sp_gmm msF3 mo3 sk2 m2 R3 pid' A junk FULL VIS3 HF3).
    - exact K1.
    - rewrite K10. exact G10.
    - rewrite K11. exact G18.
    - rewrite K12. exact G20.
    - rewrite (KK 2%bv ltac:(inb)). exact G2.
    - rewrite (KK 3%bv ltac:(inb)). exact G3.
    - rewrite (KK 4%bv ltac:(inb)). exact G4.
    - rewrite (KK 8%bv ltac:(inb)). exact G8.
    - rewrite (KK 9%bv ltac:(inb)). exact G9.
    - rewrite (KK 18%bv ltac:(inb)). exact G18.
    - rewrite (KK 19%bv ltac:(inb)). exact G19.
    - rewrite (KK 20%bv ltac:(inb)). exact G20.
    - rewrite (KK 21%bv ltac:(inb)). exact G21.
    - rewrite K22. exact G10.
    - rewrite (KK 23%bv ltac:(inb)). exact G23.
    - rewrite (KK 24%bv ltac:(inb)). exact G24.
    - rewrite (KK 25%bv ltac:(inb)). exact G25.
    - rewrite (KK 26%bv ltac:(inb)). exact G26.
    - rewrite (KK 27%bv ltac:(inb)). exact G27.
    - exact KR3.
    - eapply (ah_mpres_trans H HH); [exact MP2 | exact MP3].
    - exact MID.
    - exact ABR.
    - exact NI.
    - exact CBall.
    - exact ADDR.
    - exact SRCF.
    - exact PAD.
  Qed.

  Lemma sp_srcf_keep : forall sk mk pid' A n, Zlen cs = str_cap sb -> xpres H LB spz [] m mk -> as_RFS H LF mk ->
    as_RHEAP H sk ((pid', A, n) :: LB) mk -> sp_srcf mk.
  Proof.
    intros sk mk pid' A n FULL XP RF RH.
    destruct (sp_grow_facts FULL) as (GR & GM & GS & GL & GSh).
    pose proof aceil_facts as ((ACF1 & ACF2) & _ & _).
    pose proof (sp_chars_bytes LB m REP) as CB0.
    assert (ZL0 : 0 <= Zlen cs) by (unfold Zlen; lia).
    pose proof sp_pband as PB.
    unfold sp_srcf. destruct (sbuf_cases sb) as [E|(d & asz & E)].
    - destruct (GSh E) as [ZC GE]. rewrite E in CB0 |- *. cbn [spb_od] in CB0 |- *. rewrite ZC.
      destruct (sp_pff_range m RF0) as [FF1 FF2].
      split.
      + eapply (xpres_bytes_at H); [exact XP | exact CB0 |]. rewrite str_bytes_length. unfold Zlen in ZC. rewrite ZC.
        split; [right; right; right; right; left; lia | apply Forall_nil].
      + destruct (sp_pkeep LB spz [] m mk RF0 XP (Forall_nil _) (Forall_nil _)) as (_ & KA & _).
        split; [eapply addressable_accessible; [exact (KA ADV0) | lia | lia | unfold AAPP_HI; lia]|].
        destruct PFF as (f & Hf & K1 & K2).
        destruct (ah_RFS_range H HH LF mk RF) as [AF RR]. destruct (RR f Hf) as (Q0 & Q1 & Q2 & _).
        destruct AF as (FS1 & FS2 & FS3 & FS4). unfold AFS_HDR in Q1. unfold AIMG_TOP in FS1.
        eapply shvis_sub; [exact (ah_frm_shvis H HH LF mk f RF Hf) | lia | lia | lia | lia | lia].
    - destruct (GL d asz E) as (AM & A48 & ZC & GE). rewrite E in CB0 |- *. cbn [spb_od] in CB0 |- *.
      pose proof BLK as BLK'. rewrite E in BLK'. destruct BLK' as [HIn SHD].
      pose proof (ah_blocks H HH _ _ _ _ RH0 HIn) as (O0 & O16 & On & OI & OC & OF & OAP).
      cbn [blk_addr blk_size fst snd] in O0, O16, On, OI, OC, OF, OAP.
      split.
      + eapply (xpres_bytes_at H); [exact XP | exact CB0 |]. rewrite str_bytes_length.
        split; [eapply (aclient_range_block H); [exact HIn | lia | unfold Zlen in ZC; lia] | apply Forall_nil].
      + assert (SHD' : SHAD mk d (shadow_of asz)).
        { destruct SHD as (S0 & S8 & [UB UW]). split; [exact S0|]. split; [exact S8|].
          assert (XCS : xclient_range H LB spz [] (sh d) (Z.of_nat (length (shadow_of asz))))
            by (rewrite shadow_of_length by lia; split; [eapply (aclient_range_block_sh H); exact HIn | apply Forall_nil]).
          split; [eapply (xpres_bytes_at H); [exact XP | exact UB | exact XCS] | eapply (xpres_wr_at H); [exact XP | exact UW | exact XCS]]. }
        split; [eapply (addressable_accessible mk d asz); [split; [lia | exact SHD'] | lia | lia | unfold AAPP_HI; lia]|].
        eapply shvis_sub; [exact (ah_blk_shvis H HH _ _ _ _ _ _ RH (or_intror HIn)) | lia | lia | lia | lia | lia].
  Qed.

  Lemma sp_gnew : forall (msF1 : machine_state) (mo1 : Model) (m1 : mem) (R1 : bvmap 5 word) (e1 : word),
    Zlen cs = str_cap sb ->
    as_VIS H s msF1 = MS R1 F (Z_to_bv 64 AOPNEW) fc None m1 (seg_rom asegs) -> rfull R1 ->
    getr R1 1 = Z_to_bv 64 0x1200c4 -> getr R1 2 = Z_to_bv 64 (spz - 64) -> getr R1 3 = gp -> getr R1 4 = tp ->
    getr R1 8 = Z_to_bv 64 c -> getr R1 9 = Z_to_bv 64 p -> getr R1 10 = Z_to_bv 64 (str_grow sb) ->
    getr R1 18 = Z_to_bv 64 (spb_od sb) -> getr R1 19 = Z_to_bv 64 (str_grow sb) -> getr R1 20 = Z_to_bv 64 (Zlen cs) ->
    getr R1 21 = Z_to_bv 64 (spb_s5 sb) ->
    getr R1 23 = s7 -> getr R1 24 = s8 -> getr R1 25 = s9 -> getr R1 26 = s10 -> getr R1 27 = s11 ->
    as_AKREL H s (mkCfg msF1 mo1) -> as_MPRES H mo mo1 ->
    mem_inv asegs m1 -> stk asegs m1 lo spz -> rw_cells asegs m1 (errno_addr tp) [C4 e1] -> as_rauxv_ok H m1 B ->
    ACONST m1 -> as_RFS H LF m1 -> stack0 m1 lo shi -> as_RHEAP H s LB m1 -> rw_cells asegs m1 (spz - 64) FRAME ->
    xpres H LB spz [] m m1 -> lb_own LBo m1 ->
    as_SR H Q (mkCfg msF1 mo1).
  Proof.
    intros msF1 mo1 m1 R1 e1 FULL VIS1 HF1 G1 G2 G3 G4 G8 G9 G10 G18 G19 G20 G21 G23 G24 G25 G26 G27 KR1 MP1
      MI1 ST1 ERR1 RA1 AC1 RF1 S01 RH1 FR1 XP1 OW1.
    pose proof SPR as (SPL & SPH & SP16). pose proof LOR as [LO1 LO2].
    unfold SPB_STACK, AOPNEW_STACK, AMALLOC_STACK in LO2, SPL.
    pose proof aceil_facts as ((ACF1 & ACF2) & ACF3 & ACF4).
    destruct (sp_grow_facts FULL) as (GR & GM & GS & _ & _).
    destruct (AOK FULL) as [AOK' CK].
    assert (CMB : as_Cm H (str_grow sb) <= as_AL H s).
    { unfold spb_cost in CK. rewrite (proj2 (Z.eqb_eq _ _) FULL) in CK.
      pose proof (ah_costs H HH) as (_ & _ & CF & _).
      assert (0 <= spb_old sb).
      { destruct (sbuf_cases sb) as [E|(d & asz & E)]; rewrite E; cbn [spb_old]; [lia|].
        destruct (sp_grow_facts FULL) as (_ & _ & _ & GL' & _). destruct (GL' d asz E) as (_ & A48 & _). lia. }
      pose proof (CF (spb_old sb) ltac:(lia)). lia. }
    assert (SP64 : (spz - 64) mod 16 = 0) by (Z.div_mod_to_equations; lia).
    rewrite (rfull_eq R1 HF1) in VIS1.
    eapply (ah_seq H HH).
    { eapply (ah_opnew H HH) with (n := str_grow sb) (LB := LB) (lo := lo) (B := B) (errv := e1);
        [ exact VIS1 | exact RH1 | exact KR1 | exact AOK' | exact CMB | exact RA1 | rewrite G2, u64_of_Z by lia; lia
        | rewrite G2, u64_of_Z by lia; exact (proj1 (stk_split asegs m1 lo (spz - 64) spz ST1 ltac:(lia)))
        | exact LO1 | rewrite G2, u64_of_Z by lia; unfold AOPNEW_STACK, AMALLOC_STACK; lia
        | rewrite G4; exact ERR1 | exact MI1 | rewrite G4; exact TPV | rewrite G2, u64_of_Z by lia; exact SP64
        | exact AC1 | exact G10 | lia ]. }
    intros c2 POST. destruct c2 as [msF2 mo2].
    destruct POST as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m2 & errv2 & A & junk & p'
                      & sk2 & VIS2 & KR2 & MP2 & MI2 & ST2 & ERR2 & RAX2 & AP2 & ABR & RH2 & CB2 & ADDR & AC2 & AL2).
    cbn [cfg_ms cfg_model] in VIS2, KR2, MP2.
    rewrite G1 in VIS2. rewrite (ret_pc_even 0x1200c4 ltac:(lia) eq_refl) in VIS2.
    rewrite G2, u64_of_Z in AP2, ST2 by lia. rewrite G4 in ERR2.
    pose proof (ah_nodup H HH _ _ _ RH2) as ND. cbn [map] in ND. apply NoDup_cons_iff in ND as [NI _].
    cbn [blk_id fst] in NI.
    assert (RF2 : as_RFS H LF m2) by exact (RFS_via_apres H HH LF LB _ m1 m2 RF1 AP2).
    assert (XP2 : xpres H LB spz [] m m2).
    { eapply (xpres_trans H); [exact XP1 |].
      eapply (xpres_weaken H); [exact (xpres_of_apres H _ _ [] _ _ AP2) | lia | intros bb Hb; exact Hb | intros a Ha; exact Ha]. }
    pose proof ABR as (A0 & A16 & An & AI & ACE & AFS & AAP). unfold AIMG_TOP in AI.
    assert (PAD : p + 24 <= A \/ A + str_grow sb <= p).
    { destruct (sp_pff_range m RF0) as [FF1 FF2]. unfold AFS_SIZE in *. destruct AFS; lia. }
    eapply (sp_g2 msF2 mo2 sk2 m2 _ p' A junk FULL VIS2 (rfull_mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)).
    - exact G2.
    - exact G3.
    - exact G4.
    - exact G8.
    - exact G9.
    - reflexivity.
    - exact G18.
    - exact G19.
    - exact G20.
    - exact G21.
    - exact G23.
    - exact G24.
    - exact G25.
    - exact G26.
    - exact G27.
    - exact KR2.
    - eapply (ah_mpres_trans H HH); [exact MP1 | exact MP2].
    - split; [exact MI2|].
      split; [eapply (stk_merge asegs); [exact ST2 | | lia];
              eapply (apres_stk H); [exact AP2 | exact (proj2 (stk_split asegs m1 lo (spz - 64) spz ST1 ltac:(lia))) | lia]|].
      split; [exists errv2; exact ERR2|].
      split; [exact RAX2|]. split; [exact AC2|]. split; [exact RF2|].
      split; [eapply (stack0_xpres H); [exact (xpres_of_apres H _ _ [] _ _ AP2) | exact S01 | apply Forall_nil]|].
      split; [exact RH2|].
      split; [eapply (apres_rw_cells H); [exact AP2 | exact FR1 | left; lia]|].
      split; [exact XP2|].
      split; [exact AL2|].
      apply lb_own_cons; [exact (own_of_rw_cells _ _ _ _ CB2 ltac:(lia)) | exact (lb_own_apres H _ _ _ _ _ OW1 AP2 (proj1 LBO))].
    - exact ABR.
    - exact NI.
    - exact CB2.
    - exact ADDR.
    - exact (sp_srcf_keep sk2 m2 p' A (str_grow sb) FULL XP2 RF2 RH2).
    - exact PAD.
  Qed.

  Lemma spp_G : forall (msF : machine_state) (t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 errv : word),
    Zlen cs = str_cap sb ->
    as_VIS H s msF = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 p) (Z_to_bv 64 c) a2 a3 a4 a5 a6 a7
                             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 SPB_ENTRY) fc None m (seg_rom asegs) ->
    as_AKREL H s (mkCfg msF mo) -> rw_cells asegs m (errno_addr tp) [C4 errv] ->
    as_SR H Q (mkCfg msF mo).
  Proof.
    intros msF t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 errv FULL VIS KR ERR.
    pose proof SPR as (SPL & SPH & SP16). pose proof LOR as [LO1 LO2].
    unfold SPB_STACK, AOPNEW_STACK, AMALLOC_STACK in LO2, SPL.
    pose proof aceil_facts as ((ACF1 & ACF2) & ACF3 & ACF4).
    destruct (sp_grow_facts FULL) as (GR & GM & GS & GL & GSh).
    pose proof sp_pband as PB. pose proof sp_pfar as PD. unfold SPB_STACK, AOPNEW_STACK, AMALLOC_STACK in PD.
    remember (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 p) (Z_to_bv 64 c) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
      as R0 eqn:HR0.
    assert (HF0 : rfull R0) by (rewrite HR0; apply rfull_mkR).

    assert (CONT : forall R1 M1, CatSim.msteps asegs (MS R0 F (wz SPB_ENTRY) fc None m (seg_rom asegs)) (MS R1 F (wz AOPNEW) fc None M1 (seg_rom asegs)) ->
              munch [(spz - 64, spz)] m M1 -> wmono asegs m M1 ->
              rw_cells asegs M1 (spz - 64) (map (fun r => C8 (getr R0 r)) SPBSAVED) ->
              getr R1 1 = wz 0x1200c4 -> getr R1 2 = wz (spz - 64) -> getr R1 8 = wz c -> getr R1 9 = wz p ->
              getr R1 10 = wz (str_grow sb) -> getr R1 18 = wz (spb_od sb) -> getr R1 19 = wz (str_grow sb) ->
              getr R1 20 = wz (Zlen cs) -> getr R1 21 = wz (spb_s5 sb) ->
              (forall r, In r SPBKG -> getr R1 r = getr R0 r) ->
              as_SR H Q (mkCfg msF mo)).
    { intros R1 M1 Hms MU1 WM1 FR K1 K2 K8 K9 K10 K18 K19 K20 K21 KK.
      assert (FRM : rw_cells asegs M1 (spz - 64) FRAME) by (rewrite HR0 in FR; exact FR).
      pose proof (msteps_full asegs _ _ Hms HF0) as HF1. cbn [ms_regs] in HF1.
      assert (MI1 : mem_inv asegs M1) by exact (msteps_mem_inv asegs _ _ Hms MI0).
      pose proof (ah_fsb H HH _ _ _ RH0) as (FS1 & FS2 & FS3 & FS4).
      assert (SWL : aceil <= spz - 64) by lia.
      destruct (stack_window_ok H LB LF (spz - 64) spz SWL FS2) as (SW1 & SW2 & SW3).
      destruct (client_frame H HH s LB LF B [(spz - 64, spz)] m M1 RH0 RF0 AC0 RA0 MU1 WM1
                  ltac:(apply Forall_cons; [exact SW1 | apply Forall_nil]) ltac:(apply Forall_cons; [exact SW2 | apply Forall_nil])
                  ltac:(apply Forall_cons; [exact SW3 | apply Forall_nil]))
        as (RH1 & RF1 & AC1 & RA1).
      eapply (sr_blk H HH); [exact KR | exact VIS | exact HF0 | exact Hms |].
      intros msF1 mo1 KR1 MP1 VIS1. rewrite <- (rfull_eq R1 HF1) in VIS1.
      eapply (sp_gnew msF1 mo1 M1 R1 errv FULL VIS1 HF1).
      - exact K1.
      - exact K2.
      - rewrite (KK 3%bv ltac:(inb)), HR0. reflexivity.
      - rewrite (KK 4%bv ltac:(inb)), HR0. reflexivity.
      - exact K8.
      - exact K9.
      - exact K10.
      - exact K18.
      - exact K19.
      - exact K20.
      - exact K21.
      - rewrite (KK 23%bv ltac:(inb)), HR0. reflexivity.
      - rewrite (KK 24%bv ltac:(inb)), HR0. reflexivity.
      - rewrite (KK 25%bv ltac:(inb)), HR0. reflexivity.
      - rewrite (KK 26%bv ltac:(inb)), HR0. reflexivity.
      - rewrite (KK 27%bv ltac:(inb)), HR0. reflexivity.
      - exact KR1.
      - exact MP1.
      - exact MI1.
      - eapply BakeStackRep.stk_high_transport; [exact ST0 | exact WM1 | unfold AIMG_TOP; lia].
      - eapply rw_cells_transport; [exact ERR | exact MU1 | exact WM1 |]. rewrite TPV. rewrite u64_of_Z by (unfold ATP; lia).
        cbn. unfold ATP. split; [lia | exact I].
      - exact RA1.
      - exact AC1.
      - exact RF1.
      - eapply stack0_transport; [exact S00 | exact MU1 | exact WM1 |].
        apply Forall_cons; [left; cbn [fst]; unfold AHI_LO; lia | apply Forall_nil].
      - exact RH1.
      - exact FRM.
      - eapply (xpres_of_munch H s LB spz [] [(spz - 64, spz)] m m M1); [exact HH | exact RH0 | exact MU1 | exact WM1 |].
        apply Forall_cons; [left; cbn [fst snd]; lia | apply Forall_nil].
      - exact (lb_own_wmono _ _ _ OWN WM1). }
    destruct (sbuf_cases sb) as [E|(d & asz & E)].
    -
      destruct (GSh E) as [ZC GE].
      pose proof REP as REP'. rewrite E in REP'.
      destruct (strA_short_facts _ _ _ _ REP') as (ZL & F0 & MD). rewrite ZC in F0.
      destruct (spb_BGS_ok R0 F fc m p c spz lo ltac:(rewrite HR0; reflexivity) ltac:(rewrite HR0; reflexivity)
                   ltac:(rewrite HR0; exact spz_sp) F0 CR PWR ST0 ltac:(lia) ltac:(lia) SPH (proj1 PB) (proj2 PB) ltac:(lia))
        as (R1 & M1 & Hms & MU1 & WM1 & FR & K1 & K2 & K8 & K9 & K10 & K18 & K19 & K20 & K21 & KK).
      eapply (CONT R1 M1 Hms MU1 WM1 FR K1 K2 K8 K9).
      + rewrite K10, GE. reflexivity.
      + rewrite K18, E. reflexivity.
      + rewrite K19, GE. reflexivity.
      + rewrite K20, ZC. reflexivity.
      + rewrite K21, E. reflexivity.
      + exact KK.
    -
      destruct (GL d asz E) as (AM & A48 & ZC & GE).
      pose proof REP as REP'. rewrite E in REP'.
      destruct (strA_long_facts _ _ _ _ _ _ REP') as (ZL & D0 & D16 & AM' & AMIN & DJ & F0 & F8 & F16).
      rewrite ZC in F8.
      pose proof BLK as BLK'. rewrite E in BLK'. destruct BLK' as [HIn _].
      pose proof (ah_blocks H HH _ _ _ _ RH0 HIn) as (O0 & O16 & On & OI & OC & OF & OAP).
      cbn [blk_addr blk_size fst snd] in O0, O16, On, OI, OC, OF, OAP. unfold AIMG_TOP in OI.
      destruct (spb_BGL_ok R0 F fc m p c asz d spz lo ltac:(rewrite HR0; reflexivity) ltac:(rewrite HR0; reflexivity)
                   ltac:(rewrite HR0; exact spz_sp) F0 F8 F16 AM ltac:(lia) CR OI ltac:(lia) PWR ST0 ltac:(lia) ltac:(lia) SPH
                   (proj1 PB) (proj2 PB) ltac:(lia))
        as (R1 & M1 & Hms & MU1 & WM1 & FR & K1 & K2 & K8 & K9 & K10 & K18 & K19 & K20 & K21 & KK).
      eapply (CONT R1 M1 Hms MU1 WM1 FR K1 K2 K8 K9).
      + rewrite K10, GE. reflexivity.
      + rewrite K18, E. reflexivity.
      + rewrite K19, GE. reflexivity.
      + rewrite K20, ZC. reflexivity.
      + rewrite K21, E. reflexivity.
      + exact KK.
  Qed.

  Lemma spp_main : forall (msF : machine_state) (t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 errv : word),
    as_VIS H s msF = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 p) (Z_to_bv 64 c) a2 a3 a4 a5 a6 a7
                             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 SPB_ENTRY) fc None m (seg_rom asegs) ->
    as_AKREL H s (mkCfg msF mo) -> rw_cells asegs m (errno_addr tp) [C4 errv] ->
    as_SR H Q (mkCfg msF mo).
  Proof.
    intros msF t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 errv VIS KR ERR.
    pose proof REP as (_ & _ & _ & Hlen & _).
    destruct (Z.eq_dec (Zlen cs) (str_cap sb)) as [FULL|NF].
    - exact (spp_G msF t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 errv FULL VIS KR ERR).
    - destruct (sbuf_cases sb) as [E|(d & asz & E)].
      + apply (spp_S msF t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 errv E); [rewrite E in Hlen, NF; cbn [str_cap] in *; lia | exact VIS | exact KR | exact ERR].
      + apply (spp_L msF t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 errv d asz E); [rewrite E in Hlen, NF; cbn [str_cap] in *; lia | exact VIS | exact KR | exact ERR].
  Qed.
End SPP.

Theorem spb_ok {HCEIL : HeapCeil} : forall (H : asr), asan_rt_hyps H -> spb_stmt H.
Proof.
  intros H HH. unfold spb_stmt.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc msF m mo s LB LBo LF
    p c sb cs pid lo B shi errv.
  intros VIS -> -> CR REP BLK P8 ADV PFF OBJ PBAND PWR OWN LBO GROW AOK TRO RH KR RA SPB SP16 SP47 ST CE LOl ERR MI TPV AC RF S0 SHI.
  pose proof aceil_facts as ((ACF1 & ACF2) & _ & _).
  unfold SPB_STACK, AOPNEW_STACK, AMALLOC_STACK in LOl.
  eapply (spp_main H HH ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m mo s LB LBo LF p c sb cs pid lo B shi
            (bv_unsigned sp)); try eassumption; try reflexivity.
  - split; [unfold SPB_STACK, AOPNEW_STACK, AMALLOC_STACK; lia|]. split; [exact SP47 | exact SP16].
  - split; [exact CE | unfold SPB_STACK, AOPNEW_STACK, AMALLOC_STACK; lia].
Qed.
