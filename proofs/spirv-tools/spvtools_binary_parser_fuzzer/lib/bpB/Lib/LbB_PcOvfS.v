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
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BMState BMem BCells BArr BExec BLFrame BStep BSysStep BacX BellsX.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsIface BsCXXHeap BXXRep BsStack0 BsWalk RtB_Iface.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BakeStackRep FPSteps.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LibIface.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require Import CRep.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require StrLib ContLib.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_Kit LbB_Bridge LbB_Call LbB_Conv LbB_SR LbB_FKit LbB_Own.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_MILB LbB_DiagStmt LbB_DStat LbB_DRep LbB_DKit LbB_DKitN.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_ContStmt LbB_SegKit LbB_StrPbR LbB_StrPb LbB_PcStmt LbB_PcOvf.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require LbB_DCtorK LbB_DPdK LbB_DCtor.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Lemma xclient_range_sub' {HCEIL : HeapCeil} : forall (H : asr) LB SP X A n A' n', xclient_range H LB SP X A n ->
  A <= A' -> A' + n' <= A + n -> xclient_range H LB SP X A' n'.
Proof.
  intros H LB SP X A n A' n' [HR HX] H1 H2. split; [eapply aclient_range_sub; eauto|].
  eapply Forall_impl; [|exact HX]. intros [l h] Hlh. cbn [fst snd] in *. lia.
Qed.

Lemma ftbl_xpres {HCEIL : HeapCeil} : forall (H : asr) LB SP X W B m m' tbl lo hi,
  ftbl W B m tbl -> xpres H LB SP X m m' ->
  fin lo hi (fkeys tbl) = true -> xclient_range H LB SP X (B + lo) (hi - lo) ->
  ftbl W B m' tbl.
Proof.
  intros H LB SP X W B m m' tbl lo hi HT XP Hfin HC. unfold ftbl in *. apply Forall_forall. intros [[k w] e] Hi.
  pose proof (proj1 (Forall_forall _ _) HT (k, w, e) Hi) as RW. cbn beta iota in RW |- *.
  destruct (fin_In lo hi _ k w Hfin (fkeys_In tbl k w e Hi)) as (Hk1 & Hk2 & Hw).
  eapply (xpres_rw_cells H); [exact XP | exact RW |]. cbn [cells_size csize]. rewrite Nat.add_0_r.
  eapply xclient_range_sub'; [exact HC | lia | lia].
Qed.

Lemma addressable_xpres {HCEIL : HeapCeil} : forall (H : asr) LB SP X m m' A n,
  addressable m A n -> xpres H LB SP X m m' -> xclient_range H LB SP X (sh A) (nsh n) -> addressable m' A n.
Proof.
  intros H LB SP X m m' A n (Hn & A0 & A8 & Hb & Hw) XP HC. split; [exact Hn|]. split; [exact A0|]. split; [exact A8|].
  unfold u8arr. split.
  - eapply (xpres_bytes_at H); [exact XP | exact Hb |]. rewrite (shadow_of_length n Hn). exact HC.
  - rewrite (shadow_of_length n Hn) in *. eapply (xpres_wr_at H); [exact XP | exact Hw | exact HC].
Qed.

Lemma lb_remove_perm_ {HCEIL : HeapCeil} : forall (H : asr), asan_rt_hyps H ->
  forall p A n LB, List.NoDup (map blk_id LB) -> In (p, A, n) LB -> Permutation LB ((p, A, n) :: as_lb_remove H p LB).
Proof.
  intros H HH p A n LB ND IN. pose proof (ah_lb_remove H HH) as (L1 & L2 & L3).
  induction LB as [|b LB IH]; [destruct IN|]. cbn [map] in ND. apply NoDup_cons_iff in ND as [ND1 ND2].
  destruct (Z.eq_dec (blk_id b) p) as [E|E].
  - destruct b as [[p' A'] n']. cbn in E. subst p'. rewrite L1 by exact ND1.
    destruct IN as [EQ|IN]; [rewrite EQ; reflexivity|].
    exfalso. apply ND1. apply in_map_iff. exists (p, A, n). split; [reflexivity | exact IN].
  - rewrite L2 by exact E. destruct IN as [EQ|IN]; [subst b; cbn in E; congruence|].
    specialize (IH ND2 IN). eapply perm_trans; [apply perm_skip; exact IH|]. apply perm_swap.
Qed.

Lemma ftbl_cons1 : forall W B m k (w : nat) e v T a, CRep.fld ASEGS m a w v -> a = B + k -> wr_at asegs m (B + k) (Z.of_nat w) ->
  edenot (wenv W) e = Z_to_bv 64 v -> 0 <= B + k -> ftbl W B m T -> ftbl W B m ((k, w, e) :: T).
Proof.
  intros W B m k w e v T a HF -> HW HE H0 HT. pose proof (ftbl1_of_fld W B m k w e v HF HW HE H0) as K.
  apply Forall_cons; [exact (Forall_inv K) | exact HT].
Qed.

Lemma strA_grown : forall LB2 m2 m' s d g cs c,
  strA LB2 m2 s (SLong d g) (cs ++ [0]) -> Zlen cs + 2 <= g -> 0 <= c < 256 ->
  (forall i, 0 <= i < Zlen cs -> m' (Z_to_bv 64 (d + i)) = m2 (Z_to_bv 64 (d + i))) ->
  CRep.fld ASEGS m' (d + Zlen cs) 1 c ->
  (forall i, Zlen cs + 1 <= i < g -> CRep.fld ASEGS m' (d + i) 1 0) ->
  CRep.fld ASEGS m' s 8 (g + 1) -> CRep.fld ASEGS m' (s + 8) 8 (g - 1) -> CRep.fld ASEGS m' (s + 16) 8 d -> mdef m' s 24 ->
  strA LB2 m' s (SLong d g) (cs ++ [c] ++ repeat 0 (Z.to_nat (g - 2 - Zlen cs))).
Proof.
  intros LB2 m2 m' s d g cs c (Hs & Hs' & HD & Hlen & HM & HC & HZ) HG CR AG FC FZ F0 F8 F16 HD'.
  rewrite Zlen_app1 in Hlen, HC, HZ.
  destruct HM as (Hd & Hd16 & Hdg & Hg8 & Hg46 & HL & Hdj & _ & _ & _).
  assert (ZL0 : 0 <= Zlen cs) by (unfold Zlen; lia).
  assert (LEN' : Zlen (cs ++ [c] ++ repeat 0 (Z.to_nat (g - 2 - Zlen cs))) = g - 1).
  { rewrite StrLib.Zlen_app. change ([c] ++ repeat 0 (Z.to_nat (g - 2 - Zlen cs))) with (c :: repeat 0 (Z.to_nat (g - 2 - Zlen cs))).
    unfold Zlen at 2. cbn [length]. rewrite repeat_length. lia. }
  unfold strA, str_rep. split; [exact Hs|]. split; [exact Hs'|]. split; [exact HD'|].
  rewrite LEN'. cbn [str_cap str_data]. split; [lia|].
  split; [repeat split; assumption|].
  split.
  - intros i Hi. destruct (Z_lt_le_dec i (Zlen cs)) as [Hlt|Hge].
    + rewrite Znth_app_l by lia. destruct (HC i ltac:(lia)) as [HR HF]. rewrite Znth_app_l in HR, HF by lia.
      split; [exact HR|]. eapply fld_agree; [lia | lia | exact HF |]. intros a Ha. unfold zwin in Ha.
      replace a with (d + (a - d)) by lia. apply AG. lia.
    + rewrite StrLib.Znth_app_r by lia. destruct (Z.eq_dec i (Zlen cs)) as [->|Hne].
      * replace (Zlen cs - Zlen cs) with 0 by lia. change (Znth 0 ([c] ++ repeat 0 (Z.to_nat (g - 2 - Zlen cs)))) with c. split; [lia | exact FC].
      * change ([c] ++ repeat 0 (Z.to_nat (g - 2 - Zlen cs))) with (c :: repeat 0 (Z.to_nat (g - 2 - Zlen cs))).
        unfold Znth. replace (Z.to_nat (i - Zlen cs)) with (S (Z.to_nat (i - Zlen cs - 1))) by lia. cbn [nth].
        rewrite nth_repeat_lt by lia. split; [lia|]. apply FZ. lia.
  - replace (d + (g - 1)) with (d + (g - 1)) by lia. apply FZ. lia.
Qed.

Lemma spb_x_sbx : forall sb, spb_x sb = sbx sb.
Proof. intros [|d asz]; reflexivity. Qed.

Lemma spbx_apart : forall sb A n,
  (forall d asz, sb = SLong d asz -> (A + n <= d \/ d + asz <= A) /\ (A + n <= sh d \/ sh d + nsh asz <= A)) ->
  Forall (fun iv : Z * Z => A + n <= fst iv \/ snd iv <= A) (spb_x sb).
Proof.
  intros [|d asz] A n Hx; cbn [spb_x]; [constructor|]. destruct (Hx d asz eq_refl) as [H1 H2].
  apply Forall_cons; [cbn [fst snd]; lia | apply Forall_cons; [cbn [fst snd]; lia | apply Forall_nil]].
Qed.

Lemma stk_wmono_hi : forall W m m' lo hi, stk asegs m lo hi -> munch W m m' -> wmono asegs m m' -> AIMG_TOP <= lo ->
  stk asegs m' lo hi.
Proof.
  intros W m m' lo hi STK MU WM HL. eapply stk_transport; [exact STK | exact MU | exact WM |]. intros x Hx. right.
  pose proof STK as (T1 & T2 & T3). destruct (T3 x Hx) as [HV _].
  pose proof (WM (wa x) HV) as HV'.
  assert (HX : AIMG_TOP <= bv_unsigned (wa x)) by (unfold wa; rewrite unsigned_lit by (clear - T1 T2 Hx; lia); clear - Hx HL; lia).
  rewrite (BakeStackRep.wview_high m' (wa x) HX) in HV'.
  destruct (m' (wa x)) as [b|] eqn:Eb; [exists b; reflexivity | contradiction].
Qed.

Lemma In_zents1 : forall (j : nat) o i, o <= i < o + Z.of_nat j -> In (i, 1%nat, ELit 0) (zents1 o j).
Proof.
  induction j as [|j IH]; intros o i Hi; [lia|]. cbn [zents1].
  destruct (Z.eq_dec i o) as [->|Hne]; [left; reflexivity|]. right. apply IH. lia.
Qed.

Lemma xpres_drop_fresh' {HCEIL : HeapCeil} : forall (H : asr), asan_rt_hyps H ->
  forall LB SP X m1 m2 sk mk pid d asz,
    as_RHEAP H sk ((pid, d, asz) :: LB) mk -> ~ In pid (map blk_id LB) -> aceil <= SP ->
    xpres H LB SP (X ++ [(d, d + asz); (sh d, sh d + nsh asz)]) m1 m2 -> xpres H LB SP X m1 m2.
Proof.
  intros H HH LB SP X m1 m2 sk mk pid d asz RH NI HSP XP a Ha [Hc Hx].
  apply XP; [exact Ha|]. split; [exact Hc|].
  intros K. apply rin_ivs_app in K. destruct K as [K|K]; [exact (Hx K)|].
  destruct (sk_cls H HH sk LB pid d asz SP mk a RH NI HSP Hc) as [C|(C1 & C2 & C3)].
  - pose proof (ah_blocks H HH _ _ _ (pid, d, asz) RH (or_introl eq_refl)) as (R0 & _ & Rn & _ & RC & _). cbn in RC.
    pose proof (sh_below_aceil d) as SB.
    cbn [rin_ivs fst snd] in K. destruct K as [K|[K|K]]; [lia | | contradiction].
    assert (sh d + nsh asz <= sh aceil).
    { unfold sh, nsh. acb. Z.div_mod_to_equations. nia. }
    assert (sh aceil < aceil) by (apply sh_below_aceil; acb; unfold AAPP_HI; lia). lia.
  - cbn [rin_ivs fst snd] in K. destruct K as [K|[K|K]]; [exact (C2 K) | exact (C3 K) | contradiction].
Qed.

Lemma rtbl4_mkR : forall W R, rfull R -> rtbl W R RTQ4 ->
  R = mkR (edenot (wenv W) (EVar 34)) (edenot (wenv W) (EVar 33)) (edenot (wenv W) (EVar 48)) (edenot (wenv W) (EVar 49))
          (PropExec.getr R 5) (PropExec.getr R 6) (PropExec.getr R 7) (edenot (wenv W) (EVar 36)) (edenot (wenv W) (EVar 37))
          (edenot (wenv W) (EAlu ALU_AND (EVar 35) (ELit 255)))
          (PropExec.getr R 11) (PropExec.getr R 12) (PropExec.getr R 13) (PropExec.getr R 14) (PropExec.getr R 15)
          (PropExec.getr R 16) (PropExec.getr R 17)
          (edenot (wenv W) (EVar 38)) (edenot (wenv W) (EVar 39)) (edenot (wenv W) (EVar 40)) (edenot (wenv W) (EVar 41))
          (edenot (wenv W) (EVar 42)) (edenot (wenv W) (EVar 43)) (edenot (wenv W) (EVar 44)) (edenot (wenv W) (EVar 45))
          (edenot (wenv W) (EVar 46)) (edenot (wenv W) (EVar 47))
          (PropExec.getr R 28) (PropExec.getr R 29) (PropExec.getr R 30) (PropExec.getr R 31).
Proof.
  intros W R RF HT. rewrite (rfull_eq R RF) at 1.
  assert (G : forall r e, In (r, e) RTQ4 -> PropExec.getr R r = edenot (wenv W) e) by (intros r e Hi; exact (rtbl_In W R RTQ4 r e HT Hi)).
  rewrite (G 1%bv (EVar 34)), (G 2%bv (EVar 33)), (G 3%bv (EVar 48)), (G 4%bv (EVar 49)), (G 8%bv (EVar 36)), (G 9%bv (EVar 37)),
          (G 10%bv (EAlu ALU_AND (EVar 35) (ELit 255))), (G 18%bv (EVar 38)), (G 19%bv (EVar 39)), (G 20%bv (EVar 40)),
          (G 21%bv (EVar 41)), (G 22%bv (EVar 42)), (G 23%bv (EVar 43)), (G 24%bv (EVar 44)), (G 25%bv (EVar 45)),
          (G 26%bv (EVar 46)), (G 27%bv (EVar 47)) by (unfold RTQ4; repeat (first [left; reflexivity | right])).
  reflexivity.
Qed.

Lemma and255_small : forall c, 0 <= c <= 255 -> alu64 ALU_AND (Z_to_bv 64 c) (Z_to_bv 64 255) = Z_to_bv 64 c.
Proof.
  intros c Hc. apply bv_eq. cbn [alu64 alu]. rewrite bv_and_unsigned, !Z_to_bv_unsigned, !bv_wrap64_mod.
  rewrite (Z.mod_small c) by lia. rewrite (Z.mod_small 255) by lia. change 255 with (Z.ones 8). rewrite Z.land_ones by lia.
  apply Z.mod_small. change (2 ^ 8) with 256. lia.
Qed.

Lemma rtbl4_q : forall ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ds c data pp hm d' R,
  rfull R -> rtbl (Wq ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ds c data pp hm d') R RTQ4 -> 0 <= c <= 255 ->
  R = mkR ra sp gp tp (PropExec.getr R 5) (PropExec.getr R 6) (PropExec.getr R 7) s0 s1 (Z_to_bv 64 c)
          (PropExec.getr R 11) (PropExec.getr R 12) (PropExec.getr R 13) (PropExec.getr R 14) (PropExec.getr R 15)
          (PropExec.getr R 16) (PropExec.getr R 17) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
          (PropExec.getr R 28) (PropExec.getr R 29) (PropExec.getr R 30) (PropExec.getr R 31).
Proof.
  intros ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ds c data pp hm d' R RF HT Hc.
  rewrite (rtbl4_mkR _ R RF HT) at 1. rewrite <- (and255_small c Hc). reflexivity.
Qed.

Lemma rtbl4_l : forall ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ds c data pp hm d' asz R,
  rfull R -> rtbl (Wl ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ds c data pp hm d' asz) R RTQ4 -> 0 <= c <= 255 ->
  R = mkR ra sp gp tp (PropExec.getr R 5) (PropExec.getr R 6) (PropExec.getr R 7) s0 s1 (Z_to_bv 64 c)
          (PropExec.getr R 11) (PropExec.getr R 12) (PropExec.getr R 13) (PropExec.getr R 14) (PropExec.getr R 15)
          (PropExec.getr R 16) (PropExec.getr R 17) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
          (PropExec.getr R 28) (PropExec.getr R 29) (PropExec.getr R 30) (PropExec.getr R 31).
Proof.
  intros ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ds c data pp hm d' asz R RF HT Hc.
  rewrite (rtbl4_mkR _ R RF HT) at 1. rewrite <- (and255_small c Hc). reflexivity.
Qed.

Ltac In_tbl := repeat (first [left; reflexivity | right]).

Section OVS.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HHbp : asan_rt_hyps_bp H.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
            (m : mem) (mo : Model) (s : as_St H) (LB LBk DB : list block) (LF : list fframe) (lo B shi : Z) (errv : word)
            (ds err len c : Z) (ms : sbuf) (hm fl fill : Z) (cs : list Z) (pid : bptr).
  Hypothesis RH : as_RHEAP H s LB m.
  Hypothesis RAUX : as_rauxv_ok H m B.
  Hypothesis SPB : bv_unsigned sp <= B.
  Hypothesis SP16 : bv_unsigned sp mod 16 = 0.
  Hypothesis STK : stk asegs m lo (bv_unsigned sp).
  Hypothesis CEIL : aceil <= lo.
  Hypothesis LO : lo <= bv_unsigned sp - OVF_STACK.
  Hypothesis ERRN : rw_cells asegs m (errno_addr tp) [C4 errv].
  Hypothesis MI : mem_inv asegs m.
  Hypothesis TP : tp = Z_to_bv 64 ATP.
  Hypothesis RA2 : bv_unsigned ra mod 2 = 0.
  Hypothesis LV : LINV_P5 m.
  Hypothesis AC : ACONST m.
  Hypothesis RFS : as_RFS H LF m.
  Hypothesis S0 : stack0 m lo shi.
  Hypothesis SPS : bv_unsigned sp <= shi.
  Hypothesis CR : 0 <= c <= 255.
  Hypothesis DI : ds_inv (lbl LB) m ds err len (lbl DB) ms (dsdata ds ms + str_cap ms) hm fl fill.
  Hypothesis DBE : DB = spb_own ms pid.
  Hypothesis BLKL : forall d asz, ms = SLong d asz -> In (pid, d, asz) LB.
  Hypothesis DSA : addressable m ds DS_SIZE.
  Hypothesis DSW : wr_at asegs m ds DS_SIZE.
  Hypothesis DSO : app_obj ds DS_SIZE.
  Hypothesis SBA : sb_addr m ms.
  Hypothesis PERM : Permutation LB (DB ++ LBk).
  Hypothesis OWN : lb_own DB m.
  Hypothesis DSIN : ds_in LF ds.
  Hypothesis LEN : len + 1 <= DS_MAXLEN.
  Hypothesis BS : lb_small LB + 64512 <= RT_SMALL_MAX.
  Hypothesis BC : Z.of_nat (length LB) + 1 <= RT_CNT_MAX.
  Hypothesis BL : nlarge LB + 1 <= RT_LARGE_MAX.
  Hypothesis COST : ICM (str_grow ms) <= as_AL H s.
  Hypothesis TRO : trace_ok (as_TR H) APC0_FREE [0x1200e8].
  Hypothesis CSR : strA LB m (ds + 72) ms cs.
  Hypothesis CSL : Zlen cs = str_cap ms.

  Let HH : asan_rt_hyps H := rt_bp_base H HHbp.
  Notation spz := (bv_unsigned sp) (only parsing).
  Notation data := (dsdata ds ms) (only parsing).

  Definition Qov : as_St H -> list block -> mem -> Prop :=
    fun s' LB' m' => exists pid' d',
        Permutation LB' ((pid', d', str_grow ms) :: LBk)
     /\ ds_rep_w LB' m' ds err (len + 1) [(pid', d', str_grow ms)] (SLong d' (str_grow ms))
                 (d' + str_cap ms + 1) (d' + str_cap ms + 1) fl fill
     /\ lb_own [(pid', d', str_grow ms)] m'
     /\ xpres H LBk spz ((ds, ds + DS_SIZE) :: sbx ms) m m'
     /\ as_AL H s' >= as_AL H s - ICM (str_grow ms).
  Definition POSTov : config -> Prop :=
    pc_post H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc LF lo B shi mo (Z_to_bv 64 c) Qov.

  Lemma ov_nums : AIMG_TOP <= ds /\ ds + DS_SIZE <= lo /\ ds mod 8 = 0 /\ as_FSB H <= ds /\ ds + DS_SIZE <= as_FSB H + AFS_SIZE
                  /\ aceil + OVF_STACK <= spz /\ spz <= 2 ^ 47 /\ 0x7fff7f800000 <= aceil <= 0x7fffff800000
                  /\ AIMG_TOP <= as_FSB H /\ as_FSB H + AFS_SIZE <= aceil /\ (ds + DS_SIZE <= ALOWSH_LO \/ AHI_LO <= ds).
  Proof.
    pose proof DSIN as (IN & _ & D8 & D0). pose proof DSO as (O1 & O2 & O3).
    destruct (LbB_DCtor.inframe_facts H HH LF m ds DS_SIZE RFS IN ltac:(unfold DS_SIZE; lia) O1) as (F1 & _ & F3 & F4).
    destruct (ah_RFS_range H HH LF m RFS) as [(B1 & B2 & B3 & B4) _].
    pose proof aceil_facts as ((A1 & A2) & _ & _). pose proof (stack0_bounds m lo shi S0) as (K1 & K2 & K3).
    clear - O1 O2 O3 D8 F1 F3 F4 B1 B2 A1 A2 K1 K2 K3 LO CEIL SPS.
    unfold AAPP_HI, OVF_STACK, AOPNEW_STACK, AMALLOC_STACK in *. repeat split; lia.
  Qed.

  Lemma ov_data : 0 <= data /\ data + str_cap ms + 1 < 2 ^ 64 /\ data <= hm <= data + str_cap ms /\ str_cap ms <= len
                  /\ 0 <= str_cap ms.
  Proof.
    pose proof ov_nums as (N1 & N2 & N3 & _).
    destruct (di_sb _ _ _ _ _ _ _ _ _ _ _ DI) as [_ _ _ _ _ (cs0 & SR0 & HL0) _ _ _ HPP _ HHM _].
    pose proof (di_pl _ _ _ _ _ _ _ _ _ _ _ DI) as PL.
    replace (ds + 8 + 64) with (ds + 72) in * by lia. unfold dsdata in *.
    destruct ms as [|d asz]; cbn [str_data str_cap] in *.
    - pose proof DSO as (_ & _ & O3). unfold SSO_CAP, AIMG_TOP, DS_SIZE, AAPP_HI in *. clear - N1 O3 HHM PL. lia.
    - destruct SR0 as (_ & _ & _ & _ & (Hd & _ & Hde & _ & Ha46 & _) & _). unfold SSO_CAP in Ha46.
      clear - Hd Hde Ha46 HHM PL. lia.
  Qed.

  Definition Wo0 : list word :=
    Wo ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ds c (dsdata ds ms) (dsdata ds ms + str_cap ms) hm.

  Lemma ov_hdt : ftbl Wo0 ds m DTO0.
  Proof.
    pose proof ov_nums as (N1 & N2 & N3 & _). pose proof ov_data as (D1 & D2 & D3 & D4 & D5).
    destruct (di_sb _ _ _ _ _ _ _ _ _ _ _ DI) as [_ _ Fb Fn Fe _ Fpb Fpp Fep _ Fhm _ Fmd].
    replace (ds + 8 + 64) with (ds + 72) in * by lia. fold (dsdata ds ms) in Fpb, Fep.
    assert (WR : forall k w, 0 <= k -> k + w <= DS_SIZE -> 0 <= w -> wr_at asegs m (ds + k) w).
    { intros k w K1 K2 K3. eapply wr_at_sub; [exact DSW | lia | lia | lia]. }
    unfold DTO0, DTO0a, DTO0b. cbn [app].
    assert (V : forall v, 0 <= v < 2 ^ 64 -> bv_unsigned (Z_to_bv 64 v) = v) by (intros; apply unsigned_lit; lia).
    apply (ftbl_cons1 _ ds _ 24 8 _ 0 _ _ Fb ltac:(lia)); [apply WR; unfold DS_SIZE; lia | reflexivity | unfold AIMG_TOP in N1; lia |].
    apply (ftbl_cons1 _ ds _ 32 8 _ 0 _ _ Fn ltac:(lia)); [apply WR; unfold DS_SIZE; lia | reflexivity | unfold AIMG_TOP in N1; lia |].
    apply (ftbl_cons1 _ ds _ 40 8 _ 0 _ _ Fe ltac:(lia)); [apply WR; unfold DS_SIZE; lia | reflexivity | unfold AIMG_TOP in N1; lia |].
    apply (ftbl_cons1 _ ds _ 48 8 _ _ _ _ Fpb ltac:(lia)); [apply WR; unfold DS_SIZE; lia | reflexivity | unfold AIMG_TOP in N1; lia |].
    apply (ftbl_cons1 _ ds _ 56 8 _ _ _ _ Fpp ltac:(lia)); [apply WR; unfold DS_SIZE; lia | reflexivity | unfold AIMG_TOP in N1; lia |].
    apply (ftbl_cons1 _ ds _ 64 8 _ _ _ _ Fep ltac:(lia)); [apply WR; unfold DS_SIZE; lia | reflexivity | unfold AIMG_TOP in N1; lia |].
    apply (ftbl_cons1 _ ds _ 96 8 _ _ _ _ Fhm ltac:(lia)); [apply WR; unfold DS_SIZE; lia | reflexivity | unfold AIMG_TOP in N1; lia |].
    apply (ftbl_cons1 _ ds _ 104 4 _ _ _ _ Fmd ltac:(lia)); [apply WR; unfold DS_SIZE; lia | reflexivity | unfold AIMG_TOP in N1; lia |].
    constructor.
  Qed.

  Lemma ov_o1 : forall t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6,
    evt asegs (fun ms => exists R1 m1, ms = MS R1 F (Z_to_bv 64 SPB_ENTRY) fc None m1 (seg_rom asegs) /\ rfull R1
                  /\ rtbl Wo0 R1 RTO1 /\ ftbl Wo0 spz m1 STO1 /\ ftbl Wo0 ds m1 DTO0 /\ Po sp m ds m1 /\ mem_inv asegs m1)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (ds + 8)) (Z_to_bv 64 c) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                 t3 t4 t5 t6) F (Z_to_bv 64 AOVF) fc None m (seg_rom asegs)).
  Proof.
    intros. pose proof ov_nums as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & _).
    eapply (o1_evt ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m ds c (dsdata ds ms) (dsdata ds ms + str_cap ms) hm lo
              DSO DSW STK CEIL ltac:(clear - LO; unfold OVF_STACK, AOPNEW_STACK, AMALLOC_STACK in LO; lia) N7 N2 CR ov_hdt);
      [apply rfull_mkR | | exact MI].
    unfold rtbl, RTO0. repeat constructor. cbn [fst snd edenot]. rewrite <- w_add_g. reflexivity.
  Qed.

  Definition W1 : list (Z * Z) := [(spz - 8192, spz); (ds + 24, ds + 72); (ds + 96, ds + 108)].

  Lemma ov_w1 : Forall (aclient_write_ok H LB) W1 /\ Forall (afs_write_ok H LF) W1 /\ Forall stack0_ok W1
                /\ wins_hi W1 /\ Forall aconst_ok W1.
  Proof.
    pose proof ov_nums as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & (A1 & A2) & N9 & N10 & N11).
    pose proof DSIN as ((f & Hf & IF1 & IF2) & _).
    assert (SH : sh aceil >= 0x7fff8000) by (unfold sh, ASHADOW_BASE; clear - A1; Z.div_mod_to_equations; lia).
    unfold W1, DS_SIZE, AFS_SIZE, AIMG_TOP, AHI_LO, ALOWSH_LO, OVF_STACK, AOPNEW_STACK, AMALLOC_STACK in *.
    split; [|split; [|split; [|split]]].
    - repeat apply Forall_cons; try apply Forall_nil; unfold aclient_write_ok; cbn [fst snd]; unfold AFS_SIZE.
      + left. clear - N6. lia.
      + right; right; right; right; left. clear - N4 N5. lia.
      + right; right; right; right; left. clear - N4 N5. lia.
    - repeat apply Forall_cons; try apply Forall_nil; unfold afs_write_ok; cbn [fst snd]; unfold AFS_SIZE.
      + left. unfold ATLS_PRIV_LO, ATLS_PRIV_HI, ATP. clear - N6 N10 A1. lia.
      + right. exists f. split; [exact Hf|]. clear - IF1 IF2. lia.
      + right. exists f. split; [exact Hf|]. clear - IF1 IF2. lia.
    - repeat apply Forall_cons; try apply Forall_nil; unfold stack0_ok, AHI_LO; cbn [fst snd].
      + left. clear - N6 A1. lia.
      + destruct N11 as [N11|N11]; [right | left]; clear - N11 SH; lia.
      + destruct N11 as [N11|N11]; [right | left]; clear - N11 SH; lia.
    - unfold wins_hi, AIMG_TOP, ALOWSH_LO, AHI_LO. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd].
      + right. clear - N6 A1. lia.
      + destruct N11 as [N11|N11]; [left | right]; clear - N1 N11; lia.
      + destruct N11 as [N11|N11]; [left | right]; clear - N1 N11; lia.
    - repeat apply Forall_cons; try apply Forall_nil.
      + apply LbB_DPdK.aconst_ok_hi. clear - N6 A1. lia.
      + destruct N11 as [N11|N11]; [apply LbB_DPdK.aconst_ok_lo | apply LbB_DPdK.aconst_ok_hi]; unfold AIMG_TOP;
          clear - N1 N11; lia.
      + destruct N11 as [N11|N11]; [apply LbB_DPdK.aconst_ok_lo | apply LbB_DPdK.aconst_ok_hi]; unfold AIMG_TOP;
          clear - N1 N11; lia.
  Qed.

  Lemma agree_munch : forall W m0 m' (P : Z -> Prop), munch W m0 m' -> (forall a, P a -> 0 <= a < 2 ^ 64 /\ outside W a) ->
    CRep.agree_on P m0 m'.
  Proof.
    intros W m0 m' P MU HP a Ha. destruct (HP a Ha) as [R O]. apply MU. rewrite unsigned_lit by exact R. exact O.
  Qed.

  Lemma ov_oldblk : forall d asz, ms = SLong d asz ->
    0 < d /\ d + asz <= aceil /\ 0 <= asz /\ (ds + DS_SIZE <= d \/ d + asz <= ds) /\ aapp d asz /\ In (pid, d, asz) LB
    /\ d mod 16 = 0 /\ asz mod 8 = 0 /\ 48 <= asz /\ AIMG_TOP <= d.
  Proof.
    intros d asz E. pose proof (BLKL d asz E) as IN.
    pose proof (ah_blocks H HH _ _ _ _ RH IN) as (Q0 & Q16 & Qn & QI & QC & QF & QAPP). cbn [blk_addr blk_size fst snd] in *.
    pose proof (di_dj _ _ _ _ _ _ _ _ _ _ _ DI d asz E) as DJ.
    pose proof CSR as (_ & _ & _ & _ & HM & _). rewrite E in HM. destruct HM as (_ & _ & _ & A8 & A46 & _).
    unfold SSO_CAP in A46.
    repeat split; try assumption; try lia.
    all: clear - A8 A46; Z.div_mod_to_equations; lia.
  Qed.

  Lemma ov_m1 : forall m1, Po sp m ds m1 -> mem_inv asegs m1 ->
    strA LB m1 (ds + 72) ms cs /\ spb_blk LB m1 ms pid /\ addressable m1 (ds + 72) 24 /\ wr_at asegs m1 (ds + 72) 24
    /\ lb_own (spb_own ms pid) m1 /\ as_RHEAP H s LB m1 /\ as_rauxv_ok H m1 B /\ stk asegs m1 lo spz
    /\ rw_cells asegs m1 (errno_addr tp) [C4 errv] /\ ACONST m1 /\ as_RFS H LF m1 /\ stack0 m1 lo shi /\ LINV_P5 m1
    /\ xpres H LB spz ((ds, ds + DS_SIZE) :: sbx ms) m m1
    /\ CRep.agree_on (fun a => zwin ds (ds + 24) a \/ zwin (ds + 108) (ds + DS_SIZE) a) m m1
    /\ addressable m1 ds DS_SIZE /\ wr_at asegs m1 ds DS_SIZE.
  Proof.
    intros m1 [MU WM] MI1. change (munch W1 m m1) in MU.
    pose proof ov_nums as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & (A1 & A2) & N9 & N10 & N11).
    pose proof ov_w1 as (WC & WF & WS & WH & WA).
    pose proof DSO as (O1 & O2 & O3).
    assert (OUTW : forall a, (ds <= a < ds + 24 \/ ds + 72 <= a < ds + 96 \/ ds + 108 <= a < ds + DS_SIZE
                              \/ a < spz - 8192 /\ (a < ds \/ ds + DS_SIZE <= a)) -> outside W1 a).
    { intros a Ha. unfold W1. cbn [outside]. unfold DS_SIZE, OVF_STACK, AOPNEW_STACK, AMALLOC_STACK in *. clear - Ha N2 LO. lia. }
    split.
    { eapply str_frame; [exact CSR|]. eapply agree_munch; [exact MU|]. intros a Ha. unfold str_fp, zwin in Ha.
      destruct Ha as [Ha|Ha].
      - split; [unfold AIMG_TOP, AAPP_HI, DS_SIZE in *; clear - Ha N1 O3; lia|]. apply OUTW. clear - Ha. lia.
      - remember ms as ms0 eqn:Ems in Ha. destruct ms0 as [|d asz]; [destruct Ha|].
        destruct (ov_oldblk d asz (eq_sym Ems)) as (K0 & K1 & K2 & K3 & _).
        pose proof CSR as (_ & _ & _ & HL & _). rewrite <- Ems in HL. cbn [str_cap] in HL.
        split; [clear - Ha K0 K1 A2 HL; lia|]. apply OUTW. right; right; right. clear - Ha K1 K3 HL N6 A1.
        unfold OVF_STACK, AOPNEW_STACK, AMALLOC_STACK in *. lia. }
    split.
    { destruct ms as [|d asz] eqn:Ems; [exact I|]. cbn [spb_blk]. split; [exact (BLKL d asz eq_refl)|].
      destruct SBA as [SA SO]. destruct SO as (SO1 & SO2 & SO3).
      eapply addressable_transport_hi; [exact SA | exact MU | exact WM | exact SO3 | exact WH]. }
    assert (ADS1 : addressable m1 ds DS_SIZE) by (eapply addressable_transport_hi; [exact DSA | exact MU | exact WM | exact O3 | exact WH]).
    assert (WDS1 : wr_at asegs m1 ds DS_SIZE) by (eapply wr_at_transport; [exact DSW | exact WM]).
    split.
    { destruct (addressable_split8 m1 ds DS_SIZE 72 ADS1 ltac:(reflexivity) ltac:(reflexivity) ltac:(unfold DS_SIZE; lia)) as [_ K].
      destruct (addressable_split8 m1 (ds + 72) (DS_SIZE - 72) 24 K ltac:(reflexivity) ltac:(reflexivity) ltac:(unfold DS_SIZE; lia)) as [K' _].
      exact K'. }
    split; [eapply wr_at_sub; [exact WDS1 | lia | unfold DS_SIZE; lia | lia]|].
    split; [rewrite <- DBE; unfold lb_own in *; eapply Forall_impl; [|exact OWN]; intros b Hb; eapply wr_at_transport; [exact Hb | exact WM]|].
    split; [eapply (ah_RHEAP_frame H HH); [exact RH | exact MU | exact WM | exact WC]|].
    split; [eapply (ah_rauxv_frame H HH); [exact RAUX | exact MU | exact WM | exact WC]|].
    split.
    { eapply stk_transport; [exact STK | exact MU | exact WM |]. intros x Hx. right.
      pose proof STK as (T1 & T2 & T3). destruct (T3 x Hx) as [HV _].
      pose proof (WM (wa x) HV) as HV'.
      assert (HX : AIMG_TOP <= bv_unsigned (wa x)).
      { unfold wa. rewrite unsigned_lit by (clear - T1 T2 Hx; lia). clear - Hx CEIL A1. unfold AIMG_TOP. lia. }
      rewrite (BakeStackRep.wview_high m1 (wa x) HX) in HV'.
      destruct (m1 (wa x)) as [b|] eqn:Eb; [exists b; reflexivity | contradiction]. }
    split.
    { eapply rw_cells_transport; [exact ERRN | exact MU | exact WM |].
      unfold W1. cbn [disjoint_from cells_size csize]. rewrite TP, unsigned_lit by (clear; unfold ATP; lia).
      clear - N1 N6 A1. unfold ATP, AIMG_TOP, OVF_STACK, AOPNEW_STACK, AMALLOC_STACK in *. cbn. lia. }
    split; [eapply ACONST_frame; [exact AC | exact MU | exact WM | exact WA]|].
    split; [eapply (ah_RFS_frame H HH); [exact RFS | exact MU | exact WM | exact WF]|].
    split; [eapply stack0_transport; [exact S0 | exact MU | exact WM | exact WS]|].
    split.
    { eapply LINV_P5_cl; [exact LV|]. intros a Ha Hc. unfold wa. apply MU. rewrite unsigned_lit by exact Ha.
      apply OUTW. right; right; right. unfold aimg_client in Hc. clear - Hc N1 N6 A1.
      unfold AIMG_TOP, OVF_STACK, AOPNEW_STACK, AMALLOC_STACK in *. lia. }
    split.
    { eapply (xpres_of_munch H s LB spz _ W1 m m m1 HH RH MU WM). unfold W1.
      repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd].
      - left. clear - N6. unfold OVF_STACK, AOPNEW_STACK, AMALLOC_STACK in *. lia.
      - right. intros a Ha. cbn [rin_ivs fst snd]. left. unfold DS_SIZE. clear - Ha. lia.
      - right. intros a Ha. cbn [rin_ivs fst snd]. left. unfold DS_SIZE. clear - Ha. lia. }
    split.
    { eapply agree_munch; [exact MU|]. intros a Ha. unfold zwin in Ha.
      split; [unfold AIMG_TOP, AAPP_HI, DS_SIZE in *; clear - Ha N1 O3; lia|]. apply OUTW. clear - Ha. unfold DS_SIZE in *. lia. }
    split; [exact ADS1 | exact WDS1].
  Qed.

  Ltac rgeto HRT r G :=
    lazymatch type of HRT with
    | rtbl ?W ?R ?RT =>
        let e := eval vm_compute in (match List.find (fun re => bv_eqb (fst re) r) RT with Some re => snd re | None => ELit 0 end) in
        assert (G : PropExec.getr R r = edenot (wenv W) e)
          by (apply (rtbl_In W R RT r e HRT); apply LbB_DCtorK.inb_In'; vm_compute; reflexivity);
        unfold wenv in G; cbn [edenot] in G; unfold HLib.Eseed, reg_ev, Wo0, Wo in G;
        lazy [ev eb N.ltb N.compare PosDef.Pos.compare PosDef.Pos.compare_cont N.to_nat PosDef.Pos.to_nat PosDef.Pos.iter_op
              Init.Nat.add Nat.sub nth app] in G
    end.

  Definition pb_after (msF2 : machine_state) (mo2 : Model) (sk2 : as_St H) (m2 : mem) (R2 : bvmap 5 word)
                      (LB2 : list block) (pid2 : bptr) (d' : Z) : Prop :=
       as_VIS H sk2 msF2 = MS R2 F (Z_to_bv 64 0x126038) fc None m2 (seg_rom asegs) /\ rfull R2
    /\ rtbl Wo0 R2 RTQ0 /\ ftbl Wo0 spz m2 STO1 /\ ftbl Wo0 ds m2 DTO0
    /\ as_AKREL H sk2 (mkCfg msF2 mo2) /\ as_MPRES H mo mo2
    /\ mem_inv asegs m2 /\ stk asegs m2 lo spz /\ (exists e, rw_cells asegs m2 (errno_addr tp) [C4 e]) /\ as_rauxv_ok H m2 B
    /\ xpres H LBk spz ((ds, ds + DS_SIZE) :: sbx ms) m m2
    /\ CRep.agree_on (fun a => zwin ds (ds + 24) a \/ zwin (ds + 108) (ds + DS_SIZE) a) m m2
    /\ as_RHEAP H sk2 LB2 m2 /\ strA LB2 m2 (ds + 72) (SLong d' (str_grow ms)) (cs ++ [0])
    /\ In (pid2, d', str_grow ms) LB2 /\ SHAD m2 d' (shadow_of (str_grow ms)) /\ ~ In pid2 (map blk_id LB)
    /\ LB2 = spb_LB H LB ms pid pid2 d' /\ ablock_range H d' (str_grow ms)
    /\ addressable m2 ds DS_SIZE /\ wr_at asegs m2 ds DS_SIZE /\ wr_at asegs m2 d' (str_grow ms)
    /\ as_RFS H LF m2 /\ ACONST m2 /\ stack0 m2 lo shi /\ LINV_P5 m2
    /\ as_AL H sk2 >= as_AL H s - ICM (str_grow ms).

  Lemma ov_grow : str_grow ms <= 2 ^ 25 + 2 /\ 48 <= str_grow ms /\ str_grow ms <= 2 * str_cap ms + 48
                  /\ (exists j, 0 <= j /\ str_grow ms = 48 * 2 ^ j) /\ str_grow ms mod 16 = 0.
  Proof.
    pose proof ov_data as (_ & _ & _ & D4 & _). pose proof (di_pow _ _ _ _ _ _ _ _ _ _ _ DI) as PW.
    destruct ms as [|d asz]; cbn [str_grow str_cap] in *.
    - split; [lia|]. split; [lia|]. split; [unfold SSO_CAP; lia|]. split; [exists 0; split; [lia | reflexivity] | reflexivity].
    - destruct (PW d asz eq_refl) as (j & J0 & EJ).
      pose proof SBA as (_ & SO1 & _). unfold DS_MAXLEN, AIMG_TOP in *.
      destruct CSR as (_ & _ & _ & _ & (_ & _ & _ & _ & Ha46 & _) & _). unfold SSO_CAP in Ha46.
      split; [clear - D4 LEN Ha46; lia|]. split; [clear - Ha46; lia|]. split; [clear; lia|].
      split; [exists (j + 1); split; [clear - J0; lia | rewrite Z.pow_add_r by lia; rewrite EJ; clear; ring]|].
      rewrite EJ. clear. replace (2 * (48 * 2 ^ j)) with (16 * (6 * 2 ^ j)) by ring. rewrite Z.mul_comm. apply Z.mod_mul. lia.
  Qed.

  Lemma ov_asz : forall d asz, ms = SLong d asz -> 48 <= asz <= 2 ^ 25 /\ asz mod 16 = 0.
  Proof.
    intros d asz E. pose proof ov_data as (_ & _ & _ & D4 & _). pose proof (di_pow _ _ _ _ _ _ _ _ _ _ _ DI d asz E) as (j & J0 & EJ).
    rewrite E in D4. cbn [str_cap] in D4. unfold DS_MAXLEN in LEN.
    assert (P1 : 1 <= 2 ^ j) by (apply Z.pow_pos_nonneg in J0; [lia | lia] || (pose proof (Z.pow_pos_nonneg 2 j) ; lia)).
    split; [split; [rewrite EJ; clear - P1; lia | clear - D4 LEN; lia]|].
    rewrite EJ. replace (48 * 2 ^ j) with (16 * (3 * 2 ^ j)) by ring. rewrite Z.mul_comm. apply Z.mod_mul. lia.
  Qed.

  Lemma ov_call : forall msF1 mo1 R1 m1,
    as_VIS H s msF1 = MS R1 F (Z_to_bv 64 SPB_ENTRY) fc None m1 (seg_rom asegs) -> rfull R1 ->
    rtbl Wo0 R1 RTO1 -> ftbl Wo0 spz m1 STO1 -> ftbl Wo0 ds m1 DTO0 -> Po sp m ds m1 -> mem_inv asegs m1 ->
    as_AKREL H s (mkCfg msF1 mo1) -> as_MPRES H mo mo1 ->
    (forall msF2 mo2 sk2 m2 R2 LB2 pid2 d', pb_after msF2 mo2 sk2 m2 R2 LB2 pid2 d' -> as_SR H POSTov (mkCfg msF2 mo2)) ->
    as_SR H POSTov (mkCfg msF1 mo1).
  Proof.
    intros msF1 mo1 R1 m1 VIS1 RF1 HRT1 HST1 HDT1 PO1 MI1 KR1 MP1 K.
    destruct (ov_m1 m1 PO1 MI1) as (REP1 & BLK1 & ADV1 & WP1 & OW1 & RH1 & RX1 & ST1 & ERR1 & AC1 & RF1' & S01 & LV1 & XP1 & AG1
                                    & ADS1 & WDS1).
    pose proof ov_nums as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & (A1 & A2) & N9 & N10 & N11).
    pose proof ov_data as (D1 & D2 & D3 & D4 & D5). pose proof ov_grow as (GR1 & GR2 & _).
    pose proof DSO as (O1 & O2 & O3). pose proof DSIN as ((f & Hf & IF1 & IF2) & _).
    rgeto HRT1 (1%bv : reg) G1. rgeto HRT1 (2%bv : reg) G2. rgeto HRT1 (4%bv : reg) G4.
    rgeto HRT1 (10%bv : reg) G10. rgeto HRT1 (11%bv : reg) G11.
    rewrite <- (Z_to_bv_bv_unsigned sp) in G2. rewrite w_add_g in G2. replace (spz + -80) with (spz - 80) in G2 by lia.
    rewrite w_add_g in G10.
    assert (U2 : bv_unsigned (PropExec.getr R1 2) = spz - 80).
    { rewrite G2. apply unsigned_lit. clear - N6 N7 A1. unfold OVF_STACK, AOPNEW_STACK, AMALLOC_STACK in *. lia. }
    rewrite (rfull_eq R1 RF1) in VIS1.
    assert (SHA : sh (ds + 72) + nsh 24 = sh (ds + 96)) by (unfold sh, nsh; clear - N3; Z.div_mod_to_equations; lia).

    eapply (ah_seq H HH).
    { eapply (spb_ok H HH) with (c := 0) (p := ds + 72) (sb := ms) (cs := cs) (pid := pid) (LB := LB) (LBo := spb_own ms pid)
          (LF := LF) (lo := lo) (B := B) (shi := shi) (errv := errv).
      - exact VIS1.
      - exact G10.
      - exact G11.
      - clear; lia.
      - exact REP1.
      - exact BLK1.
      - clear - N3. Z.div_mod_to_equations. lia.
      - exact ADV1.
      - exists f. split; [exact Hf|]. clear - IF1 IF2. unfold DS_SIZE in *. lia.
      - rewrite U2. unfold obj_win. split; [|split; [|split; [|split; [|split]]]].
        + right; right; right; right; left. clear - N4 N5. unfold DS_SIZE in *. lia.
        + right; right; right; right; right; left. rewrite SHA. split; apply sh_mono; clear - N4 N5; unfold DS_SIZE in *; lia.
        + right; right; right; right; left. cbn [fst snd]. clear - N4 N5. unfold DS_SIZE in *. lia.
        + right. exists f. cbn [fst snd]. split; [exact Hf|]. clear - IF1 IF2. unfold DS_SIZE in *. lia.
        + destruct N11 as [N11|N11]; [apply LbB_DPdK.aconst_ok_lo | apply LbB_DPdK.aconst_ok_hi];
            unfold AIMG_TOP, ALOWSH_LO, AHI_LO, DS_SIZE in *; clear - N1 N11; lia.
        + left. clear - N2. unfold DS_SIZE in *. lia.
      - destruct N11 as [N11|N11]; [left | right]; unfold AIMG_TOP, ALOWSH_LO, AHI_LO, DS_SIZE, AAPP_HI in *; clear - N1 N11 O3; lia.
      - exact WP1.
      - exact OW1.
      - unfold spb_lbo. destruct ms as [|d asz] eqn:Ems; cbn [spb_own].
        + split; [intros b [] | split; [constructor | exact I]].
        + split; [intros b [<-|[]]; exact (BLKL d asz eq_refl)|]. split; [repeat constructor; intros [] | left; reflexivity].
      - clear - GR1. lia.
      - intros _. split.
        + apply (rt_bp_live H HHbp s LB m1 (str_grow ms) RH1); [clear - GR2; lia | | | ].
          * pose proof (nsmall_bounds (str_grow ms) ltac:(clear - GR2; lia)) as NB. unfold nsmall in *.
            destruct (Z.leb_spec (str_grow ms) 64512) as [Hs|Hs]; clear - BS NB Hs; lia.
          * clear - BC. lia.
          * pose proof (nlg_bounds (str_grow ms)). clear - BL H0. lia.
        + unfold spb_cost. rewrite (proj2 (Z.eqb_eq _ _) CSL).
          destruct (rt_bp_cost H HHbp) as [CF CM]. rewrite CF, CM. clear - COST. lia.
      - exact TRO.
      - exact RH1.
      - exact KR1.
      - exact RX1.
      - rewrite U2. clear - SPB. lia.
      - rewrite U2. clear - SP16. Z.div_mod_to_equations. lia.
      - rewrite U2. clear - N7. lia.
      - rewrite U2. exact (proj1 (stk_split asegs m1 lo (spz - 80) spz ST1 ltac:(clear - N6 CEIL LO; unfold OVF_STACK, AOPNEW_STACK, AMALLOC_STACK in *; lia))).
      - exact CEIL.
      - rewrite U2. clear - LO. unfold OVF_STACK, SPB_STACK, AOPNEW_STACK, AMALLOC_STACK in *. lia.
      - rewrite G4. exact ERR1.
      - exact MI1.
      - rewrite G4. exact TP.
      - exact AC1.
      - exact RF1'.
      - exact S01.
      - rewrite U2. clear - SPS. lia. }
    intros c2 POST. destruct c2 as [msF2 mo2].
    destruct POST as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m2 & errv2 & sk2 & LB2
                      & LBo2 & sb2 & pid2 & VIS2 & KR2 & MP2 & MI2 & ST2 & ERR2 & RX2 & XP2 & RH2 & REP2 & BLK2 & CASE & ADV2 & WP2
                      & OW2 & RF2 & AC2 & S02 & AL2).
    cbn [cfg_ms cfg_model] in VIS2, KR2, MP2.
    destruct CASE as [(NF & _)|(FULL & NI2 & d' & E2 & ELB & ABR & ELBo)]; [exfalso; clear - NF CSL; lia|].
    subst sb2.
    rewrite U2 in ST2, XP2. rewrite G4 in ERR2.
    rewrite G1 in VIS2. rewrite ret_pc_even in VIS2 by (clear; first [reflexivity | lia]).

    assert (XOLD : forall d asz, ms = SLong d asz ->
              0 < d /\ d + asz <= aceil /\ 0 <= asz /\ (ds + DS_SIZE <= d \/ d + asz <= ds) /\ aapp d asz
              /\ d mod 16 = 0 /\ asz mod 8 = 0 /\ AIMG_TOP <= d).
    { intros d asz E. destruct (ov_oldblk d asz E) as (K1 & K2 & K3 & K4 & K5 & _ & K7 & K8 & _ & K10). tauto. }
    assert (SHB : forall x, 0 <= x -> ALOWSH_LO <= sh x) by (intros x Hx; apply sh_ge_lowsh; exact Hx).
    assert (SHT : forall x y, 0 <= x -> 0 <= y -> x + y <= AAPP_HI -> sh x + nsh y <= AHI_LO) by (intros; apply sh_nsh_high; assumption).
    assert (XAP : forall A n, 0 <= A -> 0 <= n ->
              (A + n <= ds + 72 \/ ds + 96 <= A) ->
              (forall d asz, ms = SLong d asz -> (A + n <= d \/ d + asz <= A) /\ (A + n <= sh d \/ sh d + nsh asz <= A)) ->
              Forall (fun iv : Z * Z => A + n <= fst iv \/ snd iv <= A) ((ds + 72, ds + 72 + 24) :: spb_x ms)).
    { intros A n HA Hn H1 H2. apply Forall_cons; [cbn [fst snd]; clear - H1; lia|]. apply spbx_apart. exact H2. }
    assert (INC : forall b, In b LBk -> In b LB).
    { intros b Hb. apply (Permutation_in b (Permutation_sym PERM)). apply in_or_app. right. exact Hb. }

    assert (XDSa : forall A n, ds <= A -> A + n <= ds + DS_SIZE -> 0 <= n -> (A + n <= ds + 72 \/ ds + 96 <= A) ->
              Forall (fun iv : Z * Z => A + n <= fst iv \/ snd iv <= A) ((ds + 72, ds + 72 + 24) :: spb_x ms)).
    { intros A n K1 K2 K3 K4.
      apply XAP; [clear - K1 N1; unfold AIMG_TOP in *; lia | exact K3 | exact K4 |].
      intros d asz E. destruct (XOLD d asz E) as (L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8).
      split; [clear - L4 K1 K2; unfold DS_SIZE in *; lia|].
      pose proof (SHB d ltac:(clear - L1; lia)) as S1.
      assert (AHd : d + asz <= AAPP_HI) by (clear - L2 A2; unfold AAPP_HI; lia).
      pose proof (SHT d asz ltac:(clear - L1; lia) L3 AHd) as S2.
      clear - N11 K1 K2 S1 S2 O3. unfold ALOWSH_LO, AHI_LO, DS_SIZE, AAPP_HI in *. lia. }
    assert (XDS : forall A n, ds <= A -> A + n <= ds + DS_SIZE -> 0 <= n -> (A + n <= ds + 72 \/ ds + 96 <= A) ->
              xclient_range H LB (spz - 80) ((ds + 72, ds + 72 + 24) :: spb_x ms) A n).
    { intros A n K1 K2 K3 K4. split; [| exact (XDSa A n K1 K2 K3 K4)].
      right; right; right; right; left. clear - K1 K2 N4 N5. lia. }

    assert (XSTK : Forall (fun iv : Z * Z => spz - 80 + 80 <= fst iv \/ snd iv <= spz - 80) ((ds + 72, ds + 72 + 24) :: spb_x ms)).
    { apply XAP; [clear - N6 A1; unfold OVF_STACK, AOPNEW_STACK, AMALLOC_STACK in *; lia | clear; lia | |].
      - right. clear - N2 LO. unfold DS_SIZE, OVF_STACK, AOPNEW_STACK, AMALLOC_STACK in *. lia.
      - intros d asz E. destruct (XOLD d asz E) as (L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8).
        pose proof (sh_below_aceil (d + asz) ltac:(clear - L1 L2 L3 A2; unfold AAPP_HI; lia)) as S3.
        assert (S4 : sh d + nsh asz <= sh (d + asz)) by (unfold sh, nsh; clear - L6 L7 L1 L3; Z.div_mod_to_equations; lia).
        split; right; clear - L2 S3 S4 N6 CEIL LO; unfold OVF_STACK, AOPNEW_STACK, AMALLOC_STACK in *; lia. }

    assert (XSH : xclient_range H LB (spz - 80) ((ds + 72, ds + 72 + 24) :: spb_x ms) (sh ds) (nsh DS_SIZE)).
    { assert (E49 : sh ds + nsh DS_SIZE = sh (ds + DS_SIZE)) by (unfold sh, nsh, DS_SIZE; clear - N3; Z.div_mod_to_equations; lia).
      pose proof (SHB ds ltac:(clear - N1; unfold AIMG_TOP in *; lia)) as S1.
      pose proof (SHT ds DS_SIZE ltac:(clear - N1; unfold AIMG_TOP in *; lia) ltac:(unfold DS_SIZE; clear; lia) O3) as S2.
      split.
      - right; right; right; right; right; left. rewrite E49. split; apply sh_mono; clear - N4 N5; lia.
      - apply XAP; [clear - S1; unfold ALOWSH_LO in *; lia | unfold nsh, DS_SIZE; clear; lia | |].
        + clear - N11 S1 S2 N1. unfold ALOWSH_LO, AHI_LO, DS_SIZE, AIMG_TOP in *. lia.
        + intros d asz E. destruct (XOLD d asz E) as (L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8).
          assert (AHd : d + asz <= AAPP_HI) by (clear - L2 A2; unfold AAPP_HI; lia).
          pose proof (SHT d asz ltac:(clear - L1; lia) L3 AHd) as S5. pose proof (SHB d ltac:(clear - L1; lia)) as S6.
          split.
          * destruct L5 as [(L5a & L5b)|(L5a & L5b)]; unfold ALOWSH_LO, AHI_LO in *; [right|left]; clear - L5a L5b S1 S2 S5 S6; lia.
          * clear - L4 E49 L6 L7 L1 L3 N3. unfold sh, nsh, DS_SIZE in *. Z.div_mod_to_equations. lia. }
    pose proof HDT1 as HDTab. unfold DTO0 in HDTab. unfold ftbl in HDTab. apply Forall_app in HDTab as [HDTa HDTb].
    change (ftbl Wo0 ds m1 DTO0a) in HDTa. change (ftbl Wo0 ds m1 DTO0b) in HDTb.
    eapply (K msF2 mo2 sk2 m2 _ LB2 pid2 d').
    unfold pb_after.
    split; [exact VIS2|]. split; [apply rfull_mkR|].
    split.
    { eapply (rtbl_keep Wo0 R1 _ RTQ0 KEPT); [apply (rtbl_sub _ _ _ _ HRT1); vm_compute; reflexivity | vm_compute; reflexivity |].
      apply getr_mkR_keptR. exact (eq_sym G1). }
    split.
    { eapply (ftbl_xpres H LB (spz - 80) _ Wo0 spz m1 m2 STO1 (-80) 0 HST1 XP2); [vm_compute; reflexivity|]. split.
      - left. clear; lia.
      - eapply Forall_impl; [|exact XSTK]. intros [l h] Hlh. cbn [fst snd] in *. clear - Hlh. lia. }
    split.
    { unfold DTO0. apply ftbl_app.
      - eapply (ftbl_xpres H LB (spz - 80) _ Wo0 ds m1 m2 DTO0a 24 72 HDTa XP2); [vm_compute; reflexivity|].
        apply XDS; unfold DS_SIZE; clear; lia.
      - eapply (ftbl_xpres H LB (spz - 80) _ Wo0 ds m1 m2 DTO0b 96 108 HDTb XP2); [vm_compute; reflexivity|].
        apply XDS; unfold DS_SIZE; clear; lia. }
    split; [exact KR2|]. split; [exact (ah_mpres_trans H HH mo mo1 mo2 MP1 MP2)|]. split; [exact MI2|].
    split.
    { eapply (stk_merge asegs); [exact ST2 | | clear - N6 CEIL LO; unfold OVF_STACK, AOPNEW_STACK, AMALLOC_STACK in *; lia].
      eapply (xpres_stk H); [exact XP2 | exact (proj2 (stk_split asegs m1 lo (spz - 80) spz ST1
                                                  ltac:(clear - N6 CEIL LO; unfold OVF_STACK, AOPNEW_STACK, AMALLOC_STACK in *; lia))) | clear; lia |].
      eapply Forall_impl; [|exact XSTK]. intros [l h] Hlh. cbn [fst snd] in *. clear - Hlh. lia. }
    split; [exists errv2; exact ERR2|]. split; [exact RX2|].
    split.
    { eapply (xpres_trans H).
      - eapply (xpres_weaken H); [exact XP1 | clear; lia | exact INC | intros a Ha; exact Ha].
      - eapply (xpres_weaken H); [exact XP2 | clear; lia | exact INC |].
        intros a Ha. rewrite <- spb_x_sbx. cbn [rin_ivs fst snd] in Ha |- *. destruct Ha as [Ha|Ha]; [left; unfold DS_SIZE; clear - Ha; lia | right; exact Ha]. }
    split.
    { intros a Ha. rewrite <- (AG1 a Ha). unfold zwin in Ha.
      assert (Ra : 0 <= a < 2 ^ 64) by (clear - Ha N1 O3; unfold AIMG_TOP, AAPP_HI, DS_SIZE in *; lia).
      assert (XC : xclient H LB (spz - 80) ((ds + 72, ds + 72 + 24) :: spb_x ms) a); [| exact (proj1 (XP2 a Ra XC))].
      split.
      - right; right; right; right; left. clear - Ha N4 N5. unfold DS_SIZE in *. lia.
      - destruct Ha as [Ha|Ha].
        + pose proof (XDSa ds 24 ltac:(clear; lia) ltac:(unfold DS_SIZE; clear; lia) ltac:(clear; lia) ltac:(clear; lia)) as XA.
          clear - XA Ha. induction XA as [|[l h] X' Hlh _ IH]; [intros []|]. cbn [rin_ivs fst snd] in *. intros [K|K]; [lia | exact (IH K)].
        + pose proof (XDSa (ds + 108) (DS_SIZE - 108) ltac:(clear; lia) ltac:(clear; lia) ltac:(unfold DS_SIZE; clear; lia) ltac:(clear; lia)) as XA.
          clear - XA Ha. induction XA as [|[l h] X' Hlh _ IH]; [intros []|]. cbn [rin_ivs fst snd] in *. intros [K|K]; [lia | exact (IH K)]. }
    split; [exact RH2|]. split; [exact REP2|]. cbn [spb_blk] in BLK2. split; [exact (proj1 BLK2)|]. split; [exact (proj2 BLK2)|].
    split; [exact NI2|]. split; [exact ELB|]. split; [exact ABR|].
    split; [exact (addressable_xpres H LB (spz - 80) _ m1 m2 ds DS_SIZE ADS1 XP2 XSH)|].
    split.
    { replace DS_SIZE with (72 + (24 + 296)) by reflexivity.
      apply wr_at_app; [clear; lia | clear; lia |]. split.
      - eapply (xpres_wr_at H); [exact XP2 | eapply wr_at_sub; [exact WDS1 | clear; lia | unfold DS_SIZE; clear; lia | clear; lia] |].
        apply XDS; unfold DS_SIZE; clear; lia.
      - apply wr_at_app; [clear; lia | clear; lia |]. split; [exact WP2|].
        eapply (xpres_wr_at H); [exact XP2 | eapply wr_at_sub; [exact WDS1 | clear; lia | unfold DS_SIZE; clear; lia | clear; lia] |].
        apply XDS; unfold DS_SIZE; clear; lia. }
    split.
    { rewrite ELBo in OW2. unfold spb_LB in OW2. unfold lb_own in OW2. apply Forall_inv in OW2. exact OW2. }
    split; [exact RF2|]. split; [exact AC2|]. split; [exact S02|].
    split.
    { eapply LINV_P5_cl; [exact LV1|]. intros a Ha Hc.
      assert (XC : xclient H LB (spz - 80) ((ds + 72, ds + 72 + 24) :: spb_x ms) a); [| exact (proj1 (XP2 a Ha XC))].
      split.
      - right; left. exact Hc.
      - assert (AI : a < AIMG_TOP) by (unfold aimg_client, AIMG_TOP in *; clear - Hc; lia).
        assert (XA : Forall (fun iv : Z * Z => a + 1 <= fst iv \/ snd iv <= a) ((ds + 72, ds + 72 + 24) :: spb_x ms)).
        { apply XAP; [clear - Ha; lia | clear; lia | left; clear - AI N1; unfold AIMG_TOP in *; lia |].
          intros d asz E. destruct (XOLD d asz E) as (L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8).
          pose proof (SHB d ltac:(clear - L1; lia)) as S6.
          split; left; clear - AI L8 S6; unfold AIMG_TOP, ALOWSH_LO in *; lia. }
        clear - XA. induction XA as [|[l h] X' Hlh _ IH]; [intros []|]. cbn [rin_ivs fst snd] in *. intros [K|K]; [lia | exact (IH K)]. }
    unfold spb_cost in AL2. rewrite (proj2 (Z.eqb_eq _ _) CSL) in AL2.
    destruct (rt_bp_cost H HHbp) as [CF CM]. rewrite CF, CM in AL2. clear - AL2. lia.
  Qed.

  Definition LBr : list block := match ms with SShort => LB | SLong _ _ => as_lb_remove H pid LB end.

  Lemma ov_LBr : forall pid2 d', ~ In pid2 (map blk_id LB) ->
    spb_LB H LB ms pid pid2 d' = (pid2, d', str_grow ms) :: LBr /\ Permutation LBr LBk /\ (forall b, In b LBk -> In b LBr)
    /\ ~ In pid2 (map blk_id LBr) /\ (forall b, In b LBr -> In b LB).
  Proof.
    intros pid2 d' NI. pose proof (ah_nodup H HH _ _ _ RH) as ND. pose proof (ah_lb_remove H HH) as (L1 & L2 & L3).
    unfold LBr, spb_LB. destruct ms as [|d asz] eqn:Ems; cbn [spb_own] in DBE; subst DB; cbn [app] in PERM.
    - split; [reflexivity|]. split; [exact PERM|]. split; [intros b Hb; exact (Permutation_in b (Permutation_sym PERM) Hb)|].
      split; [exact NI | intros b Hb; exact Hb].
    - pose proof (BLKL d asz eq_refl) as IN.
      pose proof (lb_remove_perm_ H HH pid d asz LB ND IN) as P1.
      assert (P2 : Permutation (as_lb_remove H pid LB) LBk).
      { apply (Permutation_cons_inv (a := (pid, d, asz))). eapply perm_trans; [apply Permutation_sym; exact P1 | exact PERM]. }
      split; [reflexivity|]. split; [exact P2|]. split; [intros b Hb; exact (Permutation_in b (Permutation_sym P2) Hb)|].
      split; [| intros b Hb; exact (L3 _ _ _ Hb)].
      intros K. apply in_map_iff in K as (b & Eb & Hb). apply NI. apply in_map_iff. exists b. split; [exact Eb | exact (L3 _ _ _ Hb)].
  Qed.

  Lemma ov_post : forall msF2 mo2 sk2 m2 R2 LB2 pid2 d' msF' mo' m' o t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6,
    pb_after msF2 mo2 sk2 m2 R2 LB2 pid2 d' ->
    as_VIS H sk2 msF' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 c) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                               t3 t4 t5 t6) F (ret_pc ra) fc None m' (seg_rom asegs) ->
    as_AKREL H sk2 (mkCfg msF' mo') -> as_MPRES H mo2 mo' -> mem_inv asegs m' -> ACONST m' ->
    munch [(spz - 8192, spz); (ds + 24, ds + 108); (d' + o, d' + str_grow ms)] m2 m' -> wmono asegs m2 m' -> 0 <= o <= str_grow ms ->
    sb_inv (lbl LB2) m' (ds + 8) (SLong d' (str_grow ms)) (d' + str_cap ms + 1) (d' + str_cap ms + 1) ->
    POSTov (mkCfg msF' mo').
  Proof.
    intros msF2 mo2 sk2 m2 R2 LB2 pid2 d' msF' mo' m' o t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 PA VIS' KR' MP' MI' AC' MU WM O0 SB'.
    destruct PA as (VIS2 & RF2 & HRT2 & HST2 & HDT2 & KR2 & MP2 & MI2 & ST2 & (e2 & ERR2) & RX2 & XP2 & AG2 & RH2 & REP2 & IN2
                    & SH2 & NI2 & ELB & ABR & ADS2 & WDS2 & WB2 & RFS2 & AC2 & S02 & LV2 & AL2).
    pose proof ov_nums as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & (A1 & A2) & N9 & N10 & N11).
    pose proof ov_data as (D1 & D2 & D3 & D4 & D5). pose proof ov_grow as (GR1 & GR2 & GR3 & GR4 & GR5).
    pose proof DSO as (O1 & O2 & O3). pose proof DSIN as ((f & Hf & IF1 & IF2) & _).
    destruct (ov_LBr pid2 d' NI2) as (ELB2 & PRr & INr & NIr & SUBr). rewrite ELB2 in ELB. subst LB2.
    set (g := str_grow ms) in *.
    pose proof ABR as (B0 & B16 & Bn & BI & BC' & BF & BAPP).
    assert (SH : sh aceil >= 0x7fff8000) by (unfold sh, ASHADOW_BASE; clear - A1; Z.div_mod_to_equations; lia).
    set (W3 := [(spz - 8192, spz); (ds + 24, ds + 108); (d' + o, d' + g)]) in MU.
    assert (OUT3 : forall a, ((ds <= a < ds + 24 \/ ds + 108 <= a < ds + DS_SIZE) \/ a < AIMG_TOP
                              \/ (d' <= a < d' + o)) -> outside W3 a).
    { intros a Ha. unfold W3. cbn [outside].
      clear - Ha N1 N2 N4 N5 LO B0 BI BC' BF O0 CEIL. unfold g in *.
      unfold DS_SIZE, OVF_STACK, AOPNEW_STACK, AMALLOC_STACK, AIMG_TOP, AFS_SIZE in *. lia. }

    assert (WC : Forall (aclient_write_ok H ((pid2, d', g) :: LBr)) W3).
    { unfold W3. repeat apply Forall_cons; try apply Forall_nil; unfold aclient_write_ok; cbn [fst snd].
      - left. clear - N6. unfold OVF_STACK, AOPNEW_STACK, AMALLOC_STACK in *. lia.
      - right; right; right; right; left. clear - N4 N5. unfold DS_SIZE, AFS_SIZE in *. lia.
      - right; right; left. exists (pid2, d', g). split; [left; reflexivity|]. cbn [blk_addr blk_size fst snd]. clear - O0 GR1. lia. }
    assert (WF : Forall (afs_write_ok H LF) W3).
    { unfold W3. repeat apply Forall_cons; try apply Forall_nil; unfold afs_write_ok; cbn [fst snd].
      - left. unfold ATLS_PRIV_LO, ATLS_PRIV_HI, ATP. clear - N6 N10 A1. unfold AFS_SIZE, OVF_STACK, AOPNEW_STACK, AMALLOC_STACK in *. lia.
      - right. exists f. split; [exact Hf|]. clear - IF1 IF2. unfold DS_SIZE in *. lia.
      - left. unfold ATLS_PRIV_LO, ATLS_PRIV_HI, ATP. clear - BF BI O0 GR1. unfold AFS_SIZE, AIMG_TOP in *. lia. }
    assert (WS : Forall stack0_ok W3).
    { unfold W3. repeat apply Forall_cons; try apply Forall_nil; unfold stack0_ok, AHI_LO; cbn [fst snd].
      - left. clear - N6 A1. unfold OVF_STACK, AOPNEW_STACK, AMALLOC_STACK in *. lia.
      - destruct N11 as [N11|N11]; [right | left]; unfold ALOWSH_LO, AHI_LO, DS_SIZE in *; clear - N11 SH; lia.
      - destruct BAPP as [(P1 & P2)|(P1 & P2)]; [right | left]; unfold ALOWSH_LO, AHI_LO in *; clear - P1 P2 SH O0 GR1; lia. }
    assert (WH : wins_hi W3).
    { unfold W3, wins_hi. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd].
      - right. clear - N6 A1. unfold AHI_LO, OVF_STACK, AOPNEW_STACK, AMALLOC_STACK in *. lia.
      - destruct N11 as [N11|N11]; [left | right]; unfold AIMG_TOP, ALOWSH_LO, AHI_LO, DS_SIZE in *; clear - N1 N11; lia.
      - destruct BAPP as [(P1 & P2)|(P1 & P2)]; [left | right]; unfold AIMG_TOP, ALOWSH_LO, AHI_LO in *; clear - P1 P2 O0 GR1; lia. }

    assert (AG3 : CRep.agree_on (fun a => zwin ds (ds + 24) a \/ zwin (ds + 108) (ds + DS_SIZE) a) m m').
    { intros a Ha. rewrite <- (AG2 a Ha). apply MU. rewrite unsigned_lit by (unfold zwin in Ha; clear - Ha N1 O3; unfold AIMG_TOP, AAPP_HI, DS_SIZE in *; lia).
      apply OUT3. left. unfold zwin in Ha. exact Ha. }
    unfold POSTov, pc_post.
    exists t0, t1, t2, a1, a2, a3, a4, a5, a6, a7, t3, t4, t5, t6, m', e2, sk2, ((pid2, d', g) :: LBr).
    split; [exact VIS'|]. split; [exact KR'|]. split; [exact (ah_mpres_trans H HH mo mo2 mo' MP2 MP')|]. split; [exact MI'|].
    split; [eapply stk_wmono_hi; [exact ST2 | exact MU | exact WM | clear - CEIL A1; unfold AIMG_TOP; lia]|].
    split.
    { eapply rw_cells_transport; [exact ERR2 | exact MU | exact WM |].
      unfold W3. cbn [disjoint_from cells_size csize]. rewrite TP, unsigned_lit by (clear; unfold ATP; lia).
      clear - N1 N6 A1 BI O0. unfold ATP, AIMG_TOP, OVF_STACK, AOPNEW_STACK, AMALLOC_STACK in *. cbn. lia. }
    split; [eapply (ah_rauxv_frame H HH); [exact RX2 | exact MU | exact WM | exact WC]|].
    split; [eapply (ah_RHEAP_frame H HH); [exact RH2 | exact MU | exact WM | exact WC]|].
    split; [eapply (ah_RFS_frame H HH); [exact RFS2 | exact MU | exact WM | exact WF]|].
    split; [exact AC'|].
    split; [eapply stack0_transport; [exact S02 | exact MU | exact WM | exact WS]|].
    split.
    { eapply LINV_P5_cl; [exact LV2|]. intros a Ha Hc. unfold wa. apply MU. rewrite unsigned_lit by exact Ha.
      apply OUT3. right; left. unfold aimg_client, AIMG_TOP in *. clear - Hc. lia. }

    exists pid2, d'. split; [apply perm_skip; exact PRr|].
    split.
    { unfold ds_rep_w. split; [| split; [| split; [| split; [| split]]]].
      - assert (II' : ios_inv m' (ds + 112) (ds + 8) fl fill).
        { eapply ios_inv_frame; [exact (di_ios _ _ _ _ _ _ _ _ _ _ _ DI) | clear - N1; unfold AIMG_TOP in *; lia
                                | clear - O3; unfold AAPP_HI, DS_SIZE in *; lia |].
          intros a Ha. apply AG3. right. unfold zwin in *. unfold DS_SIZE. clear - Ha. lia. }
        assert (MD' : mdef m' ds 392).
        { apply mdef_of_wr_at_hi; [| exact N1]. eapply wr_at_transport; [exact WDS2 | exact WM]. }
        pose proof (ds_inv_resb (lbl LB) (lbl ((pid2, d', g) :: LBr)) m m' ds err len (len + 1) (lbl DB) ms
                      (dsdata ds ms + str_cap ms) hm fl fill (SLong d' g) (d' + str_cap ms + 1) (d' + str_cap ms + 1) fl fill
                      DI SB' II' MD') as K.
        cbn [str_blocks str_data] in K. change (lbl [(pid2, d', g)]) with [(d', g)].
        apply K.
        + intros a Ha. apply AG3. unfold zwin in *. unfold DS_SIZE. clear - Ha. lia.
        + clear; lia.
        + clear - D4 D5 LEN. lia.
        + intros d0 asz0 E. injection E as <- <-. split; [clear - D4 GR3; lia|].
          split; [unfold DS_MAXBLK; clear - GR1; lia|]. split; [exact GR4|].
          clear - BF BI BC' N4 N5 Bn. unfold DS_SIZE, AFS_SIZE in *. lia.
      - exists pid2. split; [reflexivity | left; reflexivity].
      - eapply addressable_transport_hi; [exact ADS2 | exact MU | exact WM | exact O3 | exact WH].
      - eapply wr_at_transport; [exact WDS2 | exact WM].
      - exact DSO.
      - cbn [sb_addr]. split.
        + eapply addressable_transport_hi; [split; [clear - GR2; lia | exact SH2] | exact MU | exact WM | | exact WH].
          destruct BAPP as [(P1 & P2)|(P1 & P2)]; unfold ALOWSH_LO, AAPP_HI in *; clear - P1 P2 A2; lia.
        + unfold app_obj. destruct BAPP as [(P1 & P2)|(P1 & P2)]; unfold ALOWSH_LO, AHI_LO, AAPP_HI, AIMG_TOP in *; clear - P1 P2 A2; lia. }
    split; [apply lb_own_cons; [eapply wr_at_transport; [exact WB2 | exact WM] | apply lb_own_nil]|].
    split; [| exact AL2].

    eapply (xpres_trans H); [exact XP2|].
    eapply (xpres_weaken H LBr LBk spz spz); [| clear; lia | exact INr | intros a Ha; exact Ha].
    eapply (xpres_drop_fresh' H HH LBr spz _ m2 m' sk2 m2 pid2 d' g RH2 NIr ltac:(clear - N6; unfold OVF_STACK, AOPNEW_STACK, AMALLOC_STACK in *; lia)).
    eapply (xpres_weaken H ((pid2, d', g) :: LBr) LBr spz spz); [| clear; lia | intros b Hb; right; exact Hb | intros a Ha; exact Ha].
    eapply (xpres_of_munch H sk2 _ spz _ W3 m2 m2 m' HH RH2 MU WM). unfold W3.
    repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd].
    - left. clear - N6. unfold OVF_STACK, AOPNEW_STACK, AMALLOC_STACK in *. lia.
    - right. intros a Ha. cbn [rin_ivs app fst snd]. left. unfold DS_SIZE. clear - Ha. lia.
    - right. intros a Ha. apply rin_ivs_app. right. cbn [rin_ivs fst snd]. left. clear - Ha O0. lia.
  Qed.

  Lemma ov_fin_s : ms = SShort -> forall msF2 mo2 sk2 m2 R2 LB2 pid2 d',
    pb_after msF2 mo2 sk2 m2 R2 LB2 pid2 d' -> as_SR H POSTov (mkCfg msF2 mo2).
  Proof.
    intros EMS msF2 mo2 sk2 m2 R2 LB2 pid2 d' PA.
    pose proof ov_nums as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & (A1 & A2) & N9 & N10 & N11).
    pose proof ov_data as (D1 & D2 & D3 & D4 & D5). pose proof ov_grow as (GR1 & GR2 & GR3 & GR4 & GR5).
    pose proof PA as PA'.
    destruct PA' as (VIS2 & RF2 & HRT2 & HST2 & HDT2 & KR2 & MP2 & MI2 & ST2 & _ & _ & _ & AG2 & RH2 & REP2 & IN2 & SH2 & NI2 & _
                     & ABR & ADS2 & WDS2 & WB2 & _ & AC2 & _ & _ & _).
    assert (EG : str_grow ms = 48) by (rewrite EMS; reflexivity).
    assert (EC : str_cap ms = 22) by (rewrite EMS; reflexivity).
    assert (EDT : dsdata ds ms = ds + 73) by (rewrite EMS; unfold dsdata; cbn [str_data]; lia).
    rewrite EG in REP2, IN2, SH2, ABR, WB2.
    pose proof ABR as (B0 & B16 & Bn & BI & BC' & BF & BAPP).
    assert (BAPP' : in_app_mem d' (d' + 48)) by (eapply aapp_in_app_mem; [exact BAPP | clear; lia | clear; lia]).
    assert (BAC : aconst_ok (d', d' + 48)) by (eapply aconst_ok_app; [exact BAPP | clear; lia | clear; lia]).
    assert (BV : shvis m2 d' (d' + 48)) by exact (ah_blk_shvis H HH sk2 LB2 m2 pid2 d' 48 RH2 IN2).
    assert (BDS : d' + 48 <= ds \/ ds + DS_SIZE <= d') by (clear - BF N4 N5; unfold DS_SIZE, AFS_SIZE in *; lia).

    set (Wq0 := Wq ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ds c (dsdata ds ms) (dsdata ds ms + str_cap ms) hm d').
    assert (EW : Wq0 = Wo0 ++ [Z_to_bv 64 d']) by reflexivity.
    assert (HRTq : rtbl Wq0 R2 RTQ0) by (rewrite EW; apply rtbl_wext; [vm_compute; reflexivity | exact HRT2]).
    assert (HSTq : ftbl Wq0 spz m2 STO1) by (rewrite EW; apply ftbl_wext; [vm_compute; reflexivity | exact HST2]).
    assert (HDTq : ftbl Wq0 ds m2 DTQS).
    { unfold DTQS. apply ftbl_app; [rewrite EW; apply ftbl_wext; [vm_compute; reflexivity | exact HDT2] |].
      pose proof REP2 as (_ & _ & _ & _ & (_ & _ & _ & _ & _ & _ & _ & F72 & F80 & F88) & _).
      rewrite Zlen_app1, CSL, EC in F80.
      assert (WR : forall k w, 0 <= k -> k + w <= DS_SIZE -> 0 <= w -> wr_at asegs m2 (ds + k) w).
      { intros k w K1 K2 K3. eapply wr_at_sub; [exact WDS2 | lia | lia | lia]. }
      apply (ftbl_cons1 _ ds _ 72 8 _ _ _ _ F72 ltac:(lia)); [apply WR; unfold DS_SIZE; lia | reflexivity | unfold AIMG_TOP in N1; lia |].
      apply (ftbl_cons1 _ ds _ 80 8 _ _ _ _ F80 ltac:(lia)); [apply WR; unfold DS_SIZE; lia | reflexivity | unfold AIMG_TOP in N1; lia |].
      apply (ftbl_cons1 _ ds _ 88 8 _ _ _ _ F88 ltac:(lia)); [apply WR; unfold DS_SIZE; lia | reflexivity | unfold AIMG_TOP in N1; lia |].
      constructor. }
    eapply (sr_evt H HH _ _ sk2 msF2 mo2 R2 F (Z_to_bv 64 0x126038) fc m2 (seg_rom asegs) KR2 VIS2).
    { apply (o23s_evt ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m2 ds c (dsdata ds ms) (dsdata ds ms + str_cap ms) hm lo d'
               DSO WDS2 ST2 CEIL ltac:(clear - LO; unfold OVF_STACK, AOPNEW_STACK, AMALLOC_STACK in LO; lia) N7 N2 CR
               ltac:(clear - D1 D2 D3 D5; lia)
               (conj BI (conj (ltac:(clear - BC' CEIL; lia) : d' + 48 <= lo) B16)) BDS WB2 (conj (ltac:(clear; lia) : 0 <= 48) SH2) BV BAPP' BAC MI2 AC2
               ltac:(rewrite EC; reflexivity) ltac:(rewrite EC in D3; exact D3) R2 RF2 HRTq HSTq HDTq). }
    intros msF' mo' KR' MP' HP. destruct HP as (R' & m' & E' & RF' & HRT' & HDT' & HBT' & (MU & WM) & MI' & AC').
    rewrite (rtbl4_q _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ R' RF' HRT' CR) in E'.

    pose proof DSO as (O1 & O2 & O3).
    assert (FT : forall a k w e v, a = ds + k -> In (k, w, e) DTQ4 -> edenot (wenv Wq0) e = Z_to_bv 64 v -> CRep.fld ASEGS m' a w v).
    { intros a k w e v -> Hi He. exact (fld_of_ftbl Wq0 ds m' DTQ4 k w e v HDT' Hi He). }
    assert (FB : forall a k w e v, a = d' + k -> In (k, w, e) BTQ4 -> edenot (wenv Wq0) e = Z_to_bv 64 v -> CRep.fld ASEGS m' a w v).
    { intros a k w e v -> Hi He. exact (fld_of_ftbl Wq0 d' m' BTQ4 k w e v HBT' Hi He). }
    assert (WDS' : wr_at asegs m' ds DS_SIZE) by (eapply wr_at_transport; [exact WDS2 | exact WM]).
    assert (OUTq : forall a, ((ds <= a < ds + 24 \/ ds + 108 <= a < ds + DS_SIZE) \/ (d' <= a < d' + 22)) ->
              outside [(spz - 8192, spz); (ds + 24, ds + 108); (d' + 22, d' + 48)] a).
    { intros a Ha. cbn [outside].
      clear - Ha N1 N2 N4 N5 LO B0 BI BC' BF CEIL. unfold DS_SIZE, OVF_STACK, AOPNEW_STACK, AMALLOC_STACK, AIMG_TOP, AFS_SIZE in *. lia. }
    assert (AGm : CRep.agree_on (fun a => zwin ds (ds + 24) a \/ zwin (ds + 108) (ds + DS_SIZE) a) m m').
    { intros a Ha. rewrite <- (AG2 a Ha). apply MU. rewrite unsigned_lit by (unfold zwin in Ha; clear - Ha N1 O3; unfold AIMG_TOP, AAPP_HI, DS_SIZE in *; lia).
      apply OUTq. left. unfold zwin in Ha. exact Ha. }
    destruct (di_sb _ _ _ _ _ _ _ _ _ _ _ DI) as [Fvt Floc _ _ _ _ _ _ _ _ _ _ _].
    assert (SB' : sb_inv (lbl LB2) m' (ds + 8) (SLong d' 48) (d' + 22 + 1) (d' + 22 + 1)).
    { econstructor.
      - eapply fld_agree; [clear - N1; unfold AIMG_TOP in *; lia | clear - O3; unfold AAPP_HI, DS_SIZE in *; cbn; lia | exact Fvt |].
        intros a Ha. apply AGm. left. unfold zwin in *. cbn in Ha. clear - Ha. lia.
      - eapply fld_agree; [clear - N1; unfold AIMG_TOP in *; lia | clear - O3; unfold AAPP_HI, DS_SIZE in *; cbn; lia | exact Floc |].
        intros a Ha. apply AGm. left. unfold zwin in *. cbn in Ha. clear - Ha. lia.
      - apply (FT _ 24 8%nat (ELit 0)); [clear; lia | In_tbl | reflexivity].
      - apply (FT _ 32 8%nat (ELit 0)); [clear; lia | In_tbl | reflexivity].
      - apply (FT _ 40 8%nat (ELit 0)); [clear; lia | In_tbl | reflexivity].
      - exists (cs ++ [c] ++ repeat 0 (Z.to_nat (48 - 2 - Zlen cs))). split.
        + replace (ds + 8 + 64) with (ds + 72) by (clear; lia).
          apply (strA_grown LB2 m2 m' (ds + 72) d' 48 cs c REP2); [rewrite CSL, EC; clear; lia | clear - CR; lia | | | | | | | ].
          * intros i Hi. apply MU. rewrite unsigned_lit by (rewrite CSL, EC in Hi; clear - Hi B0 BC' A2; lia).
            apply OUTq. right. rewrite CSL, EC in Hi. clear - Hi. lia.
          * rewrite CSL, EC. apply (FB _ 22 1%nat (EVar 35)); [clear; lia | In_tbl | reflexivity].
          * intros i Hi. rewrite CSL, EC in Hi. apply (FB _ i 1%nat (ELit 0)); [clear; lia | | reflexivity].
            unfold BTQ4. right. apply In_zents1. cbn. clear - Hi. lia.
          * apply (FT _ 72 8%nat (ELit 49)); [clear; lia | In_tbl | reflexivity].
          * apply (FT _ 80 8%nat (ELit 47)); [clear; lia | In_tbl | reflexivity].
          * apply (FT _ 88 8%nat (EVar 53)); [clear; lia | In_tbl | reflexivity].
          * apply mdef_of_wr_at_hi; [eapply wr_at_sub; [exact WDS' | clear; lia | unfold DS_SIZE; clear; lia | clear; lia] | clear - N1; unfold AIMG_TOP in *; lia].
        + rewrite StrLib.Zlen_app. change ([c] ++ repeat 0 (Z.to_nat (48 - 2 - Zlen cs))) with (c :: repeat 0 (Z.to_nat (48 - 2 - Zlen cs))).
          unfold Zlen at 2. cbn [length]. rewrite repeat_length. rewrite CSL, EC. cbn. reflexivity.
      - cbn [str_data]. apply (FT _ 48 8%nat (EVar 53)); [clear; lia | In_tbl | reflexivity].
      - replace (d' + 22 + 1) with (d' + 23) by (clear; lia). apply (FT _ 56 8%nat (EAlu ALU_ADD (EVar 53) (ELit 23))); [clear; lia | In_tbl | cbn [edenot]; rewrite <- w_add_g; reflexivity].
      - cbn [str_data str_cap]. apply (FT _ 64 8%nat (EAlu ALU_ADD (EVar 53) (ELit 47))); [clear; lia | In_tbl | cbn [edenot]; rewrite <- w_add_g; reflexivity].
      - cbn [str_data str_cap]. clear; lia.
      - replace (d' + 22 + 1) with (d' + 23) by (clear; lia). apply (FT _ 96 8%nat (EAlu ALU_ADD (EVar 53) (ELit 23))); [clear; lia | In_tbl | cbn [edenot]; rewrite <- w_add_g; reflexivity].
      - cbn [str_data str_cap]. clear; lia.
      - apply (FT _ 104 4%nat (ELit 16)); [clear; lia | In_tbl | reflexivity]. }
    eapply (ov_post msF2 mo2 sk2 m2 R2 LB2 pid2 d' msF' mo' m' 22 _ _ _ _ _ _ _ _ _ _ _ _ _ _ PA E' KR' MP' MI' AC');
      [rewrite EG; exact MU | exact WM | rewrite EG; clear; lia | rewrite EG, EC; exact SB'].
  Qed.

  Lemma ov_fin_l : forall d asz, ms = SLong d asz -> forall msF2 mo2 sk2 m2 R2 LB2 pid2 d',
    pb_after msF2 mo2 sk2 m2 R2 LB2 pid2 d' -> as_SR H POSTov (mkCfg msF2 mo2).
  Proof.
    intros d asz EMS msF2 mo2 sk2 m2 R2 LB2 pid2 d' PA.
    pose proof ov_nums as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & (A1 & A2) & N9 & N10 & N11).
    pose proof ov_data as (D1 & D2 & D3 & D4 & D5). pose proof ov_grow as (GR1 & GR2 & GR3 & GR4 & GR5).
    pose proof (ov_asz d asz EMS) as AR.
    pose proof PA as PA'.
    destruct PA' as (VIS2 & RF2 & HRT2 & HST2 & HDT2 & KR2 & MP2 & MI2 & ST2 & _ & _ & _ & AG2 & RH2 & REP2 & IN2 & SH2 & NI2 & _
                     & ABR & ADS2 & WDS2 & WB2 & _ & AC2 & _ & _ & _).
    assert (EG : str_grow ms = 2 * asz) by (rewrite EMS; reflexivity).
    assert (EC : str_cap ms = asz - 1) by (rewrite EMS; reflexivity).
    assert (EDT : dsdata ds ms = d) by (rewrite EMS; reflexivity).
    rewrite EG in REP2, IN2, SH2, ABR, WB2.
    pose proof ABR as (B0 & B16 & Bn & BI & BC' & BF & BAPP).
    assert (BAPP' : in_app_mem d' (d' + 2 * asz)) by (eapply aapp_in_app_mem; [exact BAPP | clear; lia | clear; lia]).
    assert (BAC : aconst_ok (d', d' + 2 * asz)) by (eapply aconst_ok_app; [exact BAPP | clear; lia | clear; lia]).
    assert (BV : shvis m2 d' (d' + 2 * asz)) by exact (ah_blk_shvis H HH sk2 LB2 m2 pid2 d' (2 * asz) RH2 IN2).
    assert (BDS : d' + 2 * asz <= ds \/ ds + DS_SIZE <= d') by (clear - BF N4 N5; unfold DS_SIZE, AFS_SIZE in *; lia).

    set (Wl0 := Wl ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ds c (dsdata ds ms) (dsdata ds ms + str_cap ms) hm d' asz).
    assert (EW : Wl0 = Wo0 ++ [Z_to_bv 64 d'; Z_to_bv 64 asz]) by reflexivity.
    assert (HRTl : rtbl Wl0 R2 RTQ0) by (rewrite EW; apply rtbl_wext; [vm_compute; reflexivity | exact HRT2]).
    assert (HSTl : ftbl Wl0 spz m2 STO1) by (rewrite EW; apply ftbl_wext; [vm_compute; reflexivity | exact HST2]).
    assert (HDTl : ftbl Wl0 ds m2 DTQL).
    { unfold DTQL. apply ftbl_app; [rewrite EW; apply ftbl_wext; [vm_compute; reflexivity | exact HDT2] |].
      pose proof REP2 as (_ & _ & _ & _ & (_ & _ & _ & _ & _ & _ & _ & F72 & F80 & F88) & _).
      rewrite Zlen_app1, CSL, EC in F80. replace (asz - 1 + 1) with asz in F80 by (clear; lia).
      assert (WR : forall k w, 0 <= k -> k + w <= DS_SIZE -> 0 <= w -> wr_at asegs m2 (ds + k) w).
      { intros k w K1 K2 K3. eapply wr_at_sub; [exact WDS2 | lia | lia | lia]. }
      apply (ftbl_cons1 _ ds _ 72 8 _ _ _ _ F72 ltac:(lia)); [apply WR; unfold DS_SIZE; lia | | unfold AIMG_TOP in N1; lia |].
      { cbn [edenot]. rewrite <- w_add_g, <- w_mul_g. reflexivity. }
      apply (ftbl_cons1 _ ds _ 80 8 _ _ _ _ F80 ltac:(lia)); [apply WR; unfold DS_SIZE; lia | reflexivity | unfold AIMG_TOP in N1; lia |].
      apply (ftbl_cons1 _ ds _ 88 8 _ _ _ _ F88 ltac:(lia)); [apply WR; unfold DS_SIZE; lia | reflexivity | unfold AIMG_TOP in N1; lia |].
      constructor. }
    eapply (sr_evt H HH _ _ sk2 msF2 mo2 R2 F (Z_to_bv 64 0x126038) fc m2 (seg_rom asegs) KR2 VIS2).
    { apply (o23l_evt ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m2 ds c (dsdata ds ms) (dsdata ds ms + str_cap ms) hm lo d' asz
               DSO WDS2 ST2 CEIL ltac:(clear - LO; unfold OVF_STACK, AOPNEW_STACK, AMALLOC_STACK in LO; lia) N7 N2 CR
               ltac:(clear - D1 D2 D3 D5; lia) AR
               (conj BI (conj (ltac:(clear - BC' CEIL; lia) : d' + 2 * asz <= lo) B16)) BDS WB2
               (conj (ltac:(clear - AR; lia) : 0 <= 2 * asz) SH2) BV BAPP' BAC MI2 AC2
               ltac:(rewrite EC; reflexivity) ltac:(rewrite EC in D3; exact D3) R2 RF2 HRTl HSTl HDTl). }
    intros msF' mo' KR' MP' HP. destruct HP as (R' & m' & E' & RF' & HRT' & HDT' & HCT' & HTT' & ZZ & (MU & WM) & MI' & AC').
    rewrite (rtbl4_l _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ R' RF' HRT' CR) in E'.

    pose proof DSO as (O1 & O2 & O3).
    assert (FT : forall a k w e v, a = ds + k -> In (k, w, e) DTL4 -> edenot (wenv Wl0) e = Z_to_bv 64 v -> CRep.fld ASEGS m' a w v).
    { intros a k w e v -> Hi He. exact (fld_of_ftbl Wl0 ds m' DTL4 k w e v HDT' Hi He). }
    assert (WDS' : wr_at asegs m' ds DS_SIZE) by (eapply wr_at_transport; [exact WDS2 | exact WM]).
    assert (OUTl : forall a, ((ds <= a < ds + 24 \/ ds + 108 <= a < ds + DS_SIZE) \/ (d' <= a < d' + asz - 1)) ->
              outside [(spz - 8192, spz); (ds + 24, ds + 108); (d' + asz - 1, d' + 2 * asz)] a).
    { intros a Ha. cbn [outside].
      clear - Ha N1 N2 N4 N5 LO B0 BI BC' BF CEIL AR. unfold DS_SIZE, OVF_STACK, AOPNEW_STACK, AMALLOC_STACK, AIMG_TOP, AFS_SIZE in *. lia. }
    assert (AGm : CRep.agree_on (fun a => zwin ds (ds + 24) a \/ zwin (ds + 108) (ds + DS_SIZE) a) m m').
    { intros a Ha. rewrite <- (AG2 a Ha). apply MU. rewrite unsigned_lit by (unfold zwin in Ha; clear - Ha N1 O3; unfold AIMG_TOP, AAPP_HI, DS_SIZE in *; lia).
      apply OUTl. left. unfold zwin in Ha. exact Ha. }
    assert (HZ : ftbl Wl0 (d' + asz) m' (zents1 (d' + asz - (d' + asz)) (Z.to_nat (asz - 1))))
      by (apply ftbl_zres1; [clear - AR; lia | exact ZZ]).
    replace (d' + asz - (d' + asz)) with 0 in HZ by (clear; lia).
    destruct (di_sb _ _ _ _ _ _ _ _ _ _ _ DI) as [Fvt Floc _ _ _ _ _ _ _ _ _ _ _].
    assert (SB' : sb_inv (lbl LB2) m' (ds + 8) (SLong d' (2 * asz)) (d' + (asz - 1) + 1) (d' + (asz - 1) + 1)).
    { replace (d' + (asz - 1) + 1) with (d' + asz) by (clear; lia).
      econstructor.
      - eapply fld_agree; [clear - N1; unfold AIMG_TOP in *; lia | clear - O3; unfold AAPP_HI, DS_SIZE in *; cbn; lia | exact Fvt |].
        intros a Ha. apply AGm. left. unfold zwin in *. cbn in Ha. clear - Ha. lia.
      - eapply fld_agree; [clear - N1; unfold AIMG_TOP in *; lia | clear - O3; unfold AAPP_HI, DS_SIZE in *; cbn; lia | exact Floc |].
        intros a Ha. apply AGm. left. unfold zwin in *. cbn in Ha. clear - Ha. lia.
      - apply (FT _ 24 8%nat (ELit 0)); [clear; lia | In_tbl | reflexivity].
      - apply (FT _ 32 8%nat (ELit 0)); [clear; lia | In_tbl | reflexivity].
      - apply (FT _ 40 8%nat (ELit 0)); [clear; lia | In_tbl | reflexivity].
      - exists (cs ++ [c] ++ repeat 0 (Z.to_nat (2 * asz - 2 - Zlen cs))). split.
        + replace (ds + 8 + 64) with (ds + 72) by (clear; lia).
          apply (strA_grown LB2 m2 m' (ds + 72) d' (2 * asz) cs c REP2); [rewrite CSL, EC; clear - AR; lia | clear - CR; lia | | | | | | | ].
          * intros i Hi. apply MU. rewrite unsigned_lit by (rewrite CSL, EC in Hi; clear - Hi B0 BC' A2; lia).
            apply OUTl. right. rewrite CSL, EC in Hi. clear - Hi. lia.
          * rewrite CSL, EC. pose proof (fld_of_ftbl Wl0 (d' + asz) m' _ (-1) 1%nat (EVar 35) c HCT' ltac:(left; reflexivity) eq_refl) as K.
            replace (d' + asz + -1) with (d' + (asz - 1)) in K by (clear; lia). exact K.
          * intros i Hi. rewrite CSL, EC in Hi. destruct (Z.eq_dec i (2 * asz - 1)) as [->|Hne].
            -- pose proof (fld_of_ftbl Wl0 (d' + 2 * asz) m' _ (-1) 1%nat (ELit 0) 0 HTT' ltac:(left; reflexivity) eq_refl) as K.
               replace (d' + 2 * asz + -1) with (d' + (2 * asz - 1)) in K by (clear; lia). exact K.
            -- pose proof (fld_of_ftbl Wl0 (d' + asz) m' _ (i - asz) 1%nat (ELit 0) 0 HZ
                             ltac:(apply In_zents1; rewrite Z2Nat.id by (clear - AR; lia); clear - Hi Hne; lia) eq_refl) as K.
               replace (d' + asz + (i - asz)) with (d' + i) in K by (clear; lia). exact K.
          * apply (FT _ 72 8%nat (EAlu ALU_ADD (EMd M_MUL (ELit 2) (EVar 54)) (ELit 1))); [clear; lia | In_tbl |].
            cbn [edenot]. rewrite <- w_add_g, <- w_mul_g. reflexivity.
          * apply (FT _ 80 8%nat (EAlu ALU_ADD (EMd M_MUL (ELit 2) (EVar 54)) (ELit (-1)))); [clear; lia | In_tbl |].
            cbn [edenot]. replace (2 * asz - 1) with (2 * asz + -1) by (clear; lia). rewrite <- w_add_g, <- w_mul_g. reflexivity.
          * apply (FT _ 88 8%nat (EVar 53)); [clear; lia | In_tbl | reflexivity].
          * apply mdef_of_wr_at_hi; [eapply wr_at_sub; [exact WDS' | clear; lia | unfold DS_SIZE; clear; lia | clear; lia] | clear - N1; unfold AIMG_TOP in *; lia].
        + rewrite StrLib.Zlen_app. change ([c] ++ repeat 0 (Z.to_nat (2 * asz - 2 - Zlen cs))) with (c :: repeat 0 (Z.to_nat (2 * asz - 2 - Zlen cs))).
          unfold Zlen at 2. cbn [length]. rewrite repeat_length. rewrite CSL, EC. cbn [str_cap]. clear - AR. lia.
      - cbn [str_data]. apply (FT _ 48 8%nat (EVar 53)); [clear; lia | In_tbl | reflexivity].
      - apply (FT _ 56 8%nat (EAlu ALU_ADD (EVar 53) (EVar 54))); [clear; lia | In_tbl | cbn [edenot]; rewrite <- w_add_g; reflexivity].
      - cbn [str_data str_cap].
        apply (FT _ 64 8%nat (EAlu ALU_ADD (EAlu ALU_ADD (EVar 53) (EMd M_MUL (ELit 2) (EVar 54))) (ELit (-1)))); [clear; lia | In_tbl |].
        cbn [edenot]. replace (d' + (2 * asz - 1)) with (d' + 2 * asz + -1) by (clear; lia). rewrite <- !w_add_g, <- w_mul_g. reflexivity.
      - cbn [str_data str_cap]. clear - AR; lia.
      - apply (FT _ 96 8%nat (EAlu ALU_ADD (EVar 53) (EVar 54))); [clear; lia | In_tbl | cbn [edenot]; rewrite <- w_add_g; reflexivity].
      - cbn [str_data str_cap]. clear - AR; lia.
      - apply (FT _ 104 4%nat (ELit 16)); [clear; lia | In_tbl | reflexivity]. }
    eapply (ov_post msF2 mo2 sk2 m2 R2 LB2 pid2 d' msF' mo' m' (asz - 1) _ _ _ _ _ _ _ _ _ _ _ _ _ _ PA E' KR' MP' MI' AC');
      [rewrite EG; replace (d' + (asz - 1)) with (d' + asz - 1) by (clear; lia); exact MU | exact WM | rewrite EG; clear - AR; lia
      | rewrite EG, EC; exact SB'].
  Qed.

  Lemma ov_main : forall t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 msF,
    as_VIS H s msF = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (ds + 8)) (Z_to_bv 64 c) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9
                             s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 AOVF) fc None m (seg_rom asegs) ->
    as_AKREL H s (mkCfg msF mo) ->
    as_SR H POSTov (mkCfg msF mo).
  Proof.
    intros t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 msF VIS KR.
    eapply (ahh_evt_then H HH _ _ s msF _ mo KR VIS (ov_o1 t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6)).
    intros msF1 mo1 KR1 MP1 HP. destruct HP as (R1 & m1 & E1 & RF1 & HRT1 & HST1 & HDT1 & PO1 & MI1).
    apply (ov_call msF1 mo1 R1 m1 E1 RF1 HRT1 HST1 HDT1 PO1 MI1 KR1 MP1).
    intros msF2 mo2 sk2 m2 R2 LB2 pid2 d' PA.
    assert (CASE : ms = SShort \/ exists d asz, ms = SLong d asz) by (destruct ms as [|d asz]; [left; reflexivity | right; eauto]).
    destruct CASE as [E|(d & asz & E)].
    - exact (ov_fin_s E msF2 mo2 sk2 m2 R2 LB2 pid2 d' PA).
    - exact (ov_fin_l d asz E msF2 mo2 sk2 m2 R2 LB2 pid2 d' PA).
  Qed.
End OVS.

Theorem ovf_okA {HCEIL : HeapCeil} : forall H, asan_rt_hyps_bp H -> ovf_stmtA H.
Proof.
  intros H HHbp ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
         F fc msF m mo s LB LBk DB LF lo B shi errv ds err len c ms hm fl fill
         PRE Ha0 Ha1 CR REP PERM OWN DSIN LEN BS BC BL COST TRO.
  destruct PRE as (VIS & RH & KR & RAUX & SPB & BB & SP16 & STK & CEIL & LO & ERRN & MI & TP & RA2 & LV & AC & RFS & S0 & SPS).
  destruct REP as (DI & BLK & DSA & DSW & DSO & SBA).
  destruct (si_str _ _ _ _ _ _ (di_sb _ _ _ _ _ _ _ _ _ _ _ DI)) as (cs & CSR & CSL).
  replace (ds + 8 + 64) with (ds + 72) in CSR by lia.
  assert (BLKx : exists pid, DB = spb_own ms pid /\ (forall d asz, ms = SLong d asz -> In (pid, d, asz) LB)).
  { destruct ms as [|d asz]; cbn [ds_blk] in BLK.
    - exists 0. split; [exact BLK | intros d asz E; discriminate E].
    - destruct BLK as (p & -> & Hin). exists p. split; [reflexivity|]. intros d0 asz0 E. injection E as <- <-. exact Hin. }
  destruct BLKx as (pid & DBE & BLKL).
  subst a0 a1.
  exact (ov_main H HHbp ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m mo s LB LBk DB LF lo B shi errv ds err len c ms
           hm fl fill cs pid RH RAUX SPB SP16 STK CEIL LO ERRN MI TP LV AC RFS S0 SPS CR DI DBE BLKL DSA DSW DSO SBA PERM OWN DSIN
           LEN BS BC BL COST TRO CSR CSL t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 msF VIS KR).
Qed.
