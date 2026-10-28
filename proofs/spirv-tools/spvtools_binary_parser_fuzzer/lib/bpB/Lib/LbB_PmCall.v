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
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BTac BArr BSysStep BExec BellsX BacX BMem BMState BLFrame.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BPrelim.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsIface BsCXXHeap BXXRep BsStack0 RtB_Iface.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LibIface FPSteps.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require Import CRep.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs Require Import PrsInv PmBase.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_Kit LbB_Bridge LbB_Conv LbB_SR LbB_FKit LbB_MILB LbB_PrsStmt LbB_Own LbB_PmBase LbB_FSlots LbB_PmOwn LbB_PmCut LbB_PmTac.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

Definition acc_ok (ins : list nat) (k n : Z) : bool :=
  forallb (fun i => let v := nth (Z.to_nat ((k + i) / 8)) (fsh_pat PM_OBJS PM_NSH ins) 0 in
                    ((v <? 8) && ((v =? 0) || ((k + i) mod 8 + 1 <=? v)))%bool)
          (map Z.of_nat (seq 0 (Z.to_nat n))).

Lemma div8_add : forall a y, a mod 8 = 0 -> (a + y) / 8 = a / 8 + y / 8.
Proof.
  intros a y H. pose proof (Z.div_mod a 8 ltac:(lia)) as D. rewrite H, Z.add_0_r in D.
  rewrite D at 1. rewrite Z.mul_comm. apply Z.div_add_l. lia.
Qed.
Lemma mod8_add : forall a y, a mod 8 = 0 -> (a + y) mod 8 = y mod 8.
Proof.
  intros a y H. pose proof (Z.div_mod a 8 ltac:(lia)) as D. rewrite H, Z.add_0_r in D.
  rewrite D at 1. rewrite Z.add_comm, Z.mul_comm. apply Z.mod_add. lia.
Qed.

Lemma in_seqZ : forall n i, 0 <= i < n -> In i (map Z.of_nat (seq 0 (Z.to_nat n))).
Proof.
  intros n i Hi. apply in_map_iff. exists (Z.to_nat i). split; [apply Z2Nat.id; lia|].
  apply in_seq. lia.
Qed.

Lemma ff_accessible : forall m ff ins k n,
  SHAD m ff (pm_fsh ins) -> 0 <= k -> 0 <= n -> k + n <= 11584 -> 0 <= ff -> ff + 11584 <= AAPP_HI ->
  acc_ok ins k n = true -> accessible m (ff + k) n.
Proof.
  intros m ff ins k n (S0 & S8 & [(B0 & B1 & B2) _]) Hk Hn Hkn Hf0 Hf1 Hok.
  split; [lia|]. split; [lia|]. intros x Hx.
  set (i := x - (ff + k)).
  pose proof (proj1 (forallb_forall _ _) Hok i (in_seqZ n i ltac:(subst i; lia))) as K. cbn beta in K.
  set (g := (k + i) / 8) in K.
  set (v := nth (Z.to_nat g) (fsh_pat PM_OBJS PM_NSH ins) 0) in K.
  apply andb_true_iff in K as [K1 K2]. apply Z.ltb_lt in K1.
  assert (Hg : 0 <= g < 1448) by (subst g; split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
  assert (Hv : 0 <= v < 256) by (subst v; apply fsh_pat_byte_range).
  exists v. split; [lia|]. split.
  - assert (Hl : (Z.to_nat g < length (pm_fsh ins))%nat) by (unfold pm_fsh; rewrite length_map, pm_fsh_len; lia).
    pose proof (B2 (Z.to_nat g) Hl) as Hm. unfold pm_fsh in Hm. rewrite nth_error_map in Hm.
    rewrite (nth_error_nth' _ 0) in Hm by (rewrite pm_fsh_len; lia). cbn [option_map] in Hm. fold v in Hm.
    replace (sh x) with (sh ff + Z.of_nat (Z.to_nat g)); [exact Hm|].
    rewrite Z2Nat.id by lia. subst g. unfold sh.
    replace x with (ff + (k + i)) by (subst i; lia). rewrite (div8_add ff (k + i) S8). lia.
  - unfold byte_ok. apply orb_true_iff in K2 as [K2|K2]; [left; apply Z.eqb_eq in K2; exact K2 | right; apply Z.leb_le in K2].
    replace x with (ff + (k + i)) by (subst i; lia). rewrite (mod8_add ff (k + i) S8). exact K2.
Qed.

Lemma ff_shvis : forall m ff ins k n,
  SHAD m ff (pm_fsh ins) -> ff mod 64 = 0 -> 0 <= k -> 0 <= n -> k + n <= 11584 -> 0 <= ff -> ff + 11584 <= AAPP_HI ->
  shvis m (ff + k) (ff + k + n).
Proof.
  intros m ff ins k n (S0 & S8 & [(B0 & B1 & B2) (W0 & W1 & W2)]) H64 Hk Hn Hkn Hf0 Hf1.
  unfold pm_fsh in *. rewrite length_map, pm_fsh_len in *. change (Z.of_nat 1448) with 1448 in *.
  pose proof (hull_lo_le (ff + k) ltac:(lia)) as (HL1 & HL2 & HL3).
  pose proof (hull_hi_ge (ff + k + n)) as HH.
  assert (HLo : ff <= hull_lo (ff + k)).
  { unfold hull_lo. assert ((ff + k) mod 64 = k mod 64).
    { replace (ff + k) with (k + (ff / 64) * 64) by (Z.div_mod_to_equations; lia). apply Z.mod_add. lia. }
    pose proof (Z.mod_pos_bound k 64 ltac:(lia)). pose proof (Z.mod_le k 64 ltac:(lia) ltac:(lia)). lia. }
  assert (HHi : hull_hi (ff + k + n) <= ff + 11584).
  { unfold hull_hi. assert ((ff + k + n) mod 64 = (k + n) mod 64).
    { replace (ff + k + n) with ((k + n) + (ff / 64) * 64) by (Z.div_mod_to_equations; lia). apply Z.mod_add. lia. }
    rewrite H. pose proof (Z.mod_pos_bound (k + n) 64 ltac:(lia)).
    assert ((k + n) + (64 - (k + n) mod 64) mod 64 <= 11584).
    { destruct (Z.eq_dec ((k + n) mod 64) 0) as [E|E].
      - rewrite E. change ((64 - 0) mod 64) with 0. lia.
      - rewrite (Z.mod_small (64 - (k + n) mod 64)) by lia.
        assert (11584 = 181 * 64) by reflexivity. Z.div_mod_to_equations. nia. }
    lia. }
  unfold shvis, stk. split.
  { unfold sh, ASHADOW_BASE. pose proof (Z.div_pos (hull_lo (ff + k)) 8 ltac:(lia) ltac:(lia)). lia. }
  split.
  { assert (hull_hi (ff + k + n) <= AAPP_HI) by lia. unfold sh, ASHADOW_BASE, AAPP_HI in *.
    assert (hull_hi (ff + k + n) / 8 <= 2 ^ 47 / 8) by (apply Z.div_le_mono; lia). change (2 ^ 47 / 8) with (2 ^ 44) in *. lia. }
  intros a Ha.
  assert (Hs1 : sh ff <= sh (hull_lo (ff + k))) by (apply sh_mono; lia).
  assert (Hs2 : sh (hull_hi (ff + k + n)) <= sh ff + 1448).
  { assert (sh (hull_hi (ff + k + n)) <= sh (ff + 11584)) by (apply sh_mono; lia).
    assert (sh (ff + 11584) = sh ff + 1448) by (unfold sh; Z.div_mod_to_equations; lia). lia. }
  set (j := Z.to_nat (a - sh ff)).
  assert (Hj : (j < 1448)%nat) by (subst j; lia).
  split.
  - replace a with (sh ff + (a - sh ff)) by lia. apply W2. lia.
  - pose proof (B2 j Hj) as Hm. rewrite nth_error_map in Hm.
    rewrite (nth_error_nth' _ 0) in Hm by (rewrite pm_fsh_len; exact Hj). cbn [option_map] in Hm.
    subst j. rewrite Z2Nat.id in Hm by lia. replace (sh ff + (a - sh ff)) with a in Hm by lia.
    eexists. exact Hm.
Qed.

Lemma disjoint_from_sub : forall W a n a' n', disjoint_from W a n -> a <= a' -> a' + n' <= a + n -> 0 <= n' ->
  disjoint_from W a' n'.
Proof.
  induction W as [|[lo hi] W IH]; intros a n a' n' D H1 H2 H3; cbn in *; [exact I|].
  destruct D as [D1 D2]. split; [lia | exact (IH a n a' n' D2 H1 H2 H3)].
Qed.

Lemma fld_munch : forall W m m' a k v, fld ASEGS m a k v -> munch W m m' -> disjoint_from W a (Z.of_nat k) ->
  0 <= a -> a + Z.of_nat k < 2 ^ 64 -> fld ASEGS m' a k v.
Proof.
  intros W m m' a k v F MU D H0 H1. eapply fld_agree; [exact H0 | exact H1 | exact F |].
  intros x Hx. unfold zwin in Hx. apply MU. rewrite unsigned_lit by lia. eapply disjoint_outside; [exact D | lia].
Qed.

Section Munch.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HH : asan_rt_hyps H.
  Variable LINV : mem -> Prop.
  Hypothesis LINV_frame : forall m m' W, LINV m -> munch W m m' -> wmono asegs m m' ->
    Forall (fun iv : Z * Z => AIMG_TOP <= fst iv) W -> LINV m'.

  Lemma pmxa_munch : forall w s LB LBs m mo c ins tbl ftbl TB spal m' W tbl' ftbl',
    pmw_okA H w -> PMXAT H LINV w s LB LBs m mo c ins tbl ftbl TB spal ->
    munch W m m' -> wmono asegs m m' -> (forall x, m x <> None -> m' x <> None) ->
    mem_inv asegs m' -> stk asegs m' (wa_lo w) (wa_sp0 w) ->
    Forall (own_ivl H w) W -> Forall (fun iv : Z * Z => fst iv <= snd iv) W ->
    disjoint_from W (sh (wa_ff w)) PM_NSH -> disjoint_from W (wa_p w + O_WIDX) 22 ->
    incl tbl' tbl -> Forall (fun ke => disjoint_from W (wa_s1 w + fst ke) 8) tbl' ->
    incl ftbl' ftbl -> Forall (fun ke => disjoint_from W (wa_ff w + fst ke) 8) ftbl' ->
    PMXAT H LINV w s LB LBs m' mo c ins tbl' ftbl' TB spal.
  Proof.
    intros w s LB LBs m mo c ins tbl ftbl TB spal m' W tbl' ftbl' OK X MU WM DM MI STK FW FLE DSH DSC It Dt If Df.
    pose proof (pmw_bounds H w OK) as BND.
    assert (FA : forall k (wd : nat) v, 72 <= k -> k + Z.of_nat wd <= 94 -> fld ASEGS m (wa_p w + k) wd v ->
                   fld ASEGS m' (wa_p w + k) wd v).
    { intros k wd v Hk1 Hk2 F. eapply fld_munch; [exact F | exact MU | | lia | lia].
      eapply disjoint_from_sub; [exact DSC | unfold O_WIDX; lia | unfold O_WIDX; lia | lia]. }
    eapply (pmxa_own0 H HH LINV LINV_frame w s LB LBs m mo c ins tbl ftbl TB spal m' W ins tbl' ftbl' OK X MU WM DM MI STK FW FLE).
    - pose proof (xa_fsh _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) as SH. eapply SHAD_transport; [exact SH | exact MU | exact WM |].
      unfold pm_fsh. rewrite length_map, pm_fsh_len. exact DSH.
    - pose proof (xa_slots _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) as SL. unfold slots_ok in *.
      apply Forall_forall. intros ke Hke. pose proof (proj1 (Forall_forall _ _) SL ke (It ke Hke)) as C.
      eapply rw_cells_transport; [exact C | exact MU | exact WM |]. cbn [cells_size csize]. exact (proj1 (Forall_forall _ _) Dt ke Hke).
    - pose proof (xa_fslots _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) as SL. unfold fslots_ok in *.
      apply Forall_forall. intros ke Hke. pose proof (proj1 (Forall_forall _ _) SL ke (If ke Hke)) as C.
      eapply rw_cells_transport; [exact C | exact MU | exact WM |]. cbn [cells_size csize]. exact (proj1 (Forall_forall _ _) Df ke Hke).
    - apply FA; [unfold O_WIDX; lia | unfold O_WIDX; cbn; lia | exact (xa_widx _ _ _ _ _ _ _ _ _ _ _ _ _ _ X)].
    - apply FA; [unfold O_ICOUNT; lia | unfold O_ICOUNT; cbn; lia | exact (xa_icount _ _ _ _ _ _ _ _ _ _ _ _ _ _ X)].
    - apply FA; [unfold O_ENDIAN; lia | unfold O_ENDIAN; cbn; lia | exact (xa_endian _ _ _ _ _ _ _ _ _ _ _ _ _ _ X)].
    - apply FA; [unfold O_FLAGS; lia | unfold O_FLAGS; cbn; lia | exact (xa_flags _ _ _ _ _ _ _ _ _ _ _ _ _ _ X)].
    - rewrite <- Z.add_assoc. apply FA; [unfold O_FLAGS; lia | unfold O_FLAGS; cbn; lia |].
      rewrite Z.add_assoc. exact (xa_retry _ _ _ _ _ _ _ _ _ _ _ _ _ _ X).
  Qed.
End Munch.

Lemma find_segment_inP : forall segs x n seg, find_segment segs x n = Some seg ->
  In seg segs /\ Z.of_N (seg_base seg) <= x /\ x + n <= Z.of_N (seg_base seg) + Z.of_N (seg_size seg).
Proof.
  induction segs as [|sg segs IH]; intros x n seg Hf; cbn [find_segment] in Hf; [discriminate|].
  destruct (Z.leb (Z.of_N (seg_base sg)) x && Z.leb (x + n) (Z.of_N (seg_base sg) + Z.of_N (seg_size sg)))%bool eqn:E.
  - injection Hf as <-. apply andb_true_iff in E as [E1 E2]. apply Z.leb_le in E1, E2. split; [left; reflexivity | lia].
  - destruct (IH x n seg Hf) as (Hin & H1 & H2). split; [right; exact Hin | lia].
Qed.

Lemma seg_rom_hiP : forall x, AIMG_TOP <= x < 2 ^ 64 -> BLPropExec.seg_rom asegs (Z_to_bv 64 x) = None.
Proof.
  intros x Hx. unfold BLPropExec.seg_rom, memory_read.
  destruct (find_segment asegs (bv_unsigned (Z_to_bv 64 x)) (Z.of_N 1)) as [seg|] eqn:E; [|reflexivity].
  apply find_segment_inP in E as (Hin & H1 & H2). pose proof (asegs_below_top _ Hin). rewrite u64_of_Z in H1, H2 by lia.
  change (Z.of_N 1) with 1 in H2. lia.
Qed.

Lemma def_of_mrd_hi : forall m x b, AIMG_TOP <= x < 2 ^ 64 -> mrd asegs m (Z_to_bv 64 x) = Some b -> m (Z_to_bv 64 x) <> None.
Proof.
  intros m x b Hx Hm. unfold mrd in Hm. destruct (m (Z_to_bv 64 x)); [discriminate|].
  rewrite seg_rom_hiP in Hm by lia. discriminate.
Qed.

Lemma outside_dec : forall (W : list (Z * Z)) x, outside W x \/ exists lo hi, In (lo, hi) W /\ lo <= x < hi.
Proof.
  induction W as [|[lo hi] W IH]; intros x; cbn [outside]; [left; exact I|].
  destruct (Z_lt_le_dec x lo) as [L|L]; [| destruct (Z_lt_le_dec x hi) as [U|U]].
  - destruct (IH x) as [O|(lo' & hi' & Hin & Hr)]; [left; split; [lia | exact O] | right; exists lo', hi'; split; [right; exact Hin | exact Hr]].
  - right. exists lo, hi. split; [left; reflexivity | lia].
  - destruct (IH x) as [O|(lo' & hi' & Hin & Hr)]; [left; split; [lia | exact O] | right; exists lo', hi'; split; [right; exact Hin | exact Hr]].
Qed.

Lemma stk_join : forall m lo mid hi, stk asegs m lo mid -> stk asegs m mid hi -> lo <= mid <= hi -> stk asegs m lo hi.
Proof.
  intros m lo mid hi (A0 & A1 & A) (B0 & B1 & B) Hm. split; [lia|]. split; [lia|].
  intros a Ha. destruct (Z_lt_le_dec a mid); [apply A | apply B]; lia.
Qed.

Definition keys_nonneg (ks : list Z) : bool := forallb (fun k => 0 <=? k) ks.
Definition fkeys_apart (k n : Z) (ks : list Z) : bool := forallb (fun j => (j + 8 <=? k) || (k + n <=? j))%bool ks.

Definition KEPT_REGS : list reg := [1; 2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv.

Section Memset.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HH : asan_rt_hyps H.
  Variable LINV : mem -> Prop.
  Hypothesis LINV_frame : forall m m' W, LINV m -> munch W m m' -> wmono asegs m m' ->
    Forall (fun iv : Z * Z => AIMG_TOP <= fst iv) W -> LINV m'.

  Lemma p_apart_ff : forall w, pmw_okA H w -> wa_ff w + 16384 <= wa_p w + O_WIDX \/ wa_p w + PARSER_SIZE <= wa_ff w.
  Proof.
    intros w OK. destruct (wk_pin H w OK) as (f & Hf0 & P1 & P2). destruct (wk_fresh H w OK) as (_ & _ & FR).
    destruct (FR f Hf0) as [D _]. change (fsz PM_FCLASS) with 16384 in D.
    unfold O_WIDX, PARSER_SIZE in *. destruct D as [D|D]; [left | right]; lia.
  Qed.

  Lemma pm_memset : forall (w : pmwA H) s LB LBs m mo c ins tbl ftbl TB spal msF R F fc (k n cv ret : Z) (Q : config -> Prop) tbl' ftbl',
    pmw_okA H w -> PMXAT H LINV w s LB LBs m mo c ins tbl ftbl TB spal ->
    as_AKREL H s (mkCfg msF mo) -> as_VIS H s msF = MS R F (Z_to_bv 64 AASAN_MEMSET) fc None m (seg_rom asegs) -> rfull R ->
    PropExec.getr R 10%bv = Z_to_bv 64 (wa_ff w + k) -> PropExec.getr R 11%bv = Z_to_bv 64 cv -> PropExec.getr R 12%bv = Z_to_bv 64 n ->
    PropExec.getr R 2%bv = Z_to_bv 64 (wa_s1 w) -> PropExec.getr R 1%bv = Z_to_bv 64 ret -> ret mod 2 = 0 -> 0 <= ret < 2 ^ 64 ->
    0 <= cv < 256 -> 24 <= k -> 0 <= n -> k + n <= 11584 -> acc_ok ins k n = true ->
    incl tbl' tbl -> keys_nonneg (map fst tbl') = true -> incl ftbl' ftbl -> fkeys_apart k n (map fst ftbl') = true ->
    fkeys_ok (map fst ftbl') = true ->
    (forall msF1 mo1 m1 R1, as_AKREL H s (mkCfg msF1 mo1) ->
       as_VIS H s msF1 = MS R1 F (Z_to_bv 64 ret) fc None m1 (seg_rom asegs) -> rfull R1 ->
       PMXAT H LINV w s LB LBs m1 mo1 c ins tbl' ftbl' TB spal ->
       (forall r, In r (10%bv :: KEPT_REGS) -> PropExec.getr R1 r = PropExec.getr R r) ->
       rw_cells asegs m1 (wa_ff w + k) [CB (Z.to_nat n) (poison_bytes (Z.to_nat n) cv)] ->
       (forall k' cs, 0 <= k' -> k' + Z.of_nat (cells_size cs) <= 16384 -> (k' + Z.of_nat (cells_size cs) <= k \/ k + n <= k') ->
          rw_cells asegs m (wa_ff w + k') cs -> rw_cells asegs m1 (wa_ff w + k') cs) ->
       as_SR H Q (mkCfg msF1 mo1)) ->
    as_SR H Q (mkCfg msF mo).
  Proof.
    intros w s LB LBs m mo c ins tbl ftbl TB spal msF R F fc k n cv ret Q tbl' ftbl' OK X KR VIS RF
           G10 G11 G12 G2 G1 Hret2 Hret Hcv Hk Hn Hkn Hacc It Ht If Hf Hfk K.
    pose proof (pm_geom H w OK) as G. cbn zeta in G.
    destruct G as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12 & Q13).
    pose proof aceil_facts as ((AC1 & AC2) & AC3 & AC4).
    pose proof (pmw_frame_facts H w OK) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10).
    pose proof (wk_stack H w OK) as (S1 & S2 & S3 & S4 & S5 & S6).
    pose proof (p_range H w OK) as (PR1 & PR2).
    pose proof (p_apart_ff w OK) as PAF.
    change (fsz PM_FCLASS) with 16384 in *.
    pose proof (xa_fwr _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) as FW. change (fsz PM_FCLASS) with 16384 in FW.
    assert (FWk : wr_at asegs m (wa_ff w + k) n).
    { destruct FW as (W0 & W1 & W2). split; [lia|]. split; [lia|]. intros i Hi.
      replace (wa_ff w + k + i) with (wa_ff w + (k + i)) by lia. apply W2. lia. }
    destruct (rw_cells_of_wr_hi m (wa_ff w + k) n FWk ltac:(unfold AFS_HDR in *; lia) Hn) as (junk & JK).
    pose proof (xa_fsh _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) as FSH.
    assert (ACC : accessible m (wa_ff w + k) n)
      by (apply (ff_accessible m (wa_ff w) ins k n FSH); [lia | lia | lia | lia | unfold AAPP_HI in *; lia | exact Hacc]).
    assert (SHV : shvis m (wa_ff w + k) (wa_ff w + k + n)) by (apply (ff_shvis m (wa_ff w) ins k n FSH); unfold AAPP_HI in *; lia).
    pose proof (xa_stk _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) as STK.
    destruct (stk_split asegs m (wa_lo w) (wa_s1 w) (wa_sp0 w) STK ltac:(lia)) as [STK1 STK2].
    rewrite (rfull_eq R RF) in VIS.
    eapply (ahh_evt_then H HH _); [exact KR | exact VIS | |].
    { eapply (ah_memset H HH) with (c := cv) (junk := junk) (lo := wa_lo w).
      - exact G11.
      - exact Hcv.
      - rewrite G10, G12, !u64_of_Z by lia. exact JK.
      - rewrite G10, G12, !u64_of_Z by lia. exact ACC.
      - rewrite G10, G12, !u64_of_Z by lia. exact SHV.
      - rewrite G2, u64_of_Z by lia. exact STK1.
      - exact S1.
      - rewrite G2, u64_of_Z by lia. unfold AINTRIN_STACK, APM_STACK in *. lia.
      - exact (xa_meminv _ _ _ _ _ _ _ _ _ _ _ _ _ _ X).
      - exact (xa_aconst _ _ _ _ _ _ _ _ _ _ _ _ _ _ X).
      - rewrite G12, u64_of_Z by lia. lia.
      - rewrite G10, G12, !u64_of_Z by lia. eapply (aapp_in_app_mem (as_FSB H) AFS_SIZE); [exact F8 | unfold AFS_HDR in *; lia | lia].
      - rewrite G10, G12, !u64_of_Z by lia. apply (own_aconst_ok H w _ OK). right; left. cbn [fst snd]. change (fsz PM_FCLASS) with 16384. lia.
      - rewrite G10, G12, G2, !u64_of_Z by lia. left. lia. }
    intros msF1 mo1 KR1 MP1 POST.
    destruct POST as (t0 & t1 & t2 & a1' & a2' & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m' & VIS1 & MU & WM & MI & STK' & RWC & AC').
    rewrite G10, G12, G2 in MU. rewrite G2 in STK'. rewrite G10, G12 in RWC.
    rewrite !u64_of_Z in MU by lia. rewrite !u64_of_Z in STK' by lia. rewrite !u64_of_Z in RWC by lia. rewrite G1 in VIS1.
    rewrite (ret_pc_even ret Hret Hret2) in VIS1.
    set (W := [(wa_ff w + k, wa_ff w + k + n); (wa_s1 w - AINTRIN_STACK, wa_s1 w)]) in MU.
    assert (DW : forall x, AIMG_TOP <= x < 2 ^ 64 ->
                   (wa_ff w + k <= x < wa_ff w + k + n \/ wa_s1 w - AINTRIN_STACK <= x < wa_s1 w) -> m' (Z_to_bv 64 x) <> None).
    { intros x Hx Hin.
      destruct Hin as [Hin|Hin].
      - destruct RWC as [[_ (B0 & B1 & B2)] _]. cbn [cells_bytes cbytes] in B2. rewrite app_nil_r in B2.
        set (i := Z.to_nat (x - (wa_ff w + k))).
        assert (Hi : (i < length (poison_bytes (Z.to_nat n) cv))%nat) by (subst i; unfold poison_bytes; rewrite repeat_length; lia).
        pose proof (B2 i Hi) as Bi. subst i. rewrite Z2Nat.id in Bi by lia. replace (wa_ff w + k + (x - (wa_ff w + k))) with x in Bi by lia.
        unfold poison_bytes in Bi. rewrite nth_error_repeat in Bi by (unfold poison_bytes in Hi; rewrite repeat_length in Hi; lia).
        unfold wa in Bi. exact (def_of_mrd_hi m' x _ Hx Bi).
      - destruct STK' as (_ & _ & SS). destruct (SS x ltac:(unfold AINTRIN_STACK in *; lia)) as [_ (b & Hb)].
        unfold wa in Hb. exact (def_of_mrd_hi m' x _ Hx Hb). }
    assert (DM : forall x, m x <> None -> m' x <> None).
    { intros x Hx. destruct (outside_dec W (bv_unsigned x)) as [Ho|(lo' & hi' & Hin & Hr)].
      - rewrite (MU x Ho). exact Hx.
      - pose proof (bv_unsigned_in_range 64 x) as Rx. change (bv_modulus 64) with (2 ^ 64) in Rx.
        rewrite <- (Z_to_bv_bv_unsigned x). subst W.
        destruct Hin as [Hin|[Hin|[]]]; injection Hin as <- <-; apply DW; unfold AINTRIN_STACK, AFS_HDR in *; lia. }
    assert (STK'' : stk asegs m' (wa_lo w) (wa_sp0 w)).
    { apply (stk_join m' (wa_lo w) (wa_s1 w) (wa_sp0 w)); [exact STK' | | lia].
      eapply (stk_transport_disjoint asegs W m m' (wa_s1 w) (wa_sp0 w) STK2 MU WM).
      subst W. cbn [disjoint_from]. unfold AINTRIN_STACK. split; [lia|]. split; [lia | exact I]. }
    assert (X1 : PMXAT H LINV w s LB LBs m' mo c ins tbl' ftbl' TB spal).
    { eapply (pmxa_munch H HH LINV LINV_frame w s LB LBs m mo c ins tbl ftbl TB spal m' W tbl' ftbl' OK X MU WM DM MI STK'').
      - subst W. apply Forall_cons; [right; left; cbn [fst snd]; change (fsz PM_FCLASS) with 16384; lia|].
        apply Forall_cons; [left; cbn [fst snd]; unfold AINTRIN_STACK, APM_STACK in *; lia | apply Forall_nil].
      - subst W. apply Forall_cons; [cbn; lia|]. apply Forall_cons; [cbn; unfold AINTRIN_STACK; lia | apply Forall_nil].
      - subst W. cbn [disjoint_from]. unfold PM_NSH, AINTRIN_STACK in *. rewrite Q13 in *.
        split; [destruct Q6 as [Q6|Q6]; [right | left]; lia|]. split; [left; lia | exact I].
      - subst W. cbn [disjoint_from]. unfold O_WIDX, O_FLAGS, AINTRIN_STACK, PARSER_SIZE in *.
        split; [destruct PAF as [D|D]; [right | left]; lia|]. split; [left; lia | exact I].
      - exact It.
      - apply Forall_forall. intros [kk e] Hin. cbn [fst].
        pose proof (proj1 (forallb_forall _ _) Ht kk (in_map fst _ (kk, e) Hin)) as Kk. apply Z.leb_le in Kk.
        subst W. cbn [disjoint_from]. unfold AINTRIN_STACK. split; [right; lia|]. split; [right; lia | exact I].
      - exact If.
      - apply Forall_forall. intros [kk e] Hin. cbn [fst].
        pose proof (proj1 (forallb_forall _ _) Hf kk (in_map fst _ (kk, e) Hin)) as Kk. apply orb_true_iff in Kk.
        pose proof (proj1 (forallb_forall _ _) Hfk kk (in_map fst _ (kk, e) Hin)) as Kb.
        apply andb_true_iff in Kb as [Kb1 Kb2]. apply Z.leb_le in Kb1. apply Z.leb_le in Kb2.
        subst W. cbn [disjoint_from]. unfold AINTRIN_STACK.
        split; [destruct Kk as [Kk|Kk]; apply Z.leb_le in Kk; [left | right]; lia|]. split; [left; lia | exact I]. }
    eapply K; [exact KR1 | exact VIS1 | apply rfull_mkR | eapply (pmxa_mpres H HH LINV); [exact X1 | exact MP1] | | exact RWC |].
    - intros r Hr.
      repeat (destruct Hr as [<-|Hr]; [first [reflexivity | (cbn; rewrite G1; reflexivity) | (cbn; reflexivity)] |]); destruct Hr.
    -
      intros k' cs Hk' Hn' Hap C. eapply rw_cells_transport; [exact C | exact MU | exact WM |].
      subst W. cbn [disjoint_from]. unfold AINTRIN_STACK. split; [lia|]. split; [lia | exact I].
  Qed.
End Memset.

Definition shz_of (n : Z) : list Z := repeat 0 (Z.to_nat (n / 8)) ++ (if Z.eqb (n mod 8) 0 then [] else [n mod 8]).

Lemma map_shz_of : forall n, map (Z_to_bv 8) (shz_of n) = shadow_of n.
Proof.
  intros n. unfold shz_of, shadow_of. rewrite map_app, map_repeat. f_equal. destruct (Z.eqb (n mod 8) 0); reflexivity.
Qed.

Definition obj_sh_ok (ins : list nat) (k n : Z) : bool :=
  ((k mod 8 =? 0) && (0 <=? k) && (0 <=? n) && (k + n <=? 11584))%bool
  && (if list_eq_dec Z.eq_dec (firstn (Z.to_nat (nsh n)) (skipn (Z.to_nat (k / 8)) (fsh_pat PM_OBJS PM_NSH ins))) (shz_of n)
      then true else false).

Lemma bytes_at_sub : forall segs m A bs i n, bytes_at segs m A bs -> (i + n <= length bs)%nat ->
  bytes_at segs m (A + Z.of_nat i) (firstn n (skipn i bs)).
Proof.
  intros segs m A bs i n (B0 & B1 & B2) Hin. unfold bytes_at. rewrite length_firstn, length_skipn.
  split; [lia|]. split; [lia|]. intros j Hj.
  replace (A + Z.of_nat i + Z.of_nat j) with (A + Z.of_nat (i + j)) by lia.
  rewrite B2 by lia. rewrite nth_error_firstn. destruct (Nat.ltb_spec j n); [| lia].
  rewrite nth_error_skipn. reflexivity.
Qed.

Lemma wr_at_sub : forall segs m A n a k, wr_at segs m A n -> A <= a -> a + k <= A + n -> 0 <= k -> wr_at segs m a k.
Proof.
  intros segs m A n a k (W0 & W1 & W2) H1 H2 H3. split; [lia|]. split; [lia|]. intros i Hi.
  replace (a + i) with (A + (a - A + i)) by lia. apply W2. lia.
Qed.

Lemma ff_addressable : forall m ff ins k n, SHAD m ff (pm_fsh ins) -> obj_sh_ok ins k n = true -> addressable m (ff + k) n.
Proof.
  intros m ff ins k n (S0 & S8 & [UB UW]) Hok. unfold obj_sh_ok in Hok.
  apply andb_true_iff in Hok as [Hb Hl]. apply andb_true_iff in Hb as [Hb H4]. apply andb_true_iff in Hb as [Hb H3].
  apply andb_true_iff in Hb as [H1 H2]. apply Z.eqb_eq in H1. apply Z.leb_le in H2. apply Z.leb_le in H3. apply Z.leb_le in H4.
  destruct (list_eq_dec Z.eq_dec _ _) as [EQ|]; [|discriminate].
  unfold pm_fsh in UB, UW. rewrite length_map, pm_fsh_len in UW. change (Z.of_nat 1448) with 1448 in UW.
  assert (Hk8 : k / 8 + nsh n <= 1448).
  { unfold nsh. assert ((k + n + 7) / 8 <= (11584 + 7) / 8) by (apply Z.div_le_mono; lia). change ((11584 + 7) / 8) with 1448 in *.
    assert (k / 8 + (n + 7) / 8 <= (k + n + 7) / 8).
    { rewrite <- (div8_add k (n + 7) H1). replace (k + (n + 7)) with (k + n + 7) by lia. lia. } lia. }
  assert (Hnsh : 0 <= nsh n) by (unfold nsh; apply Z.div_pos; lia).
  split; [exact H3|]. split; [lia|]. split; [pose proof (Z.mod_pos_bound (ff + k) 8 ltac:(lia)); rewrite Zplus_mod, S8, H1; reflexivity|].
  replace (sh (ff + k)) with (sh ff + Z.of_nat (Z.to_nat (k / 8))) by (unfold sh; rewrite Z2Nat.id by (apply Z.div_pos; lia); rewrite (div8_add ff k S8); lia).
  rewrite <- map_shz_of, <- EQ. split.
  - rewrite <- firstn_map, <- skipn_map. apply bytes_at_sub; [exact UB|].
    rewrite length_map, pm_fsh_len. lia.
  - rewrite length_map, length_firstn, length_skipn, pm_fsh_len.
    eapply wr_at_sub; [exact UW | lia | rewrite Nat2Z.inj_min, Nat2Z.inj_sub by lia; rewrite !Z2Nat.id by (try apply Z.div_pos; lia); lia | lia].
Qed.
