(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import PropExec CatSim StoreOk Hoare ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA IcptIfaceA LibIface LibIfaceA
     AxSymExec3 AxSymExec3Sound AsanPlanCore AsanPlanSoundSums BigModel BigFactsRun L5Defs L5DefsA L5Core L5CoreA L5CoreSpecsA L5StepA L5CoreB L5ParseSpecsA L5OpmodSpecsA L5ACopyS L5AStrctor
     L5DivSpecsA L5UnwindSpecsA L5ATopD L5ATopE L5ATopX L5ATopF.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.   (* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Module L5TOPA.
Import L5A. Import L5CA. Import L5CSA. Import L5SA. Import L5CB.
Abbreviation RSEGS := Asan.M.loaded_segments.
Section SCFG_1.
Context {SCFG_P : ScfgP}.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section LAYOUT.
Variables (SCRo D1 D2 D3 K1 K2 : Z) (bytes1 bytes2 : Z -> Z).      (* [comment removed for export] *)
Definition TOP_REST : Z := bytes1 268 + (64 + (8 * 268 + bytes2 268 + 8 * Z.max 268 8)).
Definition TOP_KT : Z := 5 + (K1 + K2 + 3).                        (* [comment removed for export] *)
Definition TOP_NEED (len : Z) : Z := 3 * len + 300 + TOP_REST.     (* [comment removed for export] *)
Definition TOP_STACK : Z := 208 + L5USA.CHAIN_SCR + SCRo.          (* [comment removed for export] *)
Definition TOP_FRAMES (k : Z) : Z := if k =? 1 then Z.max 5 D1 else if k =? 2 then Z.max 2 D2 else if k =? 3 then Z.max 1 D3 + 1 else 0.
Definition TOP_LEAK (k : Z) : Z := if k =? 1 then 1 else 0.        (* [comment removed for export] *)

Definition TopLayA (L : asan_layout) : lib_layoutA := {|
  lla_L := L;
  lla_entry := 0x8de88;
  lla_gp := 67584;
  lla_empty := 0x6101a0;                                           (* [comment removed for export] *)
  lla_initc := [(0x610cd8, 0x610ce0); (0x630ff8, 0x631000); (0x630d48, 0x630d50); (0x630fa0, 0x630fa8); (0xd9f40, 0xd9f60); (0xd9f70, 0xd9f78)];
                                                                   (* [comment removed for export] *)
  lla_init_img := [(0x10000, 0xd7000); (0xd9f40, 0xd9f60); (0xd9f70, 0xd9f78); (0x6101c8, 0x6101d4); (0x6103f0, 0x6103f8); (0x610c31, 0x610c37)];
  lla_td_self := 0x610c40; lla_td_tid := 0x610c60; lla_td_locale := 0x610cd8; lla_locale := 0x630fd0; lla_td_canary := 0x610cf8; lla_guard := 0x630d48; lla_auxvp := 0x630fa0;
  lla_phdr := 0x10040; lla_phent := 56; lla_phnum := 11;
  lla_rw_lo := 0xd7000;
  lla_stack := TOP_STACK;
  lla_frames := TOP_FRAMES;
  lla_leak := TOP_LEAK;
  lla_credit := fun len => (TOP_KT * hl_k_per_malloc L, hl_b_lin L * TOP_NEED len + TOP_KT * hl_b_overhead L);
  lla_foot := [(0x6101c8, 0x6101d4); (0x6103f0, 0x6103f8); (0x610c31, 0x610c37)];      (* [comment removed for export] *)
  lla_junk := [(0x610c64, 0x610c68)]                                                    (* [comment removed for export] *)
|}.
End LAYOUT.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition top_ls_okA (ar : asan_run) (g : bool * bool) (M : word -> option byte) : Prop :=
  exists av uid rnd canary hw, 0x7fff80000000 <= ar_sptop ar -> L5USA.xs_pre ar (L5USA.mkXS (fst g) (snd g) av uid rnd canary hw) M.
  (* [comment removed for export] *)
Definition TopLSA (ar : asan_run) : lib_statics := {| ls_state := (bool * bool)%type; ls_ok := top_ls_okA ar; ls_g0 := (false, false) |}.


(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Lemma str_cap_le n : 0 <= n -> 0 <= str_cap n <= n + 10.
Proof.
  intros Hn. unfold str_cap.
  assert (E : Z.lor n 7 = 8 * (n / 8) + 7).
  { pose proof (Z.add_lor_land n 7) as A. change 7 with (Z.ones 3) in A at 2. rewrite Z.land_ones in A by Lia.lia. change (2 ^ 3) with 8 in A. Lia.lia. }
  rewrite E. destruct (8 * (n / 8) + 7 =? 23) eqn:Q. apply Z.eqb_eq in Q. Lia.lia. Lia.lia.
Qed.
Lemma vblk_le m : 0 <= L5PSA.vblk m <= Z.of_nat m + 72.
Proof.
  unfold L5PSA.vblk. destruct (Nat.ltb_spec m 39). Lia.lia. unfold round_up, num_words_est. destruct (Nat.ltb_spec m 10). Lia.lia.
  rewrite Z2Nat.id. 2:{ apply Z.div_pos. pose proof (Z.div_pos (Z.of_nat m * 3402) 1024 ltac:(Lia.lia) ltac:(Lia.lia)). Lia.lia. Lia.lia. }
  Lia.lia.
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Lemma split_sign_len (s : list Z) : (length (snd (L5PSA.split_sign s)) <= length s)%nat.
Proof. unfold L5PSA.split_sign. destruct s as [|c t]. cbn; Lia.lia. destruct (c =? 45); cbn [snd length]; Lia.lia. Qed.

(* [comment removed for export] *)
Lemma ff_count_incl k (l l' : list fframe) : base.NoDup l -> incl l l' -> (ff_count k l <= ff_count k l')%nat.
Proof.
  intros ND HI. unfold ff_count. apply list_relations.list.submseteq_length. apply list_relations.list.NoDup_submseteq. apply list_relations.list.NoDup_filter. exact ND.
  intros x Hx. apply list_basics.list.list_elem_of_filter in Hx. apply list_basics.list.list_elem_of_filter. destruct Hx as [P Hx]. split. exact P.
  apply base.list_elem_of_In. apply HI. apply base.list_elem_of_In. exact Hx.
Qed.
Lemma ff_count_app k (l l' : list fframe) : ff_count k (l ++ l') = (ff_count k l + ff_count k l')%nat.
Proof. unfold ff_count. rewrite list_basics.list.filter_app. apply length_app. Qed.
Lemma ff_count_small k (LX : list fframe) : (length LX <= 1)%nat -> Forall (fun f => ff_class f = 1) LX -> Z.of_nat (ff_count k LX) <= (if k =? 1 then 1 else 0).
Proof.
  intros HL HC. destruct LX as [|f [|g r]]. 3:{ cbn [length] in HL. Lia.lia. }
  - cbn. destruct (k =? 1); Lia.lia.
  - inversion HC as [|x l0 Hf _]. subst. unfold ff_count. rewrite list_basics.list.filter_cons. destruct (base.decide _) as [X|X].
    + cbn [length]. rewrite Hf in X. destruct (1 =? k) eqn:Q. apply Z.eqb_eq in Q. subst k. cbn. Lia.lia. destruct X.
    + cbn. destruct (k =? 1); Lia.lia.
Qed.
Lemma lk_count (FF LK LK' : list fframe) k : L5USA.lk_bound LK LK' -> base.NoDup (map ff_addr (FF ++ LK')) ->
  Z.of_nat (ff_count k LK') <= Z.of_nat (ff_count k LK) + (if k =? 1 then 1 else 0).
Proof.
  intros (LX & HI & HL & HC) ND.
  assert (ND' : base.NoDup LK').
  { apply base.NoDup_ListNoDup. apply base.NoDup_ListNoDup in ND. apply NoDup_map_inv in ND. apply NoDup_app_remove_l in ND. exact ND. }
  pose proof (ff_count_incl k LK' (LX ++ LK) ND' HI) as X. rewrite ff_count_app in X. pose proof (ff_count_small k LX HL HC) as Y. Lia.lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section TOP.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface) (IL : icpt_layout).
Hypothesis LY : as0_layout L C.
Hypothesis HIok : asan_iface_ok L ar C SCFG HI.
Hypothesis UNWL : L5USA.as0_unw_layout L.
Variables (SCRo D1 D2 D3 K1 K2 : Z) (bytes1 bytes2 : Z -> Z).
(* [comment removed for export] *)
Hypothesis Hsi : strinit_spec L ar HI.
Hypothesis Hdel : opdel_sized_spec L ar HI.
Hypothesis Hcp : copy_spec L ar HI.
Hypothesis Hcps : L5ACPS.copy_stk_spec L ar HI.
Hypothesis Hcs : L5PSA.cstr_spec L ar IL HI.
Hypothesis Hsc : L5ASC.strctor_norm_spec L ar IL HI L5USA.CHAIN_SCR.
Hypothesis Hom1 : L5OMA.opmod1A_spec L ar HI L5USA.XS (L5USA.xs_pre ar) L5USA.xs_foot (L5USA.e2_landed L) (L5USA.e3_landed L) SCRo D1 D2 D3 K1 bytes1.
Hypothesis Hom2 : L5OMA.opmod2A_spec L ar HI SCRo D1 D2 D3 K2 bytes2.
Hypothesis He1 : L5USA.e1_chainA_spec L ar HI IL.
Hypothesis Hcatch1 : L5USA.catch1A_spec L ar HI.
Hypothesis Hcatch2 : L5USA.catch2A_spec L ar HI.
Hypothesis Hcatch3 : L5USA.catch3A_spec L ar HI.
(* [comment removed for export] *)
Hypothesis HSO : 0 <= SCRo /\ SCRo mod 8 = 0.
Hypothesis HK1 : 0 <= K1 /\ forall c, 0 <= c -> 0 <= bytes1 c.
Hypothesis HK2 : 0 <= K2 /\ forall c, 0 <= c -> 0 <= bytes2 c.
Hypothesis HBM : (forall c c', c <= c' -> bytes1 c <= bytes1 c') /\ (forall c c', c <= c' -> bytes2 c <= bytes2 c').
Hypothesis HCR2 : forall c, 0 <= c -> L5USA.EXC23_SZ + L5USA.REF2_SZ <= bytes1 c + (64 + (8 * c + bytes2 c + 8 * Z.max c 8)).
Hypothesis HCR3 : forall c, 0 <= c -> L5USA.EXC23_SZ + L5USA.MSG3_SZ + L5USA.REF3_SZ <= 64 + (8 * c + bytes2 c + 8 * Z.max c 8).
Local Notation Lay := (TopLayA SCRo D1 D2 D3 K1 K2 bytes1 bytes2 L).
Local Notation STK := (TOP_STACK SCRo).

Theorem top_call_okA : lib_call_okA Lay ar SCFG HI (TopLSA ar).
Proof.
  unfold lib_call_okA. intros fx g LB FF LK cr A sp ptr ra payload R M model K PRE HH HALT MI HK KONT.
  destruct PRE as [pra praok psp pgp ptp pa0 pa1 plen pptr ppay pstack pcredit pffroom pffrs pstksh pstat].
  cbn [lla_L lla_gp lla_empty lla_stack lla_frames lla_credit TopLayA] in *.
  destruct pstat as (av & uid & rnd & canary & hw & XS0). cbn [ls_ok TopLSA] in *.
  destruct pstack as (A16 & SLO & SHI & SPT & DSCR & DUP). specialize (XS0 (proj1 SPT)).
  set (st0 := L5USA.mkXS (fst g) (snd g) av uid rnd canary hw) in *.
  set (n := Z.of_nat (length payload)) in *.
  pose proof (aly_cost L C LY) as (KPM0 & LIN0 & OVH0).
  pose proof (aio_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & _ & _ & _ & _ & _ & _ & _ & _ & TOP47 & _).
  assert (NR : 0 <= n < 2 ^ 26) by (subst n; clear - plen; Lia.lia).
  assert (SC8 : STK mod 8 = 0).
  { unfold TOP_STACK, L5USA.CHAIN_SCR. destruct HSO as [_ X]. clear - X. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). Lia.lia. }
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  (* [comment removed for export] *)
  set (m := length (snd (L5PSA.split_sign (map bv_unsigned payload)))).
  set (REST := bytes1 268 + (64 + (8 * 268 + bytes2 268 + 8 * Z.max 268 8))).
  set (NEED := str_cap n + (2 * 64 + (2 * L5PSA.vblk m + REST))).
  assert (NEEDLE : 0 <= NEED <= TOP_NEED bytes1 bytes2 n).
  { pose proof (str_cap_le n (proj1 NR)) as X1. pose proof (vblk_le m) as X2.
    assert (X3 : Z.of_nat m <= n). { subst m n. pose proof (split_sign_len (map bv_unsigned payload)) as Y. rewrite length_map in Y. clear - Y; Lia.lia. }
    pose proof (proj2 HK1 268 ltac:(clear; Lia.lia)) as X4. pose proof (proj2 HK2 268 ltac:(clear; Lia.lia)) as X5. unfold TOP_NEED, TOP_REST. subst NEED REST. clear - X1 X2 X3 X4 X5. Lia.lia. }
  assert (KT0 : 0 <= TOP_KT K1 K2) by (unfold TOP_KT; destruct HK1 as [X _]; destruct HK2 as [Y _]; clear - X Y; Lia.lia).
  unfold lib_cfgA in KONT |- *. cbn [lla_L lla_entry TopLayA] in KONT |- *. rewrite (aly_segs L C LY) in *. fold (@cfg fx R 0x8de88 M model).
  assert (KONT' : forall (fx' : FPState) (g' : bool * bool) R' M' model' cr' LK' A', lib_postA Lay ar (TopLSA ar) g' LB FF cr sp payload R M R' M' cr' -> model_rt model model' -> incl A A' -> m_halted model' = None -> MInv A' model' ->
            (forall k, In k [1; 2; 3] -> Z.of_nat (ff_count k LK') <= Z.of_nat (ff_count k LK) + lla_leak Lay k) -> ri_inv HI LB FF LK' cr' A' M' (vml_of model') -> srealizes RSEGS SCFG (cfg (fx:=fx') R' ra M' model') K).
  { intros fx' g' R' M' model' cr' LK' A' X1 X2 X3 X4 X5 X6 X7. exact (KONT fx' g' R' M' model' cr' LK' A' X1 X2 X3 X4 X5 X6 X7). }
  clear KONT.
  apply (L5ATF.top_ok L ar C HI LY HIok IL SCRo D1 D2 D3 K1 K2 L5USA.CHAIN_SCR (Z.max 5 D1) (Z.max 2 D2) (Z.max 1 D3) bytes1 bytes2 st0
           Hsi Hdel Hcp Hcps Hcs Hsc Hom1 Hom2 ltac:(clear; Lia.lia) ltac:(clear; Lia.lia) HK1 HK2 HBM He1 Hcatch1 Hcatch2 Hcatch3 UNWL HCR2 HCR3
           STK fx R M model K LB FF LK cr A ptr sp ra payload).
  - unfold TOP_STACK, L5USA.CHAIN_SCR. clear - HSO; Lia.lia.
  - change COPY_SCR with 4256. unfold TOP_STACK, L5USA.CHAIN_SCR. clear - HSO; Lia.lia.
  - change L5PSA.CSTR_SCR with 4880. unfold TOP_STACK, L5USA.CHAIN_SCR. clear - HSO; Lia.lia.
  - unfold TOP_STACK, L5USA.CHAIN_SCR. clear - HSO; Lia.lia.
  - unfold TOP_STACK, L5USA.CHAIN_SCR. clear - HSO; Lia.lia.
  - exact HH.
  - split. exact HALT. exact MI.
  - exact HK.
  - exact pa0.
  - exact pa1.
  - exact NR.
  - exact pra.
  - exact praok.
  - exact psp.
  - exact A16.
  - exact ptp.
  - split. exact A16. split. exact SLO. split. exact SHI. split. exact SPT. split. exact DSCR. exact DUP.
  - unfold ffrk. exact (pffroom 1 ltac:(left; reflexivity)).
  - unfold ffrk. exact (pffroom 2 ltac:(right; left; reflexivity)).
  - unfold ffrk. exact (pffroom 3 ltac:(right; right; left; reflexivity)).
  - exact pffrs.
  - exact pstksh.
  - exact SC8.
  - exact (proj2 HSO).
  - exact pgp.
  - destruct XS0 as ((_ & _ & _ & _ & SCN) & _). destruct SCN as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & I1 & _). intros i Hi. apply I1. clear - Hi; Lia.lia.
  - exact ppay.
  - destruct pptr as [(P0 & PE)|(P0 & INB)]. subst n ptr. rewrite P0. cbn. clear; Lia.lia.
    destruct (WB _ INB) as ((Q0 & _ & _ & _ & Q4 & _) & _). cbn [fst snd] in Q0, Q4. fold n in Q4. clear - Q0 Q4 SPT. Lia.lia.
  - destruct pptr as [(P0 & _)|(P0 & INB)]. left. subst n. rewrite P0. reflexivity. right. exists ptr, n. split. exact INB. clear; Lia.lia.
  - (* [comment removed for export] *)
    intros Mk (IS1 & IS2). apply (L5ATX.xs_pre_same L ar C LY M Mk st0 UNWL). 2: exact XS0.
    intros a [(Ha & NS)|Ha]. exact (IS1 a Ha NS). exact (IS2 a Ha).
  - unfold L5OMA.acredit_for. fold REST. fold m. fold NEED. destruct pcredit as [PK PB]. cbn [fst snd] in PK, PB. fold (TOP_KT K1 K2).
    split. exact PK. eapply Z.le_trans. 2: exact PB. apply Z.add_le_mono_r. apply Z.mul_le_mono_nonneg_l. exact LIN0. exact (proj2 NEEDLE).
  - unfold TOP_STACK, L5USA.CHAIN_SCR, L5USA.CATCH_SCR. clear - HSO; Lia.lia.
  - clear; Lia.lia.
  - reflexivity.
  - (* [comment removed for export] *)
    intros fx' R' M' model' cr' LK' A' R10' RP' AH' XS' CRL' RT' IA' AM' LKB' HH'.
    destruct XS' as ([gd' fl' av' uid' rnd' canary' hw'] & XS').
    apply (KONT' fx' (gd', fl') R' M' model' cr' LK' A').
    + constructor.
      * exact R10'.
      * exact RP'.
      * fold REST in CRL'. fold m in CRL'. fold NEED in CRL'. fold (TOP_KT K1 K2) in CRL'. cbn [lla_credit TopLayA]. fold n.
        unfold credit_le, credit_sub, L5OMA.adebits in *. cbn [fst snd] in *. destruct CRL' as [C1 C2]. split. exact C1. eapply Z.le_trans. 2: exact C2.
        apply Z.sub_le_mono_l. apply Z.add_le_mono_r. apply Z.mul_le_mono_nonneg_l. exact LIN0. exact (proj2 NEEDLE).
      * (* [comment removed for export] *)
        intros a Ha Hc NF NJ. apply (proj1 AH'). split. exact Ha. split. exact Hc.
        intros rr Hr X. unfold L5ATX.UNWW, L5ATX.CWF, L5USA.xs_foot1, L5USA.EH_CAUGHT, L5USA.EH_UNCAUGHT, L5USA.UW_FLAGS, L5USA.SYSCAT_GUARD, L5USA.ERRNO in Hr. cbn [app In] in Hr.
        unfold L5.in_rng in X.
        destruct Hr as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]; cbn [fst snd] in X.
        -- apply NF. exists (0x6101c8, 0x6101d4). split. left; reflexivity. cbn [fst snd]. clear - X; Lia.lia.
        -- apply NF. exists (0x6101c8, 0x6101d4). split. left; reflexivity. cbn [fst snd]. clear - X; Lia.lia.
        -- apply NF. exists (0x6101c8, 0x6101d4). split. left; reflexivity. cbn [fst snd]. clear - X; Lia.lia.
        -- apply NF. exists (0x610c31, 0x610c37). split. right; right; left; reflexivity. cbn [fst snd]. clear - X; Lia.lia.
        -- apply NF. exists (0x6103f0, 0x6103f8). split. right; left; reflexivity. cbn [fst snd]. clear - X; Lia.lia.
        -- apply NJ. exists (0x610c64, 0x610c68). split. left; reflexivity. cbn [fst snd]. clear - X; Lia.lia.
      * exact (proj1 (proj2 AH')).
      * exact (proj2 (proj2 AH')).
      * (* [comment removed for export] *)
        cbn [lla_stack TopLayA]. intros j Hj. unfold byte_at. rewrite (proj1 AH'). exact (pstksh j Hj).
        Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
        assert (AR : S (ahl_ceil ar) <= S (sp - STK) + j <= S (ahl_ceil ar + (2 ^ 47 - ahl_ceil ar) - 1) /\ 2147450880 <= S (sp - STK) + j < 2 ^ 64).
        { unfold S, SB. unfold TOP_STACK, L5USA.CHAIN_SCR in *. clear - Hj SLO SHI SPT TOP47 HSO. Lia.lia. }
        Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
        split. clear - AR; Lia.lia. split. right; right; right; right; left. exact (proj1 AR).
        intros rr Hr X. unfold L5ATX.UNWW, L5ATX.CWF, L5USA.xs_foot1, L5USA.EH_CAUGHT, L5USA.EH_UNCAUGHT, L5USA.UW_FLAGS, L5USA.SYSCAT_GUARD, L5USA.ERRNO in Hr. cbn [app In] in Hr.
        unfold L5.in_rng in X. destruct AR as [_ AR]. repeat (destruct Hr as [<-|Hr]; [cbn [fst snd] in X; clear - X AR; Lia.lia|]). destruct Hr.
      * cbn [ls_ok TopLSA]. exists av', uid', rnd', canary', hw'. intros _. exact XS'.
    + exact RT'.
    + exact IA'.
    + exact (proj1 AM').
    + exact (proj2 AM').
    + intros k Hk. cbn [lla_leak TopLayA]. unfold TOP_LEAK.
      pose proof (aio_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH') as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & ND & _).
      exact (lk_count FF LK LK' k LKB' ND).
    + exact HH'.
Qed.

(* [comment removed for export] *)
Lemma rdn_img M lo hi : L5.img_clear M lo hi -> forall (k : nat) a, lo <= a -> a + Z.of_nat k <= hi -> 0 <= a -> hi <= 2 ^ 64 ->
  rdn RSEGS M (Z_to_bv 64 a) k = rdn RSEGS (fun _ => None) (Z_to_bv 64 a) k.
Proof.
  intros IC. induction k as [|k IH]; intros a H1 H2 H3 H4. reflexivity.
  cbn [rdn]. rewrite (IC a) by Lia.lia. rewrite (L5C.add1_lit a). rewrite (IH (a + 1)) by Lia.lia. reflexivity.
Qed.

Theorem top_statics_initA : lib_statics_initA Lay ar (TopLSA ar).
Proof.
  unfold lib_statics_initA, lib_statics_init. intros av uid rnd tid canary hw M IF.
  unfold lib_init_facts in IF. cbv zeta in IF.
  cbn [lib_view heap_view ll_heap ll_init_img ll_td_self ll_td_tid ll_td_locale ll_locale ll_td_canary ll_guard ll_auxvp HeapIface.hl_segs hl_sptop
       lla_L lla_init_img lla_td_self lla_td_tid lla_td_locale lla_locale lla_td_canary lla_guard lla_auxvp TopLayA] in IF.
  rewrite (aly_segs L C LY) in IF.
  destruct IF as (IMG & _ & _ & _ & TDL & LOC & _ & GRD & CANR & AUX & AVS & AVHI & AV8 & AUXW & UIDR & HWR & RNDS & RNDH).
  cbn [ls_ok ls_g0 TopLSA]. exists av, uid, rnd, canary, hw. intros SPT.
  assert (IC : forall lo hi, In (lo, hi) [(65536, 880640); (892736, 892768); (892784, 892792); (6357448, 6357460); (6358000, 6358008); (6360113, 6360119)] -> L5.img_clear M lo hi).
  { intros lo hi Hin i Hi. exact (IMG (lo, hi) i Hin Hi). }
  pose proof (IC _ _ ltac:(left; reflexivity)) as I1. pose proof (IC _ _ ltac:(right; left; reflexivity)) as I2. pose proof (IC _ _ ltac:(right; right; left; reflexivity)) as I3.
  pose proof (IC _ _ ltac:(do 3 right; left; reflexivity)) as I4. pose proof (IC _ _ ltac:(do 4 right; left; reflexivity)) as I5. pose proof (IC _ _ ltac:(do 5 right; left; reflexivity)) as I6. clear IC IMG.
  split. 2: exact AVS. cbn [L5USA.xs_gd L5USA.xs_fl L5USA.xs_av L5USA.xs_uid L5USA.xs_rnd L5USA.xs_canary L5USA.xs_hw fst snd].
  unfold L5USA.e1_staticsA.
  split. { unfold L5.u64_at, L5USA.EH_CAUGHT. rewrite (rdn_img M _ _ I4 8 6357448) by (cbn; Lia.lia). vm_compute. reflexivity. }
  split. { unfold L5.u32_at, L5USA.EH_UNCAUGHT. rewrite (rdn_img M _ _ I4 4 6357456) by (cbn; Lia.lia). vm_compute. reflexivity. }
  split. { unfold L5USA.syscat_guard, L5USA.SYSCAT_GUARD, L5.u8_at. split.
           rewrite (rdn_img M _ _ I5 1 6358000) by (cbn; Lia.lia). vm_compute. reflexivity.
           rewrite (rdn_img M _ _ I5 1 (6358000 + 1)) by (cbn; Lia.lia). vm_compute. reflexivity. }
  split. { unfold L5USA.uw_flags, L5USA.UW_FLAGS, L5.u8_at. split. 2: split.
           rewrite (rdn_img M _ _ I6 1 6360113) by (cbn; Lia.lia). vm_compute. reflexivity.
           rewrite (rdn_img M _ _ I6 1 (6360113 + 2)) by (cbn; Lia.lia). vm_compute. reflexivity.
           rewrite (rdn_img M _ _ I6 1 (6360113 + 4)) by (cbn; Lia.lia). vm_compute. reflexivity. }
  unfold L5USA.statics_const, L5USA.TD_LOCALE, L5USA.GLOBAL_LOCALE, L5USA.LOCALE_MSGCAT, L5USA.CANARY, L5USA.AUXVP, L5USA.SYSCAT_OBJ.
  split. exact TDL.
  split. { pose proof (LOC 5%nat ltac:(Lia.lia)) as X. exact X. }
  split. exact (L5ATX.errno_readable M).
  split. exact GRD. split. exact AUX. split. exact AV8. split. clear - AVS SPT; Lia.lia. split. exact AVHI.
  split. { intros j Hj. exact (AUXW j Hj). }
  split. clear - UIDR; Lia.lia. split. clear - RNDS RNDH SPT; Lia.lia. split. exact CANR. split. exact HWR.
  split. exact I1. split. exact I2. exact I3.
Qed.

Theorem top_statics_frameA : lib_statics_frameA Lay ar (TopLSA ar).
Proof.
  unfold lib_statics_frameA, lib_statics_frame. intros g M M' OK FOOT RO INITC.
  cbn [ls_ok TopLSA] in *. destruct OK as (av & uid & rnd & canary & hw & XS). exists av, uid, rnd, canary, hw. intros SPT. specialize (XS SPT).
  unfold in_foot, in_initc in *. cbn [lib_view heap_view ll_heap ll_foot ll_initc ll_rw_lo hl_sptop lla_L lla_foot lla_initc lla_rw_lo TopLayA] in *.
  assert (FT : forall lo hi a, In (lo, hi) [(6357448, 6357460); (6358000, 6358008); (6360113, 6360119)] -> lo <= a < hi -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
  { intros lo hi a Hin Ha. apply FOOT. clear - Hin Ha. cbn [In] in Hin. repeat (destruct Hin as [Hin|Hin]; [inversion Hin; subst; Lia.lia|]). destruct Hin. exists (lo, hi). split. exact Hin. exact Ha. }
  assert (IT : forall lo hi a, In (lo, hi) [(6360280, 6360288); (6492152, 6492160); (6491464, 6491472); (6492064, 6492072); (892736, 892768); (892784, 892792)] -> lo <= a < hi -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
  { intros lo hi a Hin Ha. apply INITC. clear - Hin Ha. cbn [In] in Hin. repeat (destruct Hin as [Hin|Hin]; [inversion Hin; subst; Lia.lia|]). destruct Hin. left. exists (lo, hi). split. exact Hin. exact Ha. }
  apply (L5ATX.xs_pre_xfer ar M M'). 4: exact XS.
  - intros a ((r & Hr & Ha) & NE).
    unfold L5USA.UNW_STATICS, L5USA.UNW_CONSTS, L5USA.EH_CAUGHT, L5USA.SYSCAT_GUARD, L5USA.UW_FLAGS, L5USA.ERRNO in Hr. cbn [app In] in Hr.
    destruct Hr as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]; cbn [fst snd] in Ha.
    + apply (FT 6357448 6357460). left; reflexivity. clear - Ha; Lia.lia.
    + apply (FT 6358000 6358008). right; left; reflexivity. clear - Ha; Lia.lia.
    + apply (FT 6360113 6360119). right; right; left; reflexivity. clear - Ha; Lia.lia.
    + exfalso. apply NE. clear - Ha; Lia.lia.
    + apply (IT 892736 892768). do 4 right; left; reflexivity. clear - Ha; Lia.lia.
    + apply (IT 892784 892792). do 5 right; left; reflexivity. clear - Ha; Lia.lia.
    + apply (IT 6360280 6360288). left; reflexivity. clear - Ha; Lia.lia.
    + apply (IT 6492152 6492160). right; left; reflexivity. clear - Ha; Lia.lia.
    + apply (IT 6491464 6491472). right; right; left; reflexivity. clear - Ha; Lia.lia.
    + apply (IT 6492064 6492072). do 3 right; left; reflexivity. clear - Ha; Lia.lia.
  - intros a Ha. apply INITC. clear - Ha SPT; Lia.lia. right. clear - Ha; Lia.lia.
  - intros I1 i Hi. apply RO. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). rewrite Z.mod_small by (clear - Hi; Lia.lia). clear - Hi; Lia.lia. exact (I1 i Hi).
Qed.

Theorem top_iface_okA : lib_iface_okA Lay ar SCFG HI (TopLSA ar).
Proof. constructor. exact top_call_okA. exact top_statics_initA. exact top_statics_frameA. Qed.
End TOP.
End SCFG_1.
End L5TOPA.
