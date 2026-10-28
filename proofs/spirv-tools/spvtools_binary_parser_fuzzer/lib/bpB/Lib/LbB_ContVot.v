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
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require Import CRep ContStmts.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LbB_Kit LbB_Bridge LbB_Call LbB_Conv LbB_SR LbB_MILB LbB_Own LbB_ContStmt LbB_ContV4R LbB_ContV4 LbB_ContVotR.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Lemma vec32A_munch : forall LB' m m' v b xs cap W, vec32A LB' m v b xs cap -> munch W m m' ->
  disjoint_from W v 24 -> disjoint_from W b (4 * Zlen xs) -> vec32A LB' m' v b xs cap.
Proof.
  intros LB' m m' v b xs cap W VEC MU D1 D2. unfold vec32A in *.
  pose proof VEC as (Hv & Hv' & _ & Hlen & Hb & _).
  eapply vec32_frame; [exact VEC|]. intros a Ha. apply MU.
  unfold vec32_fp, zwin in Ha. destruct Ha as [Ha|[Hb0 Ha]].
  - rewrite u64_of_Z by lia. eapply disjoint_outside; [exact D1 | lia].
  - assert (BB : 0 < b /\ b + 4 * cap <= 2 ^ 63) by (destruct Hb as [[E _]|(B0 & _ & _ & BC & _)]; [contradiction | lia]).
    rewrite u64_of_Z by lia. eapply disjoint_outside; [exact D2 | lia].
Qed.

Lemma vec32A_set_end : forall LB' m m' v b xs cap, vec32A LB' m v b xs cap -> AIMG_TOP <= v ->
  munch [(v + 8, v + 16)] m m' -> rw_cells asegs m' (v + 8) [C8 (Z_to_bv 64 (b + 4 * Zlen xs))] -> vec32A LB' m' v b xs cap.
Proof.
  intros LB' m m' v b xs cap VEC HV MU HC. unfold vec32A in *.
  destruct VEC as (Hv & Hv' & HD & Hlen & Hb & F0 & F1 & F2 & FE).
  assert (AG : forall a k z, 0 <= a -> a + Z.of_nat k < 2 ^ 64 -> (a + Z.of_nat k <= v + 8 \/ v + 16 <= a) ->
            fld ASEGS m a k z -> fld ASEGS m' a k z).
  { intros a k z H0 H1 H2 Hf. eapply fld_agree; [exact H0 | exact H1 | exact Hf |].
    intros a' Ha'. unfold zwin in Ha'. apply MU. rewrite u64_of_Z by lia. cbn [outside]. split; [lia | exact I]. }
  pose proof (mdef_of_rw_cells_hi _ _ _ HC ltac:(unfold AIMG_TOP in *; lia)) as MD. cbn [cells_size csize] in MD.
  unfold AIMG_TOP in HV.
  unfold vec32. split; [lia|]. split; [lia|].
  split.
  { intros i Hi. destruct (Z_lt_le_dec i 8) as [L|L]; [|destruct (Z_lt_le_dec i 16) as [L'|L']].
    - rewrite (MU (Z_to_bv 64 (v + i))); [apply HD; lia|]. rewrite u64_of_Z by lia. cbn [outside]. split; [lia | exact I].
    - replace (v + i) with (v + 8 + (i - 8)) by lia. apply MD. lia.
    - rewrite (MU (Z_to_bv 64 (v + i))); [apply HD; lia|]. rewrite u64_of_Z by lia. cbn [outside]. split; [lia | exact I]. }
  split; [exact Hlen|]. split; [exact Hb|].
  split; [apply AG; [lia | cbn; lia | cbn; lia | exact F0]|].
  split; [apply fld_of_rw_cells8; [exact HC | lia]|].
  split; [apply AG; [lia | cbn; lia | cbn; lia | exact F2]|].
  intros i Hi. destruct (FE i Hi) as [E1 E2]. split; [exact E1|].
  destruct Hb as [[-> ->]|(B0 & B16 & C0 & BC & _ & D)]; [lia|].
  apply AG; [lia | cbn; lia | cbn; lia | exact E2].
Qed.

Lemma vec32A_push : forall LB' m m' v b xs cap x, vec32A LB' m v b xs cap -> Zlen xs < cap -> mdef m' v 24 ->
  fldA m' v 8 b -> fldA m' (v + 8) 8 (b + 4 * (Zlen xs + 1)) -> fldA m' (v + 16) 8 (b + 4 * cap) ->
  (forall i, 0 <= i < Zlen xs -> fldA m' (b + 4 * i) 4 (Znth i xs)) -> fldA m' (b + 4 * Zlen xs) 4 x -> 0 <= x < 2 ^ 32 ->
  vec32A LB' m' v b (xs ++ [x]) cap.
Proof.
  intros LB' m m' v b xs cap x VEC LT MD F0 F1 F2 FE FX HX. unfold vec32A in *.
  destruct VEC as (Hv & Hv' & HD & Hlen & Hb & G0 & G1 & G2 & GE).
  unfold vec32. rewrite Zlen_app1.
  split; [lia|]. split; [lia|]. split; [exact MD|]. split; [lia|].
  split; [destruct Hb as [[_ C]|Hb]; [lia | right; exact Hb]|].
  split; [exact F0|]. split; [exact F1|]. split; [exact F2|].
  intros i Hi. destruct (Z.eq_dec i (Zlen xs)) as [->|Hne].
  - rewrite Znth_app1_eq. split; [exact HX | exact FX].
  - rewrite Znth_app1_lt by lia. split; [apply GE; lia | apply FE; lia].
Qed.

Lemma vt_wr_sub : forall mk a n a' n', wr_at asegs mk a n -> a <= a' -> a' + n' <= a + n -> 0 <= n' -> wr_at asegs mk a' n'.
Proof.
  intros mk a n a' n' (W0 & W1 & W) H1 H2 H3. split; [lia|]. split; [lia|].
  intros i Hi. replace (a' + i) with (a + (a' - a + i)) by lia. apply W. lia.
Qed.
Lemma vt_dj_sub : forall W a n a' n', disjoint_from W a n -> a <= a' -> a' + n' <= a + n -> disjoint_from W a' n'.
Proof.
  induction W as [|[l h] W IH]; intros a n a' n' D H1 H2; [exact I|]. cbn in D |- *. destruct D as [D1 D2].
  split; [lia | exact (IH a n a' n' D2 H1 H2)].
Qed.

Lemma fld_xpres {HCEIL : HeapCeil} : forall H LB SP X m m' a k z, xpres H LB SP X m m' -> xclient_range H LB SP X a (Z.of_nat k) ->
  0 <= a -> a + Z.of_nat k < 2 ^ 64 -> fldA m a k z -> fldA m' a k z.
Proof.
  intros H LB SP X m m' a k z XP XC H0 H1 Hf. unfold fldA in *. eapply fld_agree; [exact H0 | exact H1 | exact Hf |].
  intros a' Ha'. hnf in Ha'.
  destruct (XP a' ltac:(lia) (xclient_range_addr H LB SP X a (Z.of_nat k) a' XC Ha')) as [E _]. exact E.
Qed.
Lemma xcl_sub {HCEIL : HeapCeil} : forall H LB SP X A n A' n', xclient_range H LB SP X A n -> A <= A' -> A' + n' <= A + n -> 0 <= n' ->
  xclient_range H LB SP X A' n'.
Proof.
  intros H LB SP X A n A' n' [K KX] H1 H2 H3. split.
  - unfold aclient_range in *.
    destruct K as [K|[K|[(bb & Hb & K1 & K2)|[(bb & Hb & K1 & K2)|[K|[K|K]]]]]].
    + left. lia.
    + right; left. intros a Ha. apply K. lia.
    + right; right; left. exists bb. split; [exact Hb | lia].
    + right; right; right; left. exists bb. split; [exact Hb | lia].
    + right; right; right; right; left. lia.
    + right; right; right; right; right; left. lia.
    + right; right; right; right; right; right. lia.
  - eapply Forall_impl; [|exact KX]. intros [l h] Hlh. cbn [fst snd] in *. lia.
Qed.

Lemma vt_band_of_aapp {HCEIL : HeapCeil} : forall A n, aapp A n -> (0 <= A /\ A + n <= 0x7fff7000) \/ 0x10007fff8000 <= A.
Proof.
  intros A n HA. unfold aapp, aapp_lo, aapp_hi, AIMG_TOP, ALOWSH_LO, AHI_LO in HA. destruct HA; [left|right]; lia.
Qed.

Lemma v4_mod16_sub64 : forall z, z mod 16 = 0 -> (z - 64) mod 16 = 0.
Proof.
  intros z Hz. replace (z - 64) with (z + (-4) * 16) by lia. rewrite Z_mod_plus_full. exact Hz.
Qed.

Lemma v4_newcap_ge : forall cap, cap + 1 <= v4_newcap cap.
Proof.
  intros cap. unfold v4_newcap, vgrow. lia.
Qed.

Lemma vt_ret_ok : v4_ret_ok VOT_RET.
Proof.
  unfold VOT_RET. v4_ret_tac.
Qed.

Lemma vt_slot_shk : forall m b cap len, SHAD m b (cc_gen (4 * cap) (4 * len + 4)) -> b mod 16 = 0 -> 0 <= b -> 0 <= len -> len < cap ->
  exists j, LbB_Kit.shk m (b + 4 * len) j /\ (j = 0 \/ (b + 4 * len) mod 8 + 4 <= j < 8).
Proof.
  intros m b cap len SH B16 B0 L0 LC.
  assert (HL : Z.of_nat (length (cc_gen (4 * cap) (4 * len + 4))) = nsh (4 * cap)) by (apply cc_gen_length; lia).
  destruct (shk_of_SHAD m b _ (b + 4 * len) SH) as (bb & Hbb & K).
  { rewrite HL. unfold nsh. Z.div_mod_to_equations. lia. }
  replace ((b + 4 * len - b) / 8) with (4 * len / 8) in Hbb by (f_equal; lia).
  unfold cc_gen in Hbb.
  rewrite nth_error_app1 in Hbb.
  2: { apply Nat2Z.inj_lt. rewrite shadow_of_length by lia. unfold nsh. Z.div_mod_to_equations. lia. }
  exists (bv_unsigned bb). split; [exact K|].
  destruct (Z.eq_dec ((4 * len + 4) mod 8) 0) as [E|E].
  - rewrite shadow_of_nth_full in Hbb by (Z.div_mod_to_equations; lia).
    injection Hbb as <-. left. reflexivity.
  - assert (E4 : (4 * len + 4) mod 8 = 4) by (Z.div_mod_to_equations; lia).
    replace (4 * len / 8) with ((4 * len + 4) / 8) in Hbb by (Z.div_mod_to_equations; lia).
    rewrite shadow_of_nth_last in Hbb by lia. injection Hbb as <-. right. rewrite E4.
    change (bv_unsigned (b8 4)) with 4. Z.div_mod_to_equations. lia.
Qed.

Lemma aclient_write_ok_sub {HCEIL : HeapCeil} : forall H LB l h l' h', aclient_write_ok H LB (l, h) -> l <= l' -> h' <= h ->
  aclient_write_ok H LB (l', h').
Proof.
  intros H LB l h l' h' K H1 H2. unfold aclient_write_ok, aimg_client_w in *. cbn [fst snd] in *.
  destruct K as [K|[K|[(bb & Hb & K1 & K2)|[(bb & Hb & K1 & K2)|[K|[K|K]]]]]].
  - left. lia.
  - right; left. lia.
  - right; right; left. exists bb. split; [exact Hb | lia].
  - right; right; right; left. exists bb. split; [exact Hb | lia].
  - right; right; right; right; left. lia.
  - right; right; right; right; right; left. lia.
  - right; right; right; right; right; right. lia.
Qed.
Lemma afs_write_ok_sub {HCEIL : HeapCeil} : forall H LF l h l' h', afs_write_ok H LF (l, h) -> l <= l' -> h' <= h ->
  afs_write_ok H LF (l', h').
Proof.
  intros H LF l h l' h' K H1 H2. unfold afs_write_ok in *. cbn [fst snd] in *.
  destruct K as [K|(f & Hf & K1 & K2)]; [left; lia | right; exists f; split; [exact Hf | lia]].
Qed.
Lemma aconst_ok_sub : forall l h l' h', aconst_ok (l, h) -> l <= l' -> h' <= h -> aconst_ok (l', h').
Proof.
  intros l h l' h' K H1 H2 a Ha. apply K. cbn [fst snd] in *. lia.
Qed.

Inductive vhid (P : Prop) : Prop := VHid (p : P).
Ltac vhide H := apply VHid in H.
Ltac vuse H := let K := fresh H in pose proof H as [K].

Section VT.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HH : asan_rt_hyps H.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
            (m : mem) (mo : Model) (s : as_St H) (LB : list block) (LF : list fframe)
            (v b cap src x : Z) (xs : list Z) (pid : bptr) (lo B shi spz : Z).
  Hypothesis SPZ : bv_unsigned sp = spz.
  Hypothesis SPR : 2 ^ 45 + 64 <= spz /\ spz <= 2 ^ 47 /\ spz mod 16 = 0.
  Hypothesis VBAND : (0x6e8000 <= v /\ v + 24 <= 0x7fff7000) \/ (0x10007fff8000 <= v /\ v + 24 <= 2 ^ 47).
  Hypothesis OBJ : obj_win H LB LF spz lo v 24.
  Hypothesis V8 : v mod 8 = 0.
  Hypothesis VEC : vec32A LB m v b xs cap.
  Hypothesis OLD : v4_oldblk LB b cap pid.
  Hypothesis OLDSH : 0 < cap -> SHAD m b (cc_gen (4 * cap) (4 * Zlen xs)).
  Hypothesis CAPB : 4 * cap <= 2 ^ 26.
  Hypothesis GROW : Zlen xs = cap -> 4 * v4_newcap cap <= 2 ^ 26.
  Hypothesis XR : 0 <= x < 2 ^ 31.
  Hypothesis SRC : src4_keep_x H LB spz (if b =? 0 then [] else [(sh b, sh b + nsh (4 * cap))]) m src x.
  Hypothesis SRCR : src mod 4 = 0 /\ 0 <= src /\ src + 4 <= 2 ^ 47.
  Hypothesis RH0 : as_RHEAP H s LB m.
  Hypothesis SLOWOK : Zlen xs = cap -> as_alloc_ok H s LB (4 * v4_newcap cap)
                                       /\ as_Cm H (4 * v4_newcap cap) + as_Cf H (4 * cap) <= as_AL H s.
  Hypothesis TRO : trace_ok (as_TR H) APC0_FREE [v4_del_ra VOT_SLOW_RREF].
  Hypothesis RA0 : as_rauxv_ok H m B.
  Hypothesis SPB : spz <= B.
  Hypothesis ST0 : stk asegs m lo spz.
  Hypothesis LOR : aceil <= lo /\ lo <= spz - VOT_PB_STACK.
  Hypothesis MI0 : mem_inv asegs m.
  Hypothesis TPV : tp = Z_to_bv 64 ATP.
  Hypothesis AC0 : ACONST m.
  Hypothesis RF0 : as_RFS H LF m.
  Hypothesis S00 : stack0 m lo shi.
  Hypothesis SHI : spz <= shi.
  Hypothesis ADV0 : addressable m v 24.
  Hypothesis VWR : wr_at asegs m v 24.
  Hypothesis OWN : lb_own LB m.

  Let Q := votpb_post H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB LF v b cap x xs pid lo B shi m mo.
  Let FRAME : list cell := map (fun w => C8 w) [s5; s4; s3; s2; s1; s0; ra].
  Lemma vt_spz_sp : sp = Z_to_bv 64 spz.
Proof.
Proof. rewrite <- SPZ. symmetry. apply Z_to_bv_bv_unsigned. Qed.

  Lemma vt_facts :
    fldA m v 8 b /\ fldA m (v + 8) 8 (b + 4 * Zlen xs) /\ fldA m (v + 16) 8 (b + 4 * cap)
    /\ (forall i, 0 <= i < Zlen xs -> 0 <= Znth i xs < 2 ^ 32 /\ fldA m (b + 4 * i) 4 (Znth i xs))
    /\ 0 <= Zlen xs <= cap /\ ((b = 0 /\ cap = 0) \/ (0 < cap /\ In (pid, b, 4 * cap) LB /\ ablock_range H b (4 * cap)))
    /\ (b <> 0 -> v + 24 <= b \/ b + 4 * cap <= v) /\ mdef m v 24.
Proof.
Proof.
  pose proof VEC as (Hv & Hv' & HD & Hlen & Hb & F0 & F1 & F2 & FE).
  split; [exact F0|]. split; [exact F1|]. split; [exact F2|]. split; [exact FE|]. split; [lia|].
  split.
  - destruct OLD as [[E1 E2]|(Hc & HIn)]; [left; exact (conj E1 E2)|].
    right. split; [lia|]. split; [exact HIn|]. exact (ah_blocks H HH _ _ _ _ RH0 HIn).
  - split; [|exact HD]. intros NZ.
    destruct Hb as [[E _]|(_ & _ & _ & _ & _ & D)]; [contradiction | exact D].
Qed.

  Lemma vt_end : forall (msF3 : machine_state) (mo3 : Model) (sk3 : as_St H) (m3 : mem) (R3 : bvmap 5 word)
                        (LB' : list block) (b' cap' : Z) (e3 : word),
    as_VIS H sk3 msF3 = MS R3 F (Z_to_bv 64 VOT_RET) fc None m3 (seg_rom asegs) -> rfull R3 ->
    getr R3 1 = ra -> getr R3 2 = sp -> getr R3 3 = gp -> getr R3 4 = tp -> getr R3 8 = s0 -> getr R3 9 = s1 ->
    getr R3 18 = s2 -> getr R3 19 = s3 -> getr R3 20 = s4 -> getr R3 21 = s5 -> getr R3 22 = s6 -> getr R3 23 = s7 ->
    getr R3 24 = s8 -> getr R3 25 = s9 -> getr R3 26 = s10 -> getr R3 27 = s11 ->
    as_AKREL H sk3 (mkCfg msF3 mo3) -> as_MPRES H mo mo3 ->
    mem_inv asegs m3 -> stk asegs m3 lo spz -> rw_cells asegs m3 (errno_addr tp) [C4 e3] -> as_rauxv_ok H m3 B ->
    vec32A LB' m3 v b' (xs ++ [x]) cap' -> as_RHEAP H sk3 LB' m3 ->
    SHAD m3 b' (cc_gen (4 * cap') (4 * (Zlen xs + 1))) -> addressable m3 v 24 -> wr_at asegs m3 v 24 -> lb_own LB' m3 ->
    ((Zlen xs < cap /\ b' = b /\ cap' = cap /\ LB' = LB
      /\ xpres H LB spz [(v, v + 24); (b, b + 4 * cap); (sh b, sh b + nsh (4 * cap))] m m3 /\ as_AL H sk3 >= as_AL H s)
     \/ (Zlen xs = cap /\ cap' = v4_newcap cap
         /\ (exists pid', LB' = v4_newLB H LB b pid pid' b' (4 * cap') /\ ablock_range H b' (4 * cap'))
         /\ xpres H LB spz ((v, v + 24) :: v4_oldx b (4 * cap)) m m3
         /\ as_AL H sk3 >= as_AL H s - (as_Cm H (4 * cap') + as_Cf H (4 * cap)))) ->
    as_RFS H LF m3 -> ACONST m3 -> stack0 m3 lo shi ->
    as_SR H Q (mkCfg msF3 mo3).
Proof.
Proof.
  intros msF3 mo3 sk3 m3 R3 LB' b' cap' e3 VIS3 HF3 G1 G2 G3 G4 G8 G9 G18 G19 G20 G21 G22 G23 G24 G25 G26 G27 KR3 MP3
    MI3 ST3 ERR3 RA3 VEC3 RH3 SH3 ADV3 WV3 OW3 CASE RF3 AC3 S03.
  rewrite (rfull_eq R3 HF3) in VIS3.
  eapply (sr_evt H HH) with
    (P := fun ms => ms = MS (mkR ra sp gp tp (getr R3 5) (getr R3 6) (getr R3 7) s0 s1 (getr R3 10) (getr R3 11) (getr R3 12)
                               (getr R3 13) (getr R3 14) (getr R3 15) (getr R3 16) (getr R3 17) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                               (getr R3 28) (getr R3 29) (getr R3 30) (getr R3 31))
                          F (ret_pc ra) fc None m3 (seg_rom asegs));
    [exact KR3 | exact VIS3 | |].
  { rewrite G1, G2, G3, G4, G8, G9, G18, G19, G20, G21, G22, G23, G24, G25, G26, G27. apply vt_ret_ok. cbv beta. reflexivity. }
  intros msF4 mo4 KR4 MP4 HP. cbv beta in HP.
  exists (getr R3 5), (getr R3 6), (getr R3 7), (getr R3 10), (getr R3 11), (getr R3 12), (getr R3 13), (getr R3 14), (getr R3 15),
    (getr R3 16), (getr R3 17), (getr R3 28), (getr R3 29), (getr R3 30), (getr R3 31), m3, e3, sk3, LB', b', cap'.
  cbn [cfg_ms cfg_model]. rewrite SPZ.
  split; [exact HP|]. split; [exact KR4|]. split; [eapply (ah_mpres_trans H HH); eassumption|].
  split; [exact MI3|]. split; [exact ST3|]. split; [exact ERR3|]. split; [exact RA3|]. split; [exact VEC3|].
  split; [exact RH3|]. split; [exact SH3|]. split; [exact ADV3|]. split; [exact WV3|]. split; [exact OW3|].
  split; [exact CASE|]. split; [exact RF3|]. split; [exact AC3|]. exact S03.
Qed.

  Lemma vt_awo_new : forall LB', (b = 0 -> forall bb, In bb LB -> In bb LB') ->
    (b <> 0 -> forall bb, In bb LB -> blk_id bb <> pid -> In bb LB') ->
    aclient_write_ok H LB' (v + 8, v + 16).
Proof.
Proof.
  intros LB' K0 K1.
  pose proof (ah_nodup H HH _ _ _ RH0) as ND.
  pose proof aceil_facts as ((ACF1 & ACF2) & _ & _).
  assert (KEEP : forall bb, In bb LB ->
            ((blk_addr bb <= v + 8 /\ v + 16 <= blk_addr bb + blk_size bb)
             \/ (sh (blk_addr bb) <= v + 8 /\ v + 16 <= sh (blk_addr bb) + nsh (blk_size bb))) -> In bb LB').
  { intros bb Hb HR. destruct (Z.eq_dec b 0) as [E|NE]; [exact (K0 E bb Hb)|].
    apply (K1 NE bb Hb). intros Hid.
    destruct OLD as [[E _]|(Hc & HIn)]; [contradiction|].
    destruct bb as [[p A] n]. cbn [blk_id fst] in Hid. subst p.
    pose proof (nodup_id_same LB pid b (4 * cap) A n ND HIn Hb) as EQ. injection EQ as <- <-.
    cbn [blk_addr blk_size fst snd] in HR.
    assert (ABR : ablock_range H b (4 * cap)) by exact (ah_blocks H HH _ _ _ _ RH0 HIn).
    destruct ABR as (B0 & B16 & Bn & BI & BC & BF & BAPP).
    pose proof VEC as (_ & _ & _ & _ & Hb' & _).
    destruct Hb' as [[E _]|(_ & _ & _ & _ & _ & D)]; [contradiction|].
    assert (DS : v + 24 <= sh b \/ sh b + nsh (4 * cap) <= v).
    { apply v4_app_sh; [lia | lia | lia | destruct VBAND; [left | right]; lia]. }
    lia. }
  destruct OBJ as (_ & _ & WO & _ & _ & _).
  pose proof (aclient_write_ok_sub H LB v (v + 24) (v + 8) (v + 16) WO ltac:(lia) ltac:(lia)) as W8.
  unfold aclient_write_ok in W8 |- *. cbn [fst snd] in W8 |- *.
  destruct W8 as [K|[K|[(bb & Hb & L1 & L2)|[(bb & Hb & L1 & L2)|[K|[K|K]]]]]].
  - left. exact K.
  - right; left. exact K.
  - right; right; left. exists bb. split; [apply KEEP; [exact Hb | left; lia] | lia].
  - right; right; right; left. exists bb. split; [apply KEEP; [exact Hb | right; lia] | lia].
  - right; right; right; right; left. exact K.
  - right; right; right; right; right; left. exact K.
  - right; right; right; right; right; right. exact K.
Qed.

  Lemma vt_s3 : forall (msF2 : machine_state) (mo2 : Model) (sk2 : as_St H) (m2 : mem) (R2 : bvmap 5 word)
                       (LB' : list block) (b' : Z) (e2 : word),
    as_VIS H sk2 msF2 = MS R2 F (Z_to_bv 64 VOT_SRET) fc None m2 (seg_rom asegs) -> rfull R2 ->
    getr R2 2 = Z_to_bv 64 (spz - 64) -> getr R2 3 = gp -> getr R2 4 = tp -> getr R2 8 = Z_to_bv 64 (v + 8) ->
    getr R2 10 = Z_to_bv 64 (b' + 4 * (cap + 1)) -> getr R2 19 = Z_to_bv 64 (sh (v + 8)) -> getr R2 20 = Z_to_bv 64 ASHADOW_BASE ->
    getr R2 22 = s6 -> getr R2 23 = s7 -> getr R2 24 = s8 -> getr R2 25 = s9 -> getr R2 26 = s10 -> getr R2 27 = s11 ->
    as_AKREL H sk2 (mkCfg msF2 mo2) -> as_MPRES H mo mo2 ->
    Zlen xs = cap -> rw_cells asegs m2 (spz - 56) FRAME ->
    mem_inv asegs m2 -> stk asegs m2 lo spz -> rw_cells asegs m2 (errno_addr tp) [C4 e2] -> as_rauxv_ok H m2 B ->
    xpres H LB spz ((v, v + 24) :: v4_oldx b (4 * cap)) m m2 ->
    (exists pid', LB' = v4_newLB H LB b pid pid' b' (4 * v4_newcap cap) /\ ablock_range H b' (4 * v4_newcap cap)) ->
    as_RHEAP H sk2 LB' m2 -> vec32A LB' m2 v b' (xs ++ [x]) (v4_newcap cap) ->
    SHAD m2 b' (cc_gen (4 * v4_newcap cap) (4 * (cap + 1))) -> addressable m2 v 24 -> wr_at asegs m2 v 24 -> lb_own LB' m2 ->
    as_RFS H LF m2 -> ACONST m2 -> stack0 m2 lo shi ->
    as_AL H sk2 >= as_AL H s - (as_Cm H (4 * v4_newcap cap) + as_Cf H (4 * cap)) ->
    as_SR H Q (mkCfg msF2 mo2).
Proof.
Proof.
  intros msF2 mo2 sk2 m2 R2 LB' b' e2 VIS2 HF2 G2 G3 G4 G8 G10 G19 G20 G22 G23 G24 G25 G26 G27 KR2 MP2 XSL FR2
    MI2 ST2 ERR2 RA2 XP2 NEW RH2 VEC2 SH2 ADV2 WV2 OW2 RF2 AC2 S02 AL2.
  pose proof SPR as (SPL & SPH & SP16). pose proof LOR as [LO1 LO2].
  unfold VOT_PB_STACK, V4_STACK, AOPNEW_STACK, AMALLOC_STACK in LO2.
  pose proof aceil_facts as ((ACF1 & ACF2) & ACF3 & ACF4).
  pose proof (v4_newcap_ge cap) as NCG.
  pose proof vt_facts as (_ & _ & _ & _ & XL & _).
  pose proof NEW as (pid' & ELB & (A0 & A16 & An & AI & AC & AF & AAPP)).
  pose proof VEC2 as (Hv & Hv' & HD & Hlen & Hb & _).
  rewrite Zlen_app1 in Hlen.
  destruct Hb as [[E1 E2]|(B0 & B16 & C0 & BC & _ & DB)]; [lia|].
  assert (VB : 0 <= v /\ v + 24 <= 2 ^ 47) by (destruct VBAND; lia).
  destruct OBJ as (_ & _ & WO & FW & CO & SD).
  assert (VSD : v + 24 <= spz - 64 \/ spz - 64 + 64 <= v) by lia.
  assert (ADV8 : LbB_Kit.shk m2 (v + 8) 0).
  { eapply sh0_of_addressable; [exact ADV2 | change (8 * (24 / 8)) with 24; lia]. }
  assert (EM : (b' + 4 * (cap + 1)) mod 4 = 0) by (Z.div_mod_to_equations; lia).
  destruct (vt_P3_ok R2 F fc m2 v (spz - 64) (b' + 4 * (cap + 1)) s5 s4 s3 s2 s1 s0 ra G2 G8 G10 G19 G20
              ltac:(replace (spz - 64 + 8) with (spz - 56) by lia; exact FR2) ADV8
              (vt_wr_sub m2 v 24 (v + 8) 8 WV2 ltac:(lia) ltac:(lia) ltac:(lia))
              ltac:(lia) ltac:(lia) ltac:(destruct VBAND; lia) ltac:(lia) VSD ltac:(lia) EM)
    as (R' & M3 & Hms & MU3 & WM3 & CW3 & K1 & K2 & K8 & K9 & K18 & K19 & K20 & K21 & KK).
  pose proof (msteps_full asegs _ _ Hms HF2) as HF3. cbn [ms_regs] in HF3.
  assert (MI3 : mem_inv asegs M3) by exact (msteps_mem_inv asegs _ _ Hms MI2).
  assert (ST3 : stk asegs M3 lo spz) by (apply (stk_high_transport m2 M3 lo spz ST2 WM3); unfold AIMG_TOP; lia).
  assert (ERR3 : rw_cells asegs M3 (errno_addr tp) [C4 e2]).
  { eapply rw_cells_transport; [exact ERR2 | exact MU3 | exact WM3 |]. rewrite TPV. rewrite u64_of_Z by (unfold ATP; lia).
    cbn. unfold ATP. split; [destruct VBAND; lia | exact I]. }
  pose proof (ah_nodup H HH _ _ _ RH0) as ND.
  assert (AWO : aclient_write_ok H LB' (v + 8, v + 16)).
  { apply vt_awo_new.
    - intros E bb Hb. rewrite ELB. right. unfold v4_newLB. rewrite E, Z.eqb_refl. exact Hb.
    - intros NE bb Hb Hid. rewrite ELB. right. unfold v4_newLB. rewrite (proj2 (Z.eqb_neq _ _) NE).
      eapply lb_remove_keep; eauto. }
  destruct (client_frame H HH sk2 LB' LF B [(v + 8, v + 16)] m2 M3 RH2 RF2 AC2 RA2 MU3 WM3
              ltac:(apply Forall_cons; [exact AWO | apply Forall_nil])
              ltac:(apply Forall_cons; [exact (afs_write_ok_sub H LF v (v + 24) (v + 8) (v + 16) FW ltac:(lia) ltac:(lia)) | apply Forall_nil])
              ltac:(apply Forall_cons; [exact (aconst_ok_sub v (v + 24) (v + 8) (v + 16) CO ltac:(lia) ltac:(lia)) | apply Forall_nil]))
    as (RH3 & RF3 & AC3 & RA3).
  assert (VEC3 : vec32A LB' M3 v b' (xs ++ [x]) (v4_newcap cap)).
  { eapply vec32A_set_end; [exact VEC2 | unfold AIMG_TOP; destruct VBAND; lia | exact MU3 |].
    rewrite Zlen_app1, XSL. exact CW3. }
  assert (SH3 : SHAD M3 b' (cc_gen (4 * v4_newcap cap) (4 * (Zlen xs + 1)))).
  { rewrite XSL. eapply SHAD_transport; [exact SH2 | exact MU3 | exact WM3 |]. rewrite cc_gen_length by lia.
    pose proof (v4_app_sh (v + 8) 8 b' (4 * v4_newcap cap) ltac:(lia) ltac:(lia) ltac:(lia)
                  ltac:(destruct VBAND; [left | right]; lia)) as DS.
    cbn [disjoint_from]. split; [lia | exact I]. }
  assert (ADV3 : addressable M3 v 24).
  { destruct ADV2 as [Z24 SHv]. split; [exact Z24|].
    eapply SHAD_transport; [exact SHv | exact MU3 | exact WM3 |]. rewrite shadow_of_length by lia.
    pose proof (v4_app_sh (v + 8) 8 v 24 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(destruct VBAND; [left | right]; lia)) as DS.
    cbn [disjoint_from]. split; [lia | exact I]. }
  assert (S03 : stack0 M3 lo shi).
  { eapply stack0_transport; [exact S02 | exact MU3 | exact WM3 |].
    apply Forall_cons; [|apply Forall_nil]. unfold stack0_ok. cbn [fst snd].
    destruct VBAND as [VL|VH]; [right; unfold sh, ASHADOW_BASE; Z.div_mod_to_equations; lia | left; unfold AHI_LO; lia]. }
  assert (XP3 : xpres H LB spz ((v, v + 24) :: v4_oldx b (4 * cap)) m M3).
  { eapply (xpres_trans H); [exact XP2 |].
    eapply (xpres_of_munch H s LB spz _ [(v + 8, v + 16)] m m2 M3); [exact HH | exact RH0 | exact MU3 | exact WM3 |].
    apply Forall_cons; [|apply Forall_nil]. right. intros a Ha. cbn [fst snd] in Ha. cbn [rin_ivs fst snd]. left. lia. }
  eapply (sr_blk H HH); [exact KR2 | exact VIS2 | exact HF2 | exact Hms |].
  intros msF3 mo3 KR3 MP3 VIS3. rewrite <- (rfull_eq R' HF3) in VIS3.
  eapply (vt_end msF3 mo3 sk2 M3 R' LB' b' (v4_newcap cap) e2 VIS3 HF3).
  - exact K1.
  - rewrite K2, vt_spz_sp. unfold wz. f_equal. lia.
  - rewrite (KK 3%bv ltac:(inb)). exact G3.
  - rewrite (KK 4%bv ltac:(inb)). exact G4.
  - exact K8.
  - exact K9.
  - exact K18.
  - exact K19.
  - exact K20.
  - exact K21.
  - rewrite (KK 22%bv ltac:(inb)). exact G22.
  - rewrite (KK 23%bv ltac:(inb)). exact G23.
  - rewrite (KK 24%bv ltac:(inb)). exact G24.
  - rewrite (KK 25%bv ltac:(inb)). exact G25.
  - rewrite (KK 26%bv ltac:(inb)). exact G26.
  - rewrite (KK 27%bv ltac:(inb)). exact G27.
  - exact KR3.
  - eapply (ah_mpres_trans H HH); [exact MP2 | exact MP3].
  - exact MI3.
  - exact ST3.
  - exact ERR3.
  - exact RA3.
  - exact VEC3.
  - exact RH3.
  - exact SH3.
  - exact ADV3.
  - exact (wr_at_transport asegs _ _ _ _ WV2 WM3).
  - exact (lb_own_wmono _ _ _ OW2 WM3).
  - right. split; [exact XSL|]. split; [reflexivity|]. split; [exact NEW|]. split; [exact XP3 | exact AL2].
  - exact RF3.
  - exact AC3.
  - exact S03.
Qed.

  Lemma vt_after_frame : forall m1, munch [(spz - 56, spz)] m m1 -> wmono asegs m m1 -> rw_cells asegs m1 (spz - 56) FRAME ->
    as_RHEAP H s LB m1 /\ as_RFS H LF m1 /\ ACONST m1 /\ as_rauxv_ok H m1 B /\ stk asegs m1 lo spz /\ stack0 m1 lo shi
    /\ xpres H LB spz [] m m1 /\ lb_own LB m1 /\ vec32A LB m1 v b xs cap /\ addressable m1 v 24 /\ wr_at asegs m1 v 24
    /\ (0 < cap -> SHAD m1 b (cc_gen (4 * cap) (4 * Zlen xs))).
Proof.
Proof.
  intros m1 MU WM FR.
  pose proof SPR as (SPL & SPH & SP16). pose proof LOR as [LO1 LO2].
  unfold VOT_PB_STACK, V4_STACK, AOPNEW_STACK, AMALLOC_STACK in LO2.
  pose proof aceil_facts as ((ACF1 & ACF2) & ACF3 & ACF4).
  pose proof (ah_fsb H HH _ _ _ RH0) as (FS1 & FS2 & FS3 & FS4).
  destruct (stack_window_ok H LB LF (spz - 56) spz ltac:(lia) FS2) as (SW1 & SW2 & SW3).
  destruct (client_frame H HH s LB LF B [(spz - 56, spz)] m m1 RH0 RF0 AC0 RA0 MU WM
              ltac:(apply Forall_cons; [exact SW1 | apply Forall_nil]) ltac:(apply Forall_cons; [exact SW2 | apply Forall_nil])
              ltac:(apply Forall_cons; [exact SW3 | apply Forall_nil]))
    as (RH1 & RF1 & AC1 & RA1).
  pose proof vt_facts as (F0 & F1 & F2 & FE & XL & OB & DJ & MD).
  assert (VB : 0 <= v /\ v + 24 <= 2 ^ 47) by (destruct VBAND; lia).
  split; [exact RH1|]. split; [exact RF1|]. split; [exact AC1|]. split; [exact RA1|].
  split; [apply (stk_high_transport m m1 lo spz ST0 WM); unfold AIMG_TOP; lia|].
  split; [eapply stack0_transport; [exact S00 | exact MU | exact WM |];
          apply Forall_cons; [left; cbn [fst]; unfold AHI_LO; lia | apply Forall_nil]|].
  split; [eapply (xpres_of_munch H s LB spz [] [(spz - 56, spz)] m m m1); [exact HH | exact RH0 | exact MU | exact WM |];
          apply Forall_cons; [left; cbn [fst snd]; lia | apply Forall_nil]|].
  split; [exact (lb_own_wmono _ _ _ OWN WM)|].
  split.
  { eapply vec32A_munch; [exact VEC | exact MU | |].
    - destruct OBJ as (_ & _ & _ & _ & _ & SD). cbn [disjoint_from]. split; [lia | exact I].
    - cbn [disjoint_from]. split; [|exact I].
      destruct OB as [[E1 E2]|(Hc & HIn & (B0 & B16 & Bn & BI & BC & BF & BAPP))]; lia. }
  split.
  { destruct ADV0 as [A0 SH]. split; [exact A0|].
    eapply SHAD_transport; [exact SH | exact MU | exact WM |]. rewrite shadow_of_length by lia.
    pose proof (sh_nsh_high v 24 ltac:(lia) ltac:(lia) ltac:(unfold AAPP_HI; lia)) as SHV. unfold AHI_LO in SHV.
    cbn [disjoint_from]. split; [lia | exact I]. }
  split; [exact (wr_at_transport asegs _ _ _ _ VWR WM)|].
  intros Hc.
  destruct OB as [[E1 E2]|(_ & HIn & (B0 & B16 & Bn & BI & BC & BF & BAPP))]; [lia|].
  eapply SHAD_transport; [exact (OLDSH Hc) | exact MU | exact WM |]. rewrite cc_gen_length by lia.
  pose proof (sh_nsh_high b (4 * cap) ltac:(lia) ltac:(lia) ltac:(unfold AAPP_HI; lia)) as SHB. unfold AHI_LO in SHB.
  cbn [disjoint_from]. split; [lia | exact I].
Qed.

  Lemma vt_sl : forall (msF1 : machine_state) (mo1 : Model) (m1 : mem) (R1 : bvmap 5 word) (e1 : word),
    Zlen xs = cap ->
    as_VIS H s msF1 = MS R1 F (Z_to_bv 64 0xfb3d4) fc None m1 (seg_rom asegs) -> rfull R1 ->
    getr R1 1 = Z_to_bv 64 VOT_SRET -> getr R1 2 = Z_to_bv 64 (spz - 64) -> getr R1 3 = gp -> getr R1 4 = tp ->
    getr R1 8 = Z_to_bv 64 (v + 8) -> getr R1 10 = Z_to_bv 64 v -> getr R1 11 = Z_to_bv 64 src ->
    getr R1 19 = Z_to_bv 64 (sh (v + 8)) -> getr R1 20 = Z_to_bv 64 ASHADOW_BASE ->
    getr R1 22 = s6 -> getr R1 23 = s7 -> getr R1 24 = s8 -> getr R1 25 = s9 -> getr R1 26 = s10 -> getr R1 27 = s11 ->
    as_AKREL H s (mkCfg msF1 mo1) -> as_MPRES H mo mo1 ->
    munch [(spz - 56, spz)] m m1 -> wmono asegs m m1 -> rw_cells asegs m1 (spz - 56) FRAME ->
    mem_inv asegs m1 -> rw_cells asegs m1 (errno_addr tp) [C4 e1] ->
    as_SR H Q (mkCfg msF1 mo1).
Proof.
Proof.
  intros msF1 mo1 m1 R1 e1 XSL VIS1 HF1 G1 G2 G3 G4 G8 G10 G11 G19 G20 G22 G23 G24 G25 G26 G27 KR1 MP1 MU1 WM1 FR1 MI1 ERR1.
  pose proof SPR as (SPL & SPH & SP16). pose proof LOR as [LO1 LO2].
  unfold VOT_PB_STACK, V4_STACK, AOPNEW_STACK, AMALLOC_STACK in LO2.
  pose proof aceil_facts as ((ACF1 & ACF2) & ACF3 & ACF4).
  destruct (vt_after_frame m1 MU1 WM1 FR1) as (RH1 & RF1 & AC1 & RA1 & ST1 & S01 & XP1 & OW1 & VEC1 & ADV1 & WV1 & SH1).
  pose proof vt_facts as (_ & _ & _ & _ & XL & OB & DJ & MD).
  assert (VB : 0 <= v /\ v + 24 <= 2 ^ 47) by (destruct VBAND; lia).
  assert (SP64 : bv_unsigned (Z_to_bv 64 (spz - 64)) = spz - 64) by (rewrite u64_of_Z by lia; reflexivity).
  destruct (SLOWOK XSL) as [AOK CM].
  pose proof (v4slow_fa4fc H HH) as SL. unfold v4slow_stmt in SL.
  rewrite (rfull_eq R1 HF1) in VIS1.
  specialize (SL _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc msF1 m1 mo1 s LB LF v b cap src x xs pid lo B shi e1
                 VIS1 G10 G11).
  rewrite G1, G2, G3, G4, G8, G19, G20, G22, G23, G24, G25, G26, G27, SP64 in SL.
  assert (OBJ' : obj_win H LB LF (spz - 64) lo v 24).
  { destruct OBJ as (C1 & C2 & C3 & C4 & C5 & C6).
    split; [destruct C1 as [K|K]; [left; lia | right; exact K]|].
    split; [destruct C2 as [K|K]; [left; lia | right; exact K]|].
    split; [exact C3|]. split; [exact C4|]. split; [exact C5|]. lia. }
  assert (SRC4 : src4_keep H LB (spz - 64) m1 src x).
  { intros m' AC' MI' AP'. apply SRC; [exact AC' | exact MI' |].
    eapply (xpres_trans H).
    - eapply (xpres_weaken H); [exact XP1 | lia | intros bb Hb; exact Hb | intros a Ha; destruct Ha].
    - eapply (xpres_weaken H); [exact (xpres_of_apres H _ _ [] _ _ AP') | lia | intros bb Hb; exact Hb | intros a Ha; destruct Ha]. }
  assert (STs : stk asegs m1 lo (spz - 64) /\ stk asegs m1 (spz - 64) spz) by (apply (stk_split asegs); [exact ST1 | lia]).
  destruct STs as [STa STb].
  eapply (ah_seq H HH).
  { apply SL; try assumption.
    - intros Hc. pose proof (SH1 Hc) as K. rewrite XSL in K. exact K.
    - exact (GROW XSL).
    - exact (proj1 SRCR).
    - exact (proj1 (proj2 SRCR)).
    - exact (proj2 (proj2 SRCR)).
    - lia.
    - exact (v4_mod16_sub64 spz SP16).
    - lia.
    - unfold V4_STACK, AOPNEW_STACK, AMALLOC_STACK. lia.
    - rewrite u64_of_Z by (unfold VOT_SRET; lia). unfold VOT_SRET. reflexivity.
    - lia. }
  intros c2 POST. destruct c2 as [msF2 mo2].
  destruct POST as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m2 & errv2 & s2' & pid' & b'
                    & VIS2 & KR2 & MP2 & MI2 & ST2 & ERR2 & RA2 & XP2 & ABR & RH2 & VEC2 & SH2 & ADV2 & WV2 & OW2 & RF2 & AC2 & S02 & AL2).
  cbn [cfg_ms cfg_model] in VIS2, KR2, MP2.
  rewrite (ret_pc_even VOT_SRET ltac:(unfold VOT_SRET; lia) ltac:(unfold VOT_SRET; reflexivity)) in VIS2.
  rewrite ?SP64 in ST2, XP2.
  assert (XO : Forall (fun iv : Z * Z => spz <= fst iv \/ snd iv <= spz - 64) ((v, v + 24) :: v4_oldx b (4 * cap))).
  { apply Forall_cons; [cbn [fst snd]; destruct OBJ as (_ & _ & _ & _ & _ & SD); lia|].
    unfold v4_oldx. destruct (Z.eqb_spec b 0) as [E|NE]; [apply Forall_nil|].
    destruct OB as [[E1 E2]|(Hc & HIn & (B0 & B16 & Bn & BI & BC & BF & BAPP))]; [contradiction|].
    pose proof (sh_nsh_high b (4 * cap) ltac:(lia) ltac:(lia) ltac:(unfold AAPP_HI; lia)) as SHB. unfold AHI_LO in SHB.
    apply Forall_cons; [cbn [fst snd]; lia | apply Forall_cons; [cbn [fst snd]; lia | apply Forall_nil]]. }
  assert (ST2' : stk asegs m2 lo spz).
  { eapply (stk_merge asegs); [exact ST2 | | lia]. eapply (xpres_stk H); [exact XP2 | exact STb | lia | exact XO]. }
  assert (FR2 : rw_cells asegs m2 (spz - 56) FRAME).
  { eapply (xpres_rw_cells H); [exact XP2 | exact FR1 |]. split.
    - left. lia.
    - eapply Forall_impl; [|exact XO]. intros [l h] Hlh. cbn [fst snd] in *. unfold FRAME.
      rewrite v4_cells_size_map_C8'. cbn [length Z.of_nat Pos.of_succ_nat Pos.succ]. lia. }
  assert (XP2' : xpres H LB spz ((v, v + 24) :: v4_oldx b (4 * cap)) m m2).
  { eapply (xpres_trans H).
    - eapply (xpres_weaken H); [exact XP1 | lia | intros bb Hb; exact Hb | intros a Ha; destruct Ha].
    - eapply (xpres_weaken H); [exact XP2 | lia | intros bb Hb; exact Hb | intros a Ha; exact Ha]. }
  eapply (vt_s3 msF2 mo2 s2' m2 _ (v4_newLB H LB b pid pid' b' (4 * v4_newcap cap)) b' errv2 VIS2
            (rfull_mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)).
  all: try reflexivity.
  - exact KR2.
  - eapply (ah_mpres_trans H HH); [exact MP1 | exact MP2].
  - exact XSL.
  - exact FR2.
  - exact MI2.
  - exact ST2'.
  - exact ERR2.
  - exact RA2.
  - exact XP2'.
  - exists pid'. split; [reflexivity | exact ABR].
  - exact RH2.
  - exact VEC2.
  - exact SH2.
  - exact ADV2.
  - exact WV2.
  - exact OW2.
  - exact RF2.
  - exact AC2.
  - exact S02.
  - exact AL2.
Qed.

  Lemma vt_f2 : forall (msF2 : machine_state) (mo2 : Model) (m2 : mem) (R2 : bvmap 5 word) (e2 : word),
    Zlen xs < cap ->
    as_VIS H s msF2 = MS R2 F (Z_to_bv 64 VOT_FRET) fc None m2 (seg_rom asegs) -> rfull R2 ->
    getr R2 2 = Z_to_bv 64 (spz - 64) -> getr R2 3 = gp -> getr R2 4 = tp -> getr R2 8 = Z_to_bv 64 (v + 8) ->
    getr R2 9 = Z_to_bv 64 (b + 4 * Zlen xs + 4) -> getr R2 18 = Z_to_bv 64 (b + 4 * Zlen xs) ->
    getr R2 19 = Z_to_bv 64 (sh (v + 8)) -> getr R2 20 = Z_to_bv 64 ASHADOW_BASE -> getr R2 21 = Z_to_bv 64 src ->
    getr R2 22 = s6 -> getr R2 23 = s7 -> getr R2 24 = s8 -> getr R2 25 = s9 -> getr R2 26 = s10 -> getr R2 27 = s11 ->
    as_AKREL H s (mkCfg msF2 mo2) -> as_MPRES H mo mo2 ->
    rw_cells asegs m2 (spz - 56) FRAME ->
    mem_inv asegs m2 -> stk asegs m2 lo spz -> rw_cells asegs m2 (errno_addr tp) [C4 e2] -> as_rauxv_ok H m2 B ->
    as_RHEAP H s LB m2 -> as_RFS H LF m2 -> ACONST m2 -> stack0 m2 lo shi -> lb_own LB m2 ->
    xpres H LB spz [(sh b, sh b + nsh (4 * cap))] m m2 -> SHAD m2 b (cc_gen (4 * cap) (4 * Zlen xs + 4)) ->
    as_SR H Q (mkCfg msF2 mo2).
Proof.
Proof.
  intros msF2 mo2 m2 R2 e2 XLT VIS2 HF2 G2 G3 G4 G8 G9 G18 G19 G20 G21 G22 G23 G24 G25 G26 G27 KR2 MP2 FR2
    MI2 ST2 ERR2 RA2 RH2 RF2 AC2 S02 OW2 XP2 SH2.
  pose proof SPR as (SPL & SPH & SP16). pose proof LOR as [LO1 LO2].
  unfold VOT_PB_STACK, V4_STACK, AOPNEW_STACK, AMALLOC_STACK in LO2.
  pose proof aceil_facts as ((ACF1 & ACF2) & ACF3 & ACF4).
  pose proof vt_facts as (F0 & F1 & F2 & FE & XL & OB & DJ & MD).
  destruct OB as [[E1 E2]|(Hc & HIn & (B0 & B16 & Bn & BI & BC & BF & BAPP))]; [lia|].
  assert (NZ : b <> 0) by lia.
  specialize (DJ NZ).
  assert (VB : 0 <= v /\ v + 24 <= 2 ^ 47) by (destruct VBAND; lia).
  assert (VAI : AIMG_TOP <= v) by (unfold AIMG_TOP; destruct VBAND; lia).
  pose proof OBJ as (CL & CLS & WO & FW & CO & SD).
  assert (VSD : v + 24 <= spz - 64 \/ spz - 64 + 64 <= v) by lia.
  clear SD. vhide BF.
  assert (B8 : b mod 8 = 0) by exact (v4_mod16_8 b B16).
  assert (B4 : b mod 4 = 0). { clear - B16. Z.div_mod_to_equations. lia. }
  assert (DVB : v + 24 <= sh b \/ sh b + nsh (4 * cap) <= v).
  { apply v4_app_sh; [lia | lia | lia | destruct VBAND; [left | right]; lia]. }
  assert (DV8 : v + 16 <= sh v \/ sh v + nsh 24 <= v + 8).
  { pose proof (v4_app_sh (v + 8) 8 v 24 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(destruct VBAND; [left | right]; lia)) as K. lia. }
  vhide VBAND.
  assert (DBB : b + 4 * cap <= sh b \/ sh b + nsh (4 * cap) <= b).
  { apply v4_app_sh; [lia | lia | lia | destruct (vt_band_of_aapp _ _ BAPP); [left | right]; lia]. }
  assert (DSV : sh v + nsh 24 <= sh b \/ sh b + nsh (4 * cap) <= sh v).
  { apply v4_sh_apart; [lia | lia | exact V8 | exact B8 | lia | lia | lia]. }
  assert (DJ4 : v + 24 <= b + 4 * Zlen xs \/ b + 4 * Zlen xs + 4 <= v) by lia.
  vhide DJ. vhide DSV.
  assert (XCV : xclient_range H LB spz [(sh b, sh b + nsh (4 * cap))] v 24).
  { split; [exact CL|]. apply Forall_cons; [cbn [fst snd]; lia | apply Forall_nil]. }
  vhide DVB.
  assert (XCB : xclient_range H LB spz [(sh b, sh b + nsh (4 * cap))] b (4 * cap)).
  { split; [right; right; left; exists (pid, b, 4 * cap); split; [exact HIn | cbn [blk_addr blk_size fst snd]; lia]|].
    apply Forall_cons; [cbn [fst snd]; lia | apply Forall_nil]. }
  vhide DBB.
  assert (F0' : fldA m2 v 8 b).
  { eapply fld_xpres; [exact XP2 | exact (xcl_sub H LB spz _ v 24 v 8 XCV ltac:(lia) ltac:(lia) ltac:(lia)) | lia
                      | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | exact F0]. }
  assert (F2' : fldA m2 (v + 16) 8 (b + 4 * cap)).
  { eapply fld_xpres; [exact XP2 | exact (xcl_sub H LB spz _ v 24 (v + 16) 8 XCV ltac:(lia) ltac:(lia) ltac:(lia)) | lia
                      | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | exact F2]. }
  assert (FE' : forall i, 0 <= i < Zlen xs -> fldA m2 (b + 4 * i) 4 (Znth i xs)).
  { intros i Hi. eapply fld_xpres; [exact XP2 | exact (xcl_sub H LB spz _ b (4 * cap) (b + 4 * i) 4 XCB ltac:(lia) ltac:(lia) ltac:(lia))
                                   | lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | exact (proj2 (FE i Hi))]. }
  assert (MD2 : mdef m2 v 24).
  { intros i Hi. destruct (XP2 (v + i) ltac:(lia) (xclient_range_addr H LB spz _ v 24 (v + i) XCV ltac:(lia))) as [E _].
    unfold wa in E. rewrite E. exact (MD i Hi). }
  assert (ADV2 : addressable m2 v 24).
  { destruct ADV0 as [Z24 (S0 & S8 & [UB UW])]. split; [exact Z24|]. split; [exact S0|]. split; [exact S8|].
    assert (XCS : xclient_range H LB spz [(sh b, sh b + nsh (4 * cap))] (sh v) (Z.of_nat (length (shadow_of 24)))).
    { rewrite shadow_of_length by lia. split; [exact CLS|]. vuse DSV. apply Forall_cons; [cbn [fst snd]; lia | apply Forall_nil]. }
    split; [eapply (xpres_bytes_at H); [exact XP2 | exact UB | exact XCS] | eapply (xpres_wr_at H); [exact XP2 | exact UW | exact XCS]]. }
  assert (WV2 : wr_at asegs m2 v 24) by (eapply (xpres_wr_at H); [exact XP2 | exact VWR | exact XCV]).
  assert (XPS : xpres H LB spz (if b =? 0 then [] else [(sh b, sh b + nsh (4 * cap))]) m m2).
  { rewrite (proj2 (Z.eqb_neq b 0) NZ). exact XP2. }
  destruct (SRC m2 AC2 MI2 XPS) as (FX & ACC).
  destruct (v4_src_shk m2 src ACC (proj1 SRCR) (proj1 (proj2 SRCR))) as (k & SK & KRg).
  destruct (vt_slot_shk m2 b cap (Zlen xs) SH2 B16 ltac:(lia) ltac:(lia) XLT) as (j & SJ & JRg).
  assert (ADV8 : LbB_Kit.shk m2 (v + 8) 0).
  { eapply sh0_of_addressable; [exact ADV2 | change (8 * (24 / 8)) with 24; lia]. }
  assert (WB : wr_at asegs m2 b (4 * cap)).
  { pose proof (proj1 (Forall_forall _ _) OW2 _ HIn) as WB. cbn [blk_addr blk_size fst snd] in WB. exact WB. }
  destruct (vt_P2_ok R2 F fc m2 v (spz - 64) b (Zlen xs) src x k j s5 s4 s3 s2 s1 s0 ra G2 G8 G9 G18 G19 G20 G21
              ltac:(replace (spz - 64 + 8) with (spz - 56) by lia; exact FR2) FX SK KRg SJ JRg ADV8
              (vt_wr_sub m2 b (4 * cap) (b + 4 * Zlen xs) 4 WB ltac:(lia) ltac:(lia) ltac:(lia))
              (vt_wr_sub m2 v 24 (v + 8) 8 WV2 ltac:(lia) ltac:(lia) ltac:(lia))
              ltac:(lia) ltac:(lia) ltac:(vuse VBAND; destruct VBAND0; lia) ltac:(lia) VSD (v4_mod16_16le b B0 B16) B4 ltac:(lia) ltac:(lia)
              DJ4 ltac:(destruct (vt_band_of_aapp _ _ BAPP); lia) (proj1 (proj2 SRCR)) (proj2 (proj2 SRCR)) (proj1 SRCR) XR)
    as (R' & M3 & Hms & MU3 & WM3 & CV3 & CX3 & K1 & K2 & K8 & K9 & K18 & K19 & K20 & K21 & KK).
  clear SK KRg SJ JRg VSD.
  pose proof (msteps_full asegs _ _ Hms HF2) as HF3. cbn [ms_regs] in HF3.
  assert (MI3 : mem_inv asegs M3) by exact (msteps_mem_inv asegs _ _ Hms MI2).
  assert (ST3 : stk asegs M3 lo spz) by (apply (stk_high_transport m2 M3 lo spz ST2 WM3); unfold AIMG_TOP; lia).
  assert (ERR3 : rw_cells asegs M3 (errno_addr tp) [C4 e2]).
  { eapply rw_cells_transport; [exact ERR2 | exact MU3 | exact WM3 |]. rewrite TPV. rewrite u64_of_Z by (unfold ATP; lia).
    cbn. unfold AIMG_TOP, ATP in *. split; [lia | split; [lia | exact I]]. }
  assert (W1 : aclient_write_ok H LB (b + 4 * Zlen xs, b + 4 * Zlen xs + 4)).
  { right; right; left. exists (pid, b, 4 * cap). split; [exact HIn | cbn [blk_addr blk_size fst snd]; lia]. }
  assert (W2 : afs_write_ok H LF (b + 4 * Zlen xs, b + 4 * Zlen xs + 4)).
  { left. cbn [fst snd]. vuse BF. unfold AIMG_TOP in BI. split; [lia | unfold ATLS_PRIV_HI, ATP; lia]. }
  assert (W3 : aconst_ok (b + 4 * Zlen xs, b + 4 * Zlen xs + 4)) by (eapply aconst_ok_app; [exact BAPP | lia | lia]).
  destruct (client_frame H HH s LB LF B [(v + 8, v + 16); (b + 4 * Zlen xs, b + 4 * Zlen xs + 4)] m2 M3 RH2 RF2 AC2 RA2 MU3 WM3
              ltac:(apply Forall_cons; [exact (aclient_write_ok_sub H LB v (v + 24) (v + 8) (v + 16) WO ltac:(lia) ltac:(lia))
                                       | apply Forall_cons; [exact W1 | apply Forall_nil]])
              ltac:(apply Forall_cons; [exact (afs_write_ok_sub H LF v (v + 24) (v + 8) (v + 16) FW ltac:(lia) ltac:(lia))
                                       | apply Forall_cons; [exact W2 | apply Forall_nil]])
              ltac:(apply Forall_cons; [exact (aconst_ok_sub v (v + 24) (v + 8) (v + 16) CO ltac:(lia) ltac:(lia))
                                       | apply Forall_cons; [exact W3 | apply Forall_nil]]))
    as (RH3 & RF3 & AC3 & RA3).
  assert (AG : forall a k z, 0 <= a -> a + Z.of_nat k < 2 ^ 64 -> (a + Z.of_nat k <= v + 8 \/ v + 16 <= a) ->
            (a + Z.of_nat k <= b + 4 * Zlen xs \/ b + 4 * Zlen xs + 4 <= a) -> fldA m2 a k z -> fldA M3 a k z).
  { intros a k' z Ha0 Ha1 Ha2 Ha3 Hf. unfold fldA in *. eapply fld_agree; [exact Ha0 | exact Ha1 | exact Hf |].
    intros a' Ha'. unfold zwin in Ha'. apply MU3. rewrite u64_of_Z by lia. cbn [outside]. split; [lia | split; [lia | exact I]]. }
  assert (MD3 : mdef M3 v 24).
  { pose proof (mdef_of_rw_cells_hi _ _ _ CV3 ltac:(unfold AIMG_TOP in *; lia)) as MDc. cbn [cells_size csize] in MDc.
    intros i Hi. destruct (Z_lt_le_dec i 8) as [L|L]; [|destruct (Z_lt_le_dec i 16) as [L'|L']].
    - rewrite (MU3 (Z_to_bv 64 (v + i))); [apply MD2; lia|]. rewrite u64_of_Z by lia. cbn [outside]. split; [lia | split; [lia | exact I]].
    - replace (v + i) with (v + 8 + (i - 8)) by lia. apply MDc. lia.
    - rewrite (MU3 (Z_to_bv 64 (v + i))); [apply MD2; lia|]. rewrite u64_of_Z by lia. cbn [outside]. split; [lia | split; [lia | exact I]]. }
  assert (VEC3 : vec32A LB M3 v b (xs ++ [x]) cap).
  { eapply vec32A_push; [exact VEC | exact XLT | exact MD3 | | | | | | lia].
    - apply AG; [lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia
                | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | exact F0'].
    - replace (b + 4 * (Zlen xs + 1)) with (b + 4 * Zlen xs + 4) by lia. apply fld_of_rw_cells8; [exact CV3 | lia].
    - apply AG; [lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia
                | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | exact F2'].
    - intros i Hi. vuse DJ. apply AG; [lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia
                             | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | exact (FE' i Hi)].
    - apply fld_of_rw_cells4; [exact CX3 | lia]. }
  assert (SH3 : SHAD M3 b (cc_gen (4 * cap) (4 * (Zlen xs + 1)))).
  { replace (4 * (Zlen xs + 1)) with (4 * Zlen xs + 4) by lia.
    eapply SHAD_transport; [exact SH2 | exact MU3 | exact WM3 |]. rewrite cc_gen_length by lia.
    vuse DVB. vuse DBB. cbn [disjoint_from]. split; [lia | split; [lia | exact I]]. }
  assert (ADV3 : addressable M3 v 24).
  { destruct ADV2 as [Z24 SHv]. split; [exact Z24|].
    eapply SHAD_transport; [exact SHv | exact MU3 | exact WM3 |]. rewrite shadow_of_length by lia.
    pose proof (v4_app_sh b (4 * cap) v 24 ltac:(lia) ltac:(lia) ltac:(lia)
                  ltac:(destruct (vt_band_of_aapp _ _ BAPP); [left | right]; lia)) as DS2.
    cbn [disjoint_from]. split; [lia | split; [lia | exact I]]. }
  clear DV8.
  assert (S03 : stack0 M3 lo shi).
  { eapply stack0_transport; [exact S02 | exact MU3 | exact WM3 |].
    apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; unfold stack0_ok; cbn [fst snd].
    - vuse VBAND. destruct VBAND0 as [VL|VH]; [right | left; unfold AHI_LO; lia].
      clear - VL ACF1. unfold sh, ASHADOW_BASE. Z.div_mod_to_equations. lia.
    - destruct (vt_band_of_aapp _ _ BAPP) as [BL|BH]; [right | left; unfold AHI_LO; lia].
      clear - BL XLT XL ACF1. unfold sh, ASHADOW_BASE. Z.div_mod_to_equations. lia. }
  assert (XP3 : xpres H LB spz [(v, v + 24); (b, b + 4 * cap); (sh b, sh b + nsh (4 * cap))] m M3).
  { eapply (xpres_trans H).
    - eapply (xpres_weaken H); [exact XP2 | lia | intros bb Hb; exact Hb |].
      intros a Ha. cbn [rin_ivs fst snd] in Ha |- *. destruct Ha as [Ha|[]]. right. right. left. exact Ha.
    - eapply (xpres_of_munch H s LB spz _ [(v + 8, v + 16); (b + 4 * Zlen xs, b + 4 * Zlen xs + 4)] m m2 M3);
        [exact HH | exact RH0 | exact MU3 | exact WM3 |].
      apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; right; intros a Ha; cbn [fst snd] in Ha; cbn [rin_ivs fst snd].
      + left. lia.
      + right. left. lia. }
  eapply (sr_blk H HH); [exact KR2 | exact VIS2 | exact HF2 | exact Hms |].
  intros msF3 mo3 KR3 MP3 VIS3. rewrite <- (rfull_eq R' HF3) in VIS3.
  eapply (vt_end msF3 mo3 s M3 R' LB b cap e2 VIS3 HF3).
  - exact K1.
  - rewrite K2, vt_spz_sp. unfold wz. f_equal. lia.
  - rewrite (KK 3%bv ltac:(inb)). exact G3.
  - rewrite (KK 4%bv ltac:(inb)). exact G4.
  - exact K8.
  - exact K9.
  - exact K18.
  - exact K19.
  - exact K20.
  - exact K21.
  - rewrite (KK 22%bv ltac:(inb)). exact G22.
  - rewrite (KK 23%bv ltac:(inb)). exact G23.
  - rewrite (KK 24%bv ltac:(inb)). exact G24.
  - rewrite (KK 25%bv ltac:(inb)). exact G25.
  - rewrite (KK 26%bv ltac:(inb)). exact G26.
  - rewrite (KK 27%bv ltac:(inb)). exact G27.
  - exact KR3.
  - eapply (ah_mpres_trans H HH); [exact MP2 | exact MP3].
  - exact MI3.
  - exact ST3.
  - exact ERR3.
  - exact RA3.
  - exact VEC3.
  - exact RH3.
  - exact SH3.
  - exact ADV3.
  - exact (wr_at_transport asegs _ _ _ _ WV2 WM3).
  - exact (lb_own_wmono _ _ _ OW2 WM3).
  - left. split; [exact XLT|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [exact XP3 | lia].
  - exact RF3.
  - exact AC3.
  - exact S03.
Qed.

  Let HANN : annotate_gen_stmt := annotate_gen_ok.

  Lemma vt_main : forall (msF : machine_state) (t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 errv : word),
    as_VIS H s msF = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 v) (Z_to_bv 64 src) a2 a3 a4 a5 a6 a7
                             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                        F (Z_to_bv 64 VOT_PB_ENTRY) fc None m (seg_rom asegs) ->
    as_AKREL H s (mkCfg msF mo) -> rw_cells asegs m (errno_addr tp) [C4 errv] ->
    as_SR H Q (mkCfg msF mo).
Proof.
Proof.
  intros msF t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 errv VIS KR ERR.
  pose proof SPR as (SPL & SPH & SP16). pose proof LOR as [LO1 LO2].
  unfold VOT_PB_STACK, V4_STACK, AOPNEW_STACK, AMALLOC_STACK in LO2.
  pose proof vt_facts as (F0 & F1 & F2 & FE & XL & OB & DJ & MD).
  pose proof aceil_facts as ((ACF1 & ACF2) & ACF3 & ACF4).
  assert (GZ : gz m v 24) by (intros i Hi; eapply sh0_of_addressable; [exact ADV0 | change (8 * (24 / 8)) with 24; lia]).
  assert (OB0 : 0 <= b /\ b + 4 * cap < 2 ^ 47).
  { destruct OB as [[E1 E2]|(Hc & HIn & (O0 & O16 & On & OI & OC & OF & OAP))]; [rewrite E1, E2; lia | lia]. }
  assert (VSD : v + 24 <= spz - 64 \/ spz <= v) by (destruct OBJ as (_ & _ & _ & _ & _ & SD); lia).
  assert (VLO : 0x6e8000 <= v /\ v + 24 <= 2 ^ 47) by (destruct VBAND; lia).
  remember (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 v) (Z_to_bv 64 src) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
    as R0 eqn:HR0.
  assert (HF0 : rfull R0) by (rewrite HR0; apply rfull_mkR).
  assert (ERRT : forall m1, munch [(spz - 56, spz)] m m1 -> wmono asegs m m1 -> rw_cells asegs m1 (errno_addr tp) [C4 errv]).
  { intros m1 MU1 WM1. eapply rw_cells_transport; [exact ERR | exact MU1 | exact WM1 |]. rewrite TPV.
    rewrite u64_of_Z by (unfold ATP; lia). cbn. unfold ATP. split; [lia | exact I]. }
  destruct (Z_lt_le_dec (Zlen xs) cap) as [LT|GE].
  - destruct OB as [[E1 E2]|(Hc & HIn & (B0 & B16 & Bn & BI & BC & BF & BAPP))]; [lia|].
    destruct (vt_P1F_ok R0 F fc m v src spz b (Zlen xs) cap lo ltac:(rewrite HR0; reflexivity) ltac:(rewrite HR0; reflexivity)
                ltac:(rewrite HR0; exact vt_spz_sp) AC0 F0 F1 F2 GZ ST0 ltac:(lia) ltac:(lia) SPH
                (proj1 VLO) (proj2 VLO) ltac:(lia) (v4_mod16_16le b B0 B16) ltac:(lia) ltac:(lia) LT ltac:(lia))
      as (R1 & M1 & Hms & MU1 & WM1 & FR1 & K1 & K2 & K8 & K9 & K10 & K11 & K12 & K13 & K18 & K19 & K20 & K21 & KK).
    assert (FRM : rw_cells asegs M1 (spz - 56) FRAME) by (rewrite HR0 in FR1; exact FR1).
    pose proof (msteps_full asegs _ _ Hms HF0) as HF1. cbn [ms_regs] in HF1.
    assert (MI1 : mem_inv asegs M1) by exact (msteps_mem_inv asegs _ _ Hms MI0).
    pose proof (ERRT M1 MU1 WM1) as ERR1.
    destruct (vt_after_frame M1 MU1 WM1 FRM) as (RH1 & RF1 & AC1 & RA1 & ST1 & S01 & XP1 & OW1 & VEC1 & ADV1 & WV1 & SH1).
    assert (K3 : getr R1 3 = gp) by (rewrite (KK 3%bv ltac:(inb)), HR0; reflexivity).
    assert (K4 : getr R1 4 = tp) by (rewrite (KK 4%bv ltac:(inb)), HR0; reflexivity).
    assert (K22 : getr R1 22 = s6) by (rewrite (KK 22%bv ltac:(inb)), HR0; reflexivity).
    assert (K23 : getr R1 23 = s7) by (rewrite (KK 23%bv ltac:(inb)), HR0; reflexivity).
    assert (K24 : getr R1 24 = s8) by (rewrite (KK 24%bv ltac:(inb)), HR0; reflexivity).
    assert (K25 : getr R1 25 = s9) by (rewrite (KK 25%bv ltac:(inb)), HR0; reflexivity).
    assert (K26 : getr R1 26 = s10) by (rewrite (KK 26%bv ltac:(inb)), HR0; reflexivity).
    assert (K27 : getr R1 27 = s11) by (rewrite (KK 27%bv ltac:(inb)), HR0; reflexivity).
    clear KK.
    pose proof (ah_fsb H HH _ _ _ RH0) as (FS1 & FS2 & FS3 & FS4).
    assert (SHB0 : ASHADOW_BASE <= sh b) by (unfold sh; pose proof (Z.div_pos b 8 ltac:(lia) ltac:(lia)); lia).
    assert (SHL : 0x7fff8000 <= sh b) by (unfold sh, ASHADOW_BASE; Z.div_mod_to_equations; lia).
    pose proof (sh_nsh_high b (4 * cap) ltac:(lia) ltac:(lia) ltac:(unfold AAPP_HI; lia)) as SHH. unfold AHI_LO in SHH.
    pose proof (v4_app_sh (as_FSB H) AFS_SIZE b (4 * cap) ltac:(lia) ltac:(lia) ltac:(lia) (vt_band_of_aapp _ _ FS4)) as DF.
    assert (SP64 : bv_unsigned (getr R1 2) = spz - 64) by (rewrite K2; unfold wz; rewrite u64_of_Z by lia; reflexivity).
    eapply (sr_blk H HH); [exact KR | exact VIS | exact HF0 | exact Hms |].
    intros msF1 mo1 KR1 MP1 VIS1.
    eapply (ahh_evt_then H HH); [exact KR1 | exact VIS1 | |].
    { eapply HANN with (beg := b) (len := 4 * cap) (oldmid := 4 * Zlen xs) (newmid := 4 * Zlen xs + 4) (lo := lo).
      - exact K10.
      - exact K11.
      - exact K12.
      - rewrite K13. unfold wz. f_equal. lia.
      - exact (v4_mod16_8 b B16).
      - lia.
      - lia.
      - lia.
      - exact BAPP.
      - unfold AAPP_HI; lia.
      - exact (SH1 Hc).
      - rewrite SP64. exact (proj1 (stk_split asegs M1 lo (spz - 64) spz ST1 ltac:(lia))).
      - exact LO1.
      - rewrite SP64. unfold AINTRIN_STACK. lia.
      - exact MI1.
      - exact AC1.
      - unfold in_app_mem. destruct (vt_band_of_aapp _ _ BAPP) as [K|K]; [left | right]; unfold ASHADOW_BASE, AHI_LO, AAPP_HI; lia. }
    intros msF2 mo2 KR2 MP2 POST.
    destruct POST as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m2
                      & VIS2 & MU2 & WM2 & MI2 & ST2 & SH2 & AC2).
    rewrite SP64 in MU2. unfold AINTRIN_STACK in MU2.
    rewrite K1 in VIS2. unfold wz in VIS2.
    rewrite (ret_pc_even VOT_FRET ltac:(unfold VOT_FRET; lia) ltac:(unfold VOT_FRET; reflexivity)) in VIS2.
    assert (W1 : Forall (aclient_write_ok H LB) [(sh b, sh b + nsh (4 * cap)); (spz - 64 - 4096, spz - 64)]).
    { destruct (stack_window_ok H LB LF (spz - 64 - 4096) (spz - 64) ltac:(lia) FS2) as (SW1 & _ & _).
      apply Forall_cons; [|apply Forall_cons; [exact SW1 | apply Forall_nil]].
      right; right; right; left. exists (pid, b, 4 * cap). split; [exact HIn | cbn [blk_addr blk_size fst snd]; lia]. }
    assert (W2 : Forall (afs_write_ok H LF) [(sh b, sh b + nsh (4 * cap)); (spz - 64 - 4096, spz - 64)]).
    { destruct (stack_window_ok H LB LF (spz - 64 - 4096) (spz - 64) ltac:(lia) FS2) as (_ & SW2 & _).
      apply Forall_cons; [|apply Forall_cons; [exact SW2 | apply Forall_nil]].
      left. cbn [fst snd]. split; [lia | right; unfold ATLS_PRIV_HI, ATP, ASHADOW_BASE in *; lia]. }
    assert (W3 : Forall aconst_ok [(sh b, sh b + nsh (4 * cap)); (spz - 64 - 4096, spz - 64)]).
    { destruct (stack_window_ok H LB LF (spz - 64 - 4096) (spz - 64) ltac:(lia) FS2) as (_ & _ & SW3).
      apply Forall_cons; [|apply Forall_cons; [exact SW3 | apply Forall_nil]].
      apply aconst_ok_high; [apply sh_mono; unfold AIMG_TOP in *; lia | right; left; lia]. }
    destruct (client_frame H HH s LB LF B _ M1 m2 RH1 RF1 AC1 RA1 MU2 WM2 W1 W2 W3) as (RH2 & RF2 & AC2' & RA2).
    eapply (vt_f2 msF2 mo2 m2 _ errv LT VIS2 (rfull_mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)).
    + exact K2.
    + exact K3.
    + exact K4.
    + exact K8.
    + exact K9.
    + exact K18.
    + exact K19.
    + exact K20.
    + exact K21.
    + exact K22.
    + exact K23.
    + exact K24.
    + exact K25.
    + exact K26.
    + exact K27.
    + exact KR2.
    + eapply (ah_mpres_trans H HH); [exact MP1 | exact MP2].
    + eapply rw_cells_transport; [exact FRM | exact MU2 | exact WM2 |]. unfold FRAME. rewrite v4_cells_size_map_C8'.
      cbn [length Z.of_nat Pos.of_succ_nat Pos.succ disjoint_from]. split; [lia | split; [lia | exact I]].
    + exact MI2.
    + apply (stk_high_transport M1 m2 lo spz ST1 WM2). unfold AIMG_TOP. lia.
    + eapply rw_cells_transport; [exact ERR1 | exact MU2 | exact WM2 |]. rewrite TPV. rewrite u64_of_Z by (unfold ATP; lia).
      cbn. unfold ATP, ASHADOW_BASE in *. split; [lia | split; [lia | exact I]].
    + exact RA2.
    + exact RH2.
    + exact RF2.
    + exact AC2.
    + eapply stack0_transport; [exact S01 | exact MU2 | exact WM2 |].
      apply Forall_cons; [apply stack0_ok_sh; lia | apply Forall_cons; [left; cbn [fst]; unfold AHI_LO; lia | apply Forall_nil]].
    + exact (lb_own_wmono _ _ _ OW1 WM2).
    + eapply (xpres_trans H).
      * eapply (xpres_weaken H); [exact XP1 | lia | intros bb Hb; exact Hb | intros a Ha; destruct Ha].
      * eapply (xpres_of_munch H s LB spz _ _ m M1 m2); [exact HH | exact RH0 | exact MU2 | exact WM2 |].
        apply Forall_cons; [|apply Forall_cons; [left; cbn [fst snd]; lia | apply Forall_nil]].
        right. intros a Ha. cbn [fst snd] in Ha. cbn [rin_ivs fst snd]. left. exact Ha.
    + exact SH2.
  - assert (XSL : Zlen xs = cap) by lia.
    destruct (vt_P1S_ok R0 F fc m v src spz b (Zlen xs) cap lo ltac:(rewrite HR0; reflexivity) ltac:(rewrite HR0; reflexivity)
                ltac:(rewrite HR0; exact vt_spz_sp) AC0 F0 F1 F2 GZ ST0 ltac:(lia) ltac:(lia) SPH
                (proj1 VLO) (proj2 VLO) ltac:(lia) (proj1 OB0) (proj2 OB0) XSL ltac:(lia))
      as (R1 & M1 & Hms & MU1 & WM1 & FR1 & K1 & K2 & K8 & K10 & K11 & K19 & K20 & KK).
    assert (FRM : rw_cells asegs M1 (spz - 56) FRAME) by (rewrite HR0 in FR1; exact FR1).
    pose proof (msteps_full asegs _ _ Hms HF0) as HF1. cbn [ms_regs] in HF1.
    assert (MI1 : mem_inv asegs M1) by exact (msteps_mem_inv asegs _ _ Hms MI0).
    eapply (sr_blk H HH); [exact KR | exact VIS | exact HF0 | exact Hms |].
    intros msF1 mo1 KR1 MP1 VIS1. rewrite <- (rfull_eq R1 HF1) in VIS1.
    eapply (vt_sl msF1 mo1 M1 R1 errv XSL VIS1 HF1).
    + exact K1.
    + exact K2.
    + rewrite (KK 3%bv ltac:(inb)), HR0. reflexivity.
    + rewrite (KK 4%bv ltac:(inb)), HR0. reflexivity.
    + exact K8.
    + exact K10.
    + exact K11.
    + exact K19.
    + exact K20.
    + rewrite (KK 22%bv ltac:(inb)), HR0. reflexivity.
    + rewrite (KK 23%bv ltac:(inb)), HR0. reflexivity.
    + rewrite (KK 24%bv ltac:(inb)), HR0. reflexivity.
    + rewrite (KK 25%bv ltac:(inb)), HR0. reflexivity.
    + rewrite (KK 26%bv ltac:(inb)), HR0. reflexivity.
    + rewrite (KK 27%bv ltac:(inb)), HR0. reflexivity.
    + exact KR1.
    + exact MP1.
    + exact MU1.
    + exact WM1.
    + exact FRM.
    + exact MI1.
    + exact (ERRT M1 MU1 WM1).
Qed.
End VT.

Theorem votpb_ok {HCEIL : HeapCeil} : forall (H : asr), asan_rt_hyps H -> votpb_stmt H.
Proof.
Proof.
  intros H HH. unfold votpb_stmt.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc msF m mo s LB LF
    v b cap src x xs pid lo B shi errv.
  intros VIS -> -> VEC V8 ADV OBJ VBAND VWR OWN OLD OLDSH CAPB GROW SRC XR SR4 SR0 SR47 RH KR SLOW TRO RA SPB SP16 SP47 ST CE LOl
    ERR MI TPV RA2 AC RF S0 SHI.
  pose proof aceil_facts as ((ACF1 & ACF2) & _ & _).
  pose proof LOl as LOu. unfold VOT_PB_STACK, V4_STACK, AOPNEW_STACK, AMALLOC_STACK in LOu.
  eapply vt_main with (src := src) (spz := bv_unsigned sp); try eassumption; try reflexivity.
  all: lazymatch goal with
       | |- _ /\ _ /\ _ mod 16 = 0 => split; [lia|]; split; [exact SP47 | exact SP16]
       | |- _ mod 4 = 0 /\ _ => split; [exact SR4|]; split; [exact SR0 | exact SR47]
       | |- aceil <= _ /\ _ => split; [exact CE | exact LOl]
       end.
Qed.

