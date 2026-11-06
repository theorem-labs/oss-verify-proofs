(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac Arr Bytes ZBridge Frame ITree.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.LZ Require Import ITreeLZ NodesLZ.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import STRW_tac STRW_merge Ceiling.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Http Require Import HttpRep HttpTac CellConv.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.ZAW Require Import Segs Shadow Contracts AllocA0 ATac.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.ZAA Require Import AEnv ADepot ALayout APrim APrimLem AFrame ATacA ACells LJ LJU PEnv ATacFix F_poison F_memset F_gct F_prim_L0 F_hooks F_depot F_depot_C F_prim_cid APrimSpec APrimSpec2 F_prim_calloc2 F_alloc_env F_alloc_A.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Definition hb1 (b : Z) : Z := Z.lor (Z.land b 18446744073709551612) 1.
Definition hb2 (b : Z) : Z := Z.lor (Z.land (hb1 b) 143) 16.
Definition hb3 (b : Z) : Z := Z.lor (Z.land b 243) 0.
Lemma hb_facts : forall b, 0 <= b < 256 ->
  (hb1 b mod 18446744073709551616) mod 2^8 = hb1 b /\ (hb2 b mod 18446744073709551616) mod 2^8 = hb2 b /\ 0 <= hb2 b < 256 /\ Z.land (hb2 b) 3 = 1.
Proof.
  intros b Hb.
  pose proof (range_check (fun b => ((hb1 b mod 18446744073709551616) mod 2^8 =? hb1 b) && ((hb2 b mod 18446744073709551616) mod 2^8 =? hb2 b)
                                    && (0 <=? hb2 b) && (hb2 b <? 256) && (Z.land (hb2 b) 3 =? 1))
                0 256 ltac:(vm_compute; reflexivity) b ltac:(lia)) as R.
  cbn beta in R. apply andb_true_iff in R as [R R5]. apply andb_true_iff in R as [R R4]. apply andb_true_iff in R as [R R3]. apply andb_true_iff in R as [R1 R2].
  apply Z.eqb_eq in R1, R2, R5. apply Z.leb_le in R3. apply Z.ltb_lt in R4. tauto.
Qed.
Lemma hb3_facts : forall b, 0 <= b < 256 -> Z.land b 3 = 1 ->
  (hb3 b mod 18446744073709551616) mod 2^8 = hb3 b /\ 0 <= hb3 b < 256 /\ Z.land (hb3 b) 3 = 1.
Proof.
  intros b Hb L3.
  pose proof (range_check (fun b => negb (Z.land b 3 =? 1) || (((hb3 b mod 18446744073709551616) mod 2^8 =? hb3 b) && (0 <=? hb3 b) && (hb3 b <? 256) && (Z.land (hb3 b) 3 =? 1)))
                0 256 ltac:(vm_compute; reflexivity) b ltac:(lia)) as R.
  cbn beta in R. apply (proj2 (Z.eqb_eq _ _)) in L3. rewrite L3 in R. cbn [negb orb] in R.
  apply andb_true_iff in R as [R R4]. apply andb_true_iff in R as [R R3]. apply andb_true_iff in R as [R1 R2].
  apply Z.eqb_eq in R1, R4. apply Z.leb_le in R2. apply Z.ltb_lt in R3. tauto.
Qed.

Ltac hideB h := lazymatch type of h with id _ => idtac | ?P => change (id P) in h end.
Ltac unhideB h := lazymatch type of h with id ?P => change P in h | _ => idtac end.
Ltac post_callk segs m :=
  let ms' := fresh "ms'" in let PO := fresh "POST" in
  intros ms' PO;
  destruct_exs PO;
  let E := fresh "E" in let MUc := fresh "MUk" in let WMc := fresh "WMk" in let MIc := fresh "MI" in
  destruct PO as [E [MUc [WMc PO]]];
  first [ destruct PO as [MIc PO] | rename PO into MIc ];
  subst ms';
  lazymatch type of MUc with
  | munch _ m ?m' => transport_after_call segs m m' MUc WMc
  end;
  try destruct_ands PO;
  try (lazymatch goal with
  | |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
      replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ])
  end).
Tactic Notation "callk" uconstr(SPEC) :=
  lazymatch goal with
  | |- evt ?segs _ (MS _ _ _ _ _ ?m _) => eapply evt_cut; [ eapply SPEC | post_callk segs m ]
  end.

Lemma al_land_m8_48 : forall x, 0 <= x < 2^48 -> Z.land x 281474976710648 = (x / 8) * 8.
Proof.
  intros x Hx.
  assert (E48 : 281474976710648 = Z.ldiff (Z.ones 48) (Z.ones 3)) by reflexivity. rewrite E48.
  assert (D48 : forall a b, Z.land x (Z.ldiff a b) = Z.ldiff (Z.land x a) b).
  { intros a b. apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, !Z.ldiff_spec, Z.land_spec.
    destruct (Z.testbit x i), (Z.testbit a i), (Z.testbit b i); reflexivity. }
  rewrite D48. rewrite Z.land_ones by lia. rewrite Z.mod_small by lia.
  rewrite Z.ldiff_ones_r by lia. rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia. reflexivity.
Qed.

Lemma cb_word_at : forall (m : mem) A (n : nat) bs k,
  rw_cells asegs m A [CB n bs] -> 0 <= k -> 8 * k + 8 <= Z.of_nat n ->
  exists old, rw_cells asegs m (A + 8 * k) [C8 old]
  /\ forall (m' : mem) new, munch [(A + 8 * k, A + 8 * k + 8)] m m' -> wmono asegs m m' -> rw_cells asegs m' (A + 8 * k) [C8 new] ->
       exists bs', rw_cells asegs m' A [CB n bs'].
Proof.
  intros m A n bs k H K0 KN.
  set (n1 := Z.to_nat (8 * k)). set (n3 := (n - n1 - 8)%nat).
  apply (rw_cells_split_CB asegs m A [] n bs [] [n1; 8%nat; n3]) in H; [| cbn [sum_nat]; unfold n1, n3; lia].
  cbn [mk_CB_cells app] in H.
  lazymatch type of H with rw_cells _ _ _ [CB _ ?j1; CB 8 ?j2; CB _ ?j3] =>
    change (rw_cells asegs m A ([CB n1 j1] ++ [CB 8 j2; CB n3 j3])) in H; apply rw_cells_app in H; destruct H as [H1 H23];
    change (rw_cells asegs m (A + Z.of_nat (cells_size [CB n1 j1])) ([CB 8 j2] ++ [CB n3 j3])) in H23; apply rw_cells_app in H23; destruct H23 as [H2 H3] end.
  cbn [cells_size csize Nat.add] in H2, H3. rewrite Nat.add_0_r in H2, H3.
  replace (A + Z.of_nat n1) with (A + 8 * k) in H2, H3 by (unfold n1; lia).
  apply (rw_cells_CB_C8 asegs m (A + 8 * k) [] _ []) in H2. cbn [app] in H2.
  eexists. split; [exact H2|]. intros m' new MU WM HN.
  eapply (rw_cells_transport asegs _ m m') in H1; [| exact MU| exact WM| cbn [disjoint_from cells_size csize Nat.add]; unfold n1; lia].
  eapply (rw_cells_transport asegs _ m m') in H3; [| exact MU| exact WM| cbn [disjoint_from cells_size csize Nat.add]; lia].
  lazymatch type of H1 with rw_cells _ _ _ ?c1 => lazymatch type of H3 with rw_cells _ _ _ ?c3 =>
    assert (HA : rw_cells asegs m' A (c1 ++ [C8 new] ++ c3)) end end.
  { apply rw_cells_app. split; [exact H1|]. cbn [cells_size csize Nat.add]. rewrite Nat.add_0_r. replace (A + Z.of_nat n1) with (A + 8 * k) by (unfold n1; lia).
    apply rw_cells_app. split; [exact HN|]. cbn [cells_size csize Nat.add]. exact H3. }
  eapply rw_cells_ex_CB; [exact HA|]. cbn [app cells_size csize Nat.add]. unfold n1, n3. lia.
Qed.

Section HDR.
  Context {HC : HasCeiling}.
  Variables (ra gp tp t0 t1 t2 s0 a3 a5 a6 a7 s6 s7 s10 t3 t4 t5 t6 : word) (F_ : bvmap 5 word) (fc : bv 32).
  Variables (SP B M rz size needed n : Z) (m : mem).
  Hypothesis BR : 0 <= B /\ B mod 8 = 0 /\ B + needed <= 2^47.
  Hypothesis RZ : 16 <= rz <= 2048 /\ rz mod 16 = 0.
  Hypothesis SZ : 1 <= size <= 2^28 /\ rz + size <= needed /\ 0 <= n <= 2^28.
  Hypothesis SPR : 0 <= SP /\ SP + 128 <= 2^47.
  Hypothesis HM : M = B + rz - 16.

  Definition hdr_post (b0 : byte) : machine_state -> Prop :=
    fun ms' => exists a0 a1 a2 a4 m' (bits : byte),
      ms' = MS (mkR ra (wz SP) gp tp t0 t1 t2 s0 (wz size) a0 a1 a2 a3 a4 a5 a6 a7
                    (wz B) (wz needed) (wz (M + 16)) (wz M) s6 s7 (Z_to_bv 64 (-8)) (wz (M + 16 + size)) s10 (wz 1) t3 t4 t5 t6)
               F_ (wz 0x3395c) fc None m' (seg_rom asegs)
      /\ munch [(M, M + 8)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
      /\ Z.land (bv_unsigned bits) 3 = 1
      /\ rw_cells asegs m' M [C1 b0; C1 bits; C2 (wz 0); C4 (wz size)].

  #[using="BR RZ SZ HM"] Lemma hdr_spec : forall (a0 a1 a2 a4 : word) (b0 b1 : byte) (j2 j4 : list byte),
    mem_inv asegs m ->
    rw_cells asegs m (SP + 16) [C8 (wz 16)] ->
    rw_cells asegs m M [C1 b0; C1 b1; CB 2 j2; CB 4 j4] ->
    (SP + 24 <= M \/ M + 8 <= SP + 16) ->
    evt asegs (hdr_post b0)
      (MS (mkR ra (wz SP) gp tp t0 t1 t2 s0 (wz size) a0 a1 a2 a3 a4 a5 a6 a7
               (wz B) (wz needed) (wz rz) (wz n) s6 s7 (Z_to_bv 64 (-8)) (wz 7) s10 (wz 1) t3 t4 t5 t6)
          F_ (wz 0x33900) fc None m (seg_rom asegs)).
  Proof.
    intros a0 a1 a2 a4 b0 b1 j2 j4 MI FR16 HD DJ.
    pose proof (munch_refl [(M, M + 8)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    zstep. zstep. zstep.
    replace (Z.land (B + rz) 7) with 0.
    2:{ change 7 with (Z.ones 3). rewrite Z.land_ones by lia. change (2^3) with 8. clear - BR RZ. Z.div_mod_to_equations. lia. }
    zstep. if_true.
    zstep. zstep. if_cases KC; zify_cond KC. { exfalso. clear - KC BR RZ SZ. lia. } clear KC.
    replace (B + rz) with (M + 16) by (clear - HM; lia).
    zstep. zstep. zstep. zstep. zstep. zstep.
    replace (Z.shiftr size 32) with 0 by (rewrite Z.shiftr_div_pow2 by lia; symmetry; apply Z.div_small; clear - SZ; lia).
    replace (Z.shiftr n 48) with 0 by (rewrite Z.shiftr_div_pow2 by lia; symmetry; apply Z.div_small; clear - SZ; lia).
    pose proof (byte_lt256 b1) as BU. remember (bv_unsigned b1) as bu eqn:Ebu.
    destruct (hb_facts bu BU) as (HB1 & HB2 & HB2R & HB23).
    change (Z.lor (Z.land bu 18446744073709551612) 1) with (hb1 bu).
    zstep.
    assert (H1R : 0 <= hb1 bu < 256) by (rewrite <- HB1; apply Z.mod_pos_bound; lia).
    rewrite (le1_lit_of_mod8 (hb1 bu) (Z_to_bv 8 (hb1 bu))) by (rewrite HB1; symmetry; apply Z_to_bv_small; change (bv_modulus 8) with 256; exact H1R).
    mem_after_store.
    sstep. zstep.
    zstep. if_false.
    zstep. zstep. zstep. zstep.
    change (Z.lor (Z.land (hb1 bu) 143) 16) with (hb2 bu).
    zstep.
    rewrite (le1_lit_of_mod8 (hb2 bu) (Z_to_bv 8 (hb2 bu))) by (rewrite HB2; symmetry; apply Z_to_bv_small; change (bv_modulus 8) with 256; exact HB2R).
    mem_after_store.
    apply evt_done. unfold hdr_post. eexists _, _, _, _, m1, (Z_to_bv 8 (hb2 bu)). split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [assumption|].
    split; [rewrite Z_to_bv_small by (change (bv_modulus 8) with 256; exact HB2R); exact HB23| exact HD].
  Qed.
End HDR.

Section CTX.
  Context {HC : HasCeiling}.
  Variable D : dlayout.
  Variables (ra gp t2 s0 s1 s2 s3 s4 s6 s9 s11 t3 t4 t5 t6 : word) (F_ : bvmap 5 word) (fc : bv 32).
  Variables (SP lo M THR CTX STK TR total : Z) (m : mem) (hs : list Z) (ws : list word) (tr : list Z).
  Hypothesis DLO : dl_ok D.
  Hypothesis CLO : alloc_ceiling <= lo.
  Hypothesis LOQ : lo <= SP - 224.
  Hypothesis SPR : SP mod 16 = 0 /\ SP <= 2^47.
  Hypothesis THRR : 0 < THR < 2^64.
  Hypothesis MR : 0 <= M /\ M + 16 <= 2^47.

  Notation Wd := [(SP - 224, SP); (DT + 4 * bkt (depot_hash tr), DT + 4 * bkt (depot_hash tr) + 4); (DNI, DNI + 4);
                  (DN0 D + 16 * (zlen hs + 1), DN0 D + 16 * (zlen hs + 1) + 16); (SSA, SSA + 8); (SSD + 8, SSD + 12);
                  (SS0 D + 8 * total, SS0 D + 8 * total + 8 + 8 * Z.of_nat (length tr))].

  Definition ctx_post : machine_state -> Prop :=
    fun ms' => exists ra' t0 t1 a0 a1 a2 a3 a4 a5 a6 a7 s8 m' hs' total' actx,
      ms' = MS (mkR ra' (wz SP) gp (wz A0_TP) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
                    s2 s3 s4 (wz M) s6 (wz STK) s8 s9 (wz THR) s11 t3 t4 t5 t6)
               F_ (wz 0x33a14) fc None m' (seg_rom asegs)
      /\ munch ((M + 8, M + 16) :: Wd) m m' /\ wmono asegs m m' /\ mem_inv asegs m'
      /\ stk asegs m' lo SP /\ RDEPOT D hs' total' m'
      /\ ((dfind hs (depot_hash tr) <> 0 /\ hs' = hs /\ total' = total)
          \/ (dfind hs (depot_hash tr) = 0 /\ hs' = hs ++ [depot_hash tr] /\ total' = total + Z.of_nat (length tr) + 1))
      /\ rw_cells asegs m' (M + 8) [C8 actx]
      /\ (exists mD, munch Wd m mD /\ wmono asegs m mD /\ mem_inv asegs mD /\ munch [(M + 8, M + 16)] mD m' /\ wmono asegs mD m').

  #[using="HC DLO CLO LOQ SPR THRR MR"] Lemma ctx_spec : forall (t0 t1 a0 a1 a2 a3 a4 a5 a6 a7 s8 tid : word) (j8 : list byte),
    mem_inv asegs m -> stk asegs m lo SP ->
    rw_cells asegs m THR [C8 (wz CTX)] -> rw_cells asegs m (CTX + 8) [C4 tid] ->
    rw_cells asegs m STK [C8 (wz TR); C8 (wz (Z.of_nat (length tr)))] ->
    rw_cells asegs m (M + 8) [CB 8 j8] ->
    RDEPOT D hs total m -> u64arr asegs m TR ws -> firstn (length tr) ws = map wz tr -> (length tr <= length ws)%nat -> (1 <= length tr <= 30)%nat ->
    Forall (fun x => 0 <= x < 2^64) tr -> SP <= TR -> TR + 8 * Z.of_nat (length ws) <= 2^47 ->
    16 * (zlen hs + 2) <= 2^20 -> 8 * (total + Z.of_nat (length tr) + 1) <= SWIN D -> total + Z.of_nat (length tr) + 1 < 2^20 ->

    (M + 16 <= lo \/ SP <= M + 8) -> (M + 16 <= 1595336 \/ 5855224 <= M + 8) ->
    (M + 16 <= DN0 D \/ DN0 D + 2^20 <= M + 8) -> (M + 16 <= SS0 D \/ SS0 D + SWIN D <= M + 8) ->
    evt asegs ctx_post
      (MS (mkR ra (wz SP) gp (wz A0_TP) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
               s2 s3 s4 (wz M) s6 (wz STK) s8 s9 (wz THR) s11 t3 t4 t5 t6)
          F_ (wz 0x3395c) fc None m (seg_rom asegs)).
  Proof.
    intros t0 t1 a0 a1 a2 a3 a4 a5 a6 a7 s8 tid j8 MI ST THC TIDC SOBJ HW RD BUF TRW LENW LTR RNG QTR TRH ROOM_N ROOM_F ROOM_T DJ1 DJ2 DJ3 DJ4.
    pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
    zstep. if_cases KT; zify_cond KT. { exfalso. clear - KT THRR. lia. } clear KT.
    zstep. zstep. zstep. zstep.
    zstep. zstep. zstep.
    pose proof (bkt_range (depot_hash tr)) as BKR.
    assert (T0 : 0 <= total) by (destruct RD as (_ & _ & _ & _ & _ & _ & _ & _ & _ & T0 & _); exact T0).
    pose proof DLO as (DL1 & DL2 & DL3 & DL4 & DL5 & DL6 & DL7 & DL8 & DL9).
    assert (DJW : disjoint_from Wd (M + 8) 8).
    { cbn [disjoint_from]. unfold zlen in *. clear - DJ1 DJ2 DJ3 DJ4 BKR T0 ROOM_N ROOM_F LOQ DL7. lia. }
    hideB HW.
    pose proof (munch_refl ((M + 8, M + 16) :: Wd) m) as MU. pose proof (wmono_refl asegs m) as WM.
    callk (put_spec D _ gp (wz A0_TP) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F_ fc SP TR total m hs ws tr DLO RD BUF TRW LENW LTR RNG QTR TRH (proj1 SPR) ROOM_N ROOM_F ROOM_T MI lo);
      [ exact ST | exact CLO | exact LOQ | ].
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mD end.
    unhideB HW. eapply (rw_cells_transport asegs _ m mD) in HW; [| exact MUk| exact WMk| exact DJW].
    rename MUk into MUd, WMk into WMd. hideB MUd. hideB WMd.
    lazymatch goal with HM : mem_inv asegs mD |- _ => pose proof HM as MID end. hideB MID.
    zstep. zstep. zstep.
    lazymatch goal with HR : RDEPOT D ?h1 ?t1 mD |- _ => rename HR into RDD end.
    lazymatch goal with HP : _ \/ _ |- _ => rename HP into RES end.
    pose proof (munch_refl [(M + 8, M + 16)] mD) as MUs. pose proof (wmono_refl asegs mD) as WMs.
    zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mE end.
    assert (RDE : exists h1 t1, RDEPOT D h1 t1 mE /\ ((dfind hs (depot_hash tr) <> 0 /\ h1 = hs /\ t1 = total)
          \/ (dfind hs (depot_hash tr) = 0 /\ h1 = hs ++ [depot_hash tr] /\ t1 = total + Z.of_nat (length tr) + 1))).
    { lazymatch type of RDD with RDEPOT D ?h1 ?t1 mD => exists h1, t1 end. split.
      - eapply RDEPOT_frame; [exact RDD| exact MUs| exact WMs|]. unfold depot_apart. constructor; [| constructor]. cbn [fst snd].
        clear - DJ2 DJ3 DJ4. lia.
      - destruct RES as [(P1 & P2 & P3 & P4)|(P1 & _ & P3 & P4)]; [left; split; [rewrite <- P1; exact P2| split; assumption]| right; repeat split; assumption]. }
    destruct RDE as (h1 & t1' & RDE & RESE).
    apply evt_done. unfold ctx_post.
    lazymatch goal with HS : stk asegs mE _ _, HM : mem_inv asegs mE |- _ =>
      eexists _, _, _, _, _, _, _, _, _, _, _, _, mE, h1, t1', _; split; [reflexivity|];
      split; [exact MU|]; split; [exact WM|]; split; [exact HM|]; split; [exact HS|]; split; [exact RDE|]; split; [exact RESE|]; split; [exact HW|] end.
    exists mD. unhideB MUd. unhideB WMd. unhideB MID. repeat split; assumption.
  Qed.
End CTX.

Section UNPA.
  Context {HC : HasCeiling}.
  Variable E : penv.
  Variables (gp s0 s2 s3 s5 s7 s8 s9 s10 s11 : word) (F_ : bvmap 5 word) (fc : bv 32).
  Variables (SP lo U size : Z) (m : mem).
  Hypothesis QB : 0x10007fff8000 <= lo /\ lo <= SP - 64 /\ SP <= 2^47.
  Hypothesis UR : 0 <= U /\ U mod 8 = 0 /\ 1 <= size <= 2^28.
  Hypothesis UG : U + size + 8 <= 2147450880 \/ (17594333495296 <= U /\ U + size + 8 <= 2^47).

  Definition unpa_post : machine_state -> Prop :=
    fun ms' => exists ra' t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
      ms' = MS (mkR ra' (wz SP) gp (wz A0_TP) t0 t1 t2 s0 (wz size) a0 a1 a2 a3 a4 a5 a6 a7
                    s2 s3 (wz U) s5 (wz (8 * (size / 8))) s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F_ (wz 0x33b10) fc None m' (seg_rom asegs)
      /\ munch [(SP - 64, SP); (sh U, sh U + size / 8)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
      /\ stk asegs m' lo SP /\ poison_env E m'
      /\ rw_cells asegs m' (sh U) [CB (Z.to_nat (size / 8)) (repeat (Z_to_bv 8 0) (Z.to_nat (size / 8)))].

  #[using="QB UR UG"] Lemma unpa_spec : forall (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s6 t3 t4 t5 t6 : word) (j : list byte),
    mem_inv asegs m -> stk asegs m lo SP -> poison_env E m ->
    rw_cells asegs m (sh U) [CB (Z.to_nat (size / 8)) j] ->
    evt asegs unpa_post
      (MS (mkR ra (wz SP) gp (wz A0_TP) t0 t1 t2 s0 (wz size) a0 a1 a2 a3 a4 a5 a6 a7
               s2 s3 (wz U) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F_ (wz 0x33af0) fc None m (seg_rom asegs)).
  Proof.
    intros ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s6 t3 t4 t5 t6 j MI ST PE SHU.
    assert (SZ8 : exists k, 0 <= k /\ size / 8 = k /\ 8 * k <= size < 8 * k + 8) by (exists (size / 8); clear - UR; Z.div_mod_to_equations; lia).
    destruct SZ8 as (k & K0 & EK & KR). unfold unpa_post. rewrite EK. rewrite EK in SHU.
    zstep. zstep. zstep.
    rewrite (al_land_m8_48 size) by (clear - UR; lia). rewrite EK. replace (k * 8) with (8 * k) by lia.
    zstep. if_cases KZ; zify_cond KZ.
    -
      clear EK. assert (K00 : k = 0) by (clear - KZ K0; lia). subst k.
      apply evt_done. eexists _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, m. split; [reflexivity|].
      split; [apply munch_refl|]. split; [apply wmono_refl|]. split; [exact MI|]. split; [exact ST|]. split; [exact PE|].
      change (Z.to_nat 0) with 0%nat in *. cbn [repeat]. destruct j as [|? ?]; [exact SHU|]. exfalso. destruct SHU as [[WF _] _]. cbn in WF. destruct WF as [WF _]. discriminate WF.
    - zstep. zstep. zstep. zstep.
      assert (E8 : 8 * k / 8 = k) by (clear; Z.div_mod_to_equations; lia).
      pose proof (munch_refl [(SP - 64, SP); (sh U, sh U + 8 * k / 8)] m) as MU. pose proof (wmono_refl asegs m) as WM.
      callk (poison_shadow_spec_all E _ gp (wz A0_TP) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F_ fc SP lo U (8 * k) 0 m MI QB);
        [ split; [exact (proj1 (proj2 UR))|]; split; [clear; Z.div_mod_to_equations; lia|]; split; [clear - K0; lia|]; split; [| clear; lia];
          unfold poison_range; clear - UR UG KR KZ K0; lia
        | exact PE | exact ST | rewrite E8; exact SHU | ].
      rewrite E8 in *.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mP end.
      apply evt_done.
      lazymatch goal with HS : stk asegs mP _ _, HM : mem_inv asegs mP, HP : poison_env E mP, HZ : rw_cells asegs mP (sh U) _ |- _ =>
        eexists _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, mP; split; [reflexivity|];
        split; [exact MU|]; split; [exact WM|]; split; [exact HM|]; split; [exact HS|]; split; [exact HP| exact HZ] end.
  Qed.
End UNPA.

Section UNPB.
  Context {HC : HasCeiling}.
  Variable E : penv.
  Variables (gp s0 s2 s3 s5 s7 s8 s9 s10 s11 : word) (F_ : bvmap 5 word) (fc : bv 32).
  Variables (SP U size : Z) (m : mem).
  Hypothesis UR : 0 <= U /\ U mod 8 = 0 /\ 1 <= size <= 2^28.
  Hypothesis UG : U + size + 8 <= 2147450880 \/ (17594333495296 <= U /\ U + size + 8 <= 2^47).

  Definition unpb_post : machine_state -> Prop :=
    fun ms' => exists ra' t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s6 t3 t4 t5 t6 m',
      ms' = MS (mkR ra' (wz SP) gp (wz A0_TP) t0 t1 t2 s0 (wz size) a0 a1 a2 a3 a4 a5 a6 a7
                    s2 s3 (wz U) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F_ (wz 0x33ba4) fc None m' (seg_rom asegs)
      /\ munch [(sh U + size / 8, sh U + size / 8 + 1)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
      /\ (size mod 8 <> 0 -> rw_cells asegs m' (sh U + size / 8) [C1 (Z_to_bv 8 (size mod 8))])
      /\ (size mod 8 = 0 -> m' = m).

  #[using="UR UG"] Lemma unpb_spec : forall (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    mem_inv asegs m -> poison_env E m -> rw_cells asegs m AF_PARTIAL [C1 (Z_to_bv 8 1)] ->
    (size mod 8 <> 0 -> exists bp, rw_cells asegs m (sh U + size / 8) [C1 bp]) ->
    evt asegs unpb_post
      (MS (mkR ra (wz SP) gp (wz A0_TP) t0 t1 t2 s0 (wz size) a0 a1 a2 a3 a4 a5 a6 a7
               s2 s3 (wz U) s5 (wz (8 * (size / 8))) s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F_ (wz 0x33b10) fc None m (seg_rom asegs)).
  Proof.
    intros ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 MI PE AFP PB.
    assert (SZ8 : exists k r, 0 <= k /\ 0 <= r < 8 /\ size / 8 = k /\ size mod 8 = r /\ size = 8 * k + r)
      by (exists (size / 8), (size mod 8); clear - UR; Z.div_mod_to_equations; lia).
    destruct SZ8 as (k & r & K0 & RR & EK & ER & ESZ). unfold unpb_post. rewrite EK, ER. rewrite EK, ER in PB.
    zstep. if_cases KZ; zify_cond KZ.
    - apply evt_done. eexists _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, m. split; [reflexivity|].
      split; [apply munch_refl|]. split; [apply wmono_refl|]. split; [exact MI|]. split; [intros RN; exfalso; clear - KZ RN ESZ; lia| intros _; reflexivity].
    - assert (RN : r <> 0) by (clear - KZ ESZ; lia). destruct (PB RN) as (bp & PBC). clear PB.
      pose proof (munch_refl [(sh U + k, sh U + k + 1)] m) as MU. pose proof (wmono_refl asegs m) as WM.
      pe_split PE.
      zstep. zstep. zstep.
      replace (sxb (Z_to_bv 8 1)) with (Z_to_bv 64 1) by (apply bv_eq; vm_compute; reflexivity).
      zstep. zstep. zstep.
      zstep. if_false.
      zstep. zstep. zstep. zstep.
      zstep. zstep. zstep. zstep.
      replace (Z.land ((Z.b2z (2147450880 <? 2147450879) + -1) mod 18446744073709551616) 2147450879) with 2147450879 by (vm_compute; reflexivity).
      assert (SHA : 2147450880 + Z.shiftr (U + 8 * k) 3 = sh U + k).
      { rewrite Z.shiftr_div_pow2 by lia. unfold sh, SHADOW_OFF. change (2^3) with 8. clear - UR. Z.div_mod_to_equations. lia. }
      assert (PV : Z.land (Z.land size ((- 1) mod 18446744073709551616)) 7 = r).
      { change ((-1) mod 18446744073709551616) with (Z.ones 64). rewrite (Z.land_ones size 64) by lia. rewrite (Z.mod_small size) by (clear - UR; lia).
        change 7 with (Z.ones 3). rewrite Z.land_ones by lia. change (2^3) with 8. clear - ESZ RR. Z.div_mod_to_equations. lia. }
      zstep. if_cases KL; zify_cond KL.
      +
        zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
        replace (Z.land (Z.land size 18446744073709551615) 7) with r by (symmetry; exact PV). rewrite SHA.
        assert (SHR : 2147450880 <= sh U + k /\ sh U + k + 1 <= 17594333495296)
          by (unfold sh, SHADOW_OFF; clear - UR UG ESZ RR K0; Z.div_mod_to_equations; lia).
        remember (sh U + k) as PA eqn:EPA.
        zstep.
        rewrite (le1_lit_of_mod8 r (Z_to_bv 8 r)) by (rewrite Z_to_bv_small by (change (bv_modulus 8) with 256; clear - RR; lia); clear - RR; Z.div_mod_to_equations; lia).
        mem_after_store.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mQ end.
        apply evt_done. eexists _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, mQ. split; [reflexivity|].
        split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [intros _; exact PBC| intros RZ0; exfalso; exact (RN RZ0)].
      +
        assert (UH : 17594333495296 <= U /\ U + size + 8 <= 2^47) by (clear - UG KL ESZ RR K0; lia).
        zstep. zstep. zstep. zstep. zstep. zstep. zstep.
        zstep. if_cases KM; zify_cond KM.
        2:{ exfalso. clear - KM UH ESZ RR K0. lia. } clear KM.
        zstep. zstep. zstep. zstep. zstep.
        zstep. if_cases KH; zify_cond KH. { exfalso. clear - KH UH ESZ RR K0. lia. } clear KH.
        zstep.
        if_cases KH; zify_cond KH. { exfalso. clear - KH UH ESZ RR K0. lia. } clear KH.
        zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
        replace (Z.land (Z.land size 18446744073709551615) 7) with r by (symmetry; exact PV). rewrite SHA.
        assert (SHR : 2147450880 <= sh U + k /\ sh U + k + 1 <= 17594333495296)
          by (unfold sh, SHADOW_OFF; clear - UR UG ESZ RR K0; Z.div_mod_to_equations; lia).
        remember (sh U + k) as PA eqn:EPA.
        zstep.
        rewrite (le1_lit_of_mod8 r (Z_to_bv 8 r)) by (rewrite Z_to_bv_small by (change (bv_modulus 8) with 256; clear - RR; lia); clear - RR; Z.div_mod_to_equations; lia).
        mem_after_store.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mQ end.
        apply evt_done. eexists _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, mQ. split; [reflexivity|].
        split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [intros _; exact PBC| intros RZ0; exfalso; exact (RN RZ0)].
  Qed.
End UNPB.

Section STATS.
  Context {HC : HasCeiling}.
  Variable L : athread.
  Variables (gp s0 s2 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F_ : bvmap 5 word) (fc : bv 32).
  Variables (SP lo size needed : Z) (m : mem).
  Hypothesis CLO : alloc_ceiling <= lo.
  Hypothesis LOQ : lo <= SP - 32.
  Hypothesis SPR : SP mod 16 = 0 /\ SP + 16 <= 2^47.
  Hypothesis SZ : 1 <= size /\ size + 16 <= needed <= 2^40.
  Hypothesis TL : thread_layout_ok L.

  Definition stats_post : machine_state -> Prop :=
    fun ms' => exists ra' t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' ts',
      ms' = MS (mkR ra' (wz SP) gp (wz A0_TP) t0 t1 t2 s0 (wz size) a0 a1 a2 a3 a4 a5 a6 a7
                    s2 (wz needed) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F_ (wz 0x33d04) fc None m' (seg_rom asegs)
      /\ munch [(SP - 32, SP); (at_thr L + 2800, at_thr L + 3168)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
      /\ stk asegs m' lo SP /\ thread_env L m'
      /\ rw_cells asegs m' (at_thr L + 2800) [CB 368 ts'].

  #[using="HC CLO LOQ SPR SZ TL"] Lemma stats_spec : forall (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (ts : list byte),
    mem_inv asegs m -> stk asegs m lo SP -> thread_env L m ->
    rw_cells asegs m (SP + 8) [C8 (wz 1)] ->
    rw_cells asegs m (at_thr L + 2800) [CB 368 ts] ->
    evt asegs stats_post
      (MS (mkR ra (wz SP) gp (wz A0_TP) t0 t1 t2 s0 (wz size) a0 a1 a2 a3 a4 a5 a6 a7
               s2 (wz needed) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F_ (wz 0x33ba4) fc None m (seg_rom asegs)).
  Proof.
    intros ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 ts MI ST TE FR8 TS.
    pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
    pose proof TL as (T1 & T2 & T3 & T4 & T5 & T6 & T7 & _).
    pose proof (rw_cells_split_CB asegs m (at_thr L + 2800) [] _ ts [] [8%nat; 8%nat; 8%nat; 80%nat; 8%nat; 256%nat] TS ltac:(reflexivity)) as TSS.
    cbn [mk_CB_cells app] in TSS. clear TS.
    lazymatch type of TSS with rw_cells _ _ _ [CB 8 ?j1; CB 8 ?j2; CB 8 ?j3; CB 80 ?j4; CB 8 ?j5; CB 256 ?j6] =>
      remember j1 as w1 eqn:E1; remember j2 as w2 eqn:E2; remember j3 as w3 eqn:E3; remember j4 as w4 eqn:E4; remember j5 as w5 eqn:E5; remember j6 as w6 eqn:E6 end.
    clear E1 E2 E3 E4 E5 E6.
    apply (rw_cells_CB_C8 asegs m _ [] w1) in TSS. cbn [app] in TSS.
    apply (rw_cells_CB_C8 asegs m _ [_] w2) in TSS. cbn [app] in TSS.
    apply (rw_cells_CB_C8 asegs m _ [_; _] w3) in TSS. cbn [app] in TSS.
    apply (rw_cells_CB_C8 asegs m _ [_; _; _; _] w5) in TSS. cbn [app] in TSS.
    pose proof (munch_refl [(SP - 32, SP); (at_thr L + 2800, at_thr L + 3168)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    zstep.
    call (gcts_spec L _ gp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F_ fc SP m lo _ _);
      [ exact ST | exact CLO | exact LOQ | exact (proj1 SPR) | clear - SPR; lia | exact TE | exact TL | exact MI | ].
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mG end.
    zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
    rename POST into TEG. pose proof (munch_refl [(at_thr L + 2800, at_thr L + 3168)] mG) as MUs. pose proof (wmono_refl asegs mG) as WMs.
    zstep. zstep. zstep.
    zstep. if_cases KB; zify_cond KB.
    -
      eapply (evt_cut asegs (fun ms' => exists cid y2 y3 y4 y5 y6, 0 <= cid < 32 /\ ms' =
         MS (mkR (wz 211880) (wz SP) gp (wz A0_TP) t0 t1 t2 s0 (wz size) (wz (at_thr L + 2800 + 112)) (wz cid) y2 y3 y4 y5 y6 a7
                 s2 (wz needed) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F_ (wz 0x33ce8) fc None m0 (seg_rom asegs))).
      { zstep. zstep. zstep. if_cases KS; zify_cond KS.
        -
          assert (LG : exists l, 9 <= l <= 16 /\ 2 ^ l <= needed < 2 ^ (l + 1)).
          { exists (Z.log2 needed). pose proof (Z.log2_spec needed ltac:(clear - KS; lia)) as LS.
            assert (9 <= Z.log2 needed) by (apply Z.log2_le_pow2; [clear - KS; lia| change (2^9) with 512; clear - KS; lia]).
            assert (Z.log2 needed < 17) by (apply Z.log2_lt_pow2; [clear - KS; lia| change (2^17) with 131072; clear - KB; lia]).
            replace (Z.succ (Z.log2 needed)) with (Z.log2 needed + 1) in LS by lia. split; [lia| exact LS]. }
          destruct LG as (l & Hl & HL).
          do 28 zstep.
          match goal with |- context [Z_to_bv 64 (Z.lor ?a (Z.shiftr ?b 32))] => change (Z.lor a (Z.shiftr b 32)) with (smear needed) end.
          rewrite (smear_pow l needed) by (clear - Hl HL; lia).
          match goal with |- context [Z_to_bv 64 (Z.shiftr ?b 32)] => generalize (Z_to_bv 64 (Z.shiftr b 32)); intros jt1 end.
          assert (CR : 0 <= cid_code l needed < 32).
          { pose proof (class_of_range needed ltac:(clear - KS KB; lia)) as CRG. rewrite class_of_cid in CRG.
            replace (needed <=? 512) with false in CRG by (symmetry; apply Z.leb_gt; clear - KS; lia).
            replace (Z.log2 needed) with l in CRG by (symmetry; apply Z.log2_unique; [clear - Hl; lia| exact HL]). clear - CRG. lia. }
          assert (EL : l = 9 \/ l = 10 \/ l = 11 \/ l = 12 \/ l = 13 \/ l = 14 \/ l = 15 \/ l = 16) by (clear - Hl; lia).
          destruct EL as [-> |[-> |[-> |[-> |[-> |[-> |[-> | ->]]]]]]];
            match goal with |- context [Z_to_bv 64 (2 ^ (?LL + 1) - 1)] =>
              let v := eval vm_compute in (2 ^ (LL + 1) - 1) in change (2 ^ (LL + 1) - 1) with v;
              let lo := eval vm_compute in (2 ^ LL) in change (2 ^ LL) with lo in HL;
              let hi := eval vm_compute in (2 ^ (LL + 1)) in change (2 ^ (LL + 1)) with hi in HL end;
            do 27 zstep;
            apply evt_done; eexists _, _, _, _, _, _; (split; [exact CR|]); unfold cid_code; replace (at_thr L + 2800 + 112) with (at_thr L + 2912) by lia; reflexivity.
        -
          zstep. zstep. zstep.
          apply evt_done. eexists ((needed + 31) / 32), _, _, _, _, _. split; [clear - KS SZ; Z.div_mod_to_equations; lia|].
          rewrite Z.shiftr_div_pow2 by lia. change (2^5) with 32. replace (at_thr L + 2800 + 112) with (at_thr L + 2912) by lia. reflexivity. }
      cbv beta. intros msC (cid & y2 & y3 & y4 & y5 & y6 & CID & ->).
      zstep. zstep.
      rewrite Z.shiftl_mul_pow2 by lia. change (2^3) with 8. replace (cid * 8) with (8 * cid) by lia.
      split_chunk TSS 5%nat TSa TSb.
      replace (at_thr L + 2800 + 112) with (at_thr L + 2912) in TSb by lia.
      destruct (cb_word_at m0 (at_thr L + 2912) 256 w6 cid TSb (proj1 CID) ltac:(clear - CID; lia)) as (old & OLDC & BACK). clear TSb.
      assert (PAR : at_thr L + 2912 <= at_thr L + 2912 + 8 * cid /\ at_thr L + 2912 + 8 * cid + 8 <= at_thr L + 3168) by (clear - CID; lia).
      remember (at_thr L + 2912 + 8 * cid) as PA eqn:EPA.
      pose proof (munch_refl [(PA, PA + 8)] m0) as MUb. pose proof (wmono_refl asegs m0) as WMb.
      zstep. zstep. zstep.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
      zstep.
      zstep. if_false.
      assert (TE1 : thread_env L m1).
      { eapply thread_env_frame; [exact TEG| exact MUs| exact WMs|]. unfold thread_clear. constructor; [| constructor]. cbn [fst snd].
        clear - T1 T2 T3 T4 T5 ACR. lia. }
      destruct (BACK m1 _ MUb WMb OLDC) as (bs' & TSb').
      assert (TS1 : exists ts', rw_cells asegs m1 (at_thr L + 2800) [CB 368 ts']).
      { lazymatch type of TSa with rw_cells _ _ _ ?c1 => eapply (rw_cells_ex_CB m1 _ (c1 ++ [CB 256 bs'])); [| reflexivity] end.
        apply rw_cells_app. split; [exact TSa|]. cbn [cells_size csize Nat.add]. replace (at_thr L + 2800 + Z.of_nat 112) with (at_thr L + 2912) by lia. exact TSb'. }
      destruct TS1 as (ts' & TS1).
      apply evt_done. unfold stats_post.
      lazymatch goal with HS : stk asegs m1 _ _, HM : mem_inv asegs m1 |- _ =>
        eexists _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, m1, ts'; split; [reflexivity|];
        split; [exact MU|]; split; [exact WM|]; split; [exact HM|]; split; [exact HS|]; split; [exact TE1| exact TS1] end.
    -
      zstep. zstep. zstep.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
      zstep. zstep. if_true.
      assert (TE1 : thread_env L m1).
      { eapply thread_env_frame; [exact TEG| exact MUs| exact WMs|]. unfold thread_clear. constructor; [| constructor]. cbn [fst snd].
        clear - T1 T2 T3 T4 T5 ACR. lia. }
      destruct (rw_cells_ex_CB m1 _ _ 368%nat TSS ltac:(reflexivity)) as (ts' & TS1).
      apply evt_done. unfold stats_post.
      lazymatch goal with HS : stk asegs m1 _ _, HM : mem_inv asegs m1 |- _ =>
        eexists _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, m1, ts'; split; [reflexivity|];
        split; [exact MU|]; split; [exact WM|]; split; [exact HM|]; split; [exact HS|]; split; [exact TE1| exact TS1] end.
  Qed.
End STATS.

Section FILL.
  Context {HC : HasCeiling}.
  Variable E : penv.
  Variables (gp s0 s2 s3 s5 s6 s7 s8 s9 s10 s11 : word) (F_ : bvmap 5 word) (fc : bv 32).
  Variables (SP U size : Z) (m : mem).
  Hypothesis UR : 0 <= U /\ U + size <= 2^47 /\ 1 <= size <= 2^28.
  Hypothesis SPR : 0 <= SP <= 2^47.

  Definition fill_post : machine_state -> Prop :=
    fun ms' => exists ra' t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' ub',
      ms' = MS (mkR ra' (wz SP) gp (wz A0_TP) t0 t1 t2 s0 (wz size) a0 a1 a2 a3 a4 a5 a6 a7
                    s2 s3 (wz U) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F_ (wz 0x33d38) fc None m' (seg_rom asegs)
      /\ munch [(U, U + Z.min size 4096)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
      /\ rw_cells asegs m' U [CB (Z.to_nat size) ub'].

  #[using="UR"] Lemma fill_spec : forall (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (ub : list byte),
    mem_inv asegs m -> poison_env E m -> alloc_env m ->
    rw_cells asegs m U [CB (Z.to_nat size) ub] ->
    evt asegs fill_post
      (MS (mkR ra (wz SP) gp (wz A0_TP) t0 t1 t2 s0 (wz size) a0 a1 a2 a3 a4 a5 a6 a7
               s2 s3 (wz U) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F_ (wz 0x33d04) fc None m (seg_rom asegs)).
  Proof.
    intros ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 ub MI PE AE UB.
    pe_split PE. ae_split AE.
    hideB UB.
    zstep. zstep. zstep.
    replace (sx32 (Z_to_bv 64 4096)) with (Z_to_bv 64 4096) by (apply bv_eq; vm_compute; reflexivity).
    zstep. if_false.
    zstep.

    eapply (evt_cut asegs (fun ms' => ms' =
       MS (mkR ra (wz SP) gp (wz A0_TP) t0 t1 t2 s0 (wz size) (wz 725240) (wz 4096) (wz (Z.min size 4096)) a3 a4 a5 a6 a7
               s2 s3 (wz U) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F_ (wz 0x33d20) fc None m (seg_rom asegs))).
    { zstep. if_cases KF; zify_cond KF.
      - apply evt_done. replace (Z.min size 4096) with size by (clear - KF; lia). reflexivity.
      - zstep. apply evt_done. replace (Z.min size 4096) with 4096 by (clear - KF; lia). reflexivity. }
    cbv beta. intros msF ->.
    zstep. zstep. zstep. zstep.
    replace (sx32 (Z_to_bv 64 190)) with (Z_to_bv 64 190) by (apply bv_eq; vm_compute; reflexivity).
    zstep. zstep.
    assert (MN : 1 <= Z.min size 4096 <= size /\ Z.min size 4096 <= 4096) by (clear - UR; lia).
    remember (Z.min size 4096) as mn eqn:Emn.
    unhideB UB.
    apply (rw_cells_split_CB asegs m U [] _ ub [] [Z.to_nat mn; (Z.to_nat size - Z.to_nat mn)%nat]) in UB; [| cbn [sum_nat]; clear - MN; lia].
    cbn [mk_CB_cells app] in UB.
    lazymatch type of UB with rw_cells _ _ _ [CB _ ?j1; CB _ ?j2] =>
      change (rw_cells asegs m U ([CB (Z.to_nat mn) j1] ++ [CB (Z.to_nat size - Z.to_nat mn) j2])) in UB; apply rw_cells_app in UB; destruct UB as [UB1 UB2] end.
    cbn [cells_size csize Nat.add] in UB2. rewrite Nat.add_0_r, Z2Nat.id in UB2 by (clear - MN; lia).
    hideB UB2. hideB UB1.
    pose proof (munch_refl [(U, U + mn)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    assert (EU : bv_unsigned (Z_to_bv 64 U) = U) by (apply unsigned_lit; clear - UR; lia).
    assert (EM : bv_unsigned (Z_to_bv 64 mn) = mn) by (apply unsigned_lit; clear - MN; lia).
    unhideB UB1.
    callk (memset_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F_ fc m _); [ rewrite EU, EM; exact UB1 | exact MI | ].
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mF end.
    rewrite EU, EM in *.
    unhideB UB2. eapply (rw_cells_transport asegs _ m mF) in UB2; [| exact MUk| exact WMk| cbn [disjoint_from]; clear; lia].
    assert (UBF : exists ub', rw_cells asegs mF U [CB (Z.to_nat size) ub']).
    { lazymatch type of POST with rw_cells _ _ _ ?c1 => lazymatch type of UB2 with rw_cells _ _ _ ?c2 =>
        eapply (rw_cells_ex_CB mF _ (c1 ++ c2)) end end.
      - apply rw_cells_app. split; [exact POST|]. cbn [cells_size csize Nat.add]. rewrite Nat.add_0_r, Z2Nat.id by (clear - MN; lia). exact UB2.
      - cbn [app cells_size csize Nat.add]. clear - MN. lia. }
    destruct UBF as (ub' & UBF).
    apply evt_done. unfold fill_post.
    eexists _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, mF, ub'. split; [reflexivity|].
    rewrite <- Emn. split; [exact MU|]. split; [exact WM|]. split; [exact MI0| exact UBF].
  Qed.
End FILL.

Section TAIL.
  Context {HC : HasCeiling}.
  Variables (gp : word) (F_ : bvmap 5 word) (fc : bv 32).
  Variables (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word).
  Variables (SP lo B M size : Z) (m : mem).
  Hypothesis CLO : alloc_ceiling <= lo.
  Hypothesis LOQ : lo <= SP - 32.
  Hypothesis SPR : SP mod 16 = 0 /\ SP + 128 <= 2^47.
  Hypothesis BR : 6328320 <= B /\ (B = M \/ B + 16 <= M) /\ M + 16 <= lo /\ 1 <= size <= 2^28.

  Definition tail_post : machine_state -> Prop :=
    fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (bits' : byte),
      ms' = MS (mkR ra (wz (SP + 128)) gp (wz A0_TP) t0 t1 t2 s0 s1 (wz (M + 16)) a1 a2 a3 a4 a5 a6 a7
                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F_ (ret_pc ra) fc None m' (seg_rom asegs)
      /\ munch [(SP - 32, SP); (M, M + 2); (B, B + 16)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
      /\ stk asegs m' lo (SP + 128)
      /\ Z.land (bv_unsigned bits') 3 = 1
      /\ rw_cells asegs m' M [C1 (Z_to_bv 8 2); C1 bits']
      /\ (B <> M -> rw_cells asegs m' B [C8 (wz 14730877155918386873); C8 (wz M)])
      /\ (B = M -> munch [(SP - 32, SP); (M, M + 2)] m m').

  #[using="HC CLO LOQ SPR BR"] Lemma tail_spec : forall (ra' t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x8 x9 x18 x19 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6 : word)
      (b0 bits : byte) (j : list byte) (c1 c2 : word),
    mem_inv asegs m -> stk asegs m lo SP -> hooks_env m -> alloc_env m ->
    rw_cells asegs m SP [CB 8 j; C8 c1; C8 c2; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    rw_cells asegs m M [C1 b0; C1 bits] -> Z.land (bv_unsigned bits) 3 = 1 ->
    (B <> M -> exists lj, rw_cells asegs m B [CB 16 lj]) ->
    evt asegs tail_post
      (MS (mkR ra' (wz SP) gp (wz A0_TP) t0 t1 t2 x8 (wz size) a0 a1 a2 a3 a4 a5 a6 a7
               (wz B) x19 (wz (M + 16)) (wz M) x22 x23 x24 x25 x26 x27 t3 t4 t5 t6)
          F_ (wz 0x33d38) fc None m (seg_rom asegs)).
  Proof.
    intros ra' t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x8 x9 x18 x19 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6 b0 bits j c1 c2 MI ST HKE AE FR HD B3 LCH.
    pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
    ae_split AE. unfold hooks_env in HKE. destruct BR as (B0 & BM & MLO & SZR).
    pose proof (munch_refl [(SP - 32, SP); (M, M + 2); (B, B + 16)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    pose proof (munch_refl [(M, M + 2)] m) as MUh. pose proof (wmono_refl asegs m) as WMh.
    pose proof (munch_refl [(SP - 32, SP); (M, M + 2)] m) as MUp.
    zstep. zstep. zstep. zstep. zstep.
    change (sx32 (Z_to_bv 64 0)) with (Z_to_bv 64 0).
    zstep. zstep.
    zstep. zstep. zstep. zstep. zstep. zstep.
    replace (Z.land (bv_swrap 32 (0 - Z.b2z (9223372036854775808 <? 9223372036854775808)) mod 18446744073709551616) 12) with 0 by (vm_compute; reflexivity).
    pose proof (byte_lt256 bits) as BU. remember (bv_unsigned bits) as bu eqn:Ebu.
    destruct (hb3_facts bu BU B3) as (HB3 & HB3R & HB33).
    change (Z.lor (Z.land bu 243) 0) with (hb3 bu).
    zstep.
    rewrite (le1_lit_of_mod8 (hb3 bu) (Z_to_bv 8 (hb3 bu))) by (rewrite HB3; symmetry; apply Z_to_bv_small; change (bv_modulus 8) with 256; exact HB3R).
    mem_after_store.
    zstep. sstep.
    zstep. if_cases KE; zify_cond KE.
    -
      clear MUh WMh.
      zstep. zstep. zstep.
      call (malloc_hooks_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F_ fc SP m1 lo _ _ _);
        [ assumption | exact CLO | exact LOQ | exact (proj1 SPR) | clear - SPR; lia | exact HKE | assumption | ].
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mH end.
      do 15 zstep.
      zstep.
      lazymatch goal with HS : stk asegs mH _ _ |- _ => rename HS into STH end.
      release_frame FR STH (SP + 128).
      apply evt_done. unfold tail_post.
      lazymatch goal with HM : mem_inv asegs mH |- _ =>
        eexists _, _, _, _, _, _, _, _, _, _, _, _, _, _, mH, (Z_to_bv 8 (hb3 bu)); split; [reflexivity|];
        split; [exact MU|]; split; [exact WM|]; split; [exact HM|]; split; [exact STH|];
        split; [rewrite Z_to_bv_small by (change (bv_modulus 8) with 256; exact HB3R); exact HB33|]; split; [exact HD|] end.
      split; [intros NE; exfalso; clear - NE KE; lia| intros _; exact MUp].
    -
      assert (BM16 : B + 16 <= M) by (clear - BM KE; lia).
      destruct (LCH (fun e => KE (eq_sym e))) as (lj & LC). clear LCH.
      eapply (rw_cells_transport asegs _ m m1) in LC; [| exact MUh| exact WMh| cbn [disjoint_from cells_size csize Nat.add]; clear - BM16; lia].
      pose proof (rw_cells_split_CB asegs m1 B [] _ lj [] [8%nat; 8%nat] LC ltac:(reflexivity)) as LC2. cbn [mk_CB_cells app] in LC2. clear LC.
      zstep. zstep. if_cases KL; zify_cond KL. { exfalso. clear - KL BM16. lia. } clear KL.
      clear MUh WMh MUp.
      zstep. zstep. zstep. zstep. sstep.
      zstep. zstep. zstep.
      call (malloc_hooks_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F_ fc SP _ lo _ _ _);
        [ assumption | exact CLO | exact LOQ | exact (proj1 SPR) | clear - SPR; lia | exact HKE | assumption | ].
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mH end.
      do 15 zstep.
      zstep.
      lazymatch goal with HS : stk asegs mH _ _ |- _ => rename HS into STH end.
      release_frame FR STH (SP + 128).
      apply evt_done. unfold tail_post.
      lazymatch goal with HM : mem_inv asegs mH |- _ =>
        eexists _, _, _, _, _, _, _, _, _, _, _, _, _, _, mH, (Z_to_bv 8 (hb3 bu)); split; [reflexivity|];
        split; [exact MU|]; split; [exact WM|]; split; [exact HM|]; split; [exact STH|];
        split; [rewrite Z_to_bv_small by (change (bv_modulus 8) with 256; exact HB3R); exact HB33|]; split; [exact HD|] end.
      split; [intros _; exact LC2| intros EBM; exfalso; clear - EBM KE; lia].
  Qed.
End TAIL.

