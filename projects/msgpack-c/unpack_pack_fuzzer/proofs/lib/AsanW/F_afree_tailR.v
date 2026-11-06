(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib Require Arr InitMem.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require StrFun.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec Require AsanCtrl AsanEmbed.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require AImg ABase AQConst ABytes.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA Require StepF.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require AKit AKit2 AKitQ.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require F_apoison.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require F_aenqueue.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require F_adrain F_aput F_afree_tail.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require RunDraw.
Module F_afree_tailR.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase. Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics. Import LinuxProcessSemantics.LinuxProcessSem.MemImageType. Import LinuxProcessSemantics.LinuxProcessSem.State. Import LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude. Import LinuxProcessSemantics.Riscv.Instr. Import LinuxProcessSemantics.Riscv.Decode. Import LinuxProcessSemantics.Riscv.DecodeC. Import LinuxProcessSemantics.Riscv.Sem. Import LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Arr. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.InitMem.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.StrFun.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanCtrl. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanEmbed.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AImg. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ABase. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AQConst. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ABytes.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.StepF.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AKit. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AKit2. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AKitQ.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_apoison.F_apoison.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aenqueue.F_aenqueue.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aenqueue.F_aenqueueR. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_adrain. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aput. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_afree_tail.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Local Lemma outside_In8 : forall (W : list ivl) x lo hi, outside W x -> In (lo, hi) W -> ~ (lo <= x < hi)%Z.
Proof. induction W as [|[a b] W IH]; cbn; intros x lo hi H HI; [tauto|]. destruct HI as [E|HI]; [injection E; intros; subst; tauto| apply (IH x); tauto]. Qed.
Local Lemma sub_fp_cover8 : forall W W' : list ivl,
  Forall (fun iv : ivl => (snd iv <= fst iv)%Z \/ Exists (fun jv : ivl => (fst jv <= fst iv /\ snd iv <= snd jv)%Z) W') W -> sub_fp W W'.
Proof.
  intros W W' HF x HO. induction HF as [|[lo hi] W HP HF IH]; cbn; [exact I|]. split; [| exact IH].
  cbn in HP. destruct HP as [HE|HP]; [lia|]. apply Exists_exists in HP. destruct HP as ([lo' hi'] & HI & [H1 H2]). cbn in H1, H2.
  pose proof (outside_In8 _ _ _ _ HO HI). lia.
Qed.
Local Ltac fp_cheap8 := first [ match goal with Hs : bv_unsigned _ = (bv_unsigned _ + _)%Z |- _ => clear -Hs end | clear ]; Stdlib.micromega.Lia.lia.
Local Ltac fp_find8c := first [ apply Exists_cons_hd; cbn [fst snd]; split; fp_cheap8 | apply Exists_cons_tl; fp_find8c ].
Local Ltac fp_find8 := first [ apply Exists_cons_hd; cbn [fst snd]; split; lia | apply Exists_cons_tl; fp_find8 ].
Local Ltac fp_cover8 := apply sub_fp_cover8; repeat (apply Forall_cons; [ cbn [fst snd]; first [left; fp_cheap8 | right; fp_find8c | right; fp_find8] | ]); apply Forall_nil.

Local Ltac transport_after_call segs m m' MU WM ::=
  let W := lazymatch type of MU with munch ?W _ _ => W end in
  repeat match goal with
  | H : bytes_at segs m ?A2 ?bs2 |- _ =>
      first [ apply (bytes_at_transport segs W m m' A2 bs2) in H; [ | exact MU | cbn [disjoint_from]; simpl_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : wr_at segs m ?A2 ?n2 |- _ => apply (wr_at_transport segs m m' A2 n2) in H; [ | exact WM ]
  | H : rw_cells segs m ?A2 ?cs2 |- _ =>
      first [ apply (rw_cells_transport segs W m m' A2 cs2) in H; [ | exact MU | exact WM | cbn [disjoint_from]; simpl_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : ro_cells segs m ?A2 ?cs2 |- _ =>
      first [ apply (ro_cells_transport segs W m m' A2 cs2) in H; [ | exact MU | cbn [disjoint_from]; simpl_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : u8arr segs m ?A2 ?xs |- _ =>
      first [ apply (u8arr_transport segs W m m' A2 xs) in H; [ | exact MU | exact WM | cbn [disjoint_from]; simpl_sizes; simpl_arr_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : u32arr segs m ?A2 ?xs |- _ =>
      first [ apply (u32arr_transport segs W m m' A2 xs) in H; [ | exact MU | exact WM | cbn [disjoint_from]; simpl_sizes; simpl_arr_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : u64arr segs m ?A2 ?xs |- _ =>
      first [ apply (u64arr_transport segs W m m' A2 xs) in H; [ | exact MU | exact WM | cbn [disjoint_from]; simpl_sizes; simpl_arr_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : u8ro segs m ?A2 ?xs |- _ =>
      first [ apply (u8ro_transport segs W m m' A2 xs) in H; [ | exact MU | cbn [disjoint_from]; simpl_sizes; simpl_arr_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : stk segs m ?loq ?hiq |- _ =>
      first [ apply (stk_transport_disjoint segs W m m' loq hiq) in H; [ | exact MU | exact WM | cbn [disjoint_from]; slia ]
            | clear H ]
  | H : munch ?Wq ?mq m |- _ =>
      first [ apply (munch_trans Wq mq m m') in H; [ | eapply (munch_weaken W Wq m m'); [ first [ fp_cover8 | unfold sub_fp; cbn [outside]; first [ match goal with Hs : bv_unsigned _ = (bv_unsigned _ + _)%Z |- _ => clear -Hs; intros; lia end | clear; intros; lia | intros; slia ] ] | exact MU ] ]
            | fail 100 "callee footprint not inside caller footprint" ]
  | H : wmono segs ?mq m |- _ => apply (wmono_trans segs mq m m') in H; [ | exact WM ]
  end.

Local Ltac band_lin :=
  repeat match goal with H : iclr ?a ?n |- _ => unfold iclr, AIMG_LO, AIMG_HI in H end.
Local Ltac with_band H tac :=
  let H' := fresh H in pose proof H as H'; unfold sclr, iclr, ablk, KLS, AIMG_LO, AIMG_HI in H'; tac; try clear H'.

Local Ltac with_sclr tac := idtac; match goal with H : sclr ?a ?n |- _ => with_band H tac | _ => tac end.

Local Lemma sclr_int : forall a n, sclr a n -> 0 <= a -> a + n <= 18446744073709551616 ->
  exists k, 0 <= k <= 1 /\ a + n <= 2147446784 + k * 18446744073709551616 /\ 17594333495296 * k <= a.
Proof. intros a n H G1 G2. unfold sclr, KLS in H. destruct H; [exists 0 | exists 1]; lia. Qed.
Local Lemma iclr_int : forall a n, iclr a n -> a + n <= 18446744073709551616 ->
  exists k, 0 <= k <= 1 /\ 4096 <= a /\ a + n <= 65536 + k * 18446744073709551616 /\ 6483968 * k <= a.
Proof. intros a n H G2. unfold iclr, AIMG_LO, AIMG_HI in H. destruct H as [? [?|?]]; [exists 0 | exists 1]; lia. Qed.
Local Lemma ablk_int {rc : runConstT} : forall lo hi, ablk lo hi ->
  exists k, 0 <= k <= 1 /\ 6483968 <= lo /\ 17594333495296 * k <= lo /\ hi <= 2147446784 + k * 18446744073709551616 /\ hi <= ATOP.
Proof. intros lo hi H. unfold ablk, KLS, AIMG_HI in H. pose proof atop_range. destruct H as [[? ?]|[? ?]]; [exists 0 | exists 1]; lia. Qed.
Local Ltac band_int H :=
  let k := fresh "k" H in let A := fresh "KA" H in let B := fresh "KB" H in let C := fresh "KC" H in let D := fresh "KD" H in
  let G1 := fresh "G" in let G2 := fresh "G" in
  lazymatch type of H with
  | sclr ?a ?n =>
      assert (G1 : 0 <= a) by (atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia); assert (G2 : a + n <= 18446744073709551616) by (atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia);
      destruct (sclr_int a n H G1 G2) as (k & A & B & C); clear G1 G2
  | iclr ?a ?n =>
      assert (G2 : a + n <= 18446744073709551616) by (atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia);
      destruct (iclr_int a n H G2) as (k & A & B & C & D); clear G2
  | 4096 <= ?a /\ (?a + ?n <= _ \/ _ <= ?a) =>
      assert (G2 : a + n <= 18446744073709551616) by (atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia);
      destruct (iclr_int a n H G2) as (k & A & B & C & D); clear G2
  | ablk ?lo ?hi => let E := fresh "KE" H in destruct (ablk_int lo hi H) as (k & A & B & E & C & D)
  end.

Ltac ub H := let X := fresh "Y" in pose proof H as X; unbox X.

Section CANSEC1. Context {rc : runConstT}.
Definition put_to_refill_post (full : bool) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a2 a3 : word) (F : bvmap 5 word) (fc : bv 32)
    (t hm n lo lst nx bsz : Z) (hs : list word) (m : amem) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 : word) m' (j0 : list byte),
    ms' = MS (mkR (Z_to_bv 64 0x41390) (Z_to_bv 64 (bv_unsigned sp + -144)) gp tp t0 t1 t2
                  (Z_to_bv 64 (t + 2128)) (Z_to_bv 64 (t + 208))
                  (Z_to_bv 64 (t + 208)) (Z_to_bv 64 (t + 2128)) (Z_to_bv 64 0xd6458) (Z_to_bv 64 K_BATCH_CLASS) a4 a5 a6 a7
                  (Z_to_bv 64 hm) (Z_to_bv 64 (t + 80)) a3 (Z_to_bv 64 n) (Z_to_bv 64 Q_CACHE) s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x41b70) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 144, bv_unsigned sp); (shad (hm + 16), shad (hm + 16) + shlen (rup n 8))]%Z m m'
    /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp + -144)
    /\ rw_cells asegs m' (shad (hm + 16)) [CB (Z.to_nat (shlen (rup n 8))) (repeat (Z_to_bv 8 253) (Z.to_nat (shlen (rup n 8))))]
    /\ rw_cells asegs m' (bv_unsigned sp + -80) [C8 a2; C8 a3; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
    /\ rw_cells asegs m' (bv_unsigned sp + -144)
         [CB 8 j0; C8 (Z_to_bv 64 hm); C8 a2; C8 a3; C8 (Z_to_bv 64 n); C8 (Z_to_bv 64 (t + 80)); C8 (Z_to_bv 64 0xd6730); C8 (Z_to_bv 64 0x41230)]
    /\ (if full then rw_cells asegs m' lst [C8 (Z_to_bv 64 nx); C8 (Z_to_bv 64 bsz); C8 (Z_to_bv 64 1021)] /\ u64arr asegs m' (lst + 24) hs else True).

Lemma put_to_refill_spec : forall (full : bool) (t hm lst : Z) RNG
    ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (n nb fst0 qb b1 actx lo nx bsz : Z) (maxc csz : word) (hs : list word) (sjunk : list byte),
  stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - 144 ->
  mem_inv asegs m ->
  a0 = Z_to_bv 64 0xd6730 -> a1 = Z_to_bv 64 (t + 80) -> a2 = Z_to_bv 64 (t + 208) -> a4 = Z_to_bv 64 hm -> a5 = Z_to_bv 64 n ->

  rw_cells asegs m 0xd6770 [C8 (Z_to_bv 64 Q_MAX); C8 (Z_to_bv 64 Q_MIN); C8 (Z_to_bv 64 Q_CACHE)] ->
  rw_cells asegs m 0xd1510 [C8 (Z_to_bv 64 AFLAGS)] ->
  rw_cells asegs m 0xd72e4 [C4 (Z_to_bv 64 0x1000); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0xbe)] ->
  poison_cells m ->

  rw_cells asegs m hm [C1 (Z_to_bv 8 3); C1 (Z_to_bv 8 b1); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 (Z_to_bv 64 actx)] ->
  1 <= n <= Q_MAX -> 0 <= b1 < 256 -> hm mod 16 = 0 -> ablk hm (hm + 16 + rup n 8) -> hm + 16 + rup n 8 <= ATOP -> hm + 16 <= ATOP ->
  rw_cells asegs m (shad (hm + 16)) [CB (Z.to_nat (shlen (rup n 8))) sjunk] ->

  rw_cells asegs m (t + 80) [C8 (Z_to_bv 64 nb); C8 (Z_to_bv 64 fst0); C8 (Z_to_bv 64 lst); C8 (Z_to_bv 64 qb)] ->
  0 <= nb < 2^62 -> 0 <= lst < 2^64 ->
  sclr t 4096 -> t + 4096 <= ATOP -> t mod 4096 = 0 -> (hm + 16 <= t \/ t + 4096 <= hm) ->

  (if full then 0 < nb /\ rw_cells asegs m lst [C8 (Z_to_bv 64 nx); C8 (Z_to_bv 64 bsz); C8 (Z_to_bv 64 1021)]
             /\ 0x10007fff8000 <= lst /\ lst + 8192 <= ATOP
             /\ u64arr asegs m (lst + 24) hs /\ length hs = 1021%nat /\ rng RNG lst 8192
   else nb = 0 /\ lst = 0) ->
  rw_cells asegs m (t + 2128) [C4 (Z_to_bv 64 0); C4 maxc; C8 csz] ->
  (t + 4096 <= lst \/ lst + 8192 <= t \/ lst = 0) -> (hm + 16 <= lst \/ lst + 8192 <= hm) ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG t 4096 -> rng RNG hm 16 -> rng RNG (shad (hm + 16)) (shlen (rup n 8)) ->
  iclr t 4096 ->
  evtF asegs RNG (put_to_refill_post full ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a2 a3 F fc t hm n lo lst nx bsz hs m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x4108c) fc None m (seg_rom asegs)).
Proof.
  intros until sjunk. intros ST CEIL LO MI -> -> -> -> -> QK GF FLG PC HD N B1 AL HLO HHI HCE SH QC NB LST T0 T1 TAL DHT FULL CR DTL DHL RIMG RSTK RT RH RSH TI.
  band_int TI. pose proof (ablk_lin _ _ HLO) as (HL1 & HL2 & HL3 & HL4). unfold AIMG_HI in HL1. band_int HLO. band_lin. band_int T0.
  assert (SHB : 2148261376 <= shad (hm + 16) /\ shad (hm + 16) + shlen (rup n 8) <= 0x10007fff8000).
  { unfold shad, shlen, ASHOFF. rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8. unfold Q_MAX in N. Z.div_mod_to_equations. lia. }
  assert (RUP : n <= rup n 8 <= n + 7 /\ rup n 8 mod 8 = 0) by (unfold rup; Z.div_mod_to_equations; lia).
  assert (SHL : 0 < shlen (rup n 8) < 0x10000000) by (unfold shlen; rewrite Z.shiftr_div_pow2 by lia; unfold Q_MAX in N; Z.div_mod_to_equations; lia).
  word_range sp SPR.
  pose proof (munch_refl [(bv_unsigned sp - 144, bv_unsigned sp); (shad (hm + 16), shad (hm + 16) + shlen (rup n 8))]%Z m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  destruct PC as (P1 & P2 & P3 & P4 & P5 & P6 & P7).
  box DHT. box DTL. box DHL.
  destruct full; [destruct FULL as (NB1 & LB & L0 & L1 & LA0 & LEN0 & RL) | destruct FULL as [NB0 LST0]];
  unfold AIMG_HI in *.
  -
    box ST.
    call (putA_spec t hm n); try unboxed ST; try eassumption; try reflexivity; try (unfold Q_MAX, AIMG_HI in *; lia).
    try clear ST.
    rename POST into FRP.
    match goal with H : stk asegs ?mm lo _ |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename H into ST end. try rename MI0 into MI.
    box SH.
    box ST.
    step. call_sp (poison_shadow_spec RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ (hm + 16) (rup n 8) 253 lo sjunk);
      [unboxed ST| exact CEIL| lia| exact MI| repeat (split; [assumption|]); assumption| reflexivity| reflexivity| reflexivity
      | Z.div_mod_to_equations; lia| lia| lia| first [assumption | (eapply ablk_sub; [exact HLO| clear; lia| clear; lia]) | unfold ablk; right; lia | unfold ablk; left; lia]| lia| lia| lia| unboxed SH|].
    try clear ST.
    clear SH.
    try rename MI0 into MI. clear P1 P2 P3 P4 P5 P6 P7.
    match goal with H : stk asegs ?mm lo _ |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename H into ST end.
    match goal with H : rw_cells asegs ?mm (shad (hm + 16)) _ |- _ => rename H into SH' end.
    do 5 step.
    step.
    box HD. box SH'. box LA0. box LB. box FRP.
    snapshot [(bv_unsigned sp + -80 - 64, bv_unsigned sp + -80)]%Z MUe WMe.
    box ST.
    call_sp (enqueue_to_refill_spec true t lst RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ nb fst0 qb hm n nx bsz lo maxc csz);
      [unboxed ST| exact CEIL| lia| exact MI| reflexivity| reflexivity| reflexivity| reflexivity| exact QC| lia| lia
      | split; [lia|]; split; [ub LB; exact Y|]; split; [unfold AIMG_HI; lia|]; split; [unfold Q_BATCH_BYTES; lia| exact RL]
      | exact CR| exact TI| atop_facts; lia| exact TAL| ub DTL; unfold Q_BATCH_BYTES; lia|].
    try clear ST.
    try rename MI0 into MI.
    match goal with H : stk asegs ?mm lo _ |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename H into ST end.
    carry HD MUe WMe ltac:(lia). carry SH' MUe WMe ltac:(lia). carry LA0 MUe WMe ltac:(rewrite LEN0; lia). carry LB MUe WMe ltac:(lia). carry FRP MUe WMe ltac:(lia). clear MUe WMe.
    replace (bv_unsigned sp + -80 + -64) with (bv_unsigned sp + -144) in * by lia.
    unfold put_to_refill_post. finish.
    all: try assumption. all: try eassumption. all: try exact I. all: try (split; assumption).
  -
    box ST.
    call (putA_spec t hm n); try unboxed ST; try eassumption; try reflexivity; try (unfold Q_MAX, AIMG_HI in *; lia).
    try clear ST.
    rename POST into FRP.
    match goal with H : stk asegs ?mm lo _ |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename H into ST end. try rename MI0 into MI.
    box SH.
    box ST.
    step. call_sp (poison_shadow_spec RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ (hm + 16) (rup n 8) 253 lo sjunk);
      [unboxed ST| exact CEIL| lia| exact MI| repeat (split; [assumption|]); assumption| reflexivity| reflexivity| reflexivity
      | Z.div_mod_to_equations; lia| lia| lia| first [assumption | (eapply ablk_sub; [exact HLO| clear; lia| clear; lia]) | unfold ablk; right; lia | unfold ablk; left; lia]| lia| lia| lia| unboxed SH|].
    try clear ST.
    clear SH.
    try rename MI0 into MI. clear P1 P2 P3 P4 P5 P6 P7.
    match goal with H : stk asegs ?mm lo _ |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename H into ST end.
    match goal with H : rw_cells asegs ?mm (shad (hm + 16)) _ |- _ => rename H into SH' end.
    do 5 step.
    step.
    box HD. box SH'. box FRP.
    snapshot [(bv_unsigned sp + -80 - 64, bv_unsigned sp + -80)]%Z MUe WMe.
    box ST.
    call_sp (enqueue_to_refill_spec false t lst RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ nb fst0 qb hm n nx bsz lo maxc csz);
      [unboxed ST| exact CEIL| lia| exact MI| reflexivity| reflexivity| reflexivity| reflexivity| exact QC| lia| lia
      | exact NB0
      | exact CR| exact TI| atop_facts; lia| exact TAL| ub DTL; unfold Q_BATCH_BYTES; lia|].
    try clear ST.
    try rename MI0 into MI.
    match goal with H : stk asegs ?mm lo _ |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename H into ST end.
    carry HD MUe WMe ltac:(lia). carry SH' MUe WMe ltac:(lia). carry FRP MUe WMe ltac:(lia). clear MUe WMe.
    replace (bv_unsigned sp + -80 + -64) with (bv_unsigned sp + -144) in * by lia.
    unfold put_to_refill_post. finish.
    all: try assumption. all: try eassumption. all: try exact I.
Qed.

Lemma put_from_refill_spec : forall (full : bool) (g : gqd) (t hm lst b : Z) RNG
    (ra sp gp tp s0 s1 a2 a3 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (ra0 t0 t1 t2 a1 a2' a3' a4 a5 a6 a7 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) fc (m : amem) (n nb fst0 qb b1 actx lo nx bsz cnt spacebeg : Z) (maxc csz stj idxw : word) (chunks hs : list word)
    (j0 : list byte),
  let ek := EkNew full nx bsz cnt maxc csz stj idxw chunks spacebeg b hs in
  stk asegs m lo (bv_unsigned sp + -144) -> ATOP <= lo -> lo <= bv_unsigned sp - 144 ->
  mem_inv asegs m ->
  a2 = Z_to_bv 64 (t + 208) ->

  rw_cells asegs m (bv_unsigned sp + -80) [C8 a2; C8 a3; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  rw_cells asegs m (bv_unsigned sp + -144)
     [CB 8 j0; C8 (Z_to_bv 64 hm); C8 a2; C8 a3; C8 (Z_to_bv 64 n); C8 (Z_to_bv 64 (t + 80)); C8 (Z_to_bv 64 0xd6730); C8 (Z_to_bv 64 0x41230)] ->

  rw_cells asegs m 0xd6770 [C8 (Z_to_bv 64 Q_MAX); C8 (Z_to_bv 64 Q_MIN); C8 (Z_to_bv 64 Q_CACHE)] ->

  rw_cells asegs m hm [C1 (Z_to_bv 8 3); C1 (Z_to_bv 8 b1); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 (Z_to_bv 64 actx)] ->
  1 <= n <= Q_MAX -> hm mod 16 = 0 -> ablk hm (hm + 16 + rup n 8) -> hm + 16 + rup n 8 <= ATOP -> hm + 16 <= ATOP ->
  rw_cells asegs m (shad (hm + 16)) [CB (Z.to_nat (shlen (rup n 8))) (repeat (Z_to_bv 8 253) (Z.to_nat (shlen (rup n 8))))] ->

  rw_cells asegs m (t + 80) [C8 (Z_to_bv 64 nb); C8 (Z_to_bv 64 fst0); C8 (Z_to_bv 64 lst); C8 (Z_to_bv 64 qb)] ->
  0 <= nb < 2^62 -> 0 <= qb -> qb + n + 8192 < 2^62 -> 0 <= fst0 < 2^64 -> 0 <= lst < 2^64 ->
  sclr t 4096 -> t + 4096 <= ATOP -> t mod 4096 = 0 -> (hm + 16 <= t \/ t + 4096 <= hm) ->

  (if full then 0 < nb /\ rw_cells asegs m lst [C8 (Z_to_bv 64 nx); C8 (Z_to_bv 64 bsz); C8 (Z_to_bv 64 1021)]
             /\ 0 <= nx < 2^64 /\ 0 <= bsz < 2^64 /\ 0x10007fff8000 <= lst /\ lst + 8192 <= ATOP
             /\ u64arr asegs m (lst + 24) hs /\ length hs = 1021%nat
             /\ rng RNG lst 8192
   else nb = 0 /\ lst = 0) ->
  rw_cells asegs m 0xd6478 [C8 (Z_to_bv 64 spacebeg)] ->
  rw_cells asegs m (t + 2128) [C4 (Z_to_bv 64 cnt); C4 maxc; C8 csz] ->
  u32arr asegs m (t + 2128 + 16) chunks -> length chunks = 16%nat ->
  0 < cnt <= 16 -> nth_error chunks (Z.to_nat (cnt - 1)) = Some idxw -> bv_unsigned idxw < 2^32 ->
  rw_cells asegs m (t + 2784) [C8 stj] ->
  b = spacebeg + 24 * 2^32 + 16 * bv_unsigned idxw ->
  (exists bs, rw_cells asegs m b [CB (Z.to_nat 8192) bs]) ->
  0 < spacebeg -> 0x10007fff8000 <= b -> b + 8192 <= ATOP ->
  (t + 4096 <= b \/ b + 8192 <= t) -> (t + 4096 <= lst \/ lst + 8192 <= t \/ lst = 0) -> (b + 8192 <= lst \/ lst + 8192 <= b) ->
  (hm + 16 <= b \/ b + 8192 <= hm) -> (hm + 16 <= lst \/ lst + 8192 <= hm) ->
  rng RNG b 8192 ->

  dk_pre ek g RNG t lst hm (qb + ek_delta ek n) m ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG t 4096 -> rng RNG hm 16 -> rng RNG (shad (hm + 16)) (shlen (rup n 8)) ->
  iclr t 4096 ->
  evtF asegs RNG (put_tail_post ek g ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc t hm n nb fst0 lst qb b1 actx lo m)
    (MS (mkR ra0 (Z_to_bv 64 (bv_unsigned sp + -144)) gp tp t0 t1 t2 (Z_to_bv 64 (t + 2128)) (Z_to_bv 64 (t + 208))
             (Z_to_bv 64 1) a1 a2' a3' a4 a5 a6 a7
             (Z_to_bv 64 hm) (Z_to_bv 64 (t + 80)) a3 (Z_to_bv 64 n) (Z_to_bv 64 Q_CACHE) s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x41390) fc None m (seg_rom asegs)).
Proof.
  intros until j0. cbv zeta. intros ST CEIL LO MI -> FRP FRE QK HD N AL HLO HHI HCE SH' QC NB QB QBN FST LST T0 T1 TAL DHT
    FULL SB CR CH LCH CNT NTH IXS STS HB BJ SBP B0 BL1 DTB DTL DBL DHB DHL RB DK RIMG RSTK RT RH RSH TI.
  band_int TI. pose proof (ablk_lin _ _ HLO) as (HL1 & HL2 & HL3 & HL4). unfold AIMG_HI in HL1. band_int HLO. band_lin. band_int T0.
  assert (SHB : 2148261376 <= shad (hm + 16) /\ shad (hm + 16) + shlen (rup n 8) <= 0x10007fff8000).
  { unfold shad, shlen, ASHOFF. rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8. unfold Q_MAX in N. Z.div_mod_to_equations. lia. }
  assert (RUP : n <= rup n 8 <= n + 7 /\ rup n 8 mod 8 = 0) by (unfold rup; Z.div_mod_to_equations; lia).
  assert (SHL : 0 < shlen (rup n 8) < 0x10000000) by (unfold shlen; rewrite Z.shiftr_div_pow2 by lia; unfold Q_MAX in N; Z.div_mod_to_equations; lia).
  word_range sp SPR.
  pose proof (munch_refl [(bv_unsigned sp - 144, bv_unsigned sp); (shad (hm + 16), shad (hm + 16) + shlen (rup n 8));
              (t + 80, t + 112); (t + 2128, t + 2132); (t + 2784, t + 2792);
              (lst, lst + qsz lst); (b, b + 8192);
              (0xd67c8, 0xd67c8 + 4); (0xd67d0, 0xd67d0 + 32); (dk_glst g lst, dk_glst g lst + 8)]%Z m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  pose proof QK as QK0. rw_split QK0 1%nat QMX QK2. clear QK2.
  box DHT. box DTB. box DTL. box DBL. box DHB. box DHL.
  destruct BJ as [junkb BJ].
  destruct full; [destruct FULL as (NB1 & LB & NX & BSZ & L0 & L1 & LA0 & LEN0 & RL) | destruct FULL as [NB0 LST0]];
  unfold dk_glst in *; cbn [ek_pre dk_pre ek_b ek_nb ek_fst ek_lst ek_delta] in *;
  destruct DK as (MX & GC & GNB & GQB & GFST & GLST & DK');
  (destruct (g_drain g) eqn:EGD;
   [ destruct DK' as (QB1 & GQ & GFULL);
     destruct (g_full g) eqn:EGF;
     [destruct GFULL as (G1 & GLB & G3 & G4 & G5 & G6 & G7 & G8 & G9); box G5; box G6; box G7; box G8 | destruct GFULL as [GNB0 GLST0]]
   | rename DK' into QB1 ]);
  rewrite ?EGD in *; cbn [ek_pre dk_pre ek_b ek_nb ek_fst ek_lst ek_delta dk_glst] in *; unfold AIMG_HI in *.
  all: first [assert (QZE : qsz lst = 8192) by (apply qsz_pos; generalize L0; clear; intros; lia) | assert (QZE : qsz lst = 8) by (apply qsz_eq0; exact LST0)]; rewrite QZE in *.
  -
    box HD. box CH. box SH'. box GLB. box LA0. box FRP.
    snapshot [(t + 80, t + 112); (t + 2128, t + 2128 + 4); (t + 2784, t + 2784 + 8); (lst, lst + 8); (b, b + 8192)]%Z MUe WMe.
    box BJ. box STS. box CR. box LB. box QC.
    box ST.
    call_sp (enqueue_from_refill_spec true t lst b RNG _ _ _ _ _ _ _
               (Z_to_bv 64 0x41230) (Z_to_bv 64 0xd6730) (Z_to_bv 64 (t + 80)) (Z_to_bv 64 n) a3 (Z_to_bv 64 (t + 208)) (Z_to_bv 64 hm)
               _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ nb fst0 qb hm n nx bsz cnt spacebeg lo maxc csz stj idxw chunks j0);
      [unboxed ST| exact CEIL| lia| lia| exact MI| exact FRE| unboxed QC| lia| lia| unfold Q_BATCH_BYTES, Q_MAX in *; lia
      | lia| lia| lia| lia
      | split; [lia|]; split; [unboxed LB|]; unfold AIMG_HI, Q_BATCH_BYTES; repeat split; try assumption; lia
      | exact SB| unboxed CR| ub CH; exact Y| exact LCH| exact CNT| exact NTH| exact IXS| unboxed STS| unfold K_BATCH_CLASS; lia| exists junkb; unboxed BJ
      | exact TI| atop_facts; lia| exact TAL| lia| unfold AIMG_HI; lia| unfold Q_BATCH_BYTES; lia
      | ub DTB; unfold Q_BATCH_BYTES; lia| ub DTL; unfold Q_BATCH_BYTES; lia| ub DBL; unfold Q_BATCH_BYTES; lia|].
    clear BJ STS CR LB QC.
    try rename MI0 into MI.
    replace (bv_unsigned sp + -144 + 64) with (bv_unsigned sp + -80) in * by lia.
    clear ST. match goal with H : stk asegs ?mm lo (bv_unsigned sp + -80) |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename H into ST end.
    carry HD MUe WMe ltac:(ub DHT; ub DHL; ub DHB; lia). carry CH MUe WMe ltac:(rewrite LCH; ub DTL; ub DTB; lia). carry SH' MUe WMe ltac:(lia). carry LA0 MUe WMe ltac:(rewrite LEN0; ub DTL; ub DBL; lia). carry GLB MUe WMe ltac:(ub G5; ub G7; ub G8; lia). carry FRP MUe WMe ltac:(lia). clear MUe WMe.
    rename PC0 into QC'. destruct PC2 as [stj' STS']. destruct PC5 as [junkb' PC5].

    step.
    step. if_cases KD; zify_cond KD; [|exfalso; unfold Q_CACHE in *; lia].
    step. step. step. step.
    box HD.  box PC3. box PC4. box PC5. box POST. box PC1. box STS'. box LA0.
    snapshot [(bv_unsigned sp + -80 - 48, bv_unsigned sp + -80); (t + 80, t + 112); (0xd67c8, 0xd67c8 + 4); (0xd67d0, 0xd67d0 + 32); (g_lst g, g_lst g + 8)]%Z MUd WMd.
    box QC'. box GLB. box GC. box MX. box FRE. box CH.
    box ST.
    step. call_sp (drain_norecycle_spec true t (g_lst g) RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ (nb + 1) fst0 b (qb + (n + 8192)) (g_nb g) (g_fst g) (g_qb g) (g_nx g) lo);
      [unboxed ST| exact CEIL| lia| exact MI| reflexivity| reflexivity| unboxed QC'| lia| lia| lia| lia| unboxed MX| unboxed GC| lia| lia| unfold Q_MAX in *; lia| lia| lia
      | exact QMX| split; [lia|]; split; [unboxed GLB|]; unfold AIMG_HI, Q_BATCH_BYTES; repeat split; try lia; ub G5; lia| exact TI| atop_facts; lia|].
    try clear ST.
    clear QC' GLB GC MX FRE CH.
    try rename MI0 into MI.
    match goal with H : stk asegs ?mm lo _ |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename H into ST end.
    carry HD MUd WMd ltac:(ub DHT; ub G6; lia). carry PC3 MUd WMd ltac:(ub DTB; first [ub G8 | pose proof GLST0]; lia). carry PC4 MUd WMd ltac:(cbn [length]; ub DTB; first [ub G8 | pose proof GLST0]; lia). carry PC5 MUd WMd ltac:(ub DTB; first [ub G8 | pose proof GLST0]; lia). carry POST MUd WMd ltac:(ub DTL; first [ub G7 | pose proof GLST0]; lia). carry PC1 MUd WMd ltac:(first [ub G5 | pose proof GLST0]; lia). carry STS' MUd WMd ltac:(first [ub G5 | pose proof GLST0]; lia). carry LA0 MUd WMd ltac:(rewrite LEN0; ub DTL; first [ub G7 | pose proof GLST0]; lia). clear MUd WMd.
    do 10 step.
    release_frame FRP ST (bv_unsigned sp).
    unfold put_tail_post. rewrite ?QZE. unfold tcache_post, dk_post, dk_glst. rewrite ?EGD. rewrite ?EGF. cbn [ek_post ek_nb ek_fst ek_lst ek_delta ek_b]. finish.
    all: try assumption. all: try exact I. all: try (lazymatch goal with |- exists _, rw_cells _ ?mq ?Aq _ => match goal with Hq : rw_cells _ mq Aq _ |- _ => eexists; exact Hq end end).      all: try (eexists; eassumption).
  -
    box HD. box CH. box SH'. box LA0. box FRP.
    snapshot [(t + 80, t + 112); (t + 2128, t + 2128 + 4); (t + 2784, t + 2784 + 8); (lst, lst + 8); (b, b + 8192)]%Z MUe WMe.
    box BJ. box STS. box CR. box LB. box QC.
    box ST.
    call_sp (enqueue_from_refill_spec true t lst b RNG _ _ _ _ _ _ _
               (Z_to_bv 64 0x41230) (Z_to_bv 64 0xd6730) (Z_to_bv 64 (t + 80)) (Z_to_bv 64 n) a3 (Z_to_bv 64 (t + 208)) (Z_to_bv 64 hm)
               _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ nb fst0 qb hm n nx bsz cnt spacebeg lo maxc csz stj idxw chunks j0);
      [unboxed ST| exact CEIL| lia| lia| exact MI| exact FRE| unboxed QC| lia| lia| unfold Q_BATCH_BYTES, Q_MAX in *; lia
      | lia| lia| lia| lia
      | split; [lia|]; split; [unboxed LB|]; unfold AIMG_HI, Q_BATCH_BYTES; repeat split; try assumption; lia
      | exact SB| unboxed CR| ub CH; exact Y| exact LCH| exact CNT| exact NTH| exact IXS| unboxed STS| unfold K_BATCH_CLASS; lia| exists junkb; unboxed BJ
      | exact TI| atop_facts; lia| exact TAL| lia| unfold AIMG_HI; lia| unfold Q_BATCH_BYTES; lia
      | ub DTB; unfold Q_BATCH_BYTES; lia| ub DTL; unfold Q_BATCH_BYTES; lia| ub DBL; unfold Q_BATCH_BYTES; lia|].
    clear BJ STS CR LB QC.
    try rename MI0 into MI.
    replace (bv_unsigned sp + -144 + 64) with (bv_unsigned sp + -80) in * by lia.
    clear ST. match goal with H : stk asegs ?mm lo (bv_unsigned sp + -80) |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename H into ST end.
    carry HD MUe WMe ltac:(ub DHT; ub DHL; ub DHB; lia). carry CH MUe WMe ltac:(rewrite LCH; ub DTL; ub DTB; lia). carry SH' MUe WMe ltac:(lia). carry LA0 MUe WMe ltac:(rewrite LEN0; ub DTL; ub DBL; lia). carry FRP MUe WMe ltac:(lia). clear MUe WMe.
    rename PC0 into QC'. destruct PC2 as [stj' STS']. destruct PC5 as [junkb' PC5].

    step.
    step. if_cases KD; zify_cond KD; [|exfalso; unfold Q_CACHE in *; lia].
    step. step. step. step.
    box HD.  box PC3. box PC4. box PC5. box POST. box PC1. box STS'. box LA0.
    snapshot [(bv_unsigned sp + -80 - 48, bv_unsigned sp + -80); (t + 80, t + 112); (0xd67c8, 0xd67c8 + 4); (0xd67d0, 0xd67d0 + 32); (g_lst g, g_lst g + 8)]%Z MUd WMd.
    box QC'. box GC. box MX. box FRE.
    box ST.
    step. call_sp (drain_norecycle_spec false t (g_lst g) RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ (nb + 1) fst0 b (qb + (n + 8192)) (g_nb g) (g_fst g) (g_qb g) (g_nx g) lo);
      [unboxed ST| exact CEIL| lia| exact MI| reflexivity| reflexivity| unboxed QC'| lia| lia| lia| lia| unboxed MX| unboxed GC| lia| lia| unfold Q_MAX in *; lia| lia| lia
      | exact QMX| exact GNB0| exact TI| atop_facts; lia| exact I|].
    try clear ST.
    clear QC' GC MX FRE.
    try rename MI0 into MI.
    match goal with H : stk asegs ?mm lo _ |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename H into ST end.
    carry HD MUd WMd ltac:(ub DHT;  lia). carry PC3 MUd WMd ltac:(ub DTB; first [ub G8 | pose proof GLST0]; lia). carry PC4 MUd WMd ltac:(cbn [length]; ub DTB; first [ub G8 | pose proof GLST0]; lia). carry PC5 MUd WMd ltac:(ub DTB; first [ub G8 | pose proof GLST0]; lia). carry POST MUd WMd ltac:(ub DTL; first [ub G7 | pose proof GLST0]; lia). carry PC1 MUd WMd ltac:(first [ub G5 | pose proof GLST0]; lia). carry STS' MUd WMd ltac:(first [ub G5 | pose proof GLST0]; lia). carry LA0 MUd WMd ltac:(rewrite LEN0; ub DTL; first [ub G7 | pose proof GLST0]; lia). clear MUd WMd.
    do 10 step.
    release_frame FRP ST (bv_unsigned sp).
    unfold put_tail_post. rewrite ?QZE. unfold tcache_post, dk_post, dk_glst. rewrite ?EGD. rewrite ?EGF. cbn [ek_post ek_nb ek_fst ek_lst ek_delta ek_b]. finish.
    all: try assumption. all: try exact I. all: try (lazymatch goal with |- exists _, rw_cells _ ?mq ?Aq _ => match goal with Hq : rw_cells _ mq Aq _ |- _ => eexists; exact Hq end end).      all: try (eexists; eassumption).
  -
    box HD. box CH. box SH'. box LA0. box FRP.
    snapshot [(t + 80, t + 112); (t + 2128, t + 2128 + 4); (t + 2784, t + 2784 + 8); (lst, lst + 8); (b, b + 8192)]%Z MUe WMe.
    box BJ. box STS. box CR. box LB. box QC.
    box ST.
    call_sp (enqueue_from_refill_spec true t lst b RNG _ _ _ _ _ _ _
               (Z_to_bv 64 0x41230) (Z_to_bv 64 0xd6730) (Z_to_bv 64 (t + 80)) (Z_to_bv 64 n) a3 (Z_to_bv 64 (t + 208)) (Z_to_bv 64 hm)
               _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ nb fst0 qb hm n nx bsz cnt spacebeg lo maxc csz stj idxw chunks j0);
      [unboxed ST| exact CEIL| lia| lia| exact MI| exact FRE| unboxed QC| lia| lia| unfold Q_BATCH_BYTES, Q_MAX in *; lia
      | lia| lia| lia| lia
      | split; [lia|]; split; [unboxed LB|]; unfold AIMG_HI, Q_BATCH_BYTES; repeat split; try assumption; lia
      | exact SB| unboxed CR| ub CH; exact Y| exact LCH| exact CNT| exact NTH| exact IXS| unboxed STS| unfold K_BATCH_CLASS; lia| exists junkb; unboxed BJ
      | exact TI| atop_facts; lia| exact TAL| lia| unfold AIMG_HI; lia| unfold Q_BATCH_BYTES; lia
      | ub DTB; unfold Q_BATCH_BYTES; lia| ub DTL; unfold Q_BATCH_BYTES; lia| ub DBL; unfold Q_BATCH_BYTES; lia|].
    clear BJ STS CR LB QC.
    try rename MI0 into MI.
    replace (bv_unsigned sp + -144 + 64) with (bv_unsigned sp + -80) in * by lia.
    clear ST. match goal with H : stk asegs ?mm lo (bv_unsigned sp + -80) |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename H into ST end.
    carry HD MUe WMe ltac:(ub DHT; ub DHL; ub DHB; lia). carry CH MUe WMe ltac:(rewrite LCH; ub DTL; ub DTB; lia). carry SH' MUe WMe ltac:(lia). carry LA0 MUe WMe ltac:(rewrite LEN0; ub DTL; ub DBL; lia). carry FRP MUe WMe ltac:(lia). clear MUe WMe.
    rename PC0 into QC'. destruct PC2 as [stj' STS']. destruct PC5 as [junkb' PC5].

    step.
    step. if_cases KD; zify_cond KD; [exfalso; unfold Q_CACHE in *; lia|].
    step.
    do 10 step.
    release_frame FRP ST (bv_unsigned sp).
    unfold put_tail_post. rewrite ?QZE. unfold tcache_post, dk_post, dk_glst. rewrite ?EGD. rewrite ?EGF. cbn [ek_post ek_nb ek_fst ek_lst ek_delta ek_b]. finish.
    all: try assumption. all: try exact I. all: try (lazymatch goal with |- exists _, rw_cells _ ?mq ?Aq _ => match goal with Hq : rw_cells _ mq Aq _ |- _ => eexists; exact Hq end end).      all: try (eexists; eassumption).
  -
    box HD. box CH. box SH'. box GLB. box FRP.
    snapshot [(t + 80, t + 112); (t + 2128, t + 2128 + 4); (t + 2784, t + 2784 + 8); (lst, lst + 8); (b, b + 8192)]%Z MUe WMe.
    box BJ. box STS. box CR. box QC.
    box ST.
    call_sp (enqueue_from_refill_spec false t lst b RNG _ _ _ _ _ _ _
               (Z_to_bv 64 0x41230) (Z_to_bv 64 0xd6730) (Z_to_bv 64 (t + 80)) (Z_to_bv 64 n) a3 (Z_to_bv 64 (t + 208)) (Z_to_bv 64 hm)
               _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ nb fst0 qb hm n nx bsz cnt spacebeg lo maxc csz stj idxw chunks j0);
      [unboxed ST| exact CEIL| lia| lia| exact MI| exact FRE| unboxed QC| lia| lia| unfold Q_BATCH_BYTES, Q_MAX in *; lia
      | lia| lia| lia| lia
      | exact NB0
      | exact SB| unboxed CR| ub CH; exact Y| exact LCH| exact CNT| exact NTH| exact IXS| unboxed STS| unfold K_BATCH_CLASS; lia| exists junkb; unboxed BJ
      | exact TI| atop_facts; lia| exact TAL| lia| unfold AIMG_HI; lia| unfold Q_BATCH_BYTES; lia
      | ub DTB; unfold Q_BATCH_BYTES; lia| ub DTL; unfold Q_BATCH_BYTES; lia| ub DBL; unfold Q_BATCH_BYTES; lia| exact I|].
    clear BJ STS CR QC.
    try rename MI0 into MI.
    replace (bv_unsigned sp + -144 + 64) with (bv_unsigned sp + -80) in * by lia.
    clear ST. match goal with H : stk asegs ?mm lo (bv_unsigned sp + -80) |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename H into ST end.
    carry HD MUe WMe ltac:(ub DHT; ub DHL; ub DHB; lia). carry CH MUe WMe ltac:(rewrite LCH; ub DTL; ub DTB; lia). carry SH' MUe WMe ltac:(lia). carry GLB MUe WMe ltac:(ub G5; ub G7; ub G8; lia). carry FRP MUe WMe ltac:(lia). clear MUe WMe.
    rename PC0 into QC'. destruct PC2 as [stj' STS']. destruct PC5 as [junkb' PC5].

    step.
    step. if_cases KD; zify_cond KD; [|exfalso; unfold Q_CACHE in *; lia].
    step. step. step. step.
    box HD.  box PC3. box PC4. box PC5. box PC1. box STS'.
    snapshot [(bv_unsigned sp + -80 - 48, bv_unsigned sp + -80); (t + 80, t + 112); (0xd67c8, 0xd67c8 + 4); (0xd67d0, 0xd67d0 + 32); (g_lst g, g_lst g + 8)]%Z MUd WMd.
    box QC'. box GLB. box GC. box MX. box FRE. box CH.
    box ST.
    step. call_sp (drain_norecycle_spec true t (g_lst g) RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ (nb + 1) b b (qb + (n + 8192)) (g_nb g) (g_fst g) (g_qb g) (g_nx g) lo);
      [unboxed ST| exact CEIL| lia| exact MI| reflexivity| reflexivity| unboxed QC'| lia| lia| lia| lia| unboxed MX| unboxed GC| lia| lia| unfold Q_MAX in *; lia| lia| lia
      | exact QMX| split; [lia|]; split; [unboxed GLB|]; unfold AIMG_HI, Q_BATCH_BYTES; repeat split; try lia; ub G5; lia| exact TI| atop_facts; lia|].
    try clear ST.
    clear QC' GLB GC MX FRE CH.
    try rename MI0 into MI.
    match goal with H : stk asegs ?mm lo _ |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename H into ST end.
    carry HD MUd WMd ltac:(ub DHT; ub G6; lia). carry PC3 MUd WMd ltac:(ub DTB; first [ub G8 | pose proof GLST0]; lia). carry PC4 MUd WMd ltac:(cbn [length]; ub DTB; first [ub G8 | pose proof GLST0]; lia). carry PC5 MUd WMd ltac:(ub DTB; first [ub G8 | pose proof GLST0]; lia). carry PC1 MUd WMd ltac:(first [ub G5 | pose proof GLST0]; lia). carry STS' MUd WMd ltac:(first [ub G5 | pose proof GLST0]; lia). clear MUd WMd.
    do 10 step.
    release_frame FRP ST (bv_unsigned sp).
    unfold put_tail_post. rewrite ?QZE. unfold tcache_post, dk_post, dk_glst. rewrite ?EGD. rewrite ?EGF. cbn [ek_post ek_nb ek_fst ek_lst ek_delta ek_b]. finish.
    all: try assumption. all: try exact I. all: try (lazymatch goal with |- exists _, rw_cells _ ?mq ?Aq _ => match goal with Hq : rw_cells _ mq Aq _ |- _ => eexists; exact Hq end end).      all: try (eexists; eassumption).
  -
    box HD. box CH. box SH'. box FRP.
    snapshot [(t + 80, t + 112); (t + 2128, t + 2128 + 4); (t + 2784, t + 2784 + 8); (lst, lst + 8); (b, b + 8192)]%Z MUe WMe.
    box BJ. box STS. box CR. box QC.
    box ST.
    call_sp (enqueue_from_refill_spec false t lst b RNG _ _ _ _ _ _ _
               (Z_to_bv 64 0x41230) (Z_to_bv 64 0xd6730) (Z_to_bv 64 (t + 80)) (Z_to_bv 64 n) a3 (Z_to_bv 64 (t + 208)) (Z_to_bv 64 hm)
               _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ nb fst0 qb hm n nx bsz cnt spacebeg lo maxc csz stj idxw chunks j0);
      [unboxed ST| exact CEIL| lia| lia| exact MI| exact FRE| unboxed QC| lia| lia| unfold Q_BATCH_BYTES, Q_MAX in *; lia
      | lia| lia| lia| lia
      | exact NB0
      | exact SB| unboxed CR| ub CH; exact Y| exact LCH| exact CNT| exact NTH| exact IXS| unboxed STS| unfold K_BATCH_CLASS; lia| exists junkb; unboxed BJ
      | exact TI| atop_facts; lia| exact TAL| lia| unfold AIMG_HI; lia| unfold Q_BATCH_BYTES; lia
      | ub DTB; unfold Q_BATCH_BYTES; lia| ub DTL; unfold Q_BATCH_BYTES; lia| ub DBL; unfold Q_BATCH_BYTES; lia| exact I|].
    clear BJ STS CR QC.
    try rename MI0 into MI.
    replace (bv_unsigned sp + -144 + 64) with (bv_unsigned sp + -80) in * by lia.
    clear ST. match goal with H : stk asegs ?mm lo (bv_unsigned sp + -80) |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename H into ST end.
    carry HD MUe WMe ltac:(ub DHT; ub DHL; ub DHB; lia). carry CH MUe WMe ltac:(rewrite LCH; ub DTL; ub DTB; lia). carry SH' MUe WMe ltac:(lia). carry FRP MUe WMe ltac:(lia). clear MUe WMe.
    rename PC0 into QC'. destruct PC2 as [stj' STS']. destruct PC5 as [junkb' PC5].

    step.
    step. if_cases KD; zify_cond KD; [|exfalso; unfold Q_CACHE in *; lia].
    step. step. step. step.
    box HD.  box PC3. box PC4. box PC5. box PC1. box STS'.
    snapshot [(bv_unsigned sp + -80 - 48, bv_unsigned sp + -80); (t + 80, t + 112); (0xd67c8, 0xd67c8 + 4); (0xd67d0, 0xd67d0 + 32); (g_lst g, g_lst g + 8)]%Z MUd WMd.
    box QC'. box GC. box MX. box FRE.
    box ST.
    step. call_sp (drain_norecycle_spec false t (g_lst g) RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ (nb + 1) b b (qb + (n + 8192)) (g_nb g) (g_fst g) (g_qb g) (g_nx g) lo);
      [unboxed ST| exact CEIL| lia| exact MI| reflexivity| reflexivity| unboxed QC'| lia| lia| lia| lia| unboxed MX| unboxed GC| lia| lia| unfold Q_MAX in *; lia| lia| lia
      | exact QMX| exact GNB0| exact TI| atop_facts; lia| exact I|].
    try clear ST.
    clear QC' GC MX FRE.
    try rename MI0 into MI.
    match goal with H : stk asegs ?mm lo _ |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename H into ST end.
    carry HD MUd WMd ltac:(ub DHT;  lia). carry PC3 MUd WMd ltac:(ub DTB; first [ub G8 | pose proof GLST0]; lia). carry PC4 MUd WMd ltac:(cbn [length]; ub DTB; first [ub G8 | pose proof GLST0]; lia). carry PC5 MUd WMd ltac:(ub DTB; first [ub G8 | pose proof GLST0]; lia). carry PC1 MUd WMd ltac:(first [ub G5 | pose proof GLST0]; lia). carry STS' MUd WMd ltac:(first [ub G5 | pose proof GLST0]; lia). clear MUd WMd.
    do 10 step.
    release_frame FRP ST (bv_unsigned sp).
    unfold put_tail_post. rewrite ?QZE. unfold tcache_post, dk_post, dk_glst. rewrite ?EGD. rewrite ?EGF. cbn [ek_post ek_nb ek_fst ek_lst ek_delta ek_b]. finish.
    all: try assumption. all: try exact I. all: try (lazymatch goal with |- exists _, rw_cells _ ?mq ?Aq _ => match goal with Hq : rw_cells _ mq Aq _ |- _ => eexists; exact Hq end end).      all: try (eexists; eassumption).
  -
    box HD. box CH. box SH'. box FRP.
    snapshot [(t + 80, t + 112); (t + 2128, t + 2128 + 4); (t + 2784, t + 2784 + 8); (lst, lst + 8); (b, b + 8192)]%Z MUe WMe.
    box BJ. box STS. box CR. box QC.
    box ST.
    call_sp (enqueue_from_refill_spec false t lst b RNG _ _ _ _ _ _ _
               (Z_to_bv 64 0x41230) (Z_to_bv 64 0xd6730) (Z_to_bv 64 (t + 80)) (Z_to_bv 64 n) a3 (Z_to_bv 64 (t + 208)) (Z_to_bv 64 hm)
               _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ nb fst0 qb hm n nx bsz cnt spacebeg lo maxc csz stj idxw chunks j0);
      [unboxed ST| exact CEIL| lia| lia| exact MI| exact FRE| unboxed QC| lia| lia| unfold Q_BATCH_BYTES, Q_MAX in *; lia
      | lia| lia| lia| lia
      | exact NB0
      | exact SB| unboxed CR| ub CH; exact Y| exact LCH| exact CNT| exact NTH| exact IXS| unboxed STS| unfold K_BATCH_CLASS; lia| exists junkb; unboxed BJ
      | exact TI| atop_facts; lia| exact TAL| lia| unfold AIMG_HI; lia| unfold Q_BATCH_BYTES; lia
      | ub DTB; unfold Q_BATCH_BYTES; lia| ub DTL; unfold Q_BATCH_BYTES; lia| ub DBL; unfold Q_BATCH_BYTES; lia| exact I|].
    clear BJ STS CR QC.
    try rename MI0 into MI.
    replace (bv_unsigned sp + -144 + 64) with (bv_unsigned sp + -80) in * by lia.
    clear ST. match goal with H : stk asegs ?mm lo (bv_unsigned sp + -80) |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename H into ST end.
    carry HD MUe WMe ltac:(ub DHT; ub DHL; ub DHB; lia). carry CH MUe WMe ltac:(rewrite LCH; ub DTL; ub DTB; lia). carry SH' MUe WMe ltac:(lia). carry FRP MUe WMe ltac:(lia). clear MUe WMe.
    rename PC0 into QC'. destruct PC2 as [stj' STS']. destruct PC5 as [junkb' PC5].

    step.
    step. if_cases KD; zify_cond KD; [exfalso; unfold Q_CACHE in *; lia|].
    step.
    do 10 step.
    release_frame FRP ST (bv_unsigned sp).
    unfold put_tail_post. rewrite ?QZE. unfold tcache_post, dk_post, dk_glst. rewrite ?EGD. rewrite ?EGF. cbn [ek_post ek_nb ek_fst ek_lst ek_delta ek_b]. finish.
    all: try assumption. all: try exact I. all: try (lazymatch goal with |- exists _, rw_cells _ ?mq ?Aq _ => match goal with Hq : rw_cells _ mq Aq _ |- _ => eexists; exact Hq end end).      all: try (eexists; eassumption).
Qed.
End CANSEC1.
End F_afree_tailR.

From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib Require ITree Nodes Decode.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec Require STree.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require AProto ADepot_iface.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require F_aalloc_s.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require F_aalloc1.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require F_afree_iseg F_afree_front.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require F_afree_icpt.
Module F_afree_icptR.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase. Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics. Import LinuxProcessSemantics.LinuxProcessSem.MemImageType. Import LinuxProcessSemantics.LinuxProcessSem.State. Import LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude. Import LinuxProcessSemantics.Riscv.Instr. Import LinuxProcessSemantics.Riscv.Decode. Import LinuxProcessSemantics.Riscv.DecodeC. Import LinuxProcessSemantics.Riscv.Sem. Import LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.ITree. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Nodes. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Decode. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Arr. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.InitMem.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.STree. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanCtrl. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanEmbed.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AImg. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AProto. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ABase. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ABytes. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AQConst. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ADepot_iface.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.StepF.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AKit. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AKit2. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AKitQ.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_apoison.F_apoison. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aalloc_s.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aalloc1.F_aalloc1. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_afree_iseg. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_afree_front. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_afree_tail.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aenqueue.F_aenqueueR. Import F_afree_tailR. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_afree_icpt.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Local Ltac band_lin :=
  repeat match goal with H : iclr ?a ?n |- _ => unfold iclr, AIMG_LO, AIMG_HI in H end.
Local Ltac with_band H tac :=
  let H' := fresh H in pose proof H as H'; unfold sclr, iclr, ablk, KLS, AIMG_LO, AIMG_HI in H'; tac; try clear H'.

Local Ltac qlia := first [ LiaTuning.zify_prune; LiaTuning.zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker
                         | LiaTuning.zify_prune; Zify.zify; xlia zchecker ].
Local Ltac leaf2 := first [ left; qlia | right; qlia | qlia ].
Local Ltac band_leaf :=
  first [ leaf2
        | match goal with B : sclr ?a _ |- context [?a] =>
            let B' := fresh "BB" in pose proof B as B'; unfold sclr, KLS in B'; destruct B' as [B'|B']; leaf2 end
        | match goal with B : iclr ?a _ |- context [?a] =>
            let B' := fresh "BB" in pose proof B as B'; unfold iclr, AIMG_LO, AIMG_HI in B'; destruct B' as [_ [B'|B']]; leaf2 end
        | match goal with B : ablk ?a _ |- context [?a] =>
            let B' := fresh "BB" in pose proof B as B'; unfold ablk, KLS, AIMG_HI in B'; destruct B' as [[? B']|[B' ?]]; leaf2 end
        | lia ].
Local Ltac band_disj := cbn [disjoint_from fst snd]; repeat match goal with |- _ /\ _ => split end; first [exact I | band_leaf].

Local Lemma sclr_int : forall a n, sclr a n -> 0 <= a -> a + n <= 18446744073709551616 ->
  exists k, 0 <= k <= 1 /\ a + n <= 2147446784 + k * 18446744073709551616 /\ 17594333495296 * k <= a.
Proof. intros a n H G1 G2. unfold sclr, KLS in H. destruct H; [exists 0 | exists 1]; lia. Qed.
Local Lemma iclr_int : forall a n, iclr a n -> a + n <= 18446744073709551616 ->
  exists k, 0 <= k <= 1 /\ 4096 <= a /\ a + n <= 65536 + k * 18446744073709551616 /\ 6483968 * k <= a.
Proof. intros a n H G2. unfold iclr, AIMG_LO, AIMG_HI in H. destruct H as [? [?|?]]; [exists 0 | exists 1]; lia. Qed.
Local Lemma ablk_int {rc : runConstT} : forall lo hi, ablk lo hi ->
  exists k, 0 <= k <= 1 /\ 6483968 <= lo /\ 17594333495296 * k <= lo /\ hi <= 2147446784 + k * 18446744073709551616 /\ hi <= ATOP.
Proof. intros lo hi H. unfold ablk, KLS, AIMG_HI in H. pose proof atop_range. destruct H as [[? ?]|[? ?]]; [exists 0 | exists 1]; lia. Qed.
Local Ltac band_int H :=
  let k := fresh "k" H in let A := fresh "KA" H in let B := fresh "KB" H in let C := fresh "KC" H in let D := fresh "KD" H in
  let G1 := fresh "G" in let G2 := fresh "G" in
  lazymatch type of H with
  | sclr ?a ?n =>
      assert (G1 : 0 <= a) by (atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia); assert (G2 : a + n <= 18446744073709551616) by (atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia);
      destruct (sclr_int a n H G1 G2) as (k & A & B & C); clear G1 G2
  | iclr ?a ?n =>
      assert (G2 : a + n <= 18446744073709551616) by (atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia);
      destruct (iclr_int a n H G2) as (k & A & B & C & D); clear G2
  | 4096 <= ?a /\ (?a + ?n <= _ \/ _ <= ?a) =>
      assert (G2 : a + n <= 18446744073709551616) by (atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia);
      destruct (iclr_int a n H G2) as (k & A & B & C & D); clear G2
  | ablk ?lo ?hi => let E := fresh "KE" H in destruct (ablk_int lo hi H) as (k & A & B & E & C & D)
  end.

Ltac ub H := let X := fresh "Y" in pose proof H as X; unbox X.

Section CANSEC1. Context {rc : runConstT}.
Section WithDepot.
Variable DI : ADepotIface.

Notation free_W L sp t hm n lst ek g :=
  ([(bv_unsigned sp - 4096, bv_unsigned sp); (0xdacc0, 0xdacc0 + 0x81030); (0x169548, 0x169548 + 4);
    (t + 3168, t + 3169); (hm, hm + 4); (hm + 16, hm + 24); (t + 2800, t + 2800 + 368);
    (ADEPOT_LO, ADEPOT_HI); (al_nodes L, al_nodes L + 1048576); (al_store L, al_store L + 8388608);
    (shad (hm + 16), shad (hm + 16) + shlen (rup n 8)); (t + 80, t + 112); (t + 2128, t + 2132); (t + 2784, t + 2792);
    (lst, lst + qsz lst); (ek_b ek lst, ek_b ek lst + 8192);
    (0xd67c8, 0xd67c8 + 4); (0xd67d0, 0xd67d0 + 32); (dk_glst g lst, dk_glst g lst + 8)]%Z) (only parsing).
Notation toref_W L sp t hm n :=
  ([(bv_unsigned sp - 4096, bv_unsigned sp); (0xdacc0, 0xdacc0 + 0x81030); (0x169548, 0x169548 + 4);
    (t + 3168, t + 3169); (hm, hm + 4); (hm + 16, hm + 24); (t + 2800, t + 2800 + 368);
    (ADEPOT_LO, ADEPOT_HI); (al_nodes L, al_nodes L + 1048576); (al_store L, al_store L + 8388608);
    (shad (hm + 16), shad (hm + 16) + shlen (rup n 8))]%Z) (only parsing).

Definition free_to_refill_post (L : alayout) (full : bool)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (t hm n b1 actx lo lst nx bsz : Z) (hs : list word) (trt : list Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists (id : Z) (t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 : word) m' (sj' tb' : list word) (junk2 j0 : list byte),
    ms' = MS (mkR (Z_to_bv 64 0x41390) (Z_to_bv 64 (bv_unsigned sp + -2272)) gp tp t0 t1 t2
                  (Z_to_bv 64 (t + 2128)) (Z_to_bv 64 (t + 208))
                  (Z_to_bv 64 (t + 208)) (Z_to_bv 64 (t + 2128)) (Z_to_bv 64 0xd6458) (Z_to_bv 64 K_BATCH_CLASS) a4 a5 a6 a7
                  (Z_to_bv 64 hm) (Z_to_bv 64 (t + 80)) (Z_to_bv 64 (bv_unsigned sp + -2128)) (Z_to_bv 64 n) (Z_to_bv 64 Q_CACHE)
                  s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x41b70) fc None m' (seg_rom asegs)
    /\ munch (toref_W L sp t hm n) m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp + -2272)
    /\ 0 < id < 2^31
    /\ rw_cells asegs m' hm [C1 (Z_to_bv 8 3); C1 (Z_to_bv 8 b1); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 (Z_to_bv 64 actx)]
    /\ rw_cells asegs m' (hm + 16) [C8 (Z_to_bv 64 id)]
    /\ rw_cells asegs m' (shad (hm + 16)) [CB (Z.to_nat (shlen (rup n 8))) (repeat (Z_to_bv 8 253) (Z.to_nat (shlen (rup n 8))))]
    /\ u64arr asegs m' (t + 2800) sj' /\ length sj' = 46%nat
    /\ rw_cells asegs m' (t + 3168) [C1 (Z_to_bv 8 0)]
    /\ rw_cells asegs m' 0x169548 [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]
    /\ stk asegs m' 0xdacc0 (0xdacc0 + 0x81030)
    /\ (forall j, 0 <= j < 32768 -> bytes_at asegs m' (0xdacc8 + 8 * j) (le8 (Z_to_bv 64 0)))

    /\ rw_cells asegs m' (bv_unsigned sp + -2128) [C8 (Z_to_bv 64 (bv_unsigned sp + -2128 + 16)); C4 (Z_to_bv 64 (1 + Z.of_nat (length trt))); C4 (Z_to_bv 64 0)]
    /\ u64arr asegs m' (bv_unsigned sp + -2128 + 16) tb' /\ length tb' = 255%nat
    /\ rw_cells asegs m' (bv_unsigned sp + -72) [C8 sp; CB 8 junk2; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
    /\ rw_cells asegs m' (bv_unsigned sp + -2208)
         [C8 (Z_to_bv 64 (t + 208)); C8 (Z_to_bv 64 (bv_unsigned sp + -2128)); C8 s6; C8 (Z_to_bv 64 (bv_unsigned sp + -81));
          C8 (Z_to_bv 64 (bv_unsigned sp + -2128)); C8 (Z_to_bv 64 1); C8 (Z_to_bv 64 0x5e55c); C8 (Z_to_bv 64 (hm + 16)); C8 sp; C8 (Z_to_bv 64 0x5e5cc)]
    /\ rw_cells asegs m' (bv_unsigned sp + -2272)
         [CB 8 j0; C8 (Z_to_bv 64 hm); C8 (Z_to_bv 64 (t + 208)); C8 (Z_to_bv 64 (bv_unsigned sp + -2128)); C8 (Z_to_bv 64 n);
          C8 (Z_to_bv 64 (t + 80)); C8 (Z_to_bv 64 0xd6730); C8 (Z_to_bv 64 0x41230)]
    /\ (if full then rw_cells asegs m' lst [C8 (Z_to_bv 64 nx); C8 (Z_to_bv 64 bsz); C8 (Z_to_bv 64 1021)] /\ u64arr asegs m' (lst + 24) hs else True)
    /\ ADEPOT DI L m'.

Lemma free_to_refill_spec : forall (L : alayout) (ia full : bool) RNG
    ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem)
    (t ctx hm n b1 actx lo top bot nb fst0 lst qb nx bsz : Z) (uw maxc csz : word) (sj hs : list word) (sjunk : list byte) (trt : list Z),
  stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - 4096 ->
  mem_inv asegs m ->
  tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 (hm + 16) ->
  bv_unsigned sp mod 16 = 0 ->

  allocA_cells m ctx t -> poison_cells m ->
  rw_cells asegs m 0xda7bc [C4 (Z_to_bv 64 30)] ->
  rw_cells asegs m 0x16b60a [C1 (Z_to_bv 8 1)] ->
  rw_cells asegs m 0xd14f8 [C8 (Z_to_bv 64 0x169560)] -> rw_cells asegs m 0x169560 [C8 (Z_to_bv 64 4096)] ->
  rw_cells asegs m 0x16b588 [C8 (Z_to_bv 64 0)] ->
  rw_cells asegs m 0xd6770 [C8 (Z_to_bv 64 Q_MAX); C8 (Z_to_bv 64 Q_MIN); C8 (Z_to_bv 64 Q_CACHE)] ->
  rw_cells asegs m 0xd1510 [C8 (Z_to_bv 64 AFLAGS)] ->
  rw_cells asegs m 0xd72e4 [C4 (Z_to_bv 64 0x1000); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0xbe)] ->

  rw_cells asegs m 0x169548 [C1 (Z_to_bv 8 (if ia then 1 else 0)); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] ->
  stk asegs m 0xdacc0 (0xdacc0 + 0x81030) ->
  (ia = true -> forall j, 0 <= j < 32768 -> bytes_at asegs m (0xdacc8 + 8 * j) (le8 (Z_to_bv 64 0))) ->

  rw_cells asegs m (ctx + 8) [C4 (Z_to_bv 64 0)] ->
  rw_cells asegs m t [C8 (Z_to_bv 64 ctx); C8 (Z_to_bv 64 top); C8 (Z_to_bv 64 bot)] ->
  rw_cells asegs m (t + 40) [C1 (Z_to_bv 8 0)] -> rw_cells asegs m (t + 3168) [C1 (Z_to_bv 8 0)] ->
  u64arr asegs m (t + 2800) sj -> length sj = 46%nat ->
  rw_cells asegs m (t + 80) [C8 (Z_to_bv 64 nb); C8 (Z_to_bv 64 fst0); C8 (Z_to_bv 64 lst); C8 (Z_to_bv 64 qb)] ->
  0 <= nb < 2^62 -> 0 <= qb -> qb + n + 8192 < 2^62 -> 0 <= fst0 < 2^64 -> 0 <= lst < 2^64 ->
  0 < ctx -> sclr ctx 65536 -> ctx + 4096 <= ATOP ->
  sclr t 4096 -> t + 4096 <= ATOP -> t mod 4096 = 0 -> (ctx + 4096 <= t \/ t + 4096 <= ctx) ->

  rw_cells asegs m hm [C1 (Z_to_bv 8 2); C1 (Z_to_bv 8 b1); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 (Z_to_bv 64 actx)] ->
  rw_cells asegs m (hm + 16) [C8 uw] -> 0 <= b1 < 256 -> Z.land b1 3 = 1 -> 1 <= n <= Q_MAX -> hm mod 16 = 0 ->
  ablk hm (hm + 16 + rup n 8) -> hm + 16 + rup n 8 <= ATOP -> hm + 24 <= ATOP ->
  rw_cells asegs m (shad (hm + 16)) [CB (Z.to_nat (shlen (rup n 8))) sjunk] ->
  (hm + 24 <= t \/ t + 4096 <= hm) -> (hm + 24 <= ctx \/ ctx + 4096 <= hm) ->

  (if full then 0 < nb /\ rw_cells asegs m lst [C8 (Z_to_bv 64 nx); C8 (Z_to_bv 64 bsz); C8 (Z_to_bv 64 1021)]
             /\ 0x10007fff8000 <= lst /\ lst + 8192 <= ATOP
             /\ u64arr asegs m (lst + 24) hs /\ length hs = 1021%nat /\ rng RNG lst 8192
   else nb = 0 /\ lst = 0) ->
  rw_cells asegs m (t + 2128) [C4 (Z_to_bv 64 0); C4 maxc; C8 csz] ->
  (t + 4096 <= lst \/ lst + 8192 <= t \/ lst = 0) -> (hm + 24 <= lst \/ lst + 8192 <= hm) ->
  (al_nodes L + 1048576 <= lst \/ lst + 8192 <= al_nodes L) -> (al_store L + 8388608 <= lst \/ lst + 8192 <= al_store L) ->

  ADEPOT DI L m ->
  sclr (al_nodes L) 1048576 -> al_nodes L + 1048576 <= ATOP -> sclr (al_store L) 8388608 -> al_store L + 8388608 <= ATOP ->
  (hm + 24 <= al_nodes L \/ al_nodes L + 1048576 <= hm) -> (hm + 24 <= al_store L \/ al_store L + 8388608 <= hm) ->
  (t + 4096 <= al_nodes L \/ al_nodes L + 1048576 <= t) -> (t + 4096 <= al_store L \/ al_store L + 8388608 <= t) ->
  (ctx + 4096 <= al_nodes L \/ al_nodes L + 1048576 <= ctx) -> (ctx + 4096 <= al_store L \/ al_store L + 8388608 <= ctx) ->

  afree_unw RNG lo m top sp s0 ra trt ->
  bv_unsigned s0 <> bv_unsigned sp + 8 ->
  In (AFREE_PC :: trt) (al_U L) ->
  0 <= bot -> bot < bv_unsigned sp -> bot < top -> 4096 <= top <= 2^47 -> 4096 <= bv_unsigned ra -> bv_unsigned ra <> AFREE_PC ->

  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG ctx 4096 -> rng RNG t 4096 ->
  rng RNG (al_nodes L) 1048576 -> rng RNG (al_store L) 8388608 -> rng RNG hm 24 -> rng RNG (shad (hm + 16)) (shlen (rup n 8)) ->
  AIMG_HI <= ctx -> AIMG_HI <= al_nodes L -> AIMG_HI <= al_store L -> iclr t 4096 ->
  evtF asegs RNG (free_to_refill_post L full ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc t hm n b1 actx lo lst nx bsz hs trt m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 AFREE_SYM) fc None m (seg_rom asegs)).
Proof.
  intros until trt.
  intros ST CEIL LO MI TP Ha0 SP16 AC PC MCS CF34 GPG PGC HK QK GF FLG FL IAS IAM CT8 TT0 SW UW STATS LSJ QC NB QB QBN FST LST
         CX0 C0 C1 T0 T1 TAL CT2 HD HUW B1 B13 N AL HLO HHI HCE SH DHT DHC FULL CR0 DTL DHL DNL DSL DEP N0 N1 R0 R1 DHN DHS DTN DTS DCN DCS
         UNW S0NE TRU B0 BB BOTOP TOP RA4 RANE RIMG RSTK RCTX RT RNO RST RH RSH CI NI SI TI. band_lin.
  band_int TI. pose proof (ablk_lin _ _ HLO) as (HL1 & HL2 & HL3 & HL4). unfold AIMG_HI in HL1. band_int HLO. band_int C0. band_int T0. band_int N0. band_int R0.
  pose proof (afree_unw_length _ _ _ _ _ _ _ _ UNW) as LTRT.
  pose proof (afree_unw_sp47 _ _ _ _ _ _ _ _ UNW ltac:(clear -TOP; lia)) as SP47.
  pose proof PC as PC'. destruct PC' as (GOT6 & _).
  assert (RUP : n <= rup n 8 <= n + 7 /\ rup n 8 mod 8 = 0) by (clear -N; unfold rup; Z.div_mod_to_equations; lia).
  assert (SHB : 2148261376 <= shad (hm + 16) /\ shad (hm + 16) + shlen (rup n 8) <= 0x10007fff8000 /\ 0 < shlen (rup n 8)).
  { clear -N HLO HL1 HHI HCE. unfold shad, shlen, ASHOFF, rup in *. rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8. unfold Q_MAX in *. Z.div_mod_to_equations. lia. }
  unfold AIMG_HI, AFREE_SYM, AFREE_PC in *.
  word_range sp SPR.
  box DHT. box DHC. box DHN. box DHS. box DTN. box DTS. box DCN. box DCS. box CT2. box DTL. box DHL. box DNL. box DSL.

  eapply evtF_cut.
  { eapply (free_front_spec DI L ia RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
              t ctx hm n b1 actx lo top bot uw sj trt).
    all: try lazymatch goal with
         | |- stk _ _ _ _ => first [exact ST | exact IAS]
         | |- mem_inv _ _ => exact MI
         | |- allocA_cells _ _ _ => exact AC
         | |- ADEPOT _ _ _ => exact DEP
         | |- afree_unw _ _ _ _ _ _ => exact UNW
         | |- In _ _ => exact TRU
         | |- u64arr _ _ _ _ => exact STATS
         | |- _ = true -> _ => exact IAM
         | |- _ \/ _ => first [unboxed DHT | unboxed DHC | unboxed DHN | unboxed DHS | unboxed DTN | unboxed DTS | unboxed DCN | unboxed DCS | unboxed CT2]
         | |- rng _ _ _ => solve_rng
         | |- rw_cells _ _ _ [C1 _; C1 _; C2 _; C4 _; C8 _] => exact HD
         | |- rw_cells _ _ _ [C8 _; C8 _; C8 _] => exact TT0
         | |- rw_cells _ _ (_ + 16) _ => exact HUW
         | |- rw_cells _ _ (_ + 8) _ => exact CT8
         | |- rw_cells _ _ (_ + 40) _ => exact SW
         | |- rw_cells _ _ (_ + 3168) _ => exact UW
         end.
    all: try eassumption. all: try (unfold AIMG_HI, Q_MAX in *; lia).
    all: match goal with |- ?G => idtac "REMF" G end. }
  cbv beta. intros ms1 PFR. unfold free_front_post in PFR.
  destruct PFR as (id & t0a & t1a & t2a & a6a & a7a & t3a & t4a & t5a & t6a & m1 & sj1 & tb1 & junk2
                   & -> & MUf & WMf & MIf & STf & IDR & HD1 & FC1 & STATS1 & LSJ1 & UW1 & FL1 & IAS1 & IAM1 & SS1 & TB1 & LTB1 & FRS1 & DEP1).

  xport QK MUf WMf ltac:(lia). xport GF MUf WMf ltac:(lia). xport FLG MUf WMf ltac:(lia).
  xport QC MUf WMf ltac:(ub DHT; ub DTN; ub DTS; lia).
  xport SH MUf WMf ltac:(band_disj).
  xport CR0 MUf WMf ltac:(ub DHT; ub DTN; ub DTS; lia).
  assert (PC1 : poison_cells m1).
  { eapply poison_cells_frame2; [exact PC | exact MUf | exact WMf |].
    repeat (apply Forall_cons; [cbn [fst snd]; lia|]). apply Forall_nil. }
  assert (FULL1 : if full then 0 < nb /\ rw_cells asegs m1 lst [C8 (Z_to_bv 64 nx); C8 (Z_to_bv 64 bsz); C8 (Z_to_bv 64 1021)]
             /\ 0x10007fff8000 <= lst /\ lst + 8192 <= ATOP
             /\ u64arr asegs m1 (lst + 24) hs /\ length hs = 1021%nat /\ rng RNG lst 8192
           else nb = 0 /\ lst = 0).
  { destruct full; [| exact FULL]. destruct FULL as (NB1 & LB & L0 & L1 & LA0 & LEN0 & RL).
    xport LB MUf WMf ltac:(ub DTL; ub DHL; ub DNL; ub DSL; lia). xport LA0 MUf WMf ltac:(rewrite LEN0; ub DTL; ub DHL; ub DNL; ub DSL; lia).
    split; [exact NB1|]. split; [exact LB|]. split; [exact L0|]. split; [exact L1|]. split; [exact LA0|]. split; [exact LEN0| exact RL]. }
  clear FULL PC.

  name_sp sp (-2128).
  eapply evtF_cut.
  { eapply (put_to_refill_spec full t hm lst RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m1 n nb fst0 qb b1 actx lo nx bsz maxc csz hs sjunk).
    all: try lazymatch goal with
         | |- stk _ _ _ _ => rewrite Hsp; exact STf
         | |- mem_inv _ _ => exact MIf
         | |- poison_cells _ => exact PC1
         | |- @eq word _ _ => rewrite ?Esp; first [reflexivity | apply Z_to_bv_eqm; rewrite ?unsigned_lit by lia; lia]
         | |- if _ then _ else _ => exact FULL1
         | |- _ \/ _ => first [ub DHT; lia | ub DTL; lia | ub DHL; lia]
         | |- rng _ _ _ => solve_rng
         | |- rw_cells _ _ _ [C1 _; C1 _; C2 _; C4 _; C8 _] => exact HD1
         | |- rw_cells _ _ (shad _) _ => exact SH
         | |- rw_cells _ _ (_ + 80) _ => exact QC
         | |- rw_cells _ _ (_ + 2128) _ => exact CR0
         | |- iclr _ _ => exact TI
         end.
    all: try eassumption. all: try (unfold AIMG_HI, Q_MAX in *; lia).
    all: match goal with |- ?G => idtac "REMP" G end. }
  cbv beta. intros ms2 PP. unfold put_to_refill_post in PP.
  destruct PP as (t0b & t1b & t2b & a4b & a5b & a6b & a7b & t3b & t4b & t5b & t6b & m2 & j0
                  & -> & MUp & WMp & MIp & STp & SH2 & FRP & FRE & LBS).
  unname_sp. rewrite ?unsigned_lit in MUp by lia. rewrite ?unsigned_lit in STp by lia.
  rewrite ?unsigned_lit in FRP by lia. rewrite ?unsigned_lit in FRE by lia.
  replace (bv_unsigned sp + -2128 + -80) with (bv_unsigned sp + -2208) in * by lia.
  replace (bv_unsigned sp + -2128 + -144) with (bv_unsigned sp + -2272) in * by lia.

  xport HD1 MUp WMp ltac:(lia). xport FC1 MUp WMp ltac:(lia).
  xport STATS1 MUp WMp ltac:(rewrite LSJ1; lia).
  xport UW1 MUp WMp ltac:(lia).
  xport FL1 MUp WMp ltac:(lia). xport IAS1 MUp WMp ltac:(lia).
  xport SS1 MUp WMp ltac:(lia). xport TB1 MUp WMp ltac:(rewrite LTB1; lia). xport FRS1 MUp WMp ltac:(lia).
  assert (IAM2 : forall j, 0 <= j < 32768 -> bytes_at asegs m2 (0xdacc8 + 8 * j) (le8 (Z_to_bv 64 0))).
  { (intros j Hj; eapply bytes_at_agree; [exact (IAM1 j Hj)|];
    intros i Hi; apply MUp; cbn [outside]; rewrite length_le8 in Hi; rewrite wa_unsigned by lia; lia). }
  clear IAM1.
  assert (DEP2 : ADEPOT DI L m2).
  { eapply (adi_frame DI); [exact DEP1 | exact MUp | exact WMp |].
    (repeat (apply Forall_cons; [cbn [fst snd]; intros q Hq; first [lia | ub DTN; ub DTS; lia] |]); apply Forall_nil). }
  clear DEP1.

  assert (MU : munch (toref_W L sp t hm n) m m2).
  { eapply munch_trans; [| eapply munch_weaken; [| exact MUp]].
    eapply munch_weaken; [| exact MUf].
    all: solve_sub_fp sp. }
  assert (WM : wmono asegs m m2) by (eapply wmono_trans; [exact WMf| exact WMp]).
  apply evtF_done. unfold free_to_refill_post. exists id. do 11 eexists. exists m2, sj1, tb1, junk2, j0.
  split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MIp|]. split; [exact STp|]. split; [exact IDR|].
  split; [exact HD1|]. split; [exact FC1|]. split; [exact SH2|].
  split; [exact STATS1|]. split; [exact LSJ1|]. split; [exact UW1|]. split; [exact FL1|]. split; [exact IAS1|]. split; [exact IAM2|].
  split; [exact SS1|]. split; [exact TB1|]. split; [exact LTB1|]. split; [exact FRS1|]. split; [exact FRP|]. split; [exact FRE|].
  split; [exact LBS|]. exact DEP2.
  Unshelve. all: try exact STf; try exact STp.
Qed.

Lemma free_from_refill_spec : forall (L : alayout) (full : bool) (g : gqd) RNG
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (ra0 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) fc (m : amem)
    (t hm n b1 actx lo nb fst0 lst qb nx bsz cnt spacebeg id b : Z) (maxc csz stj idxw : word) (sj tb chunks hs : list word)
    (junk2 j0 : list byte) (trt : list Z),
  let ek := EkNew full nx bsz cnt maxc csz stj idxw chunks spacebeg b hs in
  stk asegs m lo (bv_unsigned sp + -2272) -> ATOP <= lo -> lo <= bv_unsigned sp - 4096 ->
  mem_inv asegs m ->

  rw_cells asegs m (bv_unsigned sp + -2128) [C8 (Z_to_bv 64 (bv_unsigned sp + -2128 + 16)); C4 (Z_to_bv 64 (1 + Z.of_nat (length trt))); C4 (Z_to_bv 64 0)] ->
  u64arr asegs m (bv_unsigned sp + -2128 + 16) tb -> length tb = 255%nat ->
  rw_cells asegs m (bv_unsigned sp + -72) [C8 sp; CB 8 junk2; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  rw_cells asegs m (bv_unsigned sp + -2208)
     [C8 (Z_to_bv 64 (t + 208)); C8 (Z_to_bv 64 (bv_unsigned sp + -2128)); C8 s6; C8 (Z_to_bv 64 (bv_unsigned sp + -81));
      C8 (Z_to_bv 64 (bv_unsigned sp + -2128)); C8 (Z_to_bv 64 1); C8 (Z_to_bv 64 0x5e55c); C8 (Z_to_bv 64 (hm + 16)); C8 sp; C8 (Z_to_bv 64 0x5e5cc)] ->
  rw_cells asegs m (bv_unsigned sp + -2272)
     [CB 8 j0; C8 (Z_to_bv 64 hm); C8 (Z_to_bv 64 (t + 208)); C8 (Z_to_bv 64 (bv_unsigned sp + -2128)); C8 (Z_to_bv 64 n);
      C8 (Z_to_bv 64 (t + 80)); C8 (Z_to_bv 64 0xd6730); C8 (Z_to_bv 64 0x41230)] ->

  rw_cells asegs m 0xd6770 [C8 (Z_to_bv 64 Q_MAX); C8 (Z_to_bv 64 Q_MIN); C8 (Z_to_bv 64 Q_CACHE)] ->

  rw_cells asegs m hm [C1 (Z_to_bv 8 3); C1 (Z_to_bv 8 b1); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 (Z_to_bv 64 actx)] ->
  rw_cells asegs m (hm + 16) [C8 (Z_to_bv 64 id)] -> 0 < id < 2^31 ->
  1 <= n <= Q_MAX -> hm mod 16 = 0 -> ablk hm (hm + 16 + rup n 8) -> hm + 16 + rup n 8 <= ATOP -> hm + 24 <= ATOP ->
  rw_cells asegs m (shad (hm + 16)) [CB (Z.to_nat (shlen (rup n 8))) (repeat (Z_to_bv 8 253) (Z.to_nat (shlen (rup n 8))))] ->

  rw_cells asegs m (t + 80) [C8 (Z_to_bv 64 nb); C8 (Z_to_bv 64 fst0); C8 (Z_to_bv 64 lst); C8 (Z_to_bv 64 qb)] ->
  0 <= nb < 2^62 -> 0 <= qb -> qb + n + 8192 < 2^62 -> 0 <= fst0 < 2^64 -> 0 <= lst < 2^64 ->
  sclr t 4096 -> t + 4096 <= ATOP -> t mod 4096 = 0 -> (hm + 24 <= t \/ t + 4096 <= hm) ->
  u64arr asegs m (t + 2800) sj -> length sj = 46%nat -> rw_cells asegs m (t + 3168) [C1 (Z_to_bv 8 0)] ->
  rw_cells asegs m 0x169548 [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] ->
  stk asegs m 0xdacc0 (0xdacc0 + 0x81030) ->
  (forall j, 0 <= j < 32768 -> bytes_at asegs m (0xdacc8 + 8 * j) (le8 (Z_to_bv 64 0))) ->

  (if full then 0 < nb /\ rw_cells asegs m lst [C8 (Z_to_bv 64 nx); C8 (Z_to_bv 64 bsz); C8 (Z_to_bv 64 1021)]
             /\ 0 <= nx < 2^64 /\ 0 <= bsz < 2^64 /\ 0x10007fff8000 <= lst /\ lst + 8192 <= ATOP
             /\ u64arr asegs m (lst + 24) hs /\ length hs = 1021%nat
             /\ rng RNG lst 8192
   else nb = 0 /\ lst = 0) ->
  rw_cells asegs m 0xd6478 [C8 (Z_to_bv 64 spacebeg)] ->
  rw_cells asegs m (t + 2128) [C4 (Z_to_bv 64 cnt); C4 maxc; C8 csz] ->
  u32arr asegs m (t + 2128 + 16) chunks -> length chunks = 16%nat ->
  0 < cnt <= 16 -> nth_error chunks (Z.to_nat (cnt - 1)) = Some idxw -> bv_unsigned idxw < 2^32 ->
  rw_cells asegs m (t + 2784) [C8 stj] ->
  b = spacebeg + 24 * 2^32 + 16 * bv_unsigned idxw ->
  (exists bs, rw_cells asegs m b [CB (Z.to_nat 8192) bs]) ->
  0 < spacebeg -> 0x10007fff8000 <= b -> b + 8192 <= ATOP ->
  (t + 4096 <= b \/ b + 8192 <= t) -> (t + 4096 <= lst \/ lst + 8192 <= t \/ lst = 0) -> (b + 8192 <= lst \/ lst + 8192 <= b) ->
  (hm + 24 <= b \/ b + 8192 <= hm) -> (hm + 24 <= lst \/ lst + 8192 <= hm) ->
  rng RNG b 8192 ->
  ek_seps ek L hm lst ->

  dk_pre ek g RNG t lst hm (qb + ek_delta ek n) m -> dk_seps g L hm ->

  ADEPOT DI L m ->
  sclr (al_nodes L) 1048576 -> al_nodes L + 1048576 <= ATOP -> sclr (al_store L) 8388608 -> al_store L + 8388608 <= ATOP ->
  (t + 4096 <= al_nodes L \/ al_nodes L + 1048576 <= t) -> (t + 4096 <= al_store L \/ al_store L + 8388608 <= t) ->
  bv_unsigned sp < 2^47 ->

  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG t 4096 -> rng RNG hm 24 -> rng RNG (shad (hm + 16)) (shlen (rup n 8)) ->
  AIMG_HI <= al_nodes L -> AIMG_HI <= al_store L -> iclr t 4096 ->
  evtF asegs RNG (free_fast_post DI L ek g ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc t hm n nb fst0 lst qb b1 actx lo m)
    (MS (mkR ra0 (Z_to_bv 64 (bv_unsigned sp + -2272)) gp tp t0 t1 t2 (Z_to_bv 64 (t + 2128)) (Z_to_bv 64 (t + 208))
             (Z_to_bv 64 1) a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 hm) (Z_to_bv 64 (t + 80)) (Z_to_bv 64 (bv_unsigned sp + -2128)) (Z_to_bv 64 n) (Z_to_bv 64 Q_CACHE)
             s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x41390) fc None m (seg_rom asegs)).
Proof.
  intros until trt. cbv zeta.
  intros ST CEIL LO MI SS TB LTB FRS FRP FRE QK HD FC IDR N AL HLO HHI HCE SH QC NB QB QBN FST LST T0 T1 TAL DHT STATS LSJ UW FL IAS IAM
         FULL SB CR CH LCH CNT NTH IXS STS HBE BJ SBP B0 BL1 DTB DTL DBL DHB DHL RB ES DK DS DEP N0 N1 R0 R1 DTN DTS SP47
         RIMG RSTK RT RH RSH NI SI TI. band_lin.
  band_int TI. pose proof (ablk_lin _ _ HLO) as (HL1 & HL2 & HL3 & HL4). unfold AIMG_HI in HL1. band_int HLO. band_int T0. band_int N0. band_int R0.
  assert (RUP : n <= rup n 8 <= n + 7 /\ rup n 8 mod 8 = 0) by (clear -N; unfold rup; Z.div_mod_to_equations; lia).
  assert (SHB : 2148261376 <= shad (hm + 16) /\ shad (hm + 16) + shlen (rup n 8) <= 0x10007fff8000 /\ 0 < shlen (rup n 8)).
  { clear -N HLO HL1 HHI HCE. unfold shad, shlen, ASHOFF, rup in *. rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8. unfold Q_MAX in *. Z.div_mod_to_equations. lia. }
  pose proof (dk_pre_pure _ g RNG L t lst hm (qb + (n + 8192)) m DK DS TI ltac:(unfold AIMG_HI; lia) NI SI
                DHL DTL ltac:(cbn [ek_seps] in ES; destruct full; [destruct ES as (_ & _ & _ & S4); destruct FULL as (_ & _ & _ & _ & L0 & _); exact (proj1 (proj2 (S4 eq_refl))) | destruct FULL as [_ ->]; unfold AIMG_HI in *; lia])
                ltac:(cbn [ek_seps] in ES; destruct full; [destruct ES as (_ & _ & _ & S4); exact (proj2 (proj2 (S4 eq_refl))) | destruct FULL as [_ ->]; unfold AIMG_HI in *; lia])
                ltac:(destruct full; [destruct FULL as (_ & _ & _ & _ & L0 & _) | destruct FULL as [_ ->]]; unfold AIMG_HI in *; lia)
                ltac:(destruct full; [destruct FULL as (_ & _ & _ & _ & L0 & L1 & _) | destruct FULL as [_ ->]]; unfold AIMG_HI in *; atop_facts; lia)
                ltac:(destruct full; [destruct FULL as (_ & _ & _ & _ & L0 & _); right | destruct FULL as [_ ->]; left]; unfold AIMG_HI in *; lia))
    as (DF1 & DF2 & DF3 & DF4 & DG0 & DG1 & DG2).
  cbn [ek_seps] in ES. destruct ES as (SB1 & SB2 & SB3 & SL).
  assert (PL2 : lst = 0 \/ 0x10007fff8000 <= lst) by (destruct full; [destruct FULL as (_ & _ & _ & _ & L0 & _); right; exact L0 | destruct FULL as [_ E0]; left; exact E0]).
  assert (PLB : lst + 8192 <= ATOP) by (destruct full; [destruct FULL as (_ & _ & _ & _ & _ & L1 & _); exact L1 | destruct FULL as [_ E0]; rewrite E0; atop_facts; lia]).
  pose proof (qsz_int lst ltac:(clear -PL2; lia) ltac:(clear -PLB; atop_facts; lia)) as (zq & QZ0 & QZ1 & QZ2 & QZ3).
  unfold AIMG_HI, AFREE_SYM, AFREE_PC in *.
  word_range sp SPR.
  box DHT. box DTN. box DTS. box DTB. box DTL. box DBL. box DHB. box DHL. box SB1. box SB2. box SB3. box DF1. box DF2. box DF3. box DF4. box DG2. box PL2.

  set (sp1 := Z_to_bv 64 (bv_unsigned sp + -2128)) in *.
  assert (Hsp : bv_unsigned sp1 = bv_unsigned sp + -2128) by (subst sp1; apply unsigned_lit; lia).
  replace (bv_unsigned sp + -2272) with (bv_unsigned sp1 + -144) in * by lia.
  replace (bv_unsigned sp + -2208) with (bv_unsigned sp1 + -80) in * by lia.

  eapply evtF_cut.
  { eapply (put_from_refill_spec full g t hm lst b RNG (Z_to_bv 64 0x5e5cc) sp1 gp tp sp (Z_to_bv 64 (hm + 16)) (Z_to_bv 64 (t + 208)) sp1
              (Z_to_bv 64 0x5e55c) (Z_to_bv 64 1) sp1 (Z_to_bv 64 (bv_unsigned sp + -81)) s6 s7 s8 s9 s10 s11
              ra0 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc m n nb fst0 qb b1 actx lo nx bsz cnt spacebeg maxc csz stj idxw chunks hs j0).
    all: try lazymatch goal with
         | |- stk _ _ _ _ => first [exact ST | exact IAS]
         | |- mem_inv _ _ => exact MI
         | |- if _ then _ else _ => exact FULL
         | |- dk_pre _ _ _ _ _ _ _ _ => exact DK
         | |- @eq word _ _ => reflexivity
         | |- @eq Z _ _ => first [exact HBE | lia]
         | |- ex _ => exact BJ
         | |- _ \/ _ => first [ub DHT; lia | ub DTB; lia | ub DTL; lia | ub DBL; lia | ub DHB; lia | ub DHL; lia]
         | |- rng _ _ _ => solve_rng
         | |- rw_cells _ _ _ [C1 _; C1 _; C2 _; C4 _; C8 _] => exact HD
         | |- rw_cells _ _ (shad _) _ => exact SH
         | |- rw_cells _ _ (_ + 80) _ => exact QC
         | |- rw_cells _ _ (_ + 2128) _ => exact CR
         | |- rw_cells _ _ (_ + 2784) _ => exact STS
         | |- rw_cells _ _ (_ + -80) _ => exact FRP
         | |- iclr _ _ => exact TI
         | |- rw_cells _ _ (_ + -144) _ => exact FRE
         | |- u32arr _ _ _ _ => exact CH
         | |- nth_error _ _ = _ => exact NTH
         end.
    all: try eassumption. all: try (unfold AIMG_HI, Q_MAX in *; lia).
    all: match goal with |- ?G => idtac "REMQ" G end. }
  cbv beta. intros ms2 PP. unfold put_tail_post in PP.
  destruct PP as (t0b & t1b & t2b & a0b & a1b & a2b & a3b & a4b & a5b & a6b & a7b & t3b & t4b & t5b & t6b & m2
                  & -> & MUp & WMp & MIp & STp & SH2 & HD2 & QC2 & EKP & DKP).
  replace (ret_pc (Z_to_bv 64 386508)) with (Z_to_bv 64 386508) by (symmetry; apply ret_pc_even; [lia|reflexivity]).

  cbn [ek_b] in MUp.
  xport FC MUp WMp ltac:(ub DHT; ub DHB; ub DHL; ub DF1; lia).
  xport STATS MUp WMp ltac:(rewrite LSJ; ub DTB; ub DTL; ub DF2; lia).
  xport UW MUp WMp ltac:(ub DTB; ub DTL; ub DF2; lia).
  xport FL MUp WMp ltac:(ub DG2; ub PL2; lia). xport IAS MUp WMp ltac:(ub DG2; ub PL2; lia).
  xport SS MUp WMp ltac:(lia). xport TB MUp WMp ltac:(rewrite LTB; lia). xport FRS MUp WMp ltac:(lia).
  assert (IAM2 : forall j, 0 <= j < 32768 -> bytes_at asegs m2 (0xdacc8 + 8 * j) (le8 (Z_to_bv 64 0))).
  { (intros j Hj; eapply bytes_at_agree; [exact (IAM j Hj)|];
    intros i Hi; apply MUp; cbn [outside]; rewrite length_le8 in Hi; rewrite wa_unsigned by lia; ub DG2; ub PL2; lia). }
  clear IAM.
  assert (DEP2 : ADEPOT DI L m2).
  { eapply (adi_frame DI); [exact DEP | exact MUp | exact WMp |].
    (repeat (apply Forall_cons; [cbn [fst snd]; intros q Hq;
      first [lia | ub DTN; ub DTS; lia | ub SB2; ub SB3; lia | ub DF3; ub DF4; ub DG2; lia
            | destruct full; [destruct (SL eq_refl) as (_ & S6 & S7); lia | destruct FULL as [_ LST0]; lia] ] |]); apply Forall_nil). }
  clear DEP.

  subst sp1. rewrite ?unsigned_lit in STp by lia. rewrite ?unsigned_lit in MUp by lia.
  apply rw_cells_of_u64arr in TB. rewrite LTB in TB.
  eapply evtF_mono.
  { (eapply (ficptD_spec RNG sp gp tp); [exact STp | atop_facts; lia | lia | exact MIp
      | eexists; split; [exact SS | reflexivity]
      | eexists; split; [replace (bv_unsigned sp + -2112) with (bv_unsigned sp + -2128 + 16) by lia; exact TB | reflexivity]
      | exact FRS | exact RIMG | solve_rng ]). }
  cbv beta. intros ms3 [-> ST3].

  assert (MU : munch (free_W L sp t hm n lst (EkNew full nx bsz cnt maxc csz stj idxw chunks spacebeg b hs) g) m m2).
  { eapply munch_weaken; [| exact MUp]. cbn [ek_b]. solve_sub_fp sp. }
  unfold free_fast_post. exists id. do 15 eexists. exists m2, sj.
  split; [reflexivity|].
  split; [exact MU|]. split; [exact WMp|]. split; [exact MIp|]. split; [exact ST3|]. split; [exact IDR|].
  split; [exact HD2|]. split; [exact FC|]. split; [exact SH2|]. split; [exact QC2|]. split; [exact EKP|]. split; [exact DKP|].
  split; [exact STATS|]. split; [exact LSJ|]. split; [exact UW|]. split; [exact FL|]. split; [exact IAS|]. split; [exact IAM2|].
  exact DEP2.
  Unshelve. all: try exact ST; try exact STp.
Qed.
End WithDepot.
End CANSEC1.
End F_afree_icptR.

Module F_afreeC_iface.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase. Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics. Import LinuxProcessSemantics.LinuxProcessSem.MemImageType. Import LinuxProcessSemantics.LinuxProcessSem.State. Import LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude. Import LinuxProcessSemantics.Riscv.Instr. Import LinuxProcessSemantics.Riscv.Decode. Import LinuxProcessSemantics.Riscv.DecodeC. Import LinuxProcessSemantics.Riscv.Sem. Import LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.ITree. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Nodes. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Decode. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Arr. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.InitMem.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.STree. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanCtrl. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanEmbed.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AImg. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AProto. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ABase. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ABytes. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AQConst. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ADepot_iface.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.StepF.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AKit. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AKit2. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AKitQ.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_apoison.F_apoison. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aalloc_s.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aalloc1.F_aalloc1. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_afree_iseg. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_afree_front. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_adrain. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_afree_tail. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_afree_icpt.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aenqueue.F_aenqueueR. Import F_afree_tailR. Import F_afree_icptR.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT}.
Definition drain_torec_post (gfull : bool) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a2 a3 : word) (F : bvmap 5 word) (fc : bv 32)
    (t nb fst lst qb gnb gfst glst gqb lo : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 AQUAR_Q) (Z_to_bv 64 Q_MIN) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x3eb38) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 48, bv_unsigned sp); (t + 80, t + 112); (0xd67c8, 0xd67c8 + 4); (0xd67d0, 0xd67d0 + 32); (glst, glst + 8)]%Z m m'
    /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp)
    /\ rw_cells asegs m' (t + 80) [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]
    /\ rw_cells asegs m' 0xd67c8 [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]
    /\ rw_cells asegs m' 0xd67d0 [C8 (Z_to_bv 64 (gnb + nb)); C8 (Z_to_bv 64 (if gfull then gfst else fst)); C8 (Z_to_bv 64 lst);
                                   C8 (Z_to_bv 64 (gqb + qb))]
    /\ (if gfull then rw_cells asegs m' glst [C8 (Z_to_bv 64 fst)] else True).

Definition drain_torec_stmt : Prop := forall (gfull : bool) (t glst : Z) RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (nb fst lst qb gnb gfst gqb gnx lo : Z),
  stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - 48 ->
  mem_inv asegs m ->
  a0 = Z_to_bv 64 AQUAR_Q -> a1 = Z_to_bv 64 (t + 80) ->
  rw_cells asegs m (t + 80) [C8 (Z_to_bv 64 nb); C8 (Z_to_bv 64 fst); C8 (Z_to_bv 64 lst); C8 (Z_to_bv 64 qb)] ->
  0 < nb < 2^63 -> 0 <= qb -> 0 <= fst < 2^64 -> 0 <= lst < 2^64 ->
  rw_cells asegs m AQ_MUTEX [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] ->
  rw_cells asegs m AQ_GCACHE [C8 (Z_to_bv 64 gnb); C8 (Z_to_bv 64 gfst); C8 (Z_to_bv 64 glst); C8 (Z_to_bv 64 gqb)] ->
  0 <= gnb < 2^62 -> 0 <= gqb -> Q_MAX < gqb + qb -> gqb + qb < 2^63 -> 0 <= gfst < 2^64 -> 0 <= glst < 2^64 ->
  rw_cells asegs m AQ_MAX [C8 (Z_to_bv 64 Q_MAX); C8 (Z_to_bv 64 Q_MIN); C8 (Z_to_bv 64 Q_CACHE)] ->
  (if gfull then 0 < gnb /\ rw_cells asegs m glst [C8 (Z_to_bv 64 gnx)] /\ AIMG_HI <= glst /\ glst + Q_BATCH_BYTES <= ATOP
                 /\ (t + 4096 <= glst \/ glst + Q_BATCH_BYTES <= t)
   else gnb = 0) ->
  iclr t 4096 -> t + 4096 <= ATOP ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG t 4096 -> (if gfull then rng RNG glst Q_BATCH_BYTES else True) ->
  evtF asegs RNG (drain_torec_post gfull ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a2 a3 F fc t nb fst lst qb gnb gfst glst gqb lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x3e994) fc None m (seg_rom asegs)).

Definition dk_preC (ek : enq_kind) (g : gqd) (RNG : footprint) (t lst hm qb' : Z) (m : amem) : Prop :=
     g_drain g = true
  /\ rw_cells asegs m 0xd67c8 [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]
  /\ rw_cells asegs m 0xd67d0 [C8 (Z_to_bv 64 (g_nb g)); C8 (Z_to_bv 64 (g_fst g)); C8 (Z_to_bv 64 (g_lst g)); C8 (Z_to_bv 64 (g_qb g))]
  /\ 0 <= g_nb g < 2^62 /\ 0 <= g_qb g /\ 0 <= g_fst g < 2^64 /\ 0 <= g_lst g < 2^64
  /\ Q_CACHE < qb' /\ Q_MAX < g_qb g + qb' /\ g_qb g + qb' < 2^63
  /\ (if g_full g then 0 < g_nb g /\ rw_cells asegs m (g_lst g) [C8 (Z_to_bv 64 (g_nx g))] /\ 0x10007fff8000 <= g_lst g /\ g_lst g + 8192 <= ATOP
                     /\ (t + 4096 <= g_lst g \/ g_lst g + 8192 <= t) /\ (hm + 16 <= g_lst g \/ g_lst g + 8 <= hm)
                     /\ (lst + 8192 <= g_lst g \/ g_lst g + 8192 <= lst) /\ (ek_b ek lst + 8192 <= g_lst g \/ g_lst g + 8192 <= ek_b ek lst)
                     /\ rng RNG (g_lst g) 8192
      else g_nb g = 0 /\ g_lst g = 0).

Definition dk_postC (g : gqd) (nb' fst' lst' qb' : Z) (m' : amem) : Prop :=
     rw_cells asegs m' 0xd67c8 [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]
  /\ rw_cells asegs m' 0xd67d0 [C8 (Z_to_bv 64 (g_nb g + nb')); C8 (Z_to_bv 64 (if g_full g then g_fst g else fst'));
                                 C8 (Z_to_bv 64 lst'); C8 (Z_to_bv 64 (g_qb g + qb'))]
  /\ (if g_full g then rw_cells asegs m' (g_lst g) [C8 (Z_to_bv 64 fst')] else True).

Definition put_frame (cbc cbs s6 s5 s4 s3 s2 s1 s0 ra : word) : list cell :=
  [C8 cbc; C8 cbs; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

Definition put_torec_post (ek : enq_kind) (g : gqd)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a3 : word) (F : bvmap 5 word) (fc : bv 32)
    (t hm n nb fst0 lst qb b1 actx lo : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 xs0 xs1 xs2 xs3 xs4 xs5 xs6 a4 a5 a6 a7 t3 t4 t5 t6 : word) m',
    ms' = MS (mkR (Z_to_bv 64 0x41168) (Z_to_bv 64 (bv_unsigned sp - 80)) gp tp t0 t1 t2 xs0 xs1
                  (Z_to_bv 64 AQUAR_Q) (Z_to_bv 64 Q_MIN) (Z_to_bv 64 (t + 208)) a3 a4 a5 a6 a7 xs2 xs3 xs4 xs5 xs6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x3eb38) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 144, bv_unsigned sp); (shad (hm + 16), shad (hm + 16) + shlen (rup n 8));
              (t + 80, t + 112); (t + 2128, t + 2132); (t + 2784, t + 2792);
              (lst, lst + qsz lst); (ek_b ek lst, ek_b ek lst + 8192);
              (0xd67c8, 0xd67c8 + 4); (0xd67d0, 0xd67d0 + 32); (dk_glst g lst, dk_glst g lst + 8)]%Z m m'
    /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp - 80)
    /\ rw_cells asegs m' (bv_unsigned sp - 80) (put_frame (Z_to_bv 64 (t + 208)) a3 s6 s5 s4 s3 s2 s1 s0 ra)
    /\ rw_cells asegs m' (shad (hm + 16)) [CB (Z.to_nat (shlen (rup n 8))) (repeat (Z_to_bv 8 253) (Z.to_nat (shlen (rup n 8))))]
    /\ rw_cells asegs m' hm [C1 (Z_to_bv 8 3); C1 (Z_to_bv 8 b1); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 (Z_to_bv 64 actx)]
    /\ rw_cells asegs m' (t + 80) [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]
    /\ ek_post ek t lst hm n m'
    /\ dk_postC g (ek_nb ek nb) (ek_fst ek fst0) (ek_lst ek lst) (qb + ek_delta ek n) m'.

Definition put_torec_stmt : Prop := forall (ek : enq_kind) (g : gqd) (t hm lst : Z) RNG
    ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (n nb fst0 qb b1 actx lo : Z) (sjunk : list byte),
  stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - 144 ->
  mem_inv asegs m ->
  a0 = Z_to_bv 64 0xd6730 -> a1 = Z_to_bv 64 (t + 80) -> a2 = Z_to_bv 64 (t + 208) -> a4 = Z_to_bv 64 hm -> a5 = Z_to_bv 64 n ->
  rw_cells asegs m 0xd6770 [C8 (Z_to_bv 64 Q_MAX); C8 (Z_to_bv 64 Q_MIN); C8 (Z_to_bv 64 Q_CACHE)] ->
  rw_cells asegs m 0xd1510 [C8 (Z_to_bv 64 AFLAGS)] ->
  rw_cells asegs m 0xd72e4 [C4 (Z_to_bv 64 0x1000); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0xbe)] ->
  poison_cells m ->
  rw_cells asegs m hm [C1 (Z_to_bv 8 3); C1 (Z_to_bv 8 b1); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 (Z_to_bv 64 actx)] ->
  1 <= n <= Q_MAX -> 0 <= b1 < 256 -> hm mod 16 = 0 -> ablk hm (hm + 16 + rup n 8) -> hm + 16 + rup n 8 <= ATOP -> hm + 16 <= ATOP ->
  rw_cells asegs m (shad (hm + 16)) [CB (Z.to_nat (shlen (rup n 8))) sjunk] ->
  rw_cells asegs m (t + 80) [C8 (Z_to_bv 64 nb); C8 (Z_to_bv 64 fst0); C8 (Z_to_bv 64 lst); C8 (Z_to_bv 64 qb)] ->
  0 <= nb < 2^62 -> 0 <= qb -> qb + n + 8192 < 2^62 -> 0 <= fst0 < 2^64 -> 0 <= lst < 2^64 ->
  sclr t 4096 -> t + 4096 <= ATOP -> t mod 4096 = 0 -> (hm + 16 <= t \/ t + 4096 <= hm) ->
  ek_pre ek RNG t nb lst n hm m ->
  dk_preC ek g RNG t lst hm (qb + ek_delta ek n) m ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG t 4096 -> rng RNG hm 16 -> rng RNG (shad (hm + 16)) (shlen (rup n 8)) ->
  iclr t 4096 ->
  evtF asegs RNG (put_torec_post ek g ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a3 F fc t hm n nb fst0 lst qb b1 actx lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x4108c) fc None m (seg_rom asegs)).

Definition put_from_refill_torec_stmt : Prop := forall (full : bool) (g : gqd) (t hm lst b : Z) RNG
    (ra sp gp tp s0 s1 a2 a3 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (ra0 t0 t1 t2 a1 a2' a3' a4 a5 a6 a7 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) fc (m : amem) (n nb fst0 qb b1 actx lo nx bsz cnt spacebeg : Z) (maxc csz stj idxw : word) (chunks hs : list word)
    (j0 : list byte),
  let ek := EkNew full nx bsz cnt maxc csz stj idxw chunks spacebeg b hs in
  stk asegs m lo (bv_unsigned sp + -144) -> ATOP <= lo -> lo <= bv_unsigned sp - 144 ->
  mem_inv asegs m ->
  a2 = Z_to_bv 64 (t + 208) ->

  rw_cells asegs m (bv_unsigned sp + -80) [C8 a2; C8 a3; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  rw_cells asegs m (bv_unsigned sp + -144)
     [CB 8 j0; C8 (Z_to_bv 64 hm); C8 a2; C8 a3; C8 (Z_to_bv 64 n); C8 (Z_to_bv 64 (t + 80)); C8 (Z_to_bv 64 0xd6730); C8 (Z_to_bv 64 0x41230)] ->

  rw_cells asegs m 0xd6770 [C8 (Z_to_bv 64 Q_MAX); C8 (Z_to_bv 64 Q_MIN); C8 (Z_to_bv 64 Q_CACHE)] ->

  rw_cells asegs m hm [C1 (Z_to_bv 8 3); C1 (Z_to_bv 8 b1); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 (Z_to_bv 64 actx)] ->
  1 <= n <= Q_MAX -> hm mod 16 = 0 -> ablk hm (hm + 16 + rup n 8) -> hm + 16 + rup n 8 <= ATOP -> hm + 16 <= ATOP ->
  rw_cells asegs m (shad (hm + 16)) [CB (Z.to_nat (shlen (rup n 8))) (repeat (Z_to_bv 8 253) (Z.to_nat (shlen (rup n 8))))] ->

  rw_cells asegs m (t + 80) [C8 (Z_to_bv 64 nb); C8 (Z_to_bv 64 fst0); C8 (Z_to_bv 64 lst); C8 (Z_to_bv 64 qb)] ->
  0 <= nb < 2^62 -> 0 <= qb -> qb + n + 8192 < 2^62 -> 0 <= fst0 < 2^64 -> 0 <= lst < 2^64 ->
  sclr t 4096 -> t + 4096 <= ATOP -> t mod 4096 = 0 -> (hm + 16 <= t \/ t + 4096 <= hm) ->

  (if full then 0 < nb /\ rw_cells asegs m lst [C8 (Z_to_bv 64 nx); C8 (Z_to_bv 64 bsz); C8 (Z_to_bv 64 1021)]
             /\ 0 <= nx < 2^64 /\ 0 <= bsz < 2^64 /\ 0x10007fff8000 <= lst /\ lst + 8192 <= ATOP
             /\ u64arr asegs m (lst + 24) hs /\ length hs = 1021%nat
             /\ rng RNG lst 8192
   else nb = 0 /\ lst = 0) ->
  rw_cells asegs m 0xd6478 [C8 (Z_to_bv 64 spacebeg)] ->
  rw_cells asegs m (t + 2128) [C4 (Z_to_bv 64 cnt); C4 maxc; C8 csz] ->
  u32arr asegs m (t + 2128 + 16) chunks -> length chunks = 16%nat ->
  0 < cnt <= 16 -> nth_error chunks (Z.to_nat (cnt - 1)) = Some idxw -> bv_unsigned idxw < 2^32 ->
  rw_cells asegs m (t + 2784) [C8 stj] ->
  b = spacebeg + 24 * 2^32 + 16 * bv_unsigned idxw ->
  (exists bs, rw_cells asegs m b [CB (Z.to_nat 8192) bs]) ->
  0 < spacebeg -> 0x10007fff8000 <= b -> b + 8192 <= ATOP ->
  (t + 4096 <= b \/ b + 8192 <= t) -> (t + 4096 <= lst \/ lst + 8192 <= t \/ lst = 0) -> (b + 8192 <= lst \/ lst + 8192 <= b) ->
  (hm + 16 <= b \/ b + 8192 <= hm) -> (hm + 16 <= lst \/ lst + 8192 <= hm) ->
  rng RNG b 8192 ->

  dk_preC ek g RNG t lst hm (qb + ek_delta ek n) m ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG t 4096 -> rng RNG hm 16 -> rng RNG (shad (hm + 16)) (shlen (rup n 8)) ->
  iclr t 4096 ->
  evtF asegs RNG (put_torec_post ek g ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a3 F fc t hm n nb fst0 lst qb b1 actx lo m)
    (MS (mkR ra0 (Z_to_bv 64 (bv_unsigned sp + -144)) gp tp t0 t1 t2 (Z_to_bv 64 (t + 2128)) (Z_to_bv 64 (t + 208))
             (Z_to_bv 64 1) a1 a2' a3' a4 a5 a6 a7
             (Z_to_bv 64 hm) (Z_to_bv 64 (t + 80)) a3 (Z_to_bv 64 n) (Z_to_bv 64 Q_CACHE) s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x41390) fc None m (seg_rom asegs)).

Section WithDepot.
Variable DI : ADepotIface.

Definition free_torec_post (L : alayout) (ek : enq_kind) (g : gqd)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (t hm n nb fst0 lst qb b1 actx lo : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists (id : Z) (t0 t1 t2 xs0 xs1 xs2 xs3 xs4 xs5 xs6 ps0 ps1 ps2 ps3 ps4 ps5 spv a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) m' (sj' : list word)
                    (csA csT : list cell) (junk2 : list byte),
    let spP := bv_unsigned sp - 2128 in
    ms' = MS (mkR (Z_to_bv 64 0x41168) (Z_to_bv 64 (spP - 80)) gp tp t0 t1 t2 xs0 xs1
                  (Z_to_bv 64 AQUAR_Q) (Z_to_bv 64 Q_MIN) (Z_to_bv 64 (t + 208)) a3 a4 a5 a6 a7 xs2 xs3 xs4 xs5 xs6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x3eb38) fc None m' (seg_rom asegs)
    /\ munch ([(bv_unsigned sp - 4096, bv_unsigned sp); (0xdacc0, 0xdacc0 + 0x81030); (0x169548, 0x169548 + 4);
               (t + 3168, t + 3169); (hm, hm + 4); (hm + 16, hm + 24); (t + 2800, t + 2800 + 368);
               (ADEPOT_LO, ADEPOT_HI); (al_nodes L, al_nodes L + 1048576); (al_store L, al_store L + 8388608);
               (shad (hm + 16), shad (hm + 16) + shlen (rup n 8)); (t + 80, t + 112); (t + 2128, t + 2132); (t + 2784, t + 2792);
               (lst, lst + qsz lst); (ek_b ek lst, ek_b ek lst + 8192);
               (0xd67c8, 0xd67c8 + 4); (0xd67d0, 0xd67d0 + 32); (dk_glst g lst, dk_glst g lst + 8)]%Z) m m'
    /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (spP - 80)
    /\ 0 < id < 2^31

    /\ rw_cells asegs m' (spP - 80) (put_frame (Z_to_bv 64 (t + 208)) a3 s6 ps5 ps4 ps3 ps2 ps1 ps0 (Z_to_bv 64 386508))

    /\ rw_cells asegs m' spP csA /\ cells_size csA = 16%nat
    /\ rw_cells asegs m' (spP + 16) csT /\ cells_size csT = 2040%nat
    /\ rw_cells asegs m' (bv_unsigned sp - 72) [C8 spv; CB 8 junk2; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
    /\ rw_cells asegs m' hm [C1 (Z_to_bv 8 3); C1 (Z_to_bv 8 b1); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 (Z_to_bv 64 actx)]
    /\ rw_cells asegs m' (hm + 16) [C8 (Z_to_bv 64 id)]
    /\ rw_cells asegs m' (shad (hm + 16)) [CB (Z.to_nat (shlen (rup n 8))) (repeat (Z_to_bv 8 253) (Z.to_nat (shlen (rup n 8))))]
    /\ rw_cells asegs m' (t + 80) [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]
    /\ ek_post ek t lst hm n m'
    /\ dk_postC g (ek_nb ek nb) (ek_fst ek fst0) (ek_lst ek lst) (qb + ek_delta ek n) m'
    /\ u64arr asegs m' (t + 2800) sj' /\ length sj' = 46%nat
    /\ rw_cells asegs m' (t + 3168) [C1 (Z_to_bv 8 0)]
    /\ rw_cells asegs m' 0x169548 [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]
    /\ stk asegs m' 0xdacc0 (0xdacc0 + 0x81030)
    /\ (forall j, 0 <= j < 32768 -> bytes_at asegs m' (0xdacc8 + 8 * j) (le8 (Z_to_bv 64 0)))
    /\ ADEPOT DI L m'.

Definition free_torec_stmt : Prop := forall (L : alayout) (ia : bool) (ek : enq_kind) (g : gqd) RNG
    ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem)
    (t ctx hm n b1 actx lo top bot nb fst0 lst qb : Z) (uw : word) (sj : list word) (sjunk : list byte) (trt : list Z),
  stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - 4096 ->
  mem_inv asegs m ->
  tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 (hm + 16) ->
  bv_unsigned sp mod 16 = 0 ->
  allocA_cells m ctx t -> poison_cells m ->
  rw_cells asegs m 0xda7bc [C4 (Z_to_bv 64 30)] ->
  rw_cells asegs m 0x16b60a [C1 (Z_to_bv 8 1)] ->
  rw_cells asegs m 0xd14f8 [C8 (Z_to_bv 64 0x169560)] -> rw_cells asegs m 0x169560 [C8 (Z_to_bv 64 4096)] ->
  rw_cells asegs m 0x16b588 [C8 (Z_to_bv 64 0)] ->
  rw_cells asegs m 0xd6770 [C8 (Z_to_bv 64 Q_MAX); C8 (Z_to_bv 64 Q_MIN); C8 (Z_to_bv 64 Q_CACHE)] ->
  rw_cells asegs m 0xd1510 [C8 (Z_to_bv 64 AFLAGS)] ->
  rw_cells asegs m 0xd72e4 [C4 (Z_to_bv 64 0x1000); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0xbe)] ->
  rw_cells asegs m 0x169548 [C1 (Z_to_bv 8 (if ia then 1 else 0)); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] ->
  stk asegs m 0xdacc0 (0xdacc0 + 0x81030) ->
  (ia = true -> forall j, 0 <= j < 32768 -> bytes_at asegs m (0xdacc8 + 8 * j) (le8 (Z_to_bv 64 0))) ->
  rw_cells asegs m (ctx + 8) [C4 (Z_to_bv 64 0)] ->
  rw_cells asegs m t [C8 (Z_to_bv 64 ctx); C8 (Z_to_bv 64 top); C8 (Z_to_bv 64 bot)] ->
  rw_cells asegs m (t + 40) [C1 (Z_to_bv 8 0)] -> rw_cells asegs m (t + 3168) [C1 (Z_to_bv 8 0)] ->
  u64arr asegs m (t + 2800) sj -> length sj = 46%nat ->
  rw_cells asegs m (t + 80) [C8 (Z_to_bv 64 nb); C8 (Z_to_bv 64 fst0); C8 (Z_to_bv 64 lst); C8 (Z_to_bv 64 qb)] ->
  0 <= nb < 2^62 -> 0 <= qb -> qb + n + 8192 < 2^62 -> 0 <= fst0 < 2^64 -> 0 <= lst < 2^64 ->
  0 < ctx -> sclr ctx 65536 -> ctx + 4096 <= ATOP ->
  sclr t 4096 -> t + 4096 <= ATOP -> t mod 4096 = 0 -> (ctx + 4096 <= t \/ t + 4096 <= ctx) ->
  rw_cells asegs m hm [C1 (Z_to_bv 8 2); C1 (Z_to_bv 8 b1); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 (Z_to_bv 64 actx)] ->
  rw_cells asegs m (hm + 16) [C8 uw] -> 0 <= b1 < 256 -> Z.land b1 3 = 1 -> 1 <= n <= Q_MAX -> hm mod 16 = 0 ->
  ablk hm (hm + 16 + rup n 8) -> hm + 16 + rup n 8 <= ATOP -> hm + 24 <= ATOP ->
  rw_cells asegs m (shad (hm + 16)) [CB (Z.to_nat (shlen (rup n 8))) sjunk] ->
  (hm + 24 <= t \/ t + 4096 <= hm) -> (hm + 24 <= ctx \/ ctx + 4096 <= hm) ->
  ek_pre ek RNG t nb lst n hm m -> ek_seps ek L hm lst ->
  dk_preC ek g RNG t lst hm (qb + ek_delta ek n) m -> dk_seps g L hm ->
  ADEPOT DI L m ->
  sclr (al_nodes L) 1048576 -> al_nodes L + 1048576 <= ATOP -> sclr (al_store L) 8388608 -> al_store L + 8388608 <= ATOP ->
  (hm + 24 <= al_nodes L \/ al_nodes L + 1048576 <= hm) -> (hm + 24 <= al_store L \/ al_store L + 8388608 <= hm) ->
  (t + 4096 <= al_nodes L \/ al_nodes L + 1048576 <= t) -> (t + 4096 <= al_store L \/ al_store L + 8388608 <= t) ->
  (ctx + 4096 <= al_nodes L \/ al_nodes L + 1048576 <= ctx) -> (ctx + 4096 <= al_store L \/ al_store L + 8388608 <= ctx) ->
  afree_unw RNG lo m top sp s0 ra trt ->
  bv_unsigned s0 <> bv_unsigned sp + 8 ->
  In (AFREE_PC :: trt) (al_U L) ->
  0 <= bot -> bot < bv_unsigned sp -> bot < top -> 4096 <= top <= 2^47 -> 4096 <= bv_unsigned ra -> bv_unsigned ra <> AFREE_PC ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG ctx 4096 -> rng RNG t 4096 ->
  rng RNG (al_nodes L) 1048576 -> rng RNG (al_store L) 8388608 -> rng RNG hm 24 -> rng RNG (shad (hm + 16)) (shlen (rup n 8)) ->
  AIMG_HI <= ctx -> AIMG_HI <= al_nodes L -> AIMG_HI <= al_store L -> iclr t 4096 ->
  evtF asegs RNG (free_torec_post L ek g ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc t hm n nb fst0 lst qb b1 actx lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 AFREE_SYM) fc None m (seg_rom asegs)).

Definition free_from_refill_torec_stmt : Prop := forall (L : alayout) (full : bool) (g : gqd) RNG
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (ra0 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) fc (m : amem)
    (t hm n b1 actx lo nb fst0 lst qb nx bsz cnt spacebeg id b : Z) (maxc csz stj idxw : word) (sj tb chunks hs : list word)
    (junk2 j0 : list byte) (trt : list Z),
  let ek := EkNew full nx bsz cnt maxc csz stj idxw chunks spacebeg b hs in
  stk asegs m lo (bv_unsigned sp + -2272) -> ATOP <= lo -> lo <= bv_unsigned sp - 4096 ->
  mem_inv asegs m ->

  rw_cells asegs m (bv_unsigned sp + -2128) [C8 (Z_to_bv 64 (bv_unsigned sp + -2128 + 16)); C4 (Z_to_bv 64 (1 + Z.of_nat (length trt))); C4 (Z_to_bv 64 0)] ->
  u64arr asegs m (bv_unsigned sp + -2128 + 16) tb -> length tb = 255%nat ->
  rw_cells asegs m (bv_unsigned sp + -72) [C8 sp; CB 8 junk2; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  rw_cells asegs m (bv_unsigned sp + -2208)
     [C8 (Z_to_bv 64 (t + 208)); C8 (Z_to_bv 64 (bv_unsigned sp + -2128)); C8 s6; C8 (Z_to_bv 64 (bv_unsigned sp + -81));
      C8 (Z_to_bv 64 (bv_unsigned sp + -2128)); C8 (Z_to_bv 64 1); C8 (Z_to_bv 64 0x5e55c); C8 (Z_to_bv 64 (hm + 16)); C8 sp; C8 (Z_to_bv 64 0x5e5cc)] ->
  rw_cells asegs m (bv_unsigned sp + -2272)
     [CB 8 j0; C8 (Z_to_bv 64 hm); C8 (Z_to_bv 64 (t + 208)); C8 (Z_to_bv 64 (bv_unsigned sp + -2128)); C8 (Z_to_bv 64 n);
      C8 (Z_to_bv 64 (t + 80)); C8 (Z_to_bv 64 0xd6730); C8 (Z_to_bv 64 0x41230)] ->

  rw_cells asegs m 0xd6770 [C8 (Z_to_bv 64 Q_MAX); C8 (Z_to_bv 64 Q_MIN); C8 (Z_to_bv 64 Q_CACHE)] ->

  rw_cells asegs m hm [C1 (Z_to_bv 8 3); C1 (Z_to_bv 8 b1); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 (Z_to_bv 64 actx)] ->
  rw_cells asegs m (hm + 16) [C8 (Z_to_bv 64 id)] -> 0 < id < 2^31 ->
  1 <= n <= Q_MAX -> hm mod 16 = 0 -> ablk hm (hm + 16 + rup n 8) -> hm + 16 + rup n 8 <= ATOP -> hm + 24 <= ATOP ->
  rw_cells asegs m (shad (hm + 16)) [CB (Z.to_nat (shlen (rup n 8))) (repeat (Z_to_bv 8 253) (Z.to_nat (shlen (rup n 8))))] ->

  rw_cells asegs m (t + 80) [C8 (Z_to_bv 64 nb); C8 (Z_to_bv 64 fst0); C8 (Z_to_bv 64 lst); C8 (Z_to_bv 64 qb)] ->
  0 <= nb < 2^62 -> 0 <= qb -> qb + n + 8192 < 2^62 -> 0 <= fst0 < 2^64 -> 0 <= lst < 2^64 ->
  sclr t 4096 -> t + 4096 <= ATOP -> t mod 4096 = 0 -> (hm + 24 <= t \/ t + 4096 <= hm) ->
  u64arr asegs m (t + 2800) sj -> length sj = 46%nat -> rw_cells asegs m (t + 3168) [C1 (Z_to_bv 8 0)] ->
  rw_cells asegs m 0x169548 [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] ->
  stk asegs m 0xdacc0 (0xdacc0 + 0x81030) ->
  (forall j, 0 <= j < 32768 -> bytes_at asegs m (0xdacc8 + 8 * j) (le8 (Z_to_bv 64 0))) ->

  (if full then 0 < nb /\ rw_cells asegs m lst [C8 (Z_to_bv 64 nx); C8 (Z_to_bv 64 bsz); C8 (Z_to_bv 64 1021)]
             /\ 0 <= nx < 2^64 /\ 0 <= bsz < 2^64 /\ 0x10007fff8000 <= lst /\ lst + 8192 <= ATOP
             /\ u64arr asegs m (lst + 24) hs /\ length hs = 1021%nat
             /\ rng RNG lst 8192
   else nb = 0 /\ lst = 0) ->
  rw_cells asegs m 0xd6478 [C8 (Z_to_bv 64 spacebeg)] ->
  rw_cells asegs m (t + 2128) [C4 (Z_to_bv 64 cnt); C4 maxc; C8 csz] ->
  u32arr asegs m (t + 2128 + 16) chunks -> length chunks = 16%nat ->
  0 < cnt <= 16 -> nth_error chunks (Z.to_nat (cnt - 1)) = Some idxw -> bv_unsigned idxw < 2^32 ->
  rw_cells asegs m (t + 2784) [C8 stj] ->
  b = spacebeg + 24 * 2^32 + 16 * bv_unsigned idxw ->
  (exists bs, rw_cells asegs m b [CB (Z.to_nat 8192) bs]) ->
  0 < spacebeg -> 0x10007fff8000 <= b -> b + 8192 <= ATOP ->
  (t + 4096 <= b \/ b + 8192 <= t) -> (t + 4096 <= lst \/ lst + 8192 <= t \/ lst = 0) -> (b + 8192 <= lst \/ lst + 8192 <= b) ->
  (hm + 24 <= b \/ b + 8192 <= hm) -> (hm + 24 <= lst \/ lst + 8192 <= hm) ->
  rng RNG b 8192 ->
  ek_seps ek L hm lst ->

  dk_preC ek g RNG t lst hm (qb + ek_delta ek n) m -> dk_seps g L hm ->

  ADEPOT DI L m ->
  sclr (al_nodes L) 1048576 -> al_nodes L + 1048576 <= ATOP -> sclr (al_store L) 8388608 -> al_store L + 8388608 <= ATOP ->
  (t + 4096 <= al_nodes L \/ al_nodes L + 1048576 <= t) -> (t + 4096 <= al_store L \/ al_store L + 8388608 <= t) ->
  bv_unsigned sp < 2^47 ->

  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG t 4096 -> rng RNG hm 24 -> rng RNG (shad (hm + 16)) (shlen (rup n 8)) ->
  AIMG_HI <= al_nodes L -> AIMG_HI <= al_store L -> iclr t 4096 ->
  evtF asegs RNG (free_torec_post L ek g ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc t hm n nb fst0 lst qb b1 actx lo m)
    (MS (mkR ra0 (Z_to_bv 64 (bv_unsigned sp + -2272)) gp tp t0 t1 t2 (Z_to_bv 64 (t + 2128)) (Z_to_bv 64 (t + 208))
             (Z_to_bv 64 1) a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 hm) (Z_to_bv 64 (t + 80)) (Z_to_bv 64 (bv_unsigned sp + -2128)) (Z_to_bv 64 n) (Z_to_bv 64 Q_CACHE)
             s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x41390) fc None m (seg_rom asegs)).
End WithDepot.
End CANSEC1.
End F_afreeC_iface.

Module F_adrainC.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase. Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics. Import LinuxProcessSemantics.LinuxProcessSem.MemImageType. Import LinuxProcessSemantics.LinuxProcessSem.State. Import LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude. Import LinuxProcessSemantics.Riscv.Instr. Import LinuxProcessSemantics.Riscv.Decode. Import LinuxProcessSemantics.Riscv.DecodeC. Import LinuxProcessSemantics.Riscv.Sem. Import LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Arr. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.InitMem.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanCtrl.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AImg. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ABase. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AQConst. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ABytes.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.StepF.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AKit. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AKit2. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AKitQ. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_adrain. Import F_afreeC_iface.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Local Ltac band_lin :=
  repeat match goal with H : iclr ?a ?n |- _ => unfold iclr, AIMG_LO, AIMG_HI in H end.

Local Ltac drain_tail MX FR ST sp :=
  step; step; zstep; step; step;
  step;
  apply (rw_C4_to_C1x4 _ _ 1 0 ltac:(lia) ltac:(lia)) in MX;
  step;
  let K3 := fresh "K3" in
  step; step; step; if_cases K3; zify_cond K3; [exfalso; unfold Q_MAX in *; lia|];
  zstep; step; step; zstep; zstep; zstep; zstep; zstep;
  apply (rw_C1x4_to_C4 _ _ 0 0 ltac:(lia) ltac:(lia)) in MX; change (0 + 256 * 0) with 0 in MX;
  amo_step; lits;
  do 4 zstep;
  amo_step;
  step; if_lit;
  zstep; zstep; step; if_lit;
  apply (rw_C4_to_C1x4 _ _ 0 1 ltac:(lia) ltac:(lia)) in MX;
  step;
  do 6 step;
  step;
  release_frame FR ST (bv_unsigned sp);
  unfold drain_torec_post; finish.

Section CANSEC1. Context {rc : runConstT}.
Theorem drain_torec : drain_torec_stmt.
Proof.
  unfold drain_torec_stmt.
  intros until lo. intros ST CEIL LO MI -> -> QC NB QB FST LST MX GC GNB GQB GQ GQ63 GFST GLST QM GFULL T0 T1 RIMG RSTK RT RGL. band_lin.
  unfold AIMG_HI, Q_BATCH_BYTES, Q_MAX, Q_MIN, Q_CACHE, AQUAR_Q, AQ_MUTEX, AQ_GCACHE, AQ_MAX, AINSTANCE in *.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (t + 80, t + 112); (0xd67c8, 0xd67c8 + 4);
                          (0xd67d0, 0xd67d0 + 32); (glst, glst + 8)]%Z m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  word_range sp SPR.
  carve_frame 48%nat ST.
  destruct gfull.
  - destruct GFULL as (GNB1 & GLB & GL0 & GL1 & DTG).
    do 6 step.
    zstep. step. zstep. step.
    apply (rw_C1x4_to_C4 _ _ 0 0 ltac:(lia) ltac:(lia)) in MX. change (0 + 256 * 0) with 0 in MX.
    amo_step. lits.
    do 4 zstep.
    amo_step.
    step. if_lit.
    zstep. step. if_lit.
    zstep. step. if_cases K0; zify_cond K0; [exfalso; lia|].
    step. step. if_cases K1; zify_cond K1; [exfalso; lia|].
    step. step. if_cases K2; zify_cond K2; [exfalso; lia|].
    step. step. step. zstep.
    step. step. step. step.
    step. step. step.
    drain_tail MX FR ST sp.
  - pose proof GFULL as GNB0. clear GFULL.
    do 6 step.
    zstep. step. zstep. step.
    apply (rw_C1x4_to_C4 _ _ 0 0 ltac:(lia) ltac:(lia)) in MX. change (0 + 256 * 0) with 0 in MX.
    amo_step. lits.
    do 4 zstep.
    amo_step.
    step. if_lit.
    zstep. step. if_lit.
    zstep. step. if_cases K0; zify_cond K0; [exfalso; lia|].
    step. step. if_cases K1; zify_cond K1; [exfalso; lia|].
    step. step. if_cases K2; zify_cond K2; [|exfalso; lia].
    step. step. step. step. step. step.
    step. step. step.
    drain_tail MX FR ST sp.
    subst gnb. exact GC.
Qed.
End CANSEC1.
End F_adrainC.

Module F_afree_tailC.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase. Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics. Import LinuxProcessSemantics.LinuxProcessSem.MemImageType. Import LinuxProcessSemantics.LinuxProcessSem.State. Import LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude. Import LinuxProcessSemantics.Riscv.Instr. Import LinuxProcessSemantics.Riscv.Decode. Import LinuxProcessSemantics.Riscv.DecodeC. Import LinuxProcessSemantics.Riscv.Sem. Import LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Arr. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.InitMem.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.StrFun.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanCtrl. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanEmbed.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AImg. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ABase. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AQConst. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ABytes.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.StepF.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AKit. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AKit2. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AKitQ.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_apoison.F_apoison.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aenqueue.F_aenqueue. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_adrain. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aput. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_afree_tail. Import F_afreeC_iface. Import F_adrainC.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Local Lemma outside_In8 : forall (W : list ivl) x lo hi, outside W x -> In (lo, hi) W -> ~ (lo <= x < hi)%Z.
Proof. induction W as [|[a b] W IH]; cbn; intros x lo hi H HI; [tauto|]. destruct HI as [E|HI]; [injection E; intros; subst; tauto| apply (IH x); tauto]. Qed.
Local Lemma sub_fp_cover8 : forall W W' : list ivl,
  Forall (fun iv : ivl => (snd iv <= fst iv)%Z \/ Exists (fun jv : ivl => (fst jv <= fst iv /\ snd iv <= snd jv)%Z) W') W -> sub_fp W W'.
Proof.
  intros W W' HF x HO. induction HF as [|[lo hi] W HP HF IH]; cbn; [exact I|]. split; [| exact IH].
  cbn in HP. destruct HP as [HE|HP]; [lia|]. apply Exists_exists in HP. destruct HP as ([lo' hi'] & HI & [H1 H2]). cbn in H1, H2.
  pose proof (outside_In8 _ _ _ _ HO HI). lia.
Qed.
Local Ltac fp_cheap8 := first [ match goal with Hs : bv_unsigned _ = (bv_unsigned _ + _)%Z |- _ => clear -Hs end | clear ]; Stdlib.micromega.Lia.lia.
Local Ltac fp_find8c := first [ apply Exists_cons_hd; cbn [fst snd]; split; fp_cheap8 | apply Exists_cons_tl; fp_find8c ].
Local Ltac fp_find8 := first [ apply Exists_cons_hd; cbn [fst snd]; split; lia | apply Exists_cons_tl; fp_find8 ].
Local Ltac fp_cover8 := apply sub_fp_cover8; repeat (apply Forall_cons; [ cbn [fst snd]; first [left; fp_cheap8 | right; fp_find8c | right; fp_find8] | ]); apply Forall_nil.

Local Ltac transport_after_call segs m m' MU WM ::=
  let W := lazymatch type of MU with munch ?W _ _ => W end in
  repeat match goal with
  | H : bytes_at segs m ?A2 ?bs2 |- _ =>
      first [ apply (bytes_at_transport segs W m m' A2 bs2) in H; [ | exact MU | cbn [disjoint_from]; simpl_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : wr_at segs m ?A2 ?n2 |- _ => apply (wr_at_transport segs m m' A2 n2) in H; [ | exact WM ]
  | H : rw_cells segs m ?A2 ?cs2 |- _ =>
      first [ apply (rw_cells_transport segs W m m' A2 cs2) in H; [ | exact MU | exact WM | cbn [disjoint_from]; simpl_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : ro_cells segs m ?A2 ?cs2 |- _ =>
      first [ apply (ro_cells_transport segs W m m' A2 cs2) in H; [ | exact MU | cbn [disjoint_from]; simpl_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : u8arr segs m ?A2 ?xs |- _ =>
      first [ apply (u8arr_transport segs W m m' A2 xs) in H; [ | exact MU | exact WM | cbn [disjoint_from]; simpl_sizes; simpl_arr_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : u32arr segs m ?A2 ?xs |- _ =>
      first [ apply (u32arr_transport segs W m m' A2 xs) in H; [ | exact MU | exact WM | cbn [disjoint_from]; simpl_sizes; simpl_arr_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : u64arr segs m ?A2 ?xs |- _ =>
      first [ apply (u64arr_transport segs W m m' A2 xs) in H; [ | exact MU | exact WM | cbn [disjoint_from]; simpl_sizes; simpl_arr_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : u8ro segs m ?A2 ?xs |- _ =>
      first [ apply (u8ro_transport segs W m m' A2 xs) in H; [ | exact MU | cbn [disjoint_from]; simpl_sizes; simpl_arr_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : stk segs m ?loq ?hiq |- _ =>
      first [ apply (stk_transport_disjoint segs W m m' loq hiq) in H; [ | exact MU | exact WM | cbn [disjoint_from]; slia ]
            | clear H ]
  | H : munch ?Wq ?mq m |- _ =>
      first [ apply (munch_trans Wq mq m m') in H; [ | eapply (munch_weaken W Wq m m'); [ first [ fp_cover8 | unfold sub_fp; cbn [outside]; first [ match goal with Hs : bv_unsigned _ = bv_unsigned _ + _ |- _ => clear -Hs; intros; lia end | clear; intros; lia | intros; slia ] ] | exact MU ] ]
            | fail 100 "callee footprint not inside caller footprint" ]
  | H : wmono segs ?mq m |- _ => apply (wmono_trans segs mq m m') in H; [ | exact WM ]
  end.

Ltac ub H := let X := fresh "Y" in pose proof H as X; unbox X.

Local Ltac band_lin :=
  repeat match goal with H : iclr ?a ?n |- _ => unfold iclr, AIMG_LO, AIMG_HI in H end.
Local Ltac with_band H tac :=
  let H' := fresh H in pose proof H as H'; unfold sclr, iclr, ablk, KLS, AIMG_LO, AIMG_HI in H'; tac; try clear H'.
Local Ltac with_sclr tac := idtac; match goal with H : sclr ?a ?n |- _ => with_band H tac | _ => tac end.
Local Ltac iclr_of H := clear -H; unfold iclr, AIMG_LO, AIMG_HI in *; lia.

Local Lemma sclr_int : forall a n, sclr a n -> 0 <= a -> a + n <= 18446744073709551616 ->
  exists k, 0 <= k <= 1 /\ a + n <= 2147446784 + k * 18446744073709551616 /\ 17594333495296 * k <= a.
Proof. intros a n H G1 G2. unfold sclr, KLS in H. destruct H; [exists 0 | exists 1]; lia. Qed.
Local Lemma iclr_int : forall a n, iclr a n -> a + n <= 18446744073709551616 ->
  exists k, 0 <= k <= 1 /\ 4096 <= a /\ a + n <= 65536 + k * 18446744073709551616 /\ 6483968 * k <= a.
Proof. intros a n H G2. unfold iclr, AIMG_LO, AIMG_HI in H. destruct H as [? [?|?]]; [exists 0 | exists 1]; lia. Qed.
Local Lemma ablk_int {rc : runConstT} : forall lo hi, ablk lo hi ->
  exists k, 0 <= k <= 1 /\ 6483968 <= lo /\ 17594333495296 * k <= lo /\ hi <= 2147446784 + k * 18446744073709551616 /\ hi <= ATOP.
Proof. intros lo hi H. unfold ablk, KLS, AIMG_HI in H. pose proof atop_range. destruct H as [[? ?]|[? ?]]; [exists 0 | exists 1]; lia. Qed.
Local Ltac band_int H :=
  let k := fresh "k" H in let A := fresh "KA" H in let B := fresh "KB" H in let C := fresh "KC" H in let D := fresh "KD" H in
  let G1 := fresh "G" in let G2 := fresh "G" in
  lazymatch type of H with
  | sclr ?a ?n =>
      assert (G1 : 0 <= a) by (atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia); assert (G2 : a + n <= 18446744073709551616) by (atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia);
      destruct (sclr_int a n H G1 G2) as (k & A & B & C); clear G1 G2
  | iclr ?a ?n =>
      assert (G2 : a + n <= 18446744073709551616) by (atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia);
      destruct (iclr_int a n H G2) as (k & A & B & C & D); clear G2
  | 4096 <= ?a /\ (?a + ?n <= _ \/ _ <= ?a) =>
      assert (G2 : a + n <= 18446744073709551616) by (atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia);
      destruct (iclr_int a n H G2) as (k & A & B & C & D); clear G2
  | ablk ?lo ?hi => let E := fresh "KE" H in destruct (ablk_int lo hi H) as (k & A & B & E & C & D)
  end.

Section CANSEC1. Context {rc : runConstT}.
Theorem put_torec : put_torec_stmt.
Proof.
  unfold put_torec_stmt.
  intros until sjunk. intros ST CEIL LO MI -> -> -> -> -> QK GF FLG PC HD N B1 AL HLO HHI HCE SH QC NB QB QBN FST LST T0 T1 TAL DHT EK DK RIMG RSTK RT RH RSH TI.
  band_int TI. pose proof (ablk_lin _ _ HLO) as (HL1 & HL2 & HL3 & HL4). unfold AIMG_HI in HL1. band_int HLO. band_lin. band_int T0.
  assert (SHB : 2148261376 <= shad (hm + 16) /\ shad (hm + 16) + shlen (rup n 8) <= 0x10007fff8000).
  { unfold shad, shlen, ASHOFF. rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8. unfold Q_MAX in N. Z.div_mod_to_equations. lia. }
  assert (RUP : n <= rup n 8 <= n + 7 /\ rup n 8 mod 8 = 0) by (unfold rup; Z.div_mod_to_equations; lia).
  assert (SHL : 0 < shlen (rup n 8) < 0x10000000) by (unfold shlen; rewrite Z.shiftr_div_pow2 by lia; unfold Q_MAX in N; Z.div_mod_to_equations; lia).
  word_range sp SPR.
  pose proof (munch_refl [(bv_unsigned sp - 144, bv_unsigned sp); (shad (hm + 16), shad (hm + 16) + shlen (rup n 8));
              (t + 80, t + 112); (t + 2128, t + 2132); (t + 2784, t + 2792);
              (lst, lst + qsz lst); (ek_b ek lst, ek_b ek lst + 8192);
              (0xd67c8, 0xd67c8 + 4); (0xd67d0, 0xd67d0 + 32); (dk_glst g lst, dk_glst g lst + 8)]%Z m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  destruct PC as (P1 & P2 & P3 & P4 & P5 & P6 & P7).
  box DHT.

  destruct ek as [nx bsz cnt hs cnt24' maxc' csz' stj' | full nx bsz cnt24 maxc csz stj idxw chunks spacebeg b hs0];
  [ destruct EK as (NB1 & LB & CNT & BSZ & BSZN & NX & LA & LEN & [junkt LJ] & L0 & L1 & DTL & DHL & CR' & STS' & RL); box DTL; box DHL
  | destruct EK as (FULL & SB & CR & CH & LCH & CNT & NTH & IXS & STS & HB & [junkb BJ] & SBP & B0 & BL1 & DTB & DTL & DBL & DHB & DHL & RB);
    box DTB; box DTL; box DBL; box DHB; box DHL;
    destruct full; [destruct FULL as (NB1 & LB & NX & BSZ & L0 & L1 & LA0 & LEN0 & RL) | destruct FULL as [NB0 LST0]] ];
  unfold dk_glst in *; cbn [ek_pre dk_preC ek_b ek_nb ek_fst ek_lst ek_delta] in *;
  destruct DK as (EGD & MX & GC & GNB & GQB & GFST & GLST & QB1 & GQ & GQ63 & GFULL);
  (destruct (g_full g) eqn:EGF;
     [destruct GFULL as (G1 & GLB & G3 & G4 & G5 & G6 & G7 & G8 & G9); box G5; box G6; box G7; box G8 | destruct GFULL as [GNB0 GLST0]]);
  rewrite ?EGD in *; cbn [ek_pre dk_preC ek_b ek_nb ek_fst ek_lst ek_delta dk_glst] in *; unfold AIMG_HI in *.
  all: first [assert (QZE : qsz lst = 8192) by (apply qsz_pos; generalize L0; clear; intros; lia) | assert (QZE : qsz lst = 8) by (apply qsz_eq0; exact LST0)]; rewrite QZE in *.
  -
    box ST.
    call (putA_spec t hm n); try unboxed ST; try eassumption; try reflexivity; try (unfold Q_MAX, AIMG_HI in *; lia).
    try clear ST.
    rename POST into FRP.
    match goal with H : stk asegs ?mm lo _ |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename H into ST end. try rename MI0 into MI.
    box SH.
    box ST.
    step. call_sp (poison_shadow_spec RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ (hm + 16) (rup n 8) 253 lo sjunk);
      [unboxed ST| exact CEIL| lia| exact MI| repeat (split; [assumption|]); assumption| reflexivity| reflexivity| reflexivity
      | Z.div_mod_to_equations; lia| lia| lia| first [assumption | (eapply ablk_sub; [exact HLO| clear; lia| clear; lia]) | unfold ablk; right; lia | unfold ablk; left; lia]| lia| lia| lia| unboxed SH|].
    try clear ST.
    clear SH.
    try rename MI0 into MI. clear P1 P2 P3 P4 P5 P6 P7.
    match goal with H : stk asegs ?mm lo _ |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename H into ST end.
    match goal with H : rw_cells asegs ?mm (shad (hm + 16)) _ |- _ => rename H into SH' end.
    do 5 step.
    step.
    box HD. box SH'. box GLB. box CR'. box STS'.
    snapshot [(bv_unsigned sp + -80 - 64, bv_unsigned sp + -80); (t + 80 + 24, t + 80 + 32); (lst + 8, lst + 24); (lst + 24 + 8 * cnt, lst + 24 + 8 * cnt + 8)]%Z MUe WMe.
    box LJ. box LB. box QC. box LA.
    box ST.
    call_sp (enqueue_append_spec (t + 80) lst cnt RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ nb fst0 qb hm n nx bsz lo hs);
      [unboxed ST| exact CEIL| lia| exact MI| reflexivity| reflexivity| reflexivity| unboxed QC| lia| lia| unfold Q_MAX in *; lia| lia| lia| lia
      | unboxed LB| exact CNT| lia| unfold Q_MAX in *; lia| lia| unboxed LA| exact LEN| exists junkt; unboxed LJ
      | iclr_of TI| atop_facts; lia| unfold AIMG_HI; lia| unfold Q_BATCH_BYTES; lia| ub DTL; unfold Q_BATCH_BYTES; lia|].
    try clear ST.
    clear LJ LB QC LA.
    try rename MI0 into MI.
    match goal with H : stk asegs ?mm lo _ |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename H into ST end.
    carry HD MUe WMe ltac:(ub DHT; ub DHL; lia). carry SH' MUe WMe ltac:(lia). carry GLB MUe WMe ltac:(ub G5; ub G7; lia). carry CR' MUe WMe ltac:(ub DTL; lia). carry STS' MUe WMe ltac:(ub DTL; lia). clear MUe WMe.
    rename POST into LJ'. rename PC1 into LB'. rename PC2 into LA'. rename PC0 into QC'. destruct LJ' as [junkt' LJ'].

    step.
    step. if_cases KD; zify_cond KD; [|exfalso; unfold Q_CACHE in *; lia].
    step. step. step. step.
    box HD.  box LB'. box LA'. box LJ'. box CR'. box STS'.
    snapshot [(bv_unsigned sp + -80 - 48, bv_unsigned sp + -80); (t + 80, t + 112); (0xd67c8, 0xd67c8 + 4); (0xd67d0, 0xd67d0 + 32); (g_lst g, g_lst g + 8)]%Z MUd WMd.
    box QC'. box GLB. box GC. box MX.
    box ST.
    step. call_sp (drain_torec true t (g_lst g) RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ nb fst0 lst (qb + n) (g_nb g) (g_fst g) (g_qb g) (g_nx g) lo);
      [unboxed ST| exact CEIL| lia| exact MI| reflexivity| reflexivity| unboxed QC'| lia| lia| lia| lia| unboxed MX| unboxed GC| lia| lia| unfold Q_MAX in *; lia| unfold Q_MAX in *; lia| lia| lia
      | exact QK| split; [lia|]; split; [unboxed GLB|]; unfold AIMG_HI, Q_BATCH_BYTES; repeat split; try lia; ub G5; lia| exact TI| atop_facts; lia|].
    try clear ST.
    clear QC' GLB GC MX.
    try rename MI0 into MI.
    match goal with H : stk asegs ?mm lo _ |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename H into ST end.
    carry HD MUd WMd ltac:(ub DHT; ub G6; lia). carry LB' MUd WMd ltac:(ub DTL; first [ub G7 | pose proof GLST0]; lia). carry LA' MUd WMd ltac:(rewrite length_app, LEN; cbn [length]; ub DTL; first [ub G7 | pose proof GLST0]; lia). carry LJ' MUd WMd ltac:(ub DTL; first [ub G7 | pose proof GLST0]; lia). carry CR' MUd WMd ltac:(first [ub G5 | pose proof GLST0]; lia). carry STS' MUd WMd ltac:(first [ub G5 | pose proof GLST0]; lia). clear MUd WMd.
    unfold put_torec_post. rewrite ?QZE. unfold put_frame, dk_postC, dk_glst. rewrite ?EGD. rewrite ?EGF. cbn [ek_post ek_nb ek_fst ek_lst ek_delta ek_b]. finish.
    all: try assumption. all: try exact I. all: try (lazymatch goal with |- exists _, rw_cells _ ?mq ?Aq _ => match goal with Hq : rw_cells _ mq Aq _ |- _ => eexists; exact Hq end end).      all: try (eexists; eassumption).
  -
    box ST.
    call (putA_spec t hm n); try unboxed ST; try eassumption; try reflexivity; try (unfold Q_MAX, AIMG_HI in *; lia).
    try clear ST.
    rename POST into FRP.
    match goal with H : stk asegs ?mm lo _ |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename H into ST end. try rename MI0 into MI.
    box SH.
    box ST.
    step. call_sp (poison_shadow_spec RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ (hm + 16) (rup n 8) 253 lo sjunk);
      [unboxed ST| exact CEIL| lia| exact MI| repeat (split; [assumption|]); assumption| reflexivity| reflexivity| reflexivity
      | Z.div_mod_to_equations; lia| lia| lia| first [assumption | (eapply ablk_sub; [exact HLO| clear; lia| clear; lia]) | unfold ablk; right; lia | unfold ablk; left; lia]| lia| lia| lia| unboxed SH|].
    try clear ST.
    clear SH.
    try rename MI0 into MI. clear P1 P2 P3 P4 P5 P6 P7.
    match goal with H : stk asegs ?mm lo _ |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename H into ST end.
    match goal with H : rw_cells asegs ?mm (shad (hm + 16)) _ |- _ => rename H into SH' end.
    do 5 step.
    step.
    box HD. box SH'. box CR'. box STS'.
    snapshot [(bv_unsigned sp + -80 - 64, bv_unsigned sp + -80); (t + 80 + 24, t + 80 + 32); (lst + 8, lst + 24); (lst + 24 + 8 * cnt, lst + 24 + 8 * cnt + 8)]%Z MUe WMe.
    box LJ. box LB. box QC. box LA.
    box ST.
    call_sp (enqueue_append_spec (t + 80) lst cnt RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ nb fst0 qb hm n nx bsz lo hs);
      [unboxed ST| exact CEIL| lia| exact MI| reflexivity| reflexivity| reflexivity| unboxed QC| lia| lia| unfold Q_MAX in *; lia| lia| lia| lia
      | unboxed LB| exact CNT| lia| unfold Q_MAX in *; lia| lia| unboxed LA| exact LEN| exists junkt; unboxed LJ
      | iclr_of TI| atop_facts; lia| unfold AIMG_HI; lia| unfold Q_BATCH_BYTES; lia| ub DTL; unfold Q_BATCH_BYTES; lia|].
    try clear ST.
    clear LJ LB QC LA.
    try rename MI0 into MI.
    match goal with H : stk asegs ?mm lo _ |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename H into ST end.
    carry HD MUe WMe ltac:(ub DHT; ub DHL; lia). carry SH' MUe WMe ltac:(lia). carry CR' MUe WMe ltac:(ub DTL; lia). carry STS' MUe WMe ltac:(ub DTL; lia). clear MUe WMe.
    rename POST into LJ'. rename PC1 into LB'. rename PC2 into LA'. rename PC0 into QC'. destruct LJ' as [junkt' LJ'].

    step.
    step. if_cases KD; zify_cond KD; [|exfalso; unfold Q_CACHE in *; lia].
    step. step. step. step.
    box HD.  box LB'. box LA'. box LJ'. box CR'. box STS'.
    snapshot [(bv_unsigned sp + -80 - 48, bv_unsigned sp + -80); (t + 80, t + 112); (0xd67c8, 0xd67c8 + 4); (0xd67d0, 0xd67d0 + 32); (g_lst g, g_lst g + 8)]%Z MUd WMd.
    box QC'. box GC. box MX.
    box ST.
    step. call_sp (drain_torec false t (g_lst g) RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ nb fst0 lst (qb + n) (g_nb g) (g_fst g) (g_qb g) (g_nx g) lo);
      [unboxed ST| exact CEIL| lia| exact MI| reflexivity| reflexivity| unboxed QC'| lia| lia| lia| lia| unboxed MX| unboxed GC| lia| lia| unfold Q_MAX in *; lia| unfold Q_MAX in *; lia| lia| lia
      | exact QK| exact GNB0| exact TI| atop_facts; lia| exact I|].
    try clear ST.
    clear QC' GC MX.
    try rename MI0 into MI.
    match goal with H : stk asegs ?mm lo _ |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename H into ST end.
    carry HD MUd WMd ltac:(ub DHT;  lia). carry LB' MUd WMd ltac:(ub DTL; first [ub G7 | pose proof GLST0]; lia). carry LA' MUd WMd ltac:(rewrite length_app, LEN; cbn [length]; ub DTL; first [ub G7 | pose proof GLST0]; lia). carry LJ' MUd WMd ltac:(ub DTL; first [ub G7 | pose proof GLST0]; lia). carry CR' MUd WMd ltac:(first [ub G5 | pose proof GLST0]; lia). carry STS' MUd WMd ltac:(first [ub G5 | pose proof GLST0]; lia). clear MUd WMd.
    unfold put_torec_post. rewrite ?QZE. unfold put_frame, dk_postC, dk_glst. rewrite ?EGD. rewrite ?EGF. cbn [ek_post ek_nb ek_fst ek_lst ek_delta ek_b]. finish.
    all: try assumption. all: try exact I. all: try (lazymatch goal with |- exists _, rw_cells _ ?mq ?Aq _ => match goal with Hq : rw_cells _ mq Aq _ |- _ => eexists; exact Hq end end).      all: try (eexists; eassumption).
  -
    box ST.
    call (putA_spec t hm n); try unboxed ST; try eassumption; try reflexivity; try (unfold Q_MAX, AIMG_HI in *; lia).
    try clear ST.
    rename POST into FRP.
    match goal with H : stk asegs ?mm lo _ |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename H into ST end. try rename MI0 into MI.
    box SH.
    box ST.
    step. call_sp (poison_shadow_spec RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ (hm + 16) (rup n 8) 253 lo sjunk);
      [unboxed ST| exact CEIL| lia| exact MI| repeat (split; [assumption|]); assumption| reflexivity| reflexivity| reflexivity
      | Z.div_mod_to_equations; lia| lia| lia| first [assumption | (eapply ablk_sub; [exact HLO| clear; lia| clear; lia]) | unfold ablk; right; lia | unfold ablk; left; lia]| lia| lia| lia| unboxed SH|].
    try clear ST.
    clear SH.
    try rename MI0 into MI. clear P1 P2 P3 P4 P5 P6 P7.
    match goal with H : stk asegs ?mm lo _ |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename H into ST end.
    match goal with H : rw_cells asegs ?mm (shad (hm + 16)) _ |- _ => rename H into SH' end.
    do 5 step.
    step.
    box HD. box CH. box SH'. box GLB. box LA0.
    snapshot [(bv_unsigned sp + -80 - 64, bv_unsigned sp + -80); (t + 80, t + 112); (t + 2128, t + 2128 + 4); (t + 2784, t + 2784 + 8); (lst, lst + 8); (b, b + 8192)]%Z MUe WMe.
    box BJ. box STS. box CR. box LB. box QC.
    box ST.
    call_sp (enqueue_new_spec true t lst b RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ nb fst0 qb hm n nx bsz cnt24 spacebeg lo maxc csz stj idxw chunks);
      [unboxed ST| exact CEIL| lia| exact MI| reflexivity| reflexivity| reflexivity| reflexivity| unboxed QC| lia| lia| unfold Q_BATCH_BYTES, Q_MAX in *; lia
      | lia| lia| lia| lia
      | split; [lia|]; split; [unboxed LB|]; unfold AIMG_HI, Q_BATCH_BYTES; repeat split; try assumption; lia
      | exact SB| unboxed CR| ub CH; exact Y| exact LCH| exact CNT| exact NTH| exact IXS| unboxed STS| unfold K_BATCH_CLASS; lia| exists junkb; unboxed BJ
      | exact TI| atop_facts; lia| exact TAL| lia| unfold AIMG_HI; lia| unfold Q_BATCH_BYTES; lia
      | ub DTB; unfold Q_BATCH_BYTES; lia| ub DTL; unfold Q_BATCH_BYTES; lia| ub DBL; unfold Q_BATCH_BYTES; lia|].
    try clear ST.
    clear BJ STS CR LB QC.
    try rename MI0 into MI.
    match goal with H : stk asegs ?mm lo _ |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename H into ST end.
    carry HD MUe WMe ltac:(ub DHT; ub DHL; ub DHB; lia). carry CH MUe WMe ltac:(rewrite LCH; ub DTL; ub DTB; lia). carry SH' MUe WMe ltac:(lia). carry LA0 MUe WMe ltac:(rewrite LEN0; ub DTL; ub DBL; lia). carry GLB MUe WMe ltac:(ub G5; ub G7; ub G8; lia). clear MUe WMe.
    rename PC0 into QC'. destruct PC2 as [stj' STS']. destruct PC5 as [junkb' PC5].

    step.
    step. if_cases KD; zify_cond KD; [|exfalso; unfold Q_CACHE in *; lia].
    step. step. step. step.
    box HD.  box PC3. box PC4. box PC5. box POST. box PC1. box STS'. box LA0.
    snapshot [(bv_unsigned sp + -80 - 48, bv_unsigned sp + -80); (t + 80, t + 112); (0xd67c8, 0xd67c8 + 4); (0xd67d0, 0xd67d0 + 32); (g_lst g, g_lst g + 8)]%Z MUd WMd.
    box QC'. box GLB. box GC. box MX. box CH.
    box ST.
    step. call_sp (drain_torec true t (g_lst g) RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ (nb + 1) fst0 b (qb + (n + 8192)) (g_nb g) (g_fst g) (g_qb g) (g_nx g) lo);
      [unboxed ST| exact CEIL| lia| exact MI| reflexivity| reflexivity| unboxed QC'| lia| lia| lia| lia| unboxed MX| unboxed GC| lia| lia| unfold Q_MAX in *; lia| unfold Q_MAX in *; lia| lia| lia
      | exact QK| split; [lia|]; split; [unboxed GLB|]; unfold AIMG_HI, Q_BATCH_BYTES; repeat split; try lia; ub G5; lia| exact TI| atop_facts; lia|].
    try clear ST.
    clear QC' GLB GC MX CH.
    try rename MI0 into MI.
    match goal with H : stk asegs ?mm lo _ |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename H into ST end.
    carry HD MUd WMd ltac:(ub DHT; ub G6; lia). carry PC3 MUd WMd ltac:(ub DTB; first [ub G8 | pose proof GLST0]; lia). carry PC4 MUd WMd ltac:(cbn [length]; ub DTB; first [ub G8 | pose proof GLST0]; lia). carry PC5 MUd WMd ltac:(ub DTB; first [ub G8 | pose proof GLST0]; lia). carry POST MUd WMd ltac:(ub DTL; first [ub G7 | pose proof GLST0]; lia). carry PC1 MUd WMd ltac:(first [ub G5 | pose proof GLST0]; lia). carry STS' MUd WMd ltac:(first [ub G5 | pose proof GLST0]; lia). carry LA0 MUd WMd ltac:(rewrite LEN0; ub DTL; first [ub G7 | pose proof GLST0]; lia). clear MUd WMd.
    unfold put_torec_post. rewrite ?QZE. unfold put_frame, dk_postC, dk_glst. rewrite ?EGD. rewrite ?EGF. cbn [ek_post ek_nb ek_fst ek_lst ek_delta ek_b]. finish.
    all: try assumption. all: try exact I. all: try (lazymatch goal with |- exists _, rw_cells _ ?mq ?Aq _ => match goal with Hq : rw_cells _ mq Aq _ |- _ => eexists; exact Hq end end).      all: try (eexists; eassumption).
  -
    box ST.
    call (putA_spec t hm n); try unboxed ST; try eassumption; try reflexivity; try (unfold Q_MAX, AIMG_HI in *; lia).
    try clear ST.
    rename POST into FRP.
    match goal with H : stk asegs ?mm lo _ |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename H into ST end. try rename MI0 into MI.
    box SH.
    box ST.
    step. call_sp (poison_shadow_spec RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ (hm + 16) (rup n 8) 253 lo sjunk);
      [unboxed ST| exact CEIL| lia| exact MI| repeat (split; [assumption|]); assumption| reflexivity| reflexivity| reflexivity
      | Z.div_mod_to_equations; lia| lia| lia| first [assumption | (eapply ablk_sub; [exact HLO| clear; lia| clear; lia]) | unfold ablk; right; lia | unfold ablk; left; lia]| lia| lia| lia| unboxed SH|].
    try clear ST.
    clear SH.
    try rename MI0 into MI. clear P1 P2 P3 P4 P5 P6 P7.
    match goal with H : stk asegs ?mm lo _ |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename H into ST end.
    match goal with H : rw_cells asegs ?mm (shad (hm + 16)) _ |- _ => rename H into SH' end.
    do 5 step.
    step.
    box HD. box CH. box SH'. box LA0.
    snapshot [(bv_unsigned sp + -80 - 64, bv_unsigned sp + -80); (t + 80, t + 112); (t + 2128, t + 2128 + 4); (t + 2784, t + 2784 + 8); (lst, lst + 8); (b, b + 8192)]%Z MUe WMe.
    box BJ. box STS. box CR. box LB. box QC.
    box ST.
    call_sp (enqueue_new_spec true t lst b RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ nb fst0 qb hm n nx bsz cnt24 spacebeg lo maxc csz stj idxw chunks);
      [unboxed ST| exact CEIL| lia| exact MI| reflexivity| reflexivity| reflexivity| reflexivity| unboxed QC| lia| lia| unfold Q_BATCH_BYTES, Q_MAX in *; lia
      | lia| lia| lia| lia
      | split; [lia|]; split; [unboxed LB|]; unfold AIMG_HI, Q_BATCH_BYTES; repeat split; try assumption; lia
      | exact SB| unboxed CR| ub CH; exact Y| exact LCH| exact CNT| exact NTH| exact IXS| unboxed STS| unfold K_BATCH_CLASS; lia| exists junkb; unboxed BJ
      | exact TI| atop_facts; lia| exact TAL| lia| unfold AIMG_HI; lia| unfold Q_BATCH_BYTES; lia
      | ub DTB; unfold Q_BATCH_BYTES; lia| ub DTL; unfold Q_BATCH_BYTES; lia| ub DBL; unfold Q_BATCH_BYTES; lia|].
    try clear ST.
    clear BJ STS CR LB QC.
    try rename MI0 into MI.
    match goal with H : stk asegs ?mm lo _ |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename H into ST end.
    carry HD MUe WMe ltac:(ub DHT; ub DHL; ub DHB; lia). carry CH MUe WMe ltac:(rewrite LCH; ub DTL; ub DTB; lia). carry SH' MUe WMe ltac:(lia). carry LA0 MUe WMe ltac:(rewrite LEN0; ub DTL; ub DBL; lia). clear MUe WMe.
    rename PC0 into QC'. destruct PC2 as [stj' STS']. destruct PC5 as [junkb' PC5].

    step.
    step. if_cases KD; zify_cond KD; [|exfalso; unfold Q_CACHE in *; lia].
    step. step. step. step.
    box HD.  box PC3. box PC4. box PC5. box POST. box PC1. box STS'. box LA0.
    snapshot [(bv_unsigned sp + -80 - 48, bv_unsigned sp + -80); (t + 80, t + 112); (0xd67c8, 0xd67c8 + 4); (0xd67d0, 0xd67d0 + 32); (g_lst g, g_lst g + 8)]%Z MUd WMd.
    box QC'. box GC. box MX.
    box ST.
    step. call_sp (drain_torec false t (g_lst g) RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ (nb + 1) fst0 b (qb + (n + 8192)) (g_nb g) (g_fst g) (g_qb g) (g_nx g) lo);
      [unboxed ST| exact CEIL| lia| exact MI| reflexivity| reflexivity| unboxed QC'| lia| lia| lia| lia| unboxed MX| unboxed GC| lia| lia| unfold Q_MAX in *; lia| unfold Q_MAX in *; lia| lia| lia
      | exact QK| exact GNB0| exact TI| atop_facts; lia| exact I|].
    try clear ST.
    clear QC' GC MX.
    try rename MI0 into MI.
    match goal with H : stk asegs ?mm lo _ |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename H into ST end.
    carry HD MUd WMd ltac:(ub DHT;  lia). carry PC3 MUd WMd ltac:(ub DTB; first [ub G8 | pose proof GLST0]; lia). carry PC4 MUd WMd ltac:(cbn [length]; ub DTB; first [ub G8 | pose proof GLST0]; lia). carry PC5 MUd WMd ltac:(ub DTB; first [ub G8 | pose proof GLST0]; lia). carry POST MUd WMd ltac:(ub DTL; first [ub G7 | pose proof GLST0]; lia). carry PC1 MUd WMd ltac:(first [ub G5 | pose proof GLST0]; lia). carry STS' MUd WMd ltac:(first [ub G5 | pose proof GLST0]; lia). carry LA0 MUd WMd ltac:(rewrite LEN0; ub DTL; first [ub G7 | pose proof GLST0]; lia). clear MUd WMd.
    unfold put_torec_post. rewrite ?QZE. unfold put_frame, dk_postC, dk_glst. rewrite ?EGD. rewrite ?EGF. cbn [ek_post ek_nb ek_fst ek_lst ek_delta ek_b]. finish.
    all: try assumption. all: try exact I. all: try (lazymatch goal with |- exists _, rw_cells _ ?mq ?Aq _ => match goal with Hq : rw_cells _ mq Aq _ |- _ => eexists; exact Hq end end).      all: try (eexists; eassumption).
  -
    box ST.
    call (putA_spec t hm n); try unboxed ST; try eassumption; try reflexivity; try (unfold Q_MAX, AIMG_HI in *; lia).
    try clear ST.
    rename POST into FRP.
    match goal with H : stk asegs ?mm lo _ |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename H into ST end. try rename MI0 into MI.
    box SH.
    box ST.
    step. call_sp (poison_shadow_spec RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ (hm + 16) (rup n 8) 253 lo sjunk);
      [unboxed ST| exact CEIL| lia| exact MI| repeat (split; [assumption|]); assumption| reflexivity| reflexivity| reflexivity
      | Z.div_mod_to_equations; lia| lia| lia| first [assumption | (eapply ablk_sub; [exact HLO| clear; lia| clear; lia]) | unfold ablk; right; lia | unfold ablk; left; lia]| lia| lia| lia| unboxed SH|].
    try clear ST.
    clear SH.
    try rename MI0 into MI. clear P1 P2 P3 P4 P5 P6 P7.
    match goal with H : stk asegs ?mm lo _ |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename H into ST end.
    match goal with H : rw_cells asegs ?mm (shad (hm + 16)) _ |- _ => rename H into SH' end.
    do 5 step.
    step.
    box HD. box CH. box SH'. box GLB.
    snapshot [(bv_unsigned sp + -80 - 64, bv_unsigned sp + -80); (t + 80, t + 112); (t + 2128, t + 2128 + 4); (t + 2784, t + 2784 + 8); (lst, lst + 8); (b, b + 8192)]%Z MUe WMe.
    box BJ. box STS. box CR. box QC.
    box ST.
    call_sp (enqueue_new_spec false t lst b RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ nb fst0 qb hm n nx bsz cnt24 spacebeg lo maxc csz stj idxw chunks);
      [unboxed ST| exact CEIL| lia| exact MI| reflexivity| reflexivity| reflexivity| reflexivity| unboxed QC| lia| lia| unfold Q_BATCH_BYTES, Q_MAX in *; lia
      | lia| lia| lia| lia
      | exact NB0
      | exact SB| unboxed CR| ub CH; exact Y| exact LCH| exact CNT| exact NTH| exact IXS| unboxed STS| unfold K_BATCH_CLASS; lia| exists junkb; unboxed BJ
      | exact TI| atop_facts; lia| exact TAL| lia| unfold AIMG_HI; lia| unfold Q_BATCH_BYTES; lia
      | ub DTB; unfold Q_BATCH_BYTES; lia| ub DTL; unfold Q_BATCH_BYTES; lia| ub DBL; unfold Q_BATCH_BYTES; lia| exact I|].
    try clear ST.
    clear BJ STS CR QC.
    try rename MI0 into MI.
    match goal with H : stk asegs ?mm lo _ |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename H into ST end.
    carry HD MUe WMe ltac:(ub DHT; ub DHL; ub DHB; lia). carry CH MUe WMe ltac:(rewrite LCH; ub DTL; ub DTB; lia). carry SH' MUe WMe ltac:(lia). carry GLB MUe WMe ltac:(ub G5; ub G7; ub G8; lia). clear MUe WMe.
    rename PC0 into QC'. destruct PC2 as [stj' STS']. destruct PC5 as [junkb' PC5].

    step.
    step. if_cases KD; zify_cond KD; [|exfalso; unfold Q_CACHE in *; lia].
    step. step. step. step.
    box HD.  box PC3. box PC4. box PC5. box PC1. box STS'.
    snapshot [(bv_unsigned sp + -80 - 48, bv_unsigned sp + -80); (t + 80, t + 112); (0xd67c8, 0xd67c8 + 4); (0xd67d0, 0xd67d0 + 32); (g_lst g, g_lst g + 8)]%Z MUd WMd.
    box QC'. box GLB. box GC. box MX. box CH.
    box ST.
    step. call_sp (drain_torec true t (g_lst g) RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ (nb + 1) b b (qb + (n + 8192)) (g_nb g) (g_fst g) (g_qb g) (g_nx g) lo);
      [unboxed ST| exact CEIL| lia| exact MI| reflexivity| reflexivity| unboxed QC'| lia| lia| lia| lia| unboxed MX| unboxed GC| lia| lia| unfold Q_MAX in *; lia| unfold Q_MAX in *; lia| lia| lia
      | exact QK| split; [lia|]; split; [unboxed GLB|]; unfold AIMG_HI, Q_BATCH_BYTES; repeat split; try lia; ub G5; lia| exact TI| atop_facts; lia|].
    try clear ST.
    clear QC' GLB GC MX CH.
    try rename MI0 into MI.
    match goal with H : stk asegs ?mm lo _ |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename H into ST end.
    carry HD MUd WMd ltac:(ub DHT; ub G6; lia). carry PC3 MUd WMd ltac:(ub DTB; first [ub G8 | pose proof GLST0]; lia). carry PC4 MUd WMd ltac:(cbn [length]; ub DTB; first [ub G8 | pose proof GLST0]; lia). carry PC5 MUd WMd ltac:(ub DTB; first [ub G8 | pose proof GLST0]; lia). carry PC1 MUd WMd ltac:(first [ub G5 | pose proof GLST0]; lia). carry STS' MUd WMd ltac:(first [ub G5 | pose proof GLST0]; lia). clear MUd WMd.
    unfold put_torec_post. rewrite ?QZE. unfold put_frame, dk_postC, dk_glst. rewrite ?EGD. rewrite ?EGF. cbn [ek_post ek_nb ek_fst ek_lst ek_delta ek_b]. finish.
    all: try assumption. all: try exact I. all: try (lazymatch goal with |- exists _, rw_cells _ ?mq ?Aq _ => match goal with Hq : rw_cells _ mq Aq _ |- _ => eexists; exact Hq end end).      all: try (eexists; eassumption).
  -
    box ST.
    call (putA_spec t hm n); try unboxed ST; try eassumption; try reflexivity; try (unfold Q_MAX, AIMG_HI in *; lia).
    try clear ST.
    rename POST into FRP.
    match goal with H : stk asegs ?mm lo _ |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename H into ST end. try rename MI0 into MI.
    box SH.
    box ST.
    step. call_sp (poison_shadow_spec RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ (hm + 16) (rup n 8) 253 lo sjunk);
      [unboxed ST| exact CEIL| lia| exact MI| repeat (split; [assumption|]); assumption| reflexivity| reflexivity| reflexivity
      | Z.div_mod_to_equations; lia| lia| lia| first [assumption | (eapply ablk_sub; [exact HLO| clear; lia| clear; lia]) | unfold ablk; right; lia | unfold ablk; left; lia]| lia| lia| lia| unboxed SH|].
    try clear ST.
    clear SH.
    try rename MI0 into MI. clear P1 P2 P3 P4 P5 P6 P7.
    match goal with H : stk asegs ?mm lo _ |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename H into ST end.
    match goal with H : rw_cells asegs ?mm (shad (hm + 16)) _ |- _ => rename H into SH' end.
    do 5 step.
    step.
    box HD. box CH. box SH'.
    snapshot [(bv_unsigned sp + -80 - 64, bv_unsigned sp + -80); (t + 80, t + 112); (t + 2128, t + 2128 + 4); (t + 2784, t + 2784 + 8); (lst, lst + 8); (b, b + 8192)]%Z MUe WMe.
    box BJ. box STS. box CR. box QC.
    box ST.
    call_sp (enqueue_new_spec false t lst b RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ nb fst0 qb hm n nx bsz cnt24 spacebeg lo maxc csz stj idxw chunks);
      [unboxed ST| exact CEIL| lia| exact MI| reflexivity| reflexivity| reflexivity| reflexivity| unboxed QC| lia| lia| unfold Q_BATCH_BYTES, Q_MAX in *; lia
      | lia| lia| lia| lia
      | exact NB0
      | exact SB| unboxed CR| ub CH; exact Y| exact LCH| exact CNT| exact NTH| exact IXS| unboxed STS| unfold K_BATCH_CLASS; lia| exists junkb; unboxed BJ
      | exact TI| atop_facts; lia| exact TAL| lia| unfold AIMG_HI; lia| unfold Q_BATCH_BYTES; lia
      | ub DTB; unfold Q_BATCH_BYTES; lia| ub DTL; unfold Q_BATCH_BYTES; lia| ub DBL; unfold Q_BATCH_BYTES; lia| exact I|].
    try clear ST.
    clear BJ STS CR QC.
    try rename MI0 into MI.
    match goal with H : stk asegs ?mm lo _ |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename H into ST end.
    carry HD MUe WMe ltac:(ub DHT; ub DHL; ub DHB; lia). carry CH MUe WMe ltac:(rewrite LCH; ub DTL; ub DTB; lia). carry SH' MUe WMe ltac:(lia). clear MUe WMe.
    rename PC0 into QC'. destruct PC2 as [stj' STS']. destruct PC5 as [junkb' PC5].

    step.
    step. if_cases KD; zify_cond KD; [|exfalso; unfold Q_CACHE in *; lia].
    step. step. step. step.
    box HD.  box PC3. box PC4. box PC5. box PC1. box STS'.
    snapshot [(bv_unsigned sp + -80 - 48, bv_unsigned sp + -80); (t + 80, t + 112); (0xd67c8, 0xd67c8 + 4); (0xd67d0, 0xd67d0 + 32); (g_lst g, g_lst g + 8)]%Z MUd WMd.
    box QC'. box GC. box MX.
    box ST.
    step. call_sp (drain_torec false t (g_lst g) RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ (nb + 1) b b (qb + (n + 8192)) (g_nb g) (g_fst g) (g_qb g) (g_nx g) lo);
      [unboxed ST| exact CEIL| lia| exact MI| reflexivity| reflexivity| unboxed QC'| lia| lia| lia| lia| unboxed MX| unboxed GC| lia| lia| unfold Q_MAX in *; lia| unfold Q_MAX in *; lia| lia| lia
      | exact QK| exact GNB0| exact TI| atop_facts; lia| exact I|].
    try clear ST.
    clear QC' GC MX.
    try rename MI0 into MI.
    match goal with H : stk asegs ?mm lo _ |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename H into ST end.
    carry HD MUd WMd ltac:(ub DHT;  lia). carry PC3 MUd WMd ltac:(ub DTB; first [ub G8 | pose proof GLST0]; lia). carry PC4 MUd WMd ltac:(cbn [length]; ub DTB; first [ub G8 | pose proof GLST0]; lia). carry PC5 MUd WMd ltac:(ub DTB; first [ub G8 | pose proof GLST0]; lia). carry PC1 MUd WMd ltac:(first [ub G5 | pose proof GLST0]; lia). carry STS' MUd WMd ltac:(first [ub G5 | pose proof GLST0]; lia). clear MUd WMd.
    unfold put_torec_post. rewrite ?QZE. unfold put_frame, dk_postC, dk_glst. rewrite ?EGD. rewrite ?EGF. cbn [ek_post ek_nb ek_fst ek_lst ek_delta ek_b]. finish.
    all: try assumption. all: try exact I. all: try (lazymatch goal with |- exists _, rw_cells _ ?mq ?Aq _ => match goal with Hq : rw_cells _ mq Aq _ |- _ => eexists; exact Hq end end).      all: try (eexists; eassumption).
Qed.
End CANSEC1.
End F_afree_tailC.

Module F_afree_tailRC.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase. Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics. Import LinuxProcessSemantics.LinuxProcessSem.MemImageType. Import LinuxProcessSemantics.LinuxProcessSem.State. Import LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude. Import LinuxProcessSemantics.Riscv.Instr. Import LinuxProcessSemantics.Riscv.Decode. Import LinuxProcessSemantics.Riscv.DecodeC. Import LinuxProcessSemantics.Riscv.Sem. Import LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Arr. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.InitMem.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.StrFun.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanCtrl. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanEmbed.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AImg. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ABase. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AQConst. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ABytes.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.StepF.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AKit. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AKit2. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AKitQ.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_apoison.F_apoison.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aenqueue.F_aenqueue.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aenqueue.F_aenqueueR. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_adrain. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aput. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_afree_tail. Import F_afree_tailR. Import F_afreeC_iface. Import F_adrainC.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Local Lemma outside_In8 : forall (W : list ivl) x lo hi, outside W x -> In (lo, hi) W -> ~ (lo <= x < hi)%Z.
Proof. induction W as [|[a b] W IH]; cbn; intros x lo hi H HI; [tauto|]. destruct HI as [E|HI]; [injection E; intros; subst; tauto| apply (IH x); tauto]. Qed.
Local Lemma sub_fp_cover8 : forall W W' : list ivl,
  Forall (fun iv : ivl => (snd iv <= fst iv)%Z \/ Exists (fun jv : ivl => (fst jv <= fst iv /\ snd iv <= snd jv)%Z) W') W -> sub_fp W W'.
Proof.
  intros W W' HF x HO. induction HF as [|[lo hi] W HP HF IH]; cbn; [exact I|]. split; [| exact IH].
  cbn in HP. destruct HP as [HE|HP]; [lia|]. apply Exists_exists in HP. destruct HP as ([lo' hi'] & HI & [H1 H2]). cbn in H1, H2.
  pose proof (outside_In8 _ _ _ _ HO HI). lia.
Qed.
Local Ltac fp_cheap8 := first [ match goal with Hs : bv_unsigned _ = (bv_unsigned _ + _)%Z |- _ => clear -Hs end | clear ]; Stdlib.micromega.Lia.lia.
Local Ltac fp_find8c := first [ apply Exists_cons_hd; cbn [fst snd]; split; fp_cheap8 | apply Exists_cons_tl; fp_find8c ].
Local Ltac fp_find8 := first [ apply Exists_cons_hd; cbn [fst snd]; split; lia | apply Exists_cons_tl; fp_find8 ].
Local Ltac fp_cover8 := apply sub_fp_cover8; repeat (apply Forall_cons; [ cbn [fst snd]; first [left; fp_cheap8 | right; fp_find8c | right; fp_find8] | ]); apply Forall_nil.

Local Ltac transport_after_call segs m m' MU WM ::=
  let W := lazymatch type of MU with munch ?W _ _ => W end in
  repeat match goal with
  | H : bytes_at segs m ?A2 ?bs2 |- _ =>
      first [ apply (bytes_at_transport segs W m m' A2 bs2) in H; [ | exact MU | cbn [disjoint_from]; simpl_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : wr_at segs m ?A2 ?n2 |- _ => apply (wr_at_transport segs m m' A2 n2) in H; [ | exact WM ]
  | H : rw_cells segs m ?A2 ?cs2 |- _ =>
      first [ apply (rw_cells_transport segs W m m' A2 cs2) in H; [ | exact MU | exact WM | cbn [disjoint_from]; simpl_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : ro_cells segs m ?A2 ?cs2 |- _ =>
      first [ apply (ro_cells_transport segs W m m' A2 cs2) in H; [ | exact MU | cbn [disjoint_from]; simpl_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : u8arr segs m ?A2 ?xs |- _ =>
      first [ apply (u8arr_transport segs W m m' A2 xs) in H; [ | exact MU | exact WM | cbn [disjoint_from]; simpl_sizes; simpl_arr_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : u32arr segs m ?A2 ?xs |- _ =>
      first [ apply (u32arr_transport segs W m m' A2 xs) in H; [ | exact MU | exact WM | cbn [disjoint_from]; simpl_sizes; simpl_arr_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : u64arr segs m ?A2 ?xs |- _ =>
      first [ apply (u64arr_transport segs W m m' A2 xs) in H; [ | exact MU | exact WM | cbn [disjoint_from]; simpl_sizes; simpl_arr_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : u8ro segs m ?A2 ?xs |- _ =>
      first [ apply (u8ro_transport segs W m m' A2 xs) in H; [ | exact MU | cbn [disjoint_from]; simpl_sizes; simpl_arr_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : stk segs m ?loq ?hiq |- _ =>
      first [ apply (stk_transport_disjoint segs W m m' loq hiq) in H; [ | exact MU | exact WM | cbn [disjoint_from]; slia ]
            | clear H ]
  | H : munch ?Wq ?mq m |- _ =>
      first [ apply (munch_trans Wq mq m m') in H; [ | eapply (munch_weaken W Wq m m'); [ first [ fp_cover8 | unfold sub_fp; cbn [outside]; first [ match goal with Hs : bv_unsigned _ = bv_unsigned _ + _ |- _ => clear -Hs; intros; lia end | clear; intros; lia | intros; slia ] ] | exact MU ] ]
            | fail 100 "callee footprint not inside caller footprint" ]
  | H : wmono segs ?mq m |- _ => apply (wmono_trans segs mq m m') in H; [ | exact WM ]
  end.

Ltac ub H := let X := fresh "Y" in pose proof H as X; unbox X.

Local Ltac band_lin :=
  repeat match goal with H : iclr ?a ?n |- _ => unfold iclr, AIMG_LO, AIMG_HI in H end.
Local Ltac with_band H tac :=
  let H' := fresh H in pose proof H as H'; unfold sclr, iclr, ablk, KLS, AIMG_LO, AIMG_HI in H'; tac; try clear H'.
Local Ltac with_sclr tac := idtac; match goal with H : sclr ?a ?n |- _ => with_band H tac | _ => tac end.

Local Lemma sclr_int : forall a n, sclr a n -> 0 <= a -> a + n <= 18446744073709551616 ->
  exists k, 0 <= k <= 1 /\ a + n <= 2147446784 + k * 18446744073709551616 /\ 17594333495296 * k <= a.
Proof. intros a n H G1 G2. unfold sclr, KLS in H. destruct H; [exists 0 | exists 1]; lia. Qed.
Local Lemma iclr_int : forall a n, iclr a n -> a + n <= 18446744073709551616 ->
  exists k, 0 <= k <= 1 /\ 4096 <= a /\ a + n <= 65536 + k * 18446744073709551616 /\ 6483968 * k <= a.
Proof. intros a n H G2. unfold iclr, AIMG_LO, AIMG_HI in H. destruct H as [? [?|?]]; [exists 0 | exists 1]; lia. Qed.
Local Lemma ablk_int {rc : runConstT} : forall lo hi, ablk lo hi ->
  exists k, 0 <= k <= 1 /\ 6483968 <= lo /\ 17594333495296 * k <= lo /\ hi <= 2147446784 + k * 18446744073709551616 /\ hi <= ATOP.
Proof. intros lo hi H. unfold ablk, KLS, AIMG_HI in H. pose proof atop_range. destruct H as [[? ?]|[? ?]]; [exists 0 | exists 1]; lia. Qed.
Local Ltac band_int H :=
  let k := fresh "k" H in let A := fresh "KA" H in let B := fresh "KB" H in let C := fresh "KC" H in let D := fresh "KD" H in
  let G1 := fresh "G" in let G2 := fresh "G" in
  lazymatch type of H with
  | sclr ?a ?n =>
      assert (G1 : 0 <= a) by (atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia); assert (G2 : a + n <= 18446744073709551616) by (atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia);
      destruct (sclr_int a n H G1 G2) as (k & A & B & C); clear G1 G2
  | iclr ?a ?n =>
      assert (G2 : a + n <= 18446744073709551616) by (atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia);
      destruct (iclr_int a n H G2) as (k & A & B & C & D); clear G2
  | 4096 <= ?a /\ (?a + ?n <= _ \/ _ <= ?a) =>
      assert (G2 : a + n <= 18446744073709551616) by (atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia);
      destruct (iclr_int a n H G2) as (k & A & B & C & D); clear G2
  | ablk ?lo ?hi => let E := fresh "KE" H in destruct (ablk_int lo hi H) as (k & A & B & E & C & D)
  end.

Section CANSEC1. Context {rc : runConstT}.
Theorem put_from_refill_torec : put_from_refill_torec_stmt.
Proof.
  unfold put_from_refill_torec_stmt.
  intros until j0. cbv zeta. intros ST CEIL LO MI -> FRP FRE QK HD N AL HLO HHI HCE SH' QC NB QB QBN FST LST T0 T1 TAL DHT
    FULL SB CR CH LCH CNT NTH IXS STS HB BJ SBP B0 BL1 DTB DTL DBL DHB DHL RB DK RIMG RSTK RT RH RSH TI.
  band_int TI. pose proof (ablk_lin _ _ HLO) as (HL1 & HL2 & HL3 & HL4). unfold AIMG_HI in HL1. band_int HLO. band_lin. band_int T0.
  assert (SHB : 2148261376 <= shad (hm + 16) /\ shad (hm + 16) + shlen (rup n 8) <= 0x10007fff8000).
  { unfold shad, shlen, ASHOFF. rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8. unfold Q_MAX in N. Z.div_mod_to_equations. lia. }
  assert (RUP : n <= rup n 8 <= n + 7 /\ rup n 8 mod 8 = 0) by (unfold rup; Z.div_mod_to_equations; lia).
  assert (SHL : 0 < shlen (rup n 8) < 0x10000000) by (unfold shlen; rewrite Z.shiftr_div_pow2 by lia; unfold Q_MAX in N; Z.div_mod_to_equations; lia).
  word_range sp SPR.
  pose proof (munch_refl [(bv_unsigned sp - 144, bv_unsigned sp); (shad (hm + 16), shad (hm + 16) + shlen (rup n 8));
              (t + 80, t + 112); (t + 2128, t + 2132); (t + 2784, t + 2792);
              (lst, lst + qsz lst); (b, b + 8192);
              (0xd67c8, 0xd67c8 + 4); (0xd67d0, 0xd67d0 + 32); (dk_glst g lst, dk_glst g lst + 8)]%Z m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  box DHT. box DTB. box DTL. box DBL. box DHB. box DHL.
  destruct BJ as [junkb BJ].
  destruct full; [destruct FULL as (NB1 & LB & NX & BSZ & L0 & L1 & LA0 & LEN0 & RL) | destruct FULL as [NB0 LST0]];
  unfold dk_glst in *; cbn [ek_pre dk_preC ek_b ek_nb ek_fst ek_lst ek_delta] in *;
  destruct DK as (EGD & MX & GC & GNB & GQB & GFST & GLST & QB1 & GQ & GQ63 & GFULL);
  (destruct (g_full g) eqn:EGF;
     [destruct GFULL as (G1 & GLB & G3 & G4 & G5 & G6 & G7 & G8 & G9); box G5; box G6; box G7; box G8 | destruct GFULL as [GNB0 GLST0]]);
  rewrite ?EGD in *; cbn [ek_pre dk_preC ek_b ek_nb ek_fst ek_lst ek_delta dk_glst] in *; unfold AIMG_HI in *.
  all: first [assert (QZE : qsz lst = 8192) by (apply qsz_pos; generalize L0; clear; intros; lia) | assert (QZE : qsz lst = 8) by (apply qsz_eq0; exact LST0)]; rewrite QZE in *.
  -
    box HD. box CH. box SH'. box GLB. box LA0. box FRP.
    snapshot [(t + 80, t + 112); (t + 2128, t + 2128 + 4); (t + 2784, t + 2784 + 8); (lst, lst + 8); (b, b + 8192)]%Z MUe WMe.
    box BJ. box STS. box CR. box LB. box QC.
    box ST.
    call_sp (enqueue_from_refill_spec true t lst b RNG _ _ _ _ _ _ _
               (Z_to_bv 64 0x41230) (Z_to_bv 64 0xd6730) (Z_to_bv 64 (t + 80)) (Z_to_bv 64 n) a3 (Z_to_bv 64 (t + 208)) (Z_to_bv 64 hm)
               _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ nb fst0 qb hm n nx bsz cnt spacebeg lo maxc csz stj idxw chunks j0);
      [unboxed ST| exact CEIL| lia| lia| exact MI| exact FRE| unboxed QC| lia| lia| unfold Q_BATCH_BYTES, Q_MAX in *; lia
      | lia| lia| lia| lia
      | split; [lia|]; split; [unboxed LB|]; unfold AIMG_HI, Q_BATCH_BYTES; repeat split; try assumption; lia
      | exact SB| unboxed CR| ub CH; exact Y| exact LCH| exact CNT| exact NTH| exact IXS| unboxed STS| unfold K_BATCH_CLASS; lia| exists junkb; unboxed BJ
      | exact TI| atop_facts; lia| exact TAL| lia| unfold AIMG_HI; lia| unfold Q_BATCH_BYTES; lia
      | ub DTB; unfold Q_BATCH_BYTES; lia| ub DTL; unfold Q_BATCH_BYTES; lia| ub DBL; unfold Q_BATCH_BYTES; lia|].
    clear BJ STS CR LB QC.
    try rename MI0 into MI.
    replace (bv_unsigned sp + -144 + 64) with (bv_unsigned sp + -80) in * by lia.
    clear ST. match goal with H : stk asegs ?mm lo (bv_unsigned sp + -80) |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename H into ST end.
    carry HD MUe WMe ltac:(ub DHT; ub DHL; ub DHB; lia). carry CH MUe WMe ltac:(rewrite LCH; ub DTL; ub DTB; lia). carry SH' MUe WMe ltac:(lia). carry LA0 MUe WMe ltac:(rewrite LEN0; ub DTL; ub DBL; lia). carry GLB MUe WMe ltac:(ub G5; ub G7; ub G8; lia). carry FRP MUe WMe ltac:(lia). clear MUe WMe.
    rename PC0 into QC'. destruct PC2 as [stj' STS']. destruct PC5 as [junkb' PC5].

    step.
    step. if_cases KD; zify_cond KD; [|exfalso; unfold Q_CACHE in *; lia].
    step. step. step. step.
    box HD.  box PC3. box PC4. box PC5. box POST. box PC1. box STS'. box LA0.
    snapshot [(bv_unsigned sp + -80 - 48, bv_unsigned sp + -80); (t + 80, t + 112); (0xd67c8, 0xd67c8 + 4); (0xd67d0, 0xd67d0 + 32); (g_lst g, g_lst g + 8)]%Z MUd WMd.
    box QC'. box GLB. box GC. box MX. box FRE. box CH.
    box ST.
    step. call_sp (drain_torec true t (g_lst g) RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ (nb + 1) fst0 b (qb + (n + 8192)) (g_nb g) (g_fst g) (g_qb g) (g_nx g) lo);
      [unboxed ST| exact CEIL| lia| exact MI| reflexivity| reflexivity| unboxed QC'| lia| lia| lia| lia| unboxed MX| unboxed GC| lia| lia| unfold Q_MAX in *; lia| unfold Q_MAX in *; lia| lia| lia
      | exact QK| split; [lia|]; split; [unboxed GLB|]; unfold AIMG_HI, Q_BATCH_BYTES; repeat split; try lia; ub G5; lia| exact TI| atop_facts; lia|].
    try clear ST.
    clear QC' GLB GC MX FRE CH.
    try rename MI0 into MI.
    match goal with H : stk asegs ?mm lo _ |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename H into ST end.
    carry HD MUd WMd ltac:(ub DHT; ub G6; lia). carry PC3 MUd WMd ltac:(ub DTB; first [ub G8 | pose proof GLST0]; lia). carry PC4 MUd WMd ltac:(cbn [length]; ub DTB; first [ub G8 | pose proof GLST0]; lia). carry PC5 MUd WMd ltac:(ub DTB; first [ub G8 | pose proof GLST0]; lia). carry POST MUd WMd ltac:(ub DTL; first [ub G7 | pose proof GLST0]; lia). carry PC1 MUd WMd ltac:(first [ub G5 | pose proof GLST0]; lia). carry STS' MUd WMd ltac:(first [ub G5 | pose proof GLST0]; lia). carry LA0 MUd WMd ltac:(rewrite LEN0; ub DTL; first [ub G7 | pose proof GLST0]; lia). clear MUd WMd.
    unfold put_torec_post. rewrite ?QZE. unfold put_frame, dk_postC, dk_glst. rewrite ?EGD. rewrite ?EGF. cbn [ek_post ek_nb ek_fst ek_lst ek_delta ek_b]. finish.
    all: try assumption. all: try exact I. all: try (lazymatch goal with |- exists _, rw_cells _ ?mq ?Aq _ => match goal with Hq : rw_cells _ mq Aq _ |- _ => eexists; exact Hq end end).      all: try (eexists; eassumption).
  -
    box HD. box CH. box SH'. box LA0. box FRP.
    snapshot [(t + 80, t + 112); (t + 2128, t + 2128 + 4); (t + 2784, t + 2784 + 8); (lst, lst + 8); (b, b + 8192)]%Z MUe WMe.
    box BJ. box STS. box CR. box LB. box QC.
    box ST.
    call_sp (enqueue_from_refill_spec true t lst b RNG _ _ _ _ _ _ _
               (Z_to_bv 64 0x41230) (Z_to_bv 64 0xd6730) (Z_to_bv 64 (t + 80)) (Z_to_bv 64 n) a3 (Z_to_bv 64 (t + 208)) (Z_to_bv 64 hm)
               _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ nb fst0 qb hm n nx bsz cnt spacebeg lo maxc csz stj idxw chunks j0);
      [unboxed ST| exact CEIL| lia| lia| exact MI| exact FRE| unboxed QC| lia| lia| unfold Q_BATCH_BYTES, Q_MAX in *; lia
      | lia| lia| lia| lia
      | split; [lia|]; split; [unboxed LB|]; unfold AIMG_HI, Q_BATCH_BYTES; repeat split; try assumption; lia
      | exact SB| unboxed CR| ub CH; exact Y| exact LCH| exact CNT| exact NTH| exact IXS| unboxed STS| unfold K_BATCH_CLASS; lia| exists junkb; unboxed BJ
      | exact TI| atop_facts; lia| exact TAL| lia| unfold AIMG_HI; lia| unfold Q_BATCH_BYTES; lia
      | ub DTB; unfold Q_BATCH_BYTES; lia| ub DTL; unfold Q_BATCH_BYTES; lia| ub DBL; unfold Q_BATCH_BYTES; lia|].
    clear BJ STS CR LB QC.
    try rename MI0 into MI.
    replace (bv_unsigned sp + -144 + 64) with (bv_unsigned sp + -80) in * by lia.
    clear ST. match goal with H : stk asegs ?mm lo (bv_unsigned sp + -80) |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename H into ST end.
    carry HD MUe WMe ltac:(ub DHT; ub DHL; ub DHB; lia). carry CH MUe WMe ltac:(rewrite LCH; ub DTL; ub DTB; lia). carry SH' MUe WMe ltac:(lia). carry LA0 MUe WMe ltac:(rewrite LEN0; ub DTL; ub DBL; lia). carry FRP MUe WMe ltac:(lia). clear MUe WMe.
    rename PC0 into QC'. destruct PC2 as [stj' STS']. destruct PC5 as [junkb' PC5].

    step.
    step. if_cases KD; zify_cond KD; [|exfalso; unfold Q_CACHE in *; lia].
    step. step. step. step.
    box HD.  box PC3. box PC4. box PC5. box POST. box PC1. box STS'. box LA0.
    snapshot [(bv_unsigned sp + -80 - 48, bv_unsigned sp + -80); (t + 80, t + 112); (0xd67c8, 0xd67c8 + 4); (0xd67d0, 0xd67d0 + 32); (g_lst g, g_lst g + 8)]%Z MUd WMd.
    box QC'. box GC. box MX. box FRE.
    box ST.
    step. call_sp (drain_torec false t (g_lst g) RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ (nb + 1) fst0 b (qb + (n + 8192)) (g_nb g) (g_fst g) (g_qb g) (g_nx g) lo);
      [unboxed ST| exact CEIL| lia| exact MI| reflexivity| reflexivity| unboxed QC'| lia| lia| lia| lia| unboxed MX| unboxed GC| lia| lia| unfold Q_MAX in *; lia| unfold Q_MAX in *; lia| lia| lia
      | exact QK| exact GNB0| exact TI| atop_facts; lia| exact I|].
    try clear ST.
    clear QC' GC MX FRE.
    try rename MI0 into MI.
    match goal with H : stk asegs ?mm lo _ |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename H into ST end.
    carry HD MUd WMd ltac:(ub DHT;  lia). carry PC3 MUd WMd ltac:(ub DTB; first [ub G8 | pose proof GLST0]; lia). carry PC4 MUd WMd ltac:(cbn [length]; ub DTB; first [ub G8 | pose proof GLST0]; lia). carry PC5 MUd WMd ltac:(ub DTB; first [ub G8 | pose proof GLST0]; lia). carry POST MUd WMd ltac:(ub DTL; first [ub G7 | pose proof GLST0]; lia). carry PC1 MUd WMd ltac:(first [ub G5 | pose proof GLST0]; lia). carry STS' MUd WMd ltac:(first [ub G5 | pose proof GLST0]; lia). carry LA0 MUd WMd ltac:(rewrite LEN0; ub DTL; first [ub G7 | pose proof GLST0]; lia). clear MUd WMd.
    unfold put_torec_post. rewrite ?QZE. unfold put_frame, dk_postC, dk_glst. rewrite ?EGD. rewrite ?EGF. cbn [ek_post ek_nb ek_fst ek_lst ek_delta ek_b]. finish.
    all: try assumption. all: try exact I. all: try (lazymatch goal with |- exists _, rw_cells _ ?mq ?Aq _ => match goal with Hq : rw_cells _ mq Aq _ |- _ => eexists; exact Hq end end).      all: try (eexists; eassumption).
  -
    box HD. box CH. box SH'. box GLB. box FRP.
    snapshot [(t + 80, t + 112); (t + 2128, t + 2128 + 4); (t + 2784, t + 2784 + 8); (lst, lst + 8); (b, b + 8192)]%Z MUe WMe.
    box BJ. box STS. box CR. box QC.
    box ST.
    call_sp (enqueue_from_refill_spec false t lst b RNG _ _ _ _ _ _ _
               (Z_to_bv 64 0x41230) (Z_to_bv 64 0xd6730) (Z_to_bv 64 (t + 80)) (Z_to_bv 64 n) a3 (Z_to_bv 64 (t + 208)) (Z_to_bv 64 hm)
               _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ nb fst0 qb hm n nx bsz cnt spacebeg lo maxc csz stj idxw chunks j0);
      [unboxed ST| exact CEIL| lia| lia| exact MI| exact FRE| unboxed QC| lia| lia| unfold Q_BATCH_BYTES, Q_MAX in *; lia
      | lia| lia| lia| lia
      | exact NB0
      | exact SB| unboxed CR| ub CH; exact Y| exact LCH| exact CNT| exact NTH| exact IXS| unboxed STS| unfold K_BATCH_CLASS; lia| exists junkb; unboxed BJ
      | exact TI| atop_facts; lia| exact TAL| lia| unfold AIMG_HI; lia| unfold Q_BATCH_BYTES; lia
      | ub DTB; unfold Q_BATCH_BYTES; lia| ub DTL; unfold Q_BATCH_BYTES; lia| ub DBL; unfold Q_BATCH_BYTES; lia| exact I|].
    clear BJ STS CR QC.
    try rename MI0 into MI.
    replace (bv_unsigned sp + -144 + 64) with (bv_unsigned sp + -80) in * by lia.
    clear ST. match goal with H : stk asegs ?mm lo (bv_unsigned sp + -80) |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename H into ST end.
    carry HD MUe WMe ltac:(ub DHT; ub DHL; ub DHB; lia). carry CH MUe WMe ltac:(rewrite LCH; ub DTL; ub DTB; lia). carry SH' MUe WMe ltac:(lia). carry GLB MUe WMe ltac:(ub G5; ub G7; ub G8; lia). carry FRP MUe WMe ltac:(lia). clear MUe WMe.
    rename PC0 into QC'. destruct PC2 as [stj' STS']. destruct PC5 as [junkb' PC5].

    step.
    step. if_cases KD; zify_cond KD; [|exfalso; unfold Q_CACHE in *; lia].
    step. step. step. step.
    box HD.  box PC3. box PC4. box PC5. box PC1. box STS'.
    snapshot [(bv_unsigned sp + -80 - 48, bv_unsigned sp + -80); (t + 80, t + 112); (0xd67c8, 0xd67c8 + 4); (0xd67d0, 0xd67d0 + 32); (g_lst g, g_lst g + 8)]%Z MUd WMd.
    box QC'. box GLB. box GC. box MX. box FRE. box CH.
    box ST.
    step. call_sp (drain_torec true t (g_lst g) RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ (nb + 1) b b (qb + (n + 8192)) (g_nb g) (g_fst g) (g_qb g) (g_nx g) lo);
      [unboxed ST| exact CEIL| lia| exact MI| reflexivity| reflexivity| unboxed QC'| lia| lia| lia| lia| unboxed MX| unboxed GC| lia| lia| unfold Q_MAX in *; lia| unfold Q_MAX in *; lia| lia| lia
      | exact QK| split; [lia|]; split; [unboxed GLB|]; unfold AIMG_HI, Q_BATCH_BYTES; repeat split; try lia; ub G5; lia| exact TI| atop_facts; lia|].
    try clear ST.
    clear QC' GLB GC MX FRE CH.
    try rename MI0 into MI.
    match goal with H : stk asegs ?mm lo _ |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename H into ST end.
    carry HD MUd WMd ltac:(ub DHT; ub G6; lia). carry PC3 MUd WMd ltac:(ub DTB; first [ub G8 | pose proof GLST0]; lia). carry PC4 MUd WMd ltac:(cbn [length]; ub DTB; first [ub G8 | pose proof GLST0]; lia). carry PC5 MUd WMd ltac:(ub DTB; first [ub G8 | pose proof GLST0]; lia). carry PC1 MUd WMd ltac:(first [ub G5 | pose proof GLST0]; lia). carry STS' MUd WMd ltac:(first [ub G5 | pose proof GLST0]; lia). clear MUd WMd.
    unfold put_torec_post. rewrite ?QZE. unfold put_frame, dk_postC, dk_glst. rewrite ?EGD. rewrite ?EGF. cbn [ek_post ek_nb ek_fst ek_lst ek_delta ek_b]. finish.
    all: try assumption. all: try exact I. all: try (lazymatch goal with |- exists _, rw_cells _ ?mq ?Aq _ => match goal with Hq : rw_cells _ mq Aq _ |- _ => eexists; exact Hq end end).      all: try (eexists; eassumption).
  -
    box HD. box CH. box SH'. box FRP.
    snapshot [(t + 80, t + 112); (t + 2128, t + 2128 + 4); (t + 2784, t + 2784 + 8); (lst, lst + 8); (b, b + 8192)]%Z MUe WMe.
    box BJ. box STS. box CR. box QC.
    box ST.
    call_sp (enqueue_from_refill_spec false t lst b RNG _ _ _ _ _ _ _
               (Z_to_bv 64 0x41230) (Z_to_bv 64 0xd6730) (Z_to_bv 64 (t + 80)) (Z_to_bv 64 n) a3 (Z_to_bv 64 (t + 208)) (Z_to_bv 64 hm)
               _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ nb fst0 qb hm n nx bsz cnt spacebeg lo maxc csz stj idxw chunks j0);
      [unboxed ST| exact CEIL| lia| lia| exact MI| exact FRE| unboxed QC| lia| lia| unfold Q_BATCH_BYTES, Q_MAX in *; lia
      | lia| lia| lia| lia
      | exact NB0
      | exact SB| unboxed CR| ub CH; exact Y| exact LCH| exact CNT| exact NTH| exact IXS| unboxed STS| unfold K_BATCH_CLASS; lia| exists junkb; unboxed BJ
      | exact TI| atop_facts; lia| exact TAL| lia| unfold AIMG_HI; lia| unfold Q_BATCH_BYTES; lia
      | ub DTB; unfold Q_BATCH_BYTES; lia| ub DTL; unfold Q_BATCH_BYTES; lia| ub DBL; unfold Q_BATCH_BYTES; lia| exact I|].
    clear BJ STS CR QC.
    try rename MI0 into MI.
    replace (bv_unsigned sp + -144 + 64) with (bv_unsigned sp + -80) in * by lia.
    clear ST. match goal with H : stk asegs ?mm lo (bv_unsigned sp + -80) |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename H into ST end.
    carry HD MUe WMe ltac:(ub DHT; ub DHL; ub DHB; lia). carry CH MUe WMe ltac:(rewrite LCH; ub DTL; ub DTB; lia). carry SH' MUe WMe ltac:(lia). carry FRP MUe WMe ltac:(lia). clear MUe WMe.
    rename PC0 into QC'. destruct PC2 as [stj' STS']. destruct PC5 as [junkb' PC5].

    step.
    step. if_cases KD; zify_cond KD; [|exfalso; unfold Q_CACHE in *; lia].
    step. step. step. step.
    box HD.  box PC3. box PC4. box PC5. box PC1. box STS'.
    snapshot [(bv_unsigned sp + -80 - 48, bv_unsigned sp + -80); (t + 80, t + 112); (0xd67c8, 0xd67c8 + 4); (0xd67d0, 0xd67d0 + 32); (g_lst g, g_lst g + 8)]%Z MUd WMd.
    box QC'. box GC. box MX. box FRE.
    box ST.
    step. call_sp (drain_torec false t (g_lst g) RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ (nb + 1) b b (qb + (n + 8192)) (g_nb g) (g_fst g) (g_qb g) (g_nx g) lo);
      [unboxed ST| exact CEIL| lia| exact MI| reflexivity| reflexivity| unboxed QC'| lia| lia| lia| lia| unboxed MX| unboxed GC| lia| lia| unfold Q_MAX in *; lia| unfold Q_MAX in *; lia| lia| lia
      | exact QK| exact GNB0| exact TI| atop_facts; lia| exact I|].
    try clear ST.
    clear QC' GC MX FRE.
    try rename MI0 into MI.
    match goal with H : stk asegs ?mm lo _ |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename H into ST end.
    carry HD MUd WMd ltac:(ub DHT;  lia). carry PC3 MUd WMd ltac:(ub DTB; first [ub G8 | pose proof GLST0]; lia). carry PC4 MUd WMd ltac:(cbn [length]; ub DTB; first [ub G8 | pose proof GLST0]; lia). carry PC5 MUd WMd ltac:(ub DTB; first [ub G8 | pose proof GLST0]; lia). carry PC1 MUd WMd ltac:(first [ub G5 | pose proof GLST0]; lia). carry STS' MUd WMd ltac:(first [ub G5 | pose proof GLST0]; lia). clear MUd WMd.
    unfold put_torec_post. rewrite ?QZE. unfold put_frame, dk_postC, dk_glst. rewrite ?EGD. rewrite ?EGF. cbn [ek_post ek_nb ek_fst ek_lst ek_delta ek_b]. finish.
    all: try assumption. all: try exact I. all: try (lazymatch goal with |- exists _, rw_cells _ ?mq ?Aq _ => match goal with Hq : rw_cells _ mq Aq _ |- _ => eexists; exact Hq end end).      all: try (eexists; eassumption).
Qed.
End CANSEC1.
End F_afree_tailRC.

From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.BothW Require BImg.
Module TwinB.

Module F_afree_tailR.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase. Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics. Import LinuxProcessSemantics.LinuxProcessSem.MemImageType. Import LinuxProcessSemantics.LinuxProcessSem.State. Import LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude. Import LinuxProcessSemantics.Riscv.Instr. Import LinuxProcessSemantics.Riscv.Decode. Import LinuxProcessSemantics.Riscv.DecodeC. Import LinuxProcessSemantics.Riscv.Sem. Import LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Arr. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.InitMem.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.StrFun.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanCtrl. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanEmbed.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.BothW.BImg. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ABase.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AQConst.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ABytes.TwinB.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.StepF.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AKit.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AKit2.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AKitQ.TwinB.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_apoison.TwinB.F_apoison.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aenqueue.TwinB.F_aenqueue.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aenqueue.TwinB.F_aenqueueR. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_adrain.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aput.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_afree_tail.TwinB.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Local Lemma outside_In8 : forall (W : list ivl) x lo hi, outside W x -> In (lo, hi) W -> ~ (lo <= x < hi)%Z.
Proof. induction W as [|[a b] W IH]; cbn; intros x lo hi H HI; [tauto|]. destruct HI as [E|HI]; [injection E; intros; subst; tauto| apply (IH x); tauto]. Qed.
Local Lemma sub_fp_cover8 : forall W W' : list ivl,
  Forall (fun iv : ivl => (snd iv <= fst iv)%Z \/ Exists (fun jv : ivl => (fst jv <= fst iv /\ snd iv <= snd jv)%Z) W') W -> sub_fp W W'.
Proof.
  intros W W' HF x HO. induction HF as [|[lo hi] W HP HF IH]; cbn; [exact I|]. split; [| exact IH].
  cbn in HP. destruct HP as [HE|HP]; [lia|]. apply Exists_exists in HP. destruct HP as ([lo' hi'] & HI & [H1 H2]). cbn in H1, H2.
  pose proof (outside_In8 _ _ _ _ HO HI). lia.
Qed.
Local Ltac fp_cheap8 := first [ match goal with Hs : bv_unsigned _ = (bv_unsigned _ + _)%Z |- _ => clear -Hs end | clear ]; Stdlib.micromega.Lia.lia.
Local Ltac fp_find8c := first [ apply Exists_cons_hd; cbn [fst snd]; split; fp_cheap8 | apply Exists_cons_tl; fp_find8c ].
Local Ltac fp_find8 := first [ apply Exists_cons_hd; cbn [fst snd]; split; lia | apply Exists_cons_tl; fp_find8 ].
Local Ltac fp_cover8 := apply sub_fp_cover8; repeat (apply Forall_cons; [ cbn [fst snd]; first [left; fp_cheap8 | right; fp_find8c | right; fp_find8] | ]); apply Forall_nil.

Local Ltac transport_after_call segs m m' MU WM ::=
  let W := lazymatch type of MU with munch ?W _ _ => W end in
  repeat match goal with
  | H : bytes_at segs m ?A2 ?bs2 |- _ =>
      first [ apply (bytes_at_transport segs W m m' A2 bs2) in H; [ | exact MU | cbn [disjoint_from]; simpl_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : wr_at segs m ?A2 ?n2 |- _ => apply (wr_at_transport segs m m' A2 n2) in H; [ | exact WM ]
  | H : rw_cells segs m ?A2 ?cs2 |- _ =>
      first [ apply (rw_cells_transport segs W m m' A2 cs2) in H; [ | exact MU | exact WM | cbn [disjoint_from]; simpl_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : ro_cells segs m ?A2 ?cs2 |- _ =>
      first [ apply (ro_cells_transport segs W m m' A2 cs2) in H; [ | exact MU | cbn [disjoint_from]; simpl_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : u8arr segs m ?A2 ?xs |- _ =>
      first [ apply (u8arr_transport segs W m m' A2 xs) in H; [ | exact MU | exact WM | cbn [disjoint_from]; simpl_sizes; simpl_arr_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : u32arr segs m ?A2 ?xs |- _ =>
      first [ apply (u32arr_transport segs W m m' A2 xs) in H; [ | exact MU | exact WM | cbn [disjoint_from]; simpl_sizes; simpl_arr_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : u64arr segs m ?A2 ?xs |- _ =>
      first [ apply (u64arr_transport segs W m m' A2 xs) in H; [ | exact MU | exact WM | cbn [disjoint_from]; simpl_sizes; simpl_arr_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : u8ro segs m ?A2 ?xs |- _ =>
      first [ apply (u8ro_transport segs W m m' A2 xs) in H; [ | exact MU | cbn [disjoint_from]; simpl_sizes; simpl_arr_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : stk segs m ?loq ?hiq |- _ =>
      first [ apply (stk_transport_disjoint segs W m m' loq hiq) in H; [ | exact MU | exact WM | cbn [disjoint_from]; slia ]
            | clear H ]
  | H : munch ?Wq ?mq m |- _ =>
      first [ apply (munch_trans Wq mq m m') in H; [ | eapply (munch_weaken W Wq m m'); [ first [ fp_cover8 | unfold sub_fp; cbn [outside]; first [ match goal with Hs : bv_unsigned _ = (bv_unsigned _ + _)%Z |- _ => clear -Hs; intros; lia end | clear; intros; lia | intros; slia ] ] | exact MU ] ]
            | fail 100 "callee footprint not inside caller footprint" ]
  | H : wmono segs ?mq m |- _ => apply (wmono_trans segs mq m m') in H; [ | exact WM ]
  end.

Local Ltac band_lin :=
  repeat match goal with H : iclr ?a ?n |- _ => unfold iclr, AIMG_LO, AIMG_HI in H end.
Local Ltac with_band H tac :=
  let H' := fresh H in pose proof H as H'; unfold sclr, iclr, ablk, KLS, AIMG_LO, AIMG_HI in H'; tac; try clear H'.

Local Ltac with_sclr tac := idtac; match goal with H : sclr ?a ?n |- _ => with_band H tac | _ => tac end.

Local Lemma sclr_int : forall a n, sclr a n -> 0 <= a -> a + n <= 18446744073709551616 ->
  exists k, 0 <= k <= 1 /\ a + n <= 2147446784 + k * 18446744073709551616 /\ 17594333495296 * k <= a.
Proof. intros a n H G1 G2. unfold sclr, KLS in H. destruct H; [exists 0 | exists 1]; lia. Qed.
Local Lemma iclr_int : forall a n, iclr a n -> a + n <= 18446744073709551616 ->
  exists k, 0 <= k <= 1 /\ 4096 <= a /\ a + n <= 65536 + k * 18446744073709551616 /\ 6492160 * k <= a.
Proof. intros a n H G2. unfold iclr, AIMG_LO, AIMG_HI in H. destruct H as [? [?|?]]; [exists 0 | exists 1]; lia. Qed.
Local Lemma ablk_int {rc : runConstT} : forall lo hi, ablk lo hi ->
  exists k, 0 <= k <= 1 /\ 6492160 <= lo /\ 17594333495296 * k <= lo /\ hi <= 2147446784 + k * 18446744073709551616 /\ hi <= ATOP.
Proof. intros lo hi H. unfold ablk, KLS, AIMG_HI in H. pose proof atop_range. destruct H as [[? ?]|[? ?]]; [exists 0 | exists 1]; lia. Qed.
Local Ltac band_int H :=
  let k := fresh "k" H in let A := fresh "KA" H in let B := fresh "KB" H in let C := fresh "KC" H in let D := fresh "KD" H in
  let G1 := fresh "G" in let G2 := fresh "G" in
  lazymatch type of H with
  | sclr ?a ?n =>
      assert (G1 : 0 <= a) by (atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia); assert (G2 : a + n <= 18446744073709551616) by (atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia);
      destruct (sclr_int a n H G1 G2) as (k & A & B & C); clear G1 G2
  | iclr ?a ?n =>
      assert (G2 : a + n <= 18446744073709551616) by (atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia);
      destruct (iclr_int a n H G2) as (k & A & B & C & D); clear G2
  | 4096 <= ?a /\ (?a + ?n <= _ \/ _ <= ?a) =>
      assert (G2 : a + n <= 18446744073709551616) by (atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia);
      destruct (iclr_int a n H G2) as (k & A & B & C & D); clear G2
  | ablk ?lo ?hi => let E := fresh "KE" H in destruct (ablk_int lo hi H) as (k & A & B & E & C & D)
  end.

Ltac ub H := let X := fresh "Y" in pose proof H as X; unbox X.

Section CANSEC1. Context {rc : runConstT}.
Definition put_to_refill_post (full : bool) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a2 a3 : word) (F : bvmap 5 word) (fc : bv 32)
    (t hm n lo lst nx bsz : Z) (hs : list word) (m : amem) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 : word) m' (j0 : list byte),
    ms' = MS (mkR (Z_to_bv 64 0x41d20) (Z_to_bv 64 (bv_unsigned sp + -144)) gp tp t0 t1 t2
                  (Z_to_bv 64 (t + 2128)) (Z_to_bv 64 (t + 208))
                  (Z_to_bv 64 (t + 208)) (Z_to_bv 64 (t + 2128)) (Z_to_bv 64 0xd8618) (Z_to_bv 64 K_BATCH_CLASS) a4 a5 a6 a7
                  (Z_to_bv 64 hm) (Z_to_bv 64 (t + 80)) a3 (Z_to_bv 64 n) (Z_to_bv 64 Q_CACHE) s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x42500) fc None m' (seg_rom bsegs)
    /\ munch [(bv_unsigned sp - 144, bv_unsigned sp); (shad (hm + 16), shad (hm + 16) + shlen (rup n 8))]%Z m m'
    /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo (bv_unsigned sp + -144)
    /\ rw_cells bsegs m' (shad (hm + 16)) [CB (Z.to_nat (shlen (rup n 8))) (repeat (Z_to_bv 8 253) (Z.to_nat (shlen (rup n 8))))]
    /\ rw_cells bsegs m' (bv_unsigned sp + -80) [C8 a2; C8 a3; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
    /\ rw_cells bsegs m' (bv_unsigned sp + -144)
         [CB 8 j0; C8 (Z_to_bv 64 hm); C8 a2; C8 a3; C8 (Z_to_bv 64 n); C8 (Z_to_bv 64 (t + 80)); C8 (Z_to_bv 64 0xd88f0); C8 (Z_to_bv 64 0x41bc0)]
    /\ (if full then rw_cells bsegs m' lst [C8 (Z_to_bv 64 nx); C8 (Z_to_bv 64 bsz); C8 (Z_to_bv 64 1021)] /\ u64arr bsegs m' (lst + 24) hs else True).

Lemma put_to_refill_spec : forall (full : bool) (t hm lst : Z) RNG
    ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (n nb fst0 qb b1 actx lo nx bsz : Z) (maxc csz : word) (hs : list word) (sjunk : list byte),
  stk bsegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - 144 ->
  mem_inv bsegs m ->
  a0 = Z_to_bv 64 0xd88f0 -> a1 = Z_to_bv 64 (t + 80) -> a2 = Z_to_bv 64 (t + 208) -> a4 = Z_to_bv 64 hm -> a5 = Z_to_bv 64 n ->

  rw_cells bsegs m 0xd8930 [C8 (Z_to_bv 64 Q_MAX); C8 (Z_to_bv 64 Q_MIN); C8 (Z_to_bv 64 Q_CACHE)] ->
  rw_cells bsegs m 0xd3628 [C8 (Z_to_bv 64 AFLAGS)] ->
  rw_cells bsegs m 0xd94a4 [C4 (Z_to_bv 64 0x1000); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0xbe)] ->
  poison_cells m ->

  rw_cells bsegs m hm [C1 (Z_to_bv 8 3); C1 (Z_to_bv 8 b1); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 (Z_to_bv 64 actx)] ->
  1 <= n <= Q_MAX -> 0 <= b1 < 256 -> hm mod 16 = 0 -> ablk hm (hm + 16 + rup n 8) -> hm + 16 + rup n 8 <= ATOP -> hm + 16 <= ATOP ->
  rw_cells bsegs m (shad (hm + 16)) [CB (Z.to_nat (shlen (rup n 8))) sjunk] ->

  rw_cells bsegs m (t + 80) [C8 (Z_to_bv 64 nb); C8 (Z_to_bv 64 fst0); C8 (Z_to_bv 64 lst); C8 (Z_to_bv 64 qb)] ->
  0 <= nb < 2^62 -> 0 <= lst < 2^64 ->
  sclr t 4096 -> t + 4096 <= ATOP -> t mod 4096 = 0 -> (hm + 16 <= t \/ t + 4096 <= hm) ->

  (if full then 0 < nb /\ rw_cells bsegs m lst [C8 (Z_to_bv 64 nx); C8 (Z_to_bv 64 bsz); C8 (Z_to_bv 64 1021)]
             /\ 0x10007fff8000 <= lst /\ lst + 8192 <= ATOP
             /\ u64arr bsegs m (lst + 24) hs /\ length hs = 1021%nat /\ rng RNG lst 8192
   else nb = 0 /\ lst = 0) ->
  rw_cells bsegs m (t + 2128) [C4 (Z_to_bv 64 0); C4 maxc; C8 csz] ->
  (t + 4096 <= lst \/ lst + 8192 <= t \/ lst = 0) -> (hm + 16 <= lst \/ lst + 8192 <= hm) ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG t 4096 -> rng RNG hm 16 -> rng RNG (shad (hm + 16)) (shlen (rup n 8)) ->
  iclr t 4096 ->
  evtF bsegs RNG (put_to_refill_post full ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a2 a3 F fc t hm n lo lst nx bsz hs m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x41a1c) fc None m (seg_rom bsegs)).
Proof.
  intros until sjunk. intros ST CEIL LO MI -> -> -> -> -> QK GF FLG PC HD N B1 AL HLO HHI HCE SH QC NB LST T0 T1 TAL DHT FULL CR DTL DHL RIMG RSTK RT RH RSH TI.
  band_int TI. pose proof (ablk_lin _ _ HLO) as (HL1 & HL2 & HL3 & HL4). unfold AIMG_HI in HL1. band_int HLO. band_lin. band_int T0.
  assert (SHB : 2148262400 <= shad (hm + 16) /\ shad (hm + 16) + shlen (rup n 8) <= 0x10007fff8000).
  { unfold shad, shlen, ASHOFF. rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8. unfold Q_MAX in N. Z.div_mod_to_equations. lia. }
  assert (RUP : n <= rup n 8 <= n + 7 /\ rup n 8 mod 8 = 0) by (unfold rup; Z.div_mod_to_equations; lia).
  assert (SHL : 0 < shlen (rup n 8) < 0x10000000) by (unfold shlen; rewrite Z.shiftr_div_pow2 by lia; unfold Q_MAX in N; Z.div_mod_to_equations; lia).
  word_range sp SPR.
  pose proof (munch_refl [(bv_unsigned sp - 144, bv_unsigned sp); (shad (hm + 16), shad (hm + 16) + shlen (rup n 8))]%Z m) as MU.
  pose proof (wmono_refl bsegs m) as WM.
  destruct PC as (P1 & P2 & P3 & P4 & P5 & P6 & P7).
  box DHT. box DTL. box DHL.
  destruct full; [destruct FULL as (NB1 & LB & L0 & L1 & LA0 & LEN0 & RL) | destruct FULL as [NB0 LST0]];
  unfold AIMG_HI in *.
  -
    box ST.
    call (putA_spec t hm n); try unboxed ST; try eassumption; try reflexivity; try (unfold Q_MAX, AIMG_HI in *; lia).
    try clear ST.
    rename POST into FRP.
    match goal with H : stk bsegs ?mm lo _ |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename H into ST end. try rename MI0 into MI.
    box SH.
    box ST.
    step. call_sp (poison_shadow_spec RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ (hm + 16) (rup n 8) 253 lo sjunk);
      [unboxed ST| exact CEIL| lia| exact MI| repeat (split; [assumption|]); assumption| reflexivity| reflexivity| reflexivity
      | Z.div_mod_to_equations; lia| lia| lia| first [assumption | (eapply ablk_sub; [exact HLO| clear; lia| clear; lia]) | unfold ablk; right; lia | unfold ablk; left; lia]| lia| lia| lia| unboxed SH|].
    try clear ST.
    clear SH.
    try rename MI0 into MI. clear P1 P2 P3 P4 P5 P6 P7.
    match goal with H : stk bsegs ?mm lo _ |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename H into ST end.
    match goal with H : rw_cells bsegs ?mm (shad (hm + 16)) _ |- _ => rename H into SH' end.
    do 5 step.
    step.
    box HD. box SH'. box LA0. box LB. box FRP.
    snapshot [(bv_unsigned sp + -80 - 64, bv_unsigned sp + -80)]%Z MUe WMe.
    box ST.
    call_sp (enqueue_to_refill_spec true t lst RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ nb fst0 qb hm n nx bsz lo maxc csz);
      [unboxed ST| exact CEIL| lia| exact MI| reflexivity| reflexivity| reflexivity| reflexivity| exact QC| lia| lia
      | split; [lia|]; split; [ub LB; exact Y|]; split; [unfold AIMG_HI; lia|]; split; [unfold Q_BATCH_BYTES; lia| exact RL]
      | exact CR| exact TI| atop_facts; lia| exact TAL| ub DTL; unfold Q_BATCH_BYTES; lia|].
    try clear ST.
    try rename MI0 into MI.
    match goal with H : stk bsegs ?mm lo _ |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename H into ST end.
    carry HD MUe WMe ltac:(lia). carry SH' MUe WMe ltac:(lia). carry LA0 MUe WMe ltac:(rewrite LEN0; lia). carry LB MUe WMe ltac:(lia). carry FRP MUe WMe ltac:(lia). clear MUe WMe.
    replace (bv_unsigned sp + -80 + -64) with (bv_unsigned sp + -144) in * by lia.
    unfold put_to_refill_post. finish.
    all: try assumption. all: try eassumption. all: try exact I. all: try (split; assumption).
  -
    box ST.
    call (putA_spec t hm n); try unboxed ST; try eassumption; try reflexivity; try (unfold Q_MAX, AIMG_HI in *; lia).
    try clear ST.
    rename POST into FRP.
    match goal with H : stk bsegs ?mm lo _ |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename H into ST end. try rename MI0 into MI.
    box SH.
    box ST.
    step. call_sp (poison_shadow_spec RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ (hm + 16) (rup n 8) 253 lo sjunk);
      [unboxed ST| exact CEIL| lia| exact MI| repeat (split; [assumption|]); assumption| reflexivity| reflexivity| reflexivity
      | Z.div_mod_to_equations; lia| lia| lia| first [assumption | (eapply ablk_sub; [exact HLO| clear; lia| clear; lia]) | unfold ablk; right; lia | unfold ablk; left; lia]| lia| lia| lia| unboxed SH|].
    try clear ST.
    clear SH.
    try rename MI0 into MI. clear P1 P2 P3 P4 P5 P6 P7.
    match goal with H : stk bsegs ?mm lo _ |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename H into ST end.
    match goal with H : rw_cells bsegs ?mm (shad (hm + 16)) _ |- _ => rename H into SH' end.
    do 5 step.
    step.
    box HD. box SH'. box FRP.
    snapshot [(bv_unsigned sp + -80 - 64, bv_unsigned sp + -80)]%Z MUe WMe.
    box ST.
    call_sp (enqueue_to_refill_spec false t lst RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ nb fst0 qb hm n nx bsz lo maxc csz);
      [unboxed ST| exact CEIL| lia| exact MI| reflexivity| reflexivity| reflexivity| reflexivity| exact QC| lia| lia
      | exact NB0
      | exact CR| exact TI| atop_facts; lia| exact TAL| ub DTL; unfold Q_BATCH_BYTES; lia|].
    try clear ST.
    try rename MI0 into MI.
    match goal with H : stk bsegs ?mm lo _ |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename H into ST end.
    carry HD MUe WMe ltac:(lia). carry SH' MUe WMe ltac:(lia). carry FRP MUe WMe ltac:(lia). clear MUe WMe.
    replace (bv_unsigned sp + -80 + -64) with (bv_unsigned sp + -144) in * by lia.
    unfold put_to_refill_post. finish.
    all: try assumption. all: try eassumption. all: try exact I.
Qed.

Lemma put_from_refill_spec : forall (full : bool) (g : gqd) (t hm lst b : Z) RNG
    (ra sp gp tp s0 s1 a2 a3 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (ra0 t0 t1 t2 a1 a2' a3' a4 a5 a6 a7 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) fc (m : amem) (n nb fst0 qb b1 actx lo nx bsz cnt spacebeg : Z) (maxc csz stj idxw : word) (chunks hs : list word)
    (j0 : list byte),
  let ek := EkNew full nx bsz cnt maxc csz stj idxw chunks spacebeg b hs in
  stk bsegs m lo (bv_unsigned sp + -144) -> ATOP <= lo -> lo <= bv_unsigned sp - 144 ->
  mem_inv bsegs m ->
  a2 = Z_to_bv 64 (t + 208) ->

  rw_cells bsegs m (bv_unsigned sp + -80) [C8 a2; C8 a3; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  rw_cells bsegs m (bv_unsigned sp + -144)
     [CB 8 j0; C8 (Z_to_bv 64 hm); C8 a2; C8 a3; C8 (Z_to_bv 64 n); C8 (Z_to_bv 64 (t + 80)); C8 (Z_to_bv 64 0xd88f0); C8 (Z_to_bv 64 0x41bc0)] ->

  rw_cells bsegs m 0xd8930 [C8 (Z_to_bv 64 Q_MAX); C8 (Z_to_bv 64 Q_MIN); C8 (Z_to_bv 64 Q_CACHE)] ->

  rw_cells bsegs m hm [C1 (Z_to_bv 8 3); C1 (Z_to_bv 8 b1); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 (Z_to_bv 64 actx)] ->
  1 <= n <= Q_MAX -> hm mod 16 = 0 -> ablk hm (hm + 16 + rup n 8) -> hm + 16 + rup n 8 <= ATOP -> hm + 16 <= ATOP ->
  rw_cells bsegs m (shad (hm + 16)) [CB (Z.to_nat (shlen (rup n 8))) (repeat (Z_to_bv 8 253) (Z.to_nat (shlen (rup n 8))))] ->

  rw_cells bsegs m (t + 80) [C8 (Z_to_bv 64 nb); C8 (Z_to_bv 64 fst0); C8 (Z_to_bv 64 lst); C8 (Z_to_bv 64 qb)] ->
  0 <= nb < 2^62 -> 0 <= qb -> qb + n + 8192 < 2^62 -> 0 <= fst0 < 2^64 -> 0 <= lst < 2^64 ->
  sclr t 4096 -> t + 4096 <= ATOP -> t mod 4096 = 0 -> (hm + 16 <= t \/ t + 4096 <= hm) ->

  (if full then 0 < nb /\ rw_cells bsegs m lst [C8 (Z_to_bv 64 nx); C8 (Z_to_bv 64 bsz); C8 (Z_to_bv 64 1021)]
             /\ 0 <= nx < 2^64 /\ 0 <= bsz < 2^64 /\ 0x10007fff8000 <= lst /\ lst + 8192 <= ATOP
             /\ u64arr bsegs m (lst + 24) hs /\ length hs = 1021%nat
             /\ rng RNG lst 8192
   else nb = 0 /\ lst = 0) ->
  rw_cells bsegs m 0xd8638 [C8 (Z_to_bv 64 spacebeg)] ->
  rw_cells bsegs m (t + 2128) [C4 (Z_to_bv 64 cnt); C4 maxc; C8 csz] ->
  u32arr bsegs m (t + 2128 + 16) chunks -> length chunks = 16%nat ->
  0 < cnt <= 16 -> nth_error chunks (Z.to_nat (cnt - 1)) = Some idxw -> bv_unsigned idxw < 2^32 ->
  rw_cells bsegs m (t + 2784) [C8 stj] ->
  b = spacebeg + 24 * 2^32 + 16 * bv_unsigned idxw ->
  (exists bs, rw_cells bsegs m b [CB (Z.to_nat 8192) bs]) ->
  0 < spacebeg -> 0x10007fff8000 <= b -> b + 8192 <= ATOP ->
  (t + 4096 <= b \/ b + 8192 <= t) -> (t + 4096 <= lst \/ lst + 8192 <= t \/ lst = 0) -> (b + 8192 <= lst \/ lst + 8192 <= b) ->
  (hm + 16 <= b \/ b + 8192 <= hm) -> (hm + 16 <= lst \/ lst + 8192 <= hm) ->
  rng RNG b 8192 ->

  dk_pre ek g RNG t lst hm (qb + ek_delta ek n) m ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG t 4096 -> rng RNG hm 16 -> rng RNG (shad (hm + 16)) (shlen (rup n 8)) ->
  iclr t 4096 ->
  evtF bsegs RNG (put_tail_post ek g ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc t hm n nb fst0 lst qb b1 actx lo m)
    (MS (mkR ra0 (Z_to_bv 64 (bv_unsigned sp + -144)) gp tp t0 t1 t2 (Z_to_bv 64 (t + 2128)) (Z_to_bv 64 (t + 208))
             (Z_to_bv 64 1) a1 a2' a3' a4 a5 a6 a7
             (Z_to_bv 64 hm) (Z_to_bv 64 (t + 80)) a3 (Z_to_bv 64 n) (Z_to_bv 64 Q_CACHE) s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x41d20) fc None m (seg_rom bsegs)).
Proof.
  intros until j0. cbv zeta. intros ST CEIL LO MI -> FRP FRE QK HD N AL HLO HHI HCE SH' QC NB QB QBN FST LST T0 T1 TAL DHT
    FULL SB CR CH LCH CNT NTH IXS STS HB BJ SBP B0 BL1 DTB DTL DBL DHB DHL RB DK RIMG RSTK RT RH RSH TI.
  band_int TI. pose proof (ablk_lin _ _ HLO) as (HL1 & HL2 & HL3 & HL4). unfold AIMG_HI in HL1. band_int HLO. band_lin. band_int T0.
  assert (SHB : 2148262400 <= shad (hm + 16) /\ shad (hm + 16) + shlen (rup n 8) <= 0x10007fff8000).
  { unfold shad, shlen, ASHOFF. rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8. unfold Q_MAX in N. Z.div_mod_to_equations. lia. }
  assert (RUP : n <= rup n 8 <= n + 7 /\ rup n 8 mod 8 = 0) by (unfold rup; Z.div_mod_to_equations; lia).
  assert (SHL : 0 < shlen (rup n 8) < 0x10000000) by (unfold shlen; rewrite Z.shiftr_div_pow2 by lia; unfold Q_MAX in N; Z.div_mod_to_equations; lia).
  word_range sp SPR.
  pose proof (munch_refl [(bv_unsigned sp - 144, bv_unsigned sp); (shad (hm + 16), shad (hm + 16) + shlen (rup n 8));
              (t + 80, t + 112); (t + 2128, t + 2132); (t + 2784, t + 2792);
              (lst, lst + qsz lst); (b, b + 8192);
              (0xd8988, 0xd8988 + 4); (0xd8990, 0xd8990 + 32); (dk_glst g lst, dk_glst g lst + 8)]%Z m) as MU.
  pose proof (wmono_refl bsegs m) as WM.
  pose proof QK as QK0. rw_split QK0 1%nat QMX QK2. clear QK2.
  box DHT. box DTB. box DTL. box DBL. box DHB. box DHL.
  destruct BJ as [junkb BJ].
  destruct full; [destruct FULL as (NB1 & LB & NX & BSZ & L0 & L1 & LA0 & LEN0 & RL) | destruct FULL as [NB0 LST0]];
  unfold dk_glst in *; cbn [ek_pre dk_pre ek_b ek_nb ek_fst ek_lst ek_delta] in *;
  destruct DK as (MX & GC & GNB & GQB & GFST & GLST & DK');
  (destruct (g_drain g) eqn:EGD;
   [ destruct DK' as (QB1 & GQ & GFULL);
     destruct (g_full g) eqn:EGF;
     [destruct GFULL as (G1 & GLB & G3 & G4 & G5 & G6 & G7 & G8 & G9); box G5; box G6; box G7; box G8 | destruct GFULL as [GNB0 GLST0]]
   | rename DK' into QB1 ]);
  rewrite ?EGD in *; cbn [ek_pre dk_pre ek_b ek_nb ek_fst ek_lst ek_delta dk_glst] in *; unfold AIMG_HI in *.
  all: first [assert (QZE : qsz lst = 8192) by (apply qsz_pos; generalize L0; clear; intros; lia) | assert (QZE : qsz lst = 8) by (apply qsz_eq0; exact LST0)]; rewrite QZE in *.
  -
    box HD. box CH. box SH'. box GLB. box LA0. box FRP.
    snapshot [(t + 80, t + 112); (t + 2128, t + 2128 + 4); (t + 2784, t + 2784 + 8); (lst, lst + 8); (b, b + 8192)]%Z MUe WMe.
    box BJ. box STS. box CR. box LB. box QC.
    box ST.
    call_sp (enqueue_from_refill_spec true t lst b RNG _ _ _ _ _ _ _
               (Z_to_bv 64 0x41bc0) (Z_to_bv 64 0xd88f0) (Z_to_bv 64 (t + 80)) (Z_to_bv 64 n) a3 (Z_to_bv 64 (t + 208)) (Z_to_bv 64 hm)
               _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ nb fst0 qb hm n nx bsz cnt spacebeg lo maxc csz stj idxw chunks j0);
      [unboxed ST| exact CEIL| lia| lia| exact MI| exact FRE| unboxed QC| lia| lia| unfold Q_BATCH_BYTES, Q_MAX in *; lia
      | lia| lia| lia| lia
      | split; [lia|]; split; [unboxed LB|]; unfold AIMG_HI, Q_BATCH_BYTES; repeat split; try assumption; lia
      | exact SB| unboxed CR| ub CH; exact Y| exact LCH| exact CNT| exact NTH| exact IXS| unboxed STS| unfold K_BATCH_CLASS; lia| exists junkb; unboxed BJ
      | exact TI| atop_facts; lia| exact TAL| lia| unfold AIMG_HI; lia| unfold Q_BATCH_BYTES; lia
      | ub DTB; unfold Q_BATCH_BYTES; lia| ub DTL; unfold Q_BATCH_BYTES; lia| ub DBL; unfold Q_BATCH_BYTES; lia|].
    clear BJ STS CR LB QC.
    try rename MI0 into MI.
    replace (bv_unsigned sp + -144 + 64) with (bv_unsigned sp + -80) in * by lia.
    clear ST. match goal with H : stk bsegs ?mm lo (bv_unsigned sp + -80) |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename H into ST end.
    carry HD MUe WMe ltac:(ub DHT; ub DHL; ub DHB; lia). carry CH MUe WMe ltac:(rewrite LCH; ub DTL; ub DTB; lia). carry SH' MUe WMe ltac:(lia). carry LA0 MUe WMe ltac:(rewrite LEN0; ub DTL; ub DBL; lia). carry GLB MUe WMe ltac:(ub G5; ub G7; ub G8; lia). carry FRP MUe WMe ltac:(lia). clear MUe WMe.
    rename PC0 into QC'. destruct PC2 as [stj' STS']. destruct PC5 as [junkb' PC5].

    step.
    step. if_cases KD; zify_cond KD; [|exfalso; unfold Q_CACHE in *; lia].
    step. step. step. step.
    box HD.  box PC3. box PC4. box PC5. box POST. box PC1. box STS'. box LA0.
    snapshot [(bv_unsigned sp + -80 - 48, bv_unsigned sp + -80); (t + 80, t + 112); (0xd8988, 0xd8988 + 4); (0xd8990, 0xd8990 + 32); (g_lst g, g_lst g + 8)]%Z MUd WMd.
    box QC'. box GLB. box GC. box MX. box FRE. box CH.
    box ST.
    step. call_sp (drain_norecycle_spec true t (g_lst g) RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ (nb + 1) fst0 b (qb + (n + 8192)) (g_nb g) (g_fst g) (g_qb g) (g_nx g) lo);
      [unboxed ST| exact CEIL| lia| exact MI| reflexivity| reflexivity| unboxed QC'| lia| lia| lia| lia| unboxed MX| unboxed GC| lia| lia| unfold Q_MAX in *; lia| lia| lia
      | exact QMX| split; [lia|]; split; [unboxed GLB|]; unfold AIMG_HI, Q_BATCH_BYTES; repeat split; try lia; ub G5; lia| exact TI| atop_facts; lia|].
    try clear ST.
    clear QC' GLB GC MX FRE CH.
    try rename MI0 into MI.
    match goal with H : stk bsegs ?mm lo _ |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename H into ST end.
    carry HD MUd WMd ltac:(ub DHT; ub G6; lia). carry PC3 MUd WMd ltac:(ub DTB; first [ub G8 | pose proof GLST0]; lia). carry PC4 MUd WMd ltac:(cbn [length]; ub DTB; first [ub G8 | pose proof GLST0]; lia). carry PC5 MUd WMd ltac:(ub DTB; first [ub G8 | pose proof GLST0]; lia). carry POST MUd WMd ltac:(ub DTL; first [ub G7 | pose proof GLST0]; lia). carry PC1 MUd WMd ltac:(first [ub G5 | pose proof GLST0]; lia). carry STS' MUd WMd ltac:(first [ub G5 | pose proof GLST0]; lia). carry LA0 MUd WMd ltac:(rewrite LEN0; ub DTL; first [ub G7 | pose proof GLST0]; lia). clear MUd WMd.
    do 10 step.
    release_frame FRP ST (bv_unsigned sp).
    unfold put_tail_post. rewrite ?QZE. unfold tcache_post, dk_post, dk_glst. rewrite ?EGD. rewrite ?EGF. cbn [ek_post ek_nb ek_fst ek_lst ek_delta ek_b]. finish.
    all: try assumption. all: try exact I. all: try (lazymatch goal with |- exists _, rw_cells _ ?mq ?Aq _ => match goal with Hq : rw_cells _ mq Aq _ |- _ => eexists; exact Hq end end).      all: try (eexists; eassumption).
  -
    box HD. box CH. box SH'. box LA0. box FRP.
    snapshot [(t + 80, t + 112); (t + 2128, t + 2128 + 4); (t + 2784, t + 2784 + 8); (lst, lst + 8); (b, b + 8192)]%Z MUe WMe.
    box BJ. box STS. box CR. box LB. box QC.
    box ST.
    call_sp (enqueue_from_refill_spec true t lst b RNG _ _ _ _ _ _ _
               (Z_to_bv 64 0x41bc0) (Z_to_bv 64 0xd88f0) (Z_to_bv 64 (t + 80)) (Z_to_bv 64 n) a3 (Z_to_bv 64 (t + 208)) (Z_to_bv 64 hm)
               _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ nb fst0 qb hm n nx bsz cnt spacebeg lo maxc csz stj idxw chunks j0);
      [unboxed ST| exact CEIL| lia| lia| exact MI| exact FRE| unboxed QC| lia| lia| unfold Q_BATCH_BYTES, Q_MAX in *; lia
      | lia| lia| lia| lia
      | split; [lia|]; split; [unboxed LB|]; unfold AIMG_HI, Q_BATCH_BYTES; repeat split; try assumption; lia
      | exact SB| unboxed CR| ub CH; exact Y| exact LCH| exact CNT| exact NTH| exact IXS| unboxed STS| unfold K_BATCH_CLASS; lia| exists junkb; unboxed BJ
      | exact TI| atop_facts; lia| exact TAL| lia| unfold AIMG_HI; lia| unfold Q_BATCH_BYTES; lia
      | ub DTB; unfold Q_BATCH_BYTES; lia| ub DTL; unfold Q_BATCH_BYTES; lia| ub DBL; unfold Q_BATCH_BYTES; lia|].
    clear BJ STS CR LB QC.
    try rename MI0 into MI.
    replace (bv_unsigned sp + -144 + 64) with (bv_unsigned sp + -80) in * by lia.
    clear ST. match goal with H : stk bsegs ?mm lo (bv_unsigned sp + -80) |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename H into ST end.
    carry HD MUe WMe ltac:(ub DHT; ub DHL; ub DHB; lia). carry CH MUe WMe ltac:(rewrite LCH; ub DTL; ub DTB; lia). carry SH' MUe WMe ltac:(lia). carry LA0 MUe WMe ltac:(rewrite LEN0; ub DTL; ub DBL; lia). carry FRP MUe WMe ltac:(lia). clear MUe WMe.
    rename PC0 into QC'. destruct PC2 as [stj' STS']. destruct PC5 as [junkb' PC5].

    step.
    step. if_cases KD; zify_cond KD; [|exfalso; unfold Q_CACHE in *; lia].
    step. step. step. step.
    box HD.  box PC3. box PC4. box PC5. box POST. box PC1. box STS'. box LA0.
    snapshot [(bv_unsigned sp + -80 - 48, bv_unsigned sp + -80); (t + 80, t + 112); (0xd8988, 0xd8988 + 4); (0xd8990, 0xd8990 + 32); (g_lst g, g_lst g + 8)]%Z MUd WMd.
    box QC'. box GC. box MX. box FRE.
    box ST.
    step. call_sp (drain_norecycle_spec false t (g_lst g) RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ (nb + 1) fst0 b (qb + (n + 8192)) (g_nb g) (g_fst g) (g_qb g) (g_nx g) lo);
      [unboxed ST| exact CEIL| lia| exact MI| reflexivity| reflexivity| unboxed QC'| lia| lia| lia| lia| unboxed MX| unboxed GC| lia| lia| unfold Q_MAX in *; lia| lia| lia
      | exact QMX| exact GNB0| exact TI| atop_facts; lia| exact I|].
    try clear ST.
    clear QC' GC MX FRE.
    try rename MI0 into MI.
    match goal with H : stk bsegs ?mm lo _ |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename H into ST end.
    carry HD MUd WMd ltac:(ub DHT;  lia). carry PC3 MUd WMd ltac:(ub DTB; first [ub G8 | pose proof GLST0]; lia). carry PC4 MUd WMd ltac:(cbn [length]; ub DTB; first [ub G8 | pose proof GLST0]; lia). carry PC5 MUd WMd ltac:(ub DTB; first [ub G8 | pose proof GLST0]; lia). carry POST MUd WMd ltac:(ub DTL; first [ub G7 | pose proof GLST0]; lia). carry PC1 MUd WMd ltac:(first [ub G5 | pose proof GLST0]; lia). carry STS' MUd WMd ltac:(first [ub G5 | pose proof GLST0]; lia). carry LA0 MUd WMd ltac:(rewrite LEN0; ub DTL; first [ub G7 | pose proof GLST0]; lia). clear MUd WMd.
    do 10 step.
    release_frame FRP ST (bv_unsigned sp).
    unfold put_tail_post. rewrite ?QZE. unfold tcache_post, dk_post, dk_glst. rewrite ?EGD. rewrite ?EGF. cbn [ek_post ek_nb ek_fst ek_lst ek_delta ek_b]. finish.
    all: try assumption. all: try exact I. all: try (lazymatch goal with |- exists _, rw_cells _ ?mq ?Aq _ => match goal with Hq : rw_cells _ mq Aq _ |- _ => eexists; exact Hq end end).      all: try (eexists; eassumption).
  -
    box HD. box CH. box SH'. box LA0. box FRP.
    snapshot [(t + 80, t + 112); (t + 2128, t + 2128 + 4); (t + 2784, t + 2784 + 8); (lst, lst + 8); (b, b + 8192)]%Z MUe WMe.
    box BJ. box STS. box CR. box LB. box QC.
    box ST.
    call_sp (enqueue_from_refill_spec true t lst b RNG _ _ _ _ _ _ _
               (Z_to_bv 64 0x41bc0) (Z_to_bv 64 0xd88f0) (Z_to_bv 64 (t + 80)) (Z_to_bv 64 n) a3 (Z_to_bv 64 (t + 208)) (Z_to_bv 64 hm)
               _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ nb fst0 qb hm n nx bsz cnt spacebeg lo maxc csz stj idxw chunks j0);
      [unboxed ST| exact CEIL| lia| lia| exact MI| exact FRE| unboxed QC| lia| lia| unfold Q_BATCH_BYTES, Q_MAX in *; lia
      | lia| lia| lia| lia
      | split; [lia|]; split; [unboxed LB|]; unfold AIMG_HI, Q_BATCH_BYTES; repeat split; try assumption; lia
      | exact SB| unboxed CR| ub CH; exact Y| exact LCH| exact CNT| exact NTH| exact IXS| unboxed STS| unfold K_BATCH_CLASS; lia| exists junkb; unboxed BJ
      | exact TI| atop_facts; lia| exact TAL| lia| unfold AIMG_HI; lia| unfold Q_BATCH_BYTES; lia
      | ub DTB; unfold Q_BATCH_BYTES; lia| ub DTL; unfold Q_BATCH_BYTES; lia| ub DBL; unfold Q_BATCH_BYTES; lia|].
    clear BJ STS CR LB QC.
    try rename MI0 into MI.
    replace (bv_unsigned sp + -144 + 64) with (bv_unsigned sp + -80) in * by lia.
    clear ST. match goal with H : stk bsegs ?mm lo (bv_unsigned sp + -80) |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename H into ST end.
    carry HD MUe WMe ltac:(ub DHT; ub DHL; ub DHB; lia). carry CH MUe WMe ltac:(rewrite LCH; ub DTL; ub DTB; lia). carry SH' MUe WMe ltac:(lia). carry LA0 MUe WMe ltac:(rewrite LEN0; ub DTL; ub DBL; lia). carry FRP MUe WMe ltac:(lia). clear MUe WMe.
    rename PC0 into QC'. destruct PC2 as [stj' STS']. destruct PC5 as [junkb' PC5].

    step.
    step. if_cases KD; zify_cond KD; [exfalso; unfold Q_CACHE in *; lia|].
    step.
    do 10 step.
    release_frame FRP ST (bv_unsigned sp).
    unfold put_tail_post. rewrite ?QZE. unfold tcache_post, dk_post, dk_glst. rewrite ?EGD. rewrite ?EGF. cbn [ek_post ek_nb ek_fst ek_lst ek_delta ek_b]. finish.
    all: try assumption. all: try exact I. all: try (lazymatch goal with |- exists _, rw_cells _ ?mq ?Aq _ => match goal with Hq : rw_cells _ mq Aq _ |- _ => eexists; exact Hq end end).      all: try (eexists; eassumption).
  -
    box HD. box CH. box SH'. box GLB. box FRP.
    snapshot [(t + 80, t + 112); (t + 2128, t + 2128 + 4); (t + 2784, t + 2784 + 8); (lst, lst + 8); (b, b + 8192)]%Z MUe WMe.
    box BJ. box STS. box CR. box QC.
    box ST.
    call_sp (enqueue_from_refill_spec false t lst b RNG _ _ _ _ _ _ _
               (Z_to_bv 64 0x41bc0) (Z_to_bv 64 0xd88f0) (Z_to_bv 64 (t + 80)) (Z_to_bv 64 n) a3 (Z_to_bv 64 (t + 208)) (Z_to_bv 64 hm)
               _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ nb fst0 qb hm n nx bsz cnt spacebeg lo maxc csz stj idxw chunks j0);
      [unboxed ST| exact CEIL| lia| lia| exact MI| exact FRE| unboxed QC| lia| lia| unfold Q_BATCH_BYTES, Q_MAX in *; lia
      | lia| lia| lia| lia
      | exact NB0
      | exact SB| unboxed CR| ub CH; exact Y| exact LCH| exact CNT| exact NTH| exact IXS| unboxed STS| unfold K_BATCH_CLASS; lia| exists junkb; unboxed BJ
      | exact TI| atop_facts; lia| exact TAL| lia| unfold AIMG_HI; lia| unfold Q_BATCH_BYTES; lia
      | ub DTB; unfold Q_BATCH_BYTES; lia| ub DTL; unfold Q_BATCH_BYTES; lia| ub DBL; unfold Q_BATCH_BYTES; lia| exact I|].
    clear BJ STS CR QC.
    try rename MI0 into MI.
    replace (bv_unsigned sp + -144 + 64) with (bv_unsigned sp + -80) in * by lia.
    clear ST. match goal with H : stk bsegs ?mm lo (bv_unsigned sp + -80) |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename H into ST end.
    carry HD MUe WMe ltac:(ub DHT; ub DHL; ub DHB; lia). carry CH MUe WMe ltac:(rewrite LCH; ub DTL; ub DTB; lia). carry SH' MUe WMe ltac:(lia). carry GLB MUe WMe ltac:(ub G5; ub G7; ub G8; lia). carry FRP MUe WMe ltac:(lia). clear MUe WMe.
    rename PC0 into QC'. destruct PC2 as [stj' STS']. destruct PC5 as [junkb' PC5].

    step.
    step. if_cases KD; zify_cond KD; [|exfalso; unfold Q_CACHE in *; lia].
    step. step. step. step.
    box HD.  box PC3. box PC4. box PC5. box PC1. box STS'.
    snapshot [(bv_unsigned sp + -80 - 48, bv_unsigned sp + -80); (t + 80, t + 112); (0xd8988, 0xd8988 + 4); (0xd8990, 0xd8990 + 32); (g_lst g, g_lst g + 8)]%Z MUd WMd.
    box QC'. box GLB. box GC. box MX. box FRE. box CH.
    box ST.
    step. call_sp (drain_norecycle_spec true t (g_lst g) RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ (nb + 1) b b (qb + (n + 8192)) (g_nb g) (g_fst g) (g_qb g) (g_nx g) lo);
      [unboxed ST| exact CEIL| lia| exact MI| reflexivity| reflexivity| unboxed QC'| lia| lia| lia| lia| unboxed MX| unboxed GC| lia| lia| unfold Q_MAX in *; lia| lia| lia
      | exact QMX| split; [lia|]; split; [unboxed GLB|]; unfold AIMG_HI, Q_BATCH_BYTES; repeat split; try lia; ub G5; lia| exact TI| atop_facts; lia|].
    try clear ST.
    clear QC' GLB GC MX FRE CH.
    try rename MI0 into MI.
    match goal with H : stk bsegs ?mm lo _ |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename H into ST end.
    carry HD MUd WMd ltac:(ub DHT; ub G6; lia). carry PC3 MUd WMd ltac:(ub DTB; first [ub G8 | pose proof GLST0]; lia). carry PC4 MUd WMd ltac:(cbn [length]; ub DTB; first [ub G8 | pose proof GLST0]; lia). carry PC5 MUd WMd ltac:(ub DTB; first [ub G8 | pose proof GLST0]; lia). carry PC1 MUd WMd ltac:(first [ub G5 | pose proof GLST0]; lia). carry STS' MUd WMd ltac:(first [ub G5 | pose proof GLST0]; lia). clear MUd WMd.
    do 10 step.
    release_frame FRP ST (bv_unsigned sp).
    unfold put_tail_post. rewrite ?QZE. unfold tcache_post, dk_post, dk_glst. rewrite ?EGD. rewrite ?EGF. cbn [ek_post ek_nb ek_fst ek_lst ek_delta ek_b]. finish.
    all: try assumption. all: try exact I. all: try (lazymatch goal with |- exists _, rw_cells _ ?mq ?Aq _ => match goal with Hq : rw_cells _ mq Aq _ |- _ => eexists; exact Hq end end).      all: try (eexists; eassumption).
  -
    box HD. box CH. box SH'. box FRP.
    snapshot [(t + 80, t + 112); (t + 2128, t + 2128 + 4); (t + 2784, t + 2784 + 8); (lst, lst + 8); (b, b + 8192)]%Z MUe WMe.
    box BJ. box STS. box CR. box QC.
    box ST.
    call_sp (enqueue_from_refill_spec false t lst b RNG _ _ _ _ _ _ _
               (Z_to_bv 64 0x41bc0) (Z_to_bv 64 0xd88f0) (Z_to_bv 64 (t + 80)) (Z_to_bv 64 n) a3 (Z_to_bv 64 (t + 208)) (Z_to_bv 64 hm)
               _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ nb fst0 qb hm n nx bsz cnt spacebeg lo maxc csz stj idxw chunks j0);
      [unboxed ST| exact CEIL| lia| lia| exact MI| exact FRE| unboxed QC| lia| lia| unfold Q_BATCH_BYTES, Q_MAX in *; lia
      | lia| lia| lia| lia
      | exact NB0
      | exact SB| unboxed CR| ub CH; exact Y| exact LCH| exact CNT| exact NTH| exact IXS| unboxed STS| unfold K_BATCH_CLASS; lia| exists junkb; unboxed BJ
      | exact TI| atop_facts; lia| exact TAL| lia| unfold AIMG_HI; lia| unfold Q_BATCH_BYTES; lia
      | ub DTB; unfold Q_BATCH_BYTES; lia| ub DTL; unfold Q_BATCH_BYTES; lia| ub DBL; unfold Q_BATCH_BYTES; lia| exact I|].
    clear BJ STS CR QC.
    try rename MI0 into MI.
    replace (bv_unsigned sp + -144 + 64) with (bv_unsigned sp + -80) in * by lia.
    clear ST. match goal with H : stk bsegs ?mm lo (bv_unsigned sp + -80) |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename H into ST end.
    carry HD MUe WMe ltac:(ub DHT; ub DHL; ub DHB; lia). carry CH MUe WMe ltac:(rewrite LCH; ub DTL; ub DTB; lia). carry SH' MUe WMe ltac:(lia). carry FRP MUe WMe ltac:(lia). clear MUe WMe.
    rename PC0 into QC'. destruct PC2 as [stj' STS']. destruct PC5 as [junkb' PC5].

    step.
    step. if_cases KD; zify_cond KD; [|exfalso; unfold Q_CACHE in *; lia].
    step. step. step. step.
    box HD.  box PC3. box PC4. box PC5. box PC1. box STS'.
    snapshot [(bv_unsigned sp + -80 - 48, bv_unsigned sp + -80); (t + 80, t + 112); (0xd8988, 0xd8988 + 4); (0xd8990, 0xd8990 + 32); (g_lst g, g_lst g + 8)]%Z MUd WMd.
    box QC'. box GC. box MX. box FRE.
    box ST.
    step. call_sp (drain_norecycle_spec false t (g_lst g) RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ (nb + 1) b b (qb + (n + 8192)) (g_nb g) (g_fst g) (g_qb g) (g_nx g) lo);
      [unboxed ST| exact CEIL| lia| exact MI| reflexivity| reflexivity| unboxed QC'| lia| lia| lia| lia| unboxed MX| unboxed GC| lia| lia| unfold Q_MAX in *; lia| lia| lia
      | exact QMX| exact GNB0| exact TI| atop_facts; lia| exact I|].
    try clear ST.
    clear QC' GC MX FRE.
    try rename MI0 into MI.
    match goal with H : stk bsegs ?mm lo _ |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename H into ST end.
    carry HD MUd WMd ltac:(ub DHT;  lia). carry PC3 MUd WMd ltac:(ub DTB; first [ub G8 | pose proof GLST0]; lia). carry PC4 MUd WMd ltac:(cbn [length]; ub DTB; first [ub G8 | pose proof GLST0]; lia). carry PC5 MUd WMd ltac:(ub DTB; first [ub G8 | pose proof GLST0]; lia). carry PC1 MUd WMd ltac:(first [ub G5 | pose proof GLST0]; lia). carry STS' MUd WMd ltac:(first [ub G5 | pose proof GLST0]; lia). clear MUd WMd.
    do 10 step.
    release_frame FRP ST (bv_unsigned sp).
    unfold put_tail_post. rewrite ?QZE. unfold tcache_post, dk_post, dk_glst. rewrite ?EGD. rewrite ?EGF. cbn [ek_post ek_nb ek_fst ek_lst ek_delta ek_b]. finish.
    all: try assumption. all: try exact I. all: try (lazymatch goal with |- exists _, rw_cells _ ?mq ?Aq _ => match goal with Hq : rw_cells _ mq Aq _ |- _ => eexists; exact Hq end end).      all: try (eexists; eassumption).
  -
    box HD. box CH. box SH'. box FRP.
    snapshot [(t + 80, t + 112); (t + 2128, t + 2128 + 4); (t + 2784, t + 2784 + 8); (lst, lst + 8); (b, b + 8192)]%Z MUe WMe.
    box BJ. box STS. box CR. box QC.
    box ST.
    call_sp (enqueue_from_refill_spec false t lst b RNG _ _ _ _ _ _ _
               (Z_to_bv 64 0x41bc0) (Z_to_bv 64 0xd88f0) (Z_to_bv 64 (t + 80)) (Z_to_bv 64 n) a3 (Z_to_bv 64 (t + 208)) (Z_to_bv 64 hm)
               _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ nb fst0 qb hm n nx bsz cnt spacebeg lo maxc csz stj idxw chunks j0);
      [unboxed ST| exact CEIL| lia| lia| exact MI| exact FRE| unboxed QC| lia| lia| unfold Q_BATCH_BYTES, Q_MAX in *; lia
      | lia| lia| lia| lia
      | exact NB0
      | exact SB| unboxed CR| ub CH; exact Y| exact LCH| exact CNT| exact NTH| exact IXS| unboxed STS| unfold K_BATCH_CLASS; lia| exists junkb; unboxed BJ
      | exact TI| atop_facts; lia| exact TAL| lia| unfold AIMG_HI; lia| unfold Q_BATCH_BYTES; lia
      | ub DTB; unfold Q_BATCH_BYTES; lia| ub DTL; unfold Q_BATCH_BYTES; lia| ub DBL; unfold Q_BATCH_BYTES; lia| exact I|].
    clear BJ STS CR QC.
    try rename MI0 into MI.
    replace (bv_unsigned sp + -144 + 64) with (bv_unsigned sp + -80) in * by lia.
    clear ST. match goal with H : stk bsegs ?mm lo (bv_unsigned sp + -80) |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename H into ST end.
    carry HD MUe WMe ltac:(ub DHT; ub DHL; ub DHB; lia). carry CH MUe WMe ltac:(rewrite LCH; ub DTL; ub DTB; lia). carry SH' MUe WMe ltac:(lia). carry FRP MUe WMe ltac:(lia). clear MUe WMe.
    rename PC0 into QC'. destruct PC2 as [stj' STS']. destruct PC5 as [junkb' PC5].

    step.
    step. if_cases KD; zify_cond KD; [exfalso; unfold Q_CACHE in *; lia|].
    step.
    do 10 step.
    release_frame FRP ST (bv_unsigned sp).
    unfold put_tail_post. rewrite ?QZE. unfold tcache_post, dk_post, dk_glst. rewrite ?EGD. rewrite ?EGF. cbn [ek_post ek_nb ek_fst ek_lst ek_delta ek_b]. finish.
    all: try assumption. all: try exact I. all: try (lazymatch goal with |- exists _, rw_cells _ ?mq ?Aq _ => match goal with Hq : rw_cells _ mq Aq _ |- _ => eexists; exact Hq end end).      all: try (eexists; eassumption).
Qed.
End CANSEC1.
End F_afree_tailR.

Module F_afree_icptR.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase. Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics. Import LinuxProcessSemantics.LinuxProcessSem.MemImageType. Import LinuxProcessSemantics.LinuxProcessSem.State. Import LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude. Import LinuxProcessSemantics.Riscv.Instr. Import LinuxProcessSemantics.Riscv.Decode. Import LinuxProcessSemantics.Riscv.DecodeC. Import LinuxProcessSemantics.Riscv.Sem. Import LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.ITree. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Nodes. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Decode. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Arr. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.InitMem.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.STree. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanCtrl. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanEmbed.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.BothW.BImg. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AProto.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ABase.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ABytes.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AQConst.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ADepot_iface.TwinB.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.StepF.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AKit.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AKit2.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AKitQ.TwinB.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_apoison.TwinB.F_apoison. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aalloc_s.TwinB.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aalloc1.TwinB.F_aalloc1. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_afree_iseg.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_afree_front.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_afree_tail.TwinB.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aenqueue.TwinB.F_aenqueueR. Import F_afree_tailR. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_afree_icpt.TwinB.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Local Ltac band_lin :=
  repeat match goal with H : iclr ?a ?n |- _ => unfold iclr, AIMG_LO, AIMG_HI in H end.
Local Ltac with_band H tac :=
  let H' := fresh H in pose proof H as H'; unfold sclr, iclr, ablk, KLS, AIMG_LO, AIMG_HI in H'; tac; try clear H'.

Local Ltac qlia := first [ LiaTuning.zify_prune; LiaTuning.zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker
                         | LiaTuning.zify_prune; Zify.zify; xlia zchecker ].
Local Ltac leaf2 := first [ left; qlia | right; qlia | qlia ].
Local Ltac band_leaf :=
  first [ leaf2
        | match goal with B : sclr ?a _ |- context [?a] =>
            let B' := fresh "BB" in pose proof B as B'; unfold sclr, KLS in B'; destruct B' as [B'|B']; leaf2 end
        | match goal with B : iclr ?a _ |- context [?a] =>
            let B' := fresh "BB" in pose proof B as B'; unfold iclr, AIMG_LO, AIMG_HI in B'; destruct B' as [_ [B'|B']]; leaf2 end
        | match goal with B : ablk ?a _ |- context [?a] =>
            let B' := fresh "BB" in pose proof B as B'; unfold ablk, KLS, AIMG_HI in B'; destruct B' as [[? B']|[B' ?]]; leaf2 end
        | lia ].
Local Ltac band_disj := cbn [disjoint_from fst snd]; repeat match goal with |- _ /\ _ => split end; first [exact I | band_leaf].

Local Lemma sclr_int : forall a n, sclr a n -> 0 <= a -> a + n <= 18446744073709551616 ->
  exists k, 0 <= k <= 1 /\ a + n <= 2147446784 + k * 18446744073709551616 /\ 17594333495296 * k <= a.
Proof. intros a n H G1 G2. unfold sclr, KLS in H. destruct H; [exists 0 | exists 1]; lia. Qed.
Local Lemma iclr_int : forall a n, iclr a n -> a + n <= 18446744073709551616 ->
  exists k, 0 <= k <= 1 /\ 4096 <= a /\ a + n <= 65536 + k * 18446744073709551616 /\ 6492160 * k <= a.
Proof. intros a n H G2. unfold iclr, AIMG_LO, AIMG_HI in H. destruct H as [? [?|?]]; [exists 0 | exists 1]; lia. Qed.
Local Lemma ablk_int {rc : runConstT} : forall lo hi, ablk lo hi ->
  exists k, 0 <= k <= 1 /\ 6492160 <= lo /\ 17594333495296 * k <= lo /\ hi <= 2147446784 + k * 18446744073709551616 /\ hi <= ATOP.
Proof. intros lo hi H. unfold ablk, KLS, AIMG_HI in H. pose proof atop_range. destruct H as [[? ?]|[? ?]]; [exists 0 | exists 1]; lia. Qed.
Local Ltac band_int H :=
  let k := fresh "k" H in let A := fresh "KA" H in let B := fresh "KB" H in let C := fresh "KC" H in let D := fresh "KD" H in
  let G1 := fresh "G" in let G2 := fresh "G" in
  lazymatch type of H with
  | sclr ?a ?n =>
      assert (G1 : 0 <= a) by (atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia); assert (G2 : a + n <= 18446744073709551616) by (atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia);
      destruct (sclr_int a n H G1 G2) as (k & A & B & C); clear G1 G2
  | iclr ?a ?n =>
      assert (G2 : a + n <= 18446744073709551616) by (atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia);
      destruct (iclr_int a n H G2) as (k & A & B & C & D); clear G2
  | 4096 <= ?a /\ (?a + ?n <= _ \/ _ <= ?a) =>
      assert (G2 : a + n <= 18446744073709551616) by (atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia);
      destruct (iclr_int a n H G2) as (k & A & B & C & D); clear G2
  | ablk ?lo ?hi => let E := fresh "KE" H in destruct (ablk_int lo hi H) as (k & A & B & E & C & D)
  end.

Ltac ub H := let X := fresh "Y" in pose proof H as X; unbox X.

Section CANSEC1. Context {rc : runConstT}.
Section WithDepot.
Variable DI : ADepotIface.

Notation free_W L sp t hm n lst ek g :=
  ([(bv_unsigned sp - 4096, bv_unsigned sp); (0xdce80, 0xdce80 + 0x81030); (0x16b708, 0x16b708 + 4);
    (t + 3168, t + 3169); (hm, hm + 4); (hm + 16, hm + 24); (t + 2800, t + 2800 + 368);
    (ADEPOT_LO, ADEPOT_HI); (al_nodes L, al_nodes L + 1048576); (al_store L, al_store L + 8388608);
    (shad (hm + 16), shad (hm + 16) + shlen (rup n 8)); (t + 80, t + 112); (t + 2128, t + 2132); (t + 2784, t + 2792);
    (lst, lst + qsz lst); (ek_b ek lst, ek_b ek lst + 8192);
    (0xd8988, 0xd8988 + 4); (0xd8990, 0xd8990 + 32); (dk_glst g lst, dk_glst g lst + 8)]%Z) (only parsing).
Notation toref_W L sp t hm n :=
  ([(bv_unsigned sp - 4096, bv_unsigned sp); (0xdce80, 0xdce80 + 0x81030); (0x16b708, 0x16b708 + 4);
    (t + 3168, t + 3169); (hm, hm + 4); (hm + 16, hm + 24); (t + 2800, t + 2800 + 368);
    (ADEPOT_LO, ADEPOT_HI); (al_nodes L, al_nodes L + 1048576); (al_store L, al_store L + 8388608);
    (shad (hm + 16), shad (hm + 16) + shlen (rup n 8))]%Z) (only parsing).

Definition free_to_refill_post (L : alayout) (full : bool)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (t hm n b1 actx lo lst nx bsz : Z) (hs : list word) (trt : list Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists (id : Z) (t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 : word) m' (sj' tb' : list word) (junk2 j0 : list byte),
    ms' = MS (mkR (Z_to_bv 64 0x41d20) (Z_to_bv 64 (bv_unsigned sp + -2272)) gp tp t0 t1 t2
                  (Z_to_bv 64 (t + 2128)) (Z_to_bv 64 (t + 208))
                  (Z_to_bv 64 (t + 208)) (Z_to_bv 64 (t + 2128)) (Z_to_bv 64 0xd8618) (Z_to_bv 64 K_BATCH_CLASS) a4 a5 a6 a7
                  (Z_to_bv 64 hm) (Z_to_bv 64 (t + 80)) (Z_to_bv 64 (bv_unsigned sp + -2128)) (Z_to_bv 64 n) (Z_to_bv 64 Q_CACHE)
                  s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x42500) fc None m' (seg_rom bsegs)
    /\ munch (toref_W L sp t hm n) m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo (bv_unsigned sp + -2272)
    /\ 0 < id < 2^31
    /\ rw_cells bsegs m' hm [C1 (Z_to_bv 8 3); C1 (Z_to_bv 8 b1); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 (Z_to_bv 64 actx)]
    /\ rw_cells bsegs m' (hm + 16) [C8 (Z_to_bv 64 id)]
    /\ rw_cells bsegs m' (shad (hm + 16)) [CB (Z.to_nat (shlen (rup n 8))) (repeat (Z_to_bv 8 253) (Z.to_nat (shlen (rup n 8))))]
    /\ u64arr bsegs m' (t + 2800) sj' /\ length sj' = 46%nat
    /\ rw_cells bsegs m' (t + 3168) [C1 (Z_to_bv 8 0)]
    /\ rw_cells bsegs m' 0x16b708 [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]
    /\ stk bsegs m' 0xdce80 (0xdce80 + 0x81030)
    /\ (forall j, 0 <= j < 32768 -> bytes_at bsegs m' (0xdce88 + 8 * j) (le8 (Z_to_bv 64 0)))

    /\ rw_cells bsegs m' (bv_unsigned sp + -2128) [C8 (Z_to_bv 64 (bv_unsigned sp + -2128 + 16)); C4 (Z_to_bv 64 (1 + Z.of_nat (length trt))); C4 (Z_to_bv 64 0)]
    /\ u64arr bsegs m' (bv_unsigned sp + -2128 + 16) tb' /\ length tb' = 255%nat
    /\ rw_cells bsegs m' (bv_unsigned sp + -72) [C8 sp; CB 8 junk2; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
    /\ rw_cells bsegs m' (bv_unsigned sp + -2208)
         [C8 (Z_to_bv 64 (t + 208)); C8 (Z_to_bv 64 (bv_unsigned sp + -2128)); C8 s6; C8 (Z_to_bv 64 (bv_unsigned sp + -81));
          C8 (Z_to_bv 64 (bv_unsigned sp + -2128)); C8 (Z_to_bv 64 1); C8 (Z_to_bv 64 0x5eeec); C8 (Z_to_bv 64 (hm + 16)); C8 sp; C8 (Z_to_bv 64 0x5ef5c)]
    /\ rw_cells bsegs m' (bv_unsigned sp + -2272)
         [CB 8 j0; C8 (Z_to_bv 64 hm); C8 (Z_to_bv 64 (t + 208)); C8 (Z_to_bv 64 (bv_unsigned sp + -2128)); C8 (Z_to_bv 64 n);
          C8 (Z_to_bv 64 (t + 80)); C8 (Z_to_bv 64 0xd88f0); C8 (Z_to_bv 64 0x41bc0)]
    /\ (if full then rw_cells bsegs m' lst [C8 (Z_to_bv 64 nx); C8 (Z_to_bv 64 bsz); C8 (Z_to_bv 64 1021)] /\ u64arr bsegs m' (lst + 24) hs else True)
    /\ ADEPOT DI L m'.

Lemma free_to_refill_spec : forall (L : alayout) (ia full : bool) RNG
    ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem)
    (t ctx hm n b1 actx lo top bot nb fst0 lst qb nx bsz : Z) (uw maxc csz : word) (sj hs : list word) (sjunk : list byte) (trt : list Z),
  stk bsegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - 4096 ->
  mem_inv bsegs m ->
  tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 (hm + 16) ->
  bv_unsigned sp mod 16 = 0 ->

  allocA_cells m ctx t -> poison_cells m ->
  rw_cells bsegs m 0xdc97c [C4 (Z_to_bv 64 30)] ->
  rw_cells bsegs m 0x16d7ca [C1 (Z_to_bv 8 1)] ->
  rw_cells bsegs m 0xd3610 [C8 (Z_to_bv 64 0x16b720)] -> rw_cells bsegs m 0x16b720 [C8 (Z_to_bv 64 4096)] ->
  rw_cells bsegs m 0x16d748 [C8 (Z_to_bv 64 0)] ->
  rw_cells bsegs m 0xd8930 [C8 (Z_to_bv 64 Q_MAX); C8 (Z_to_bv 64 Q_MIN); C8 (Z_to_bv 64 Q_CACHE)] ->
  rw_cells bsegs m 0xd3628 [C8 (Z_to_bv 64 AFLAGS)] ->
  rw_cells bsegs m 0xd94a4 [C4 (Z_to_bv 64 0x1000); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0xbe)] ->

  rw_cells bsegs m 0x16b708 [C1 (Z_to_bv 8 (if ia then 1 else 0)); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] ->
  stk bsegs m 0xdce80 (0xdce80 + 0x81030) ->
  (ia = true -> forall j, 0 <= j < 32768 -> bytes_at bsegs m (0xdce88 + 8 * j) (le8 (Z_to_bv 64 0))) ->

  rw_cells bsegs m (ctx + 8) [C4 (Z_to_bv 64 0)] ->
  rw_cells bsegs m t [C8 (Z_to_bv 64 ctx); C8 (Z_to_bv 64 top); C8 (Z_to_bv 64 bot)] ->
  rw_cells bsegs m (t + 40) [C1 (Z_to_bv 8 0)] -> rw_cells bsegs m (t + 3168) [C1 (Z_to_bv 8 0)] ->
  u64arr bsegs m (t + 2800) sj -> length sj = 46%nat ->
  rw_cells bsegs m (t + 80) [C8 (Z_to_bv 64 nb); C8 (Z_to_bv 64 fst0); C8 (Z_to_bv 64 lst); C8 (Z_to_bv 64 qb)] ->
  0 <= nb < 2^62 -> 0 <= qb -> qb + n + 8192 < 2^62 -> 0 <= fst0 < 2^64 -> 0 <= lst < 2^64 ->
  0 < ctx -> sclr ctx 65536 -> ctx + 4096 <= ATOP ->
  sclr t 4096 -> t + 4096 <= ATOP -> t mod 4096 = 0 -> (ctx + 4096 <= t \/ t + 4096 <= ctx) ->

  rw_cells bsegs m hm [C1 (Z_to_bv 8 2); C1 (Z_to_bv 8 b1); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 (Z_to_bv 64 actx)] ->
  rw_cells bsegs m (hm + 16) [C8 uw] -> 0 <= b1 < 256 -> Z.land b1 3 = 1 -> 1 <= n <= Q_MAX -> hm mod 16 = 0 ->
  ablk hm (hm + 16 + rup n 8) -> hm + 16 + rup n 8 <= ATOP -> hm + 24 <= ATOP ->
  rw_cells bsegs m (shad (hm + 16)) [CB (Z.to_nat (shlen (rup n 8))) sjunk] ->
  (hm + 24 <= t \/ t + 4096 <= hm) -> (hm + 24 <= ctx \/ ctx + 4096 <= hm) ->

  (if full then 0 < nb /\ rw_cells bsegs m lst [C8 (Z_to_bv 64 nx); C8 (Z_to_bv 64 bsz); C8 (Z_to_bv 64 1021)]
             /\ 0x10007fff8000 <= lst /\ lst + 8192 <= ATOP
             /\ u64arr bsegs m (lst + 24) hs /\ length hs = 1021%nat /\ rng RNG lst 8192
   else nb = 0 /\ lst = 0) ->
  rw_cells bsegs m (t + 2128) [C4 (Z_to_bv 64 0); C4 maxc; C8 csz] ->
  (t + 4096 <= lst \/ lst + 8192 <= t \/ lst = 0) -> (hm + 24 <= lst \/ lst + 8192 <= hm) ->
  (al_nodes L + 1048576 <= lst \/ lst + 8192 <= al_nodes L) -> (al_store L + 8388608 <= lst \/ lst + 8192 <= al_store L) ->

  ADEPOT DI L m ->
  sclr (al_nodes L) 1048576 -> al_nodes L + 1048576 <= ATOP -> sclr (al_store L) 8388608 -> al_store L + 8388608 <= ATOP ->
  (hm + 24 <= al_nodes L \/ al_nodes L + 1048576 <= hm) -> (hm + 24 <= al_store L \/ al_store L + 8388608 <= hm) ->
  (t + 4096 <= al_nodes L \/ al_nodes L + 1048576 <= t) -> (t + 4096 <= al_store L \/ al_store L + 8388608 <= t) ->
  (ctx + 4096 <= al_nodes L \/ al_nodes L + 1048576 <= ctx) -> (ctx + 4096 <= al_store L \/ al_store L + 8388608 <= ctx) ->

  afree_unw RNG lo m top sp s0 ra trt ->
  bv_unsigned s0 <> bv_unsigned sp + 8 ->
  In (AFREE_PC :: trt) (al_U L) ->
  0 <= bot -> bot < bv_unsigned sp -> bot < top -> 4096 <= top <= 2^47 -> 4096 <= bv_unsigned ra -> bv_unsigned ra <> AFREE_PC ->

  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG ctx 4096 -> rng RNG t 4096 ->
  rng RNG (al_nodes L) 1048576 -> rng RNG (al_store L) 8388608 -> rng RNG hm 24 -> rng RNG (shad (hm + 16)) (shlen (rup n 8)) ->
  AIMG_HI <= ctx -> AIMG_HI <= al_nodes L -> AIMG_HI <= al_store L -> iclr t 4096 ->
  evtF bsegs RNG (free_to_refill_post L full ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc t hm n b1 actx lo lst nx bsz hs trt m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 AFREE_SYM) fc None m (seg_rom bsegs)).
Proof.
  intros until trt.
  intros ST CEIL LO MI TP Ha0 SP16 AC PC MCS CF34 GPG PGC HK QK GF FLG FL IAS IAM CT8 TT0 SW UW STATS LSJ QC NB QB QBN FST LST
         CX0 C0 C1 T0 T1 TAL CT2 HD HUW B1 B13 N AL HLO HHI HCE SH DHT DHC FULL CR0 DTL DHL DNL DSL DEP N0 N1 R0 R1 DHN DHS DTN DTS DCN DCS
         UNW S0NE TRU B0 BB BOTOP TOP RA4 RANE RIMG RSTK RCTX RT RNO RST RH RSH CI NI SI TI. band_lin.
  band_int TI. pose proof (ablk_lin _ _ HLO) as (HL1 & HL2 & HL3 & HL4). unfold AIMG_HI in HL1. band_int HLO. band_int C0. band_int T0. band_int N0. band_int R0.
  pose proof (afree_unw_length _ _ _ _ _ _ _ _ UNW) as LTRT.
  pose proof (afree_unw_sp47 _ _ _ _ _ _ _ _ UNW ltac:(clear -TOP; lia)) as SP47.
  pose proof PC as PC'. destruct PC' as (GOT6 & _).
  assert (RUP : n <= rup n 8 <= n + 7 /\ rup n 8 mod 8 = 0) by (clear -N; unfold rup; Z.div_mod_to_equations; lia).
  assert (SHB : 2148262400 <= shad (hm + 16) /\ shad (hm + 16) + shlen (rup n 8) <= 0x10007fff8000 /\ 0 < shlen (rup n 8)).
  { clear -N HLO HL1 HHI HCE. unfold shad, shlen, ASHOFF, rup in *. rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8. unfold Q_MAX in *. Z.div_mod_to_equations. lia. }
  unfold AIMG_HI, AFREE_SYM, AFREE_PC in *.
  word_range sp SPR.
  box DHT. box DHC. box DHN. box DHS. box DTN. box DTS. box DCN. box DCS. box CT2. box DTL. box DHL. box DNL. box DSL.

  eapply evtF_cut.
  { eapply (free_front_spec DI L ia RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
              t ctx hm n b1 actx lo top bot uw sj trt).
    all: try lazymatch goal with
         | |- stk _ _ _ _ => first [exact ST | exact IAS]
         | |- mem_inv _ _ => exact MI
         | |- allocA_cells _ _ _ => exact AC
         | |- ADEPOT _ _ _ => exact DEP
         | |- afree_unw _ _ _ _ _ _ => exact UNW
         | |- In _ _ => exact TRU
         | |- u64arr _ _ _ _ => exact STATS
         | |- _ = true -> _ => exact IAM
         | |- _ \/ _ => first [unboxed DHT | unboxed DHC | unboxed DHN | unboxed DHS | unboxed DTN | unboxed DTS | unboxed DCN | unboxed DCS | unboxed CT2]
         | |- rng _ _ _ => solve_rng
         | |- rw_cells _ _ _ [C1 _; C1 _; C2 _; C4 _; C8 _] => exact HD
         | |- rw_cells _ _ _ [C8 _; C8 _; C8 _] => exact TT0
         | |- rw_cells _ _ (_ + 16) _ => exact HUW
         | |- rw_cells _ _ (_ + 8) _ => exact CT8
         | |- rw_cells _ _ (_ + 40) _ => exact SW
         | |- rw_cells _ _ (_ + 3168) _ => exact UW
         end.
    all: try eassumption. all: try (unfold AIMG_HI, Q_MAX in *; lia).
    all: match goal with |- ?G => idtac "REMF" G end. }
  cbv beta. intros ms1 PFR. unfold free_front_post in PFR.
  destruct PFR as (id & t0a & t1a & t2a & a6a & a7a & t3a & t4a & t5a & t6a & m1 & sj1 & tb1 & junk2
                   & -> & MUf & WMf & MIf & STf & IDR & HD1 & FC1 & STATS1 & LSJ1 & UW1 & FL1 & IAS1 & IAM1 & SS1 & TB1 & LTB1 & FRS1 & DEP1).

  xport QK MUf WMf ltac:(lia). xport GF MUf WMf ltac:(lia). xport FLG MUf WMf ltac:(lia).
  xport QC MUf WMf ltac:(ub DHT; ub DTN; ub DTS; lia).
  xport SH MUf WMf ltac:(band_disj).
  xport CR0 MUf WMf ltac:(ub DHT; ub DTN; ub DTS; lia).
  assert (PC1 : poison_cells m1).
  { eapply poison_cells_frame2; [exact PC | exact MUf | exact WMf |].
    repeat (apply Forall_cons; [cbn [fst snd]; lia|]). apply Forall_nil. }
  assert (FULL1 : if full then 0 < nb /\ rw_cells bsegs m1 lst [C8 (Z_to_bv 64 nx); C8 (Z_to_bv 64 bsz); C8 (Z_to_bv 64 1021)]
             /\ 0x10007fff8000 <= lst /\ lst + 8192 <= ATOP
             /\ u64arr bsegs m1 (lst + 24) hs /\ length hs = 1021%nat /\ rng RNG lst 8192
           else nb = 0 /\ lst = 0).
  { destruct full; [| exact FULL]. destruct FULL as (NB1 & LB & L0 & L1 & LA0 & LEN0 & RL).
    xport LB MUf WMf ltac:(ub DTL; ub DHL; ub DNL; ub DSL; lia). xport LA0 MUf WMf ltac:(rewrite LEN0; ub DTL; ub DHL; ub DNL; ub DSL; lia).
    split; [exact NB1|]. split; [exact LB|]. split; [exact L0|]. split; [exact L1|]. split; [exact LA0|]. split; [exact LEN0| exact RL]. }
  clear FULL PC.

  name_sp sp (-2128).
  eapply evtF_cut.
  { eapply (put_to_refill_spec full t hm lst RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m1 n nb fst0 qb b1 actx lo nx bsz maxc csz hs sjunk).
    all: try lazymatch goal with
         | |- stk _ _ _ _ => rewrite Hsp; exact STf
         | |- mem_inv _ _ => exact MIf
         | |- poison_cells _ => exact PC1
         | |- @eq word _ _ => rewrite ?Esp; first [reflexivity | apply Z_to_bv_eqm; rewrite ?unsigned_lit by lia; lia]
         | |- if _ then _ else _ => exact FULL1
         | |- _ \/ _ => first [ub DHT; lia | ub DTL; lia | ub DHL; lia]
         | |- rng _ _ _ => solve_rng
         | |- rw_cells _ _ _ [C1 _; C1 _; C2 _; C4 _; C8 _] => exact HD1
         | |- rw_cells _ _ (shad _) _ => exact SH
         | |- rw_cells _ _ (_ + 80) _ => exact QC
         | |- rw_cells _ _ (_ + 2128) _ => exact CR0
         | |- iclr _ _ => exact TI
         end.
    all: try eassumption. all: try (unfold AIMG_HI, Q_MAX in *; lia).
    all: match goal with |- ?G => idtac "REMP" G end. }
  cbv beta. intros ms2 PP. unfold put_to_refill_post in PP.
  destruct PP as (t0b & t1b & t2b & a4b & a5b & a6b & a7b & t3b & t4b & t5b & t6b & m2 & j0
                  & -> & MUp & WMp & MIp & STp & SH2 & FRP & FRE & LBS).
  unname_sp. rewrite ?unsigned_lit in MUp by lia. rewrite ?unsigned_lit in STp by lia.
  rewrite ?unsigned_lit in FRP by lia. rewrite ?unsigned_lit in FRE by lia.
  replace (bv_unsigned sp + -2128 + -80) with (bv_unsigned sp + -2208) in * by lia.
  replace (bv_unsigned sp + -2128 + -144) with (bv_unsigned sp + -2272) in * by lia.

  xport HD1 MUp WMp ltac:(lia). xport FC1 MUp WMp ltac:(lia).
  xport STATS1 MUp WMp ltac:(rewrite LSJ1; lia).
  xport UW1 MUp WMp ltac:(lia).
  xport FL1 MUp WMp ltac:(lia). xport IAS1 MUp WMp ltac:(lia).
  xport SS1 MUp WMp ltac:(lia). xport TB1 MUp WMp ltac:(rewrite LTB1; lia). xport FRS1 MUp WMp ltac:(lia).
  assert (IAM2 : forall j, 0 <= j < 32768 -> bytes_at bsegs m2 (0xdce88 + 8 * j) (le8 (Z_to_bv 64 0))).
  { (intros j Hj; eapply bytes_at_agree; [exact (IAM1 j Hj)|];
    intros i Hi; apply MUp; cbn [outside]; rewrite length_le8 in Hi; rewrite wa_unsigned by lia; lia). }
  clear IAM1.
  assert (DEP2 : ADEPOT DI L m2).
  { eapply (adi_frame DI); [exact DEP1 | exact MUp | exact WMp |].
    (repeat (apply Forall_cons; [cbn [fst snd]; intros q Hq; first [lia | ub DTN; ub DTS; lia] |]); apply Forall_nil). }
  clear DEP1.

  assert (MU : munch (toref_W L sp t hm n) m m2).
  { eapply munch_trans; [| eapply munch_weaken; [| exact MUp]].
    eapply munch_weaken; [| exact MUf].
    all: solve_sub_fp sp. }
  assert (WM : wmono bsegs m m2) by (eapply wmono_trans; [exact WMf| exact WMp]).
  apply evtF_done. unfold free_to_refill_post. exists id. do 11 eexists. exists m2, sj1, tb1, junk2, j0.
  split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MIp|]. split; [exact STp|]. split; [exact IDR|].
  split; [exact HD1|]. split; [exact FC1|]. split; [exact SH2|].
  split; [exact STATS1|]. split; [exact LSJ1|]. split; [exact UW1|]. split; [exact FL1|]. split; [exact IAS1|]. split; [exact IAM2|].
  split; [exact SS1|]. split; [exact TB1|]. split; [exact LTB1|]. split; [exact FRS1|]. split; [exact FRP|]. split; [exact FRE|].
  split; [exact LBS|]. exact DEP2.
  Unshelve. all: try exact STf; try exact STp.
Qed.

Lemma free_from_refill_spec : forall (L : alayout) (full : bool) (g : gqd) RNG
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (ra0 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) fc (m : amem)
    (t hm n b1 actx lo nb fst0 lst qb nx bsz cnt spacebeg id b : Z) (maxc csz stj idxw : word) (sj tb chunks hs : list word)
    (junk2 j0 : list byte) (trt : list Z),
  let ek := EkNew full nx bsz cnt maxc csz stj idxw chunks spacebeg b hs in
  stk bsegs m lo (bv_unsigned sp + -2272) -> ATOP <= lo -> lo <= bv_unsigned sp - 4096 ->
  mem_inv bsegs m ->

  rw_cells bsegs m (bv_unsigned sp + -2128) [C8 (Z_to_bv 64 (bv_unsigned sp + -2128 + 16)); C4 (Z_to_bv 64 (1 + Z.of_nat (length trt))); C4 (Z_to_bv 64 0)] ->
  u64arr bsegs m (bv_unsigned sp + -2128 + 16) tb -> length tb = 255%nat ->
  rw_cells bsegs m (bv_unsigned sp + -72) [C8 sp; CB 8 junk2; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  rw_cells bsegs m (bv_unsigned sp + -2208)
     [C8 (Z_to_bv 64 (t + 208)); C8 (Z_to_bv 64 (bv_unsigned sp + -2128)); C8 s6; C8 (Z_to_bv 64 (bv_unsigned sp + -81));
      C8 (Z_to_bv 64 (bv_unsigned sp + -2128)); C8 (Z_to_bv 64 1); C8 (Z_to_bv 64 0x5eeec); C8 (Z_to_bv 64 (hm + 16)); C8 sp; C8 (Z_to_bv 64 0x5ef5c)] ->
  rw_cells bsegs m (bv_unsigned sp + -2272)
     [CB 8 j0; C8 (Z_to_bv 64 hm); C8 (Z_to_bv 64 (t + 208)); C8 (Z_to_bv 64 (bv_unsigned sp + -2128)); C8 (Z_to_bv 64 n);
      C8 (Z_to_bv 64 (t + 80)); C8 (Z_to_bv 64 0xd88f0); C8 (Z_to_bv 64 0x41bc0)] ->

  rw_cells bsegs m 0xd8930 [C8 (Z_to_bv 64 Q_MAX); C8 (Z_to_bv 64 Q_MIN); C8 (Z_to_bv 64 Q_CACHE)] ->

  rw_cells bsegs m hm [C1 (Z_to_bv 8 3); C1 (Z_to_bv 8 b1); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 (Z_to_bv 64 actx)] ->
  rw_cells bsegs m (hm + 16) [C8 (Z_to_bv 64 id)] -> 0 < id < 2^31 ->
  1 <= n <= Q_MAX -> hm mod 16 = 0 -> ablk hm (hm + 16 + rup n 8) -> hm + 16 + rup n 8 <= ATOP -> hm + 24 <= ATOP ->
  rw_cells bsegs m (shad (hm + 16)) [CB (Z.to_nat (shlen (rup n 8))) (repeat (Z_to_bv 8 253) (Z.to_nat (shlen (rup n 8))))] ->

  rw_cells bsegs m (t + 80) [C8 (Z_to_bv 64 nb); C8 (Z_to_bv 64 fst0); C8 (Z_to_bv 64 lst); C8 (Z_to_bv 64 qb)] ->
  0 <= nb < 2^62 -> 0 <= qb -> qb + n + 8192 < 2^62 -> 0 <= fst0 < 2^64 -> 0 <= lst < 2^64 ->
  sclr t 4096 -> t + 4096 <= ATOP -> t mod 4096 = 0 -> (hm + 24 <= t \/ t + 4096 <= hm) ->
  u64arr bsegs m (t + 2800) sj -> length sj = 46%nat -> rw_cells bsegs m (t + 3168) [C1 (Z_to_bv 8 0)] ->
  rw_cells bsegs m 0x16b708 [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] ->
  stk bsegs m 0xdce80 (0xdce80 + 0x81030) ->
  (forall j, 0 <= j < 32768 -> bytes_at bsegs m (0xdce88 + 8 * j) (le8 (Z_to_bv 64 0))) ->

  (if full then 0 < nb /\ rw_cells bsegs m lst [C8 (Z_to_bv 64 nx); C8 (Z_to_bv 64 bsz); C8 (Z_to_bv 64 1021)]
             /\ 0 <= nx < 2^64 /\ 0 <= bsz < 2^64 /\ 0x10007fff8000 <= lst /\ lst + 8192 <= ATOP
             /\ u64arr bsegs m (lst + 24) hs /\ length hs = 1021%nat
             /\ rng RNG lst 8192
   else nb = 0 /\ lst = 0) ->
  rw_cells bsegs m 0xd8638 [C8 (Z_to_bv 64 spacebeg)] ->
  rw_cells bsegs m (t + 2128) [C4 (Z_to_bv 64 cnt); C4 maxc; C8 csz] ->
  u32arr bsegs m (t + 2128 + 16) chunks -> length chunks = 16%nat ->
  0 < cnt <= 16 -> nth_error chunks (Z.to_nat (cnt - 1)) = Some idxw -> bv_unsigned idxw < 2^32 ->
  rw_cells bsegs m (t + 2784) [C8 stj] ->
  b = spacebeg + 24 * 2^32 + 16 * bv_unsigned idxw ->
  (exists bs, rw_cells bsegs m b [CB (Z.to_nat 8192) bs]) ->
  0 < spacebeg -> 0x10007fff8000 <= b -> b + 8192 <= ATOP ->
  (t + 4096 <= b \/ b + 8192 <= t) -> (t + 4096 <= lst \/ lst + 8192 <= t \/ lst = 0) -> (b + 8192 <= lst \/ lst + 8192 <= b) ->
  (hm + 24 <= b \/ b + 8192 <= hm) -> (hm + 24 <= lst \/ lst + 8192 <= hm) ->
  rng RNG b 8192 ->
  ek_seps ek L hm lst ->

  dk_pre ek g RNG t lst hm (qb + ek_delta ek n) m -> dk_seps g L hm ->

  ADEPOT DI L m ->
  sclr (al_nodes L) 1048576 -> al_nodes L + 1048576 <= ATOP -> sclr (al_store L) 8388608 -> al_store L + 8388608 <= ATOP ->
  (t + 4096 <= al_nodes L \/ al_nodes L + 1048576 <= t) -> (t + 4096 <= al_store L \/ al_store L + 8388608 <= t) ->
  bv_unsigned sp < 2^47 ->

  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG t 4096 -> rng RNG hm 24 -> rng RNG (shad (hm + 16)) (shlen (rup n 8)) ->
  AIMG_HI <= al_nodes L -> AIMG_HI <= al_store L -> iclr t 4096 ->
  evtF bsegs RNG (free_fast_post DI L ek g ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc t hm n nb fst0 lst qb b1 actx lo m)
    (MS (mkR ra0 (Z_to_bv 64 (bv_unsigned sp + -2272)) gp tp t0 t1 t2 (Z_to_bv 64 (t + 2128)) (Z_to_bv 64 (t + 208))
             (Z_to_bv 64 1) a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 hm) (Z_to_bv 64 (t + 80)) (Z_to_bv 64 (bv_unsigned sp + -2128)) (Z_to_bv 64 n) (Z_to_bv 64 Q_CACHE)
             s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x41d20) fc None m (seg_rom bsegs)).
Proof.
  intros until trt. cbv zeta.
  intros ST CEIL LO MI SS TB LTB FRS FRP FRE QK HD FC IDR N AL HLO HHI HCE SH QC NB QB QBN FST LST T0 T1 TAL DHT STATS LSJ UW FL IAS IAM
         FULL SB CR CH LCH CNT NTH IXS STS HBE BJ SBP B0 BL1 DTB DTL DBL DHB DHL RB ES DK DS DEP N0 N1 R0 R1 DTN DTS SP47
         RIMG RSTK RT RH RSH NI SI TI. band_lin.
  band_int TI. pose proof (ablk_lin _ _ HLO) as (HL1 & HL2 & HL3 & HL4). unfold AIMG_HI in HL1. band_int HLO. band_int T0. band_int N0. band_int R0.
  assert (RUP : n <= rup n 8 <= n + 7 /\ rup n 8 mod 8 = 0) by (clear -N; unfold rup; Z.div_mod_to_equations; lia).
  assert (SHB : 2148262400 <= shad (hm + 16) /\ shad (hm + 16) + shlen (rup n 8) <= 0x10007fff8000 /\ 0 < shlen (rup n 8)).
  { clear -N HLO HL1 HHI HCE. unfold shad, shlen, ASHOFF, rup in *. rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8. unfold Q_MAX in *. Z.div_mod_to_equations. lia. }
  pose proof (dk_pre_pure _ g RNG L t lst hm (qb + (n + 8192)) m DK DS TI ltac:(unfold AIMG_HI; lia) NI SI
                DHL DTL ltac:(cbn [ek_seps] in ES; destruct full; [destruct ES as (_ & _ & _ & S4); destruct FULL as (_ & _ & _ & _ & L0 & _); exact (proj1 (proj2 (S4 eq_refl))) | destruct FULL as [_ ->]; unfold AIMG_HI in *; lia])
                ltac:(cbn [ek_seps] in ES; destruct full; [destruct ES as (_ & _ & _ & S4); exact (proj2 (proj2 (S4 eq_refl))) | destruct FULL as [_ ->]; unfold AIMG_HI in *; lia])
                ltac:(destruct full; [destruct FULL as (_ & _ & _ & _ & L0 & _) | destruct FULL as [_ ->]]; unfold AIMG_HI in *; lia)
                ltac:(destruct full; [destruct FULL as (_ & _ & _ & _ & L0 & L1 & _) | destruct FULL as [_ ->]]; unfold AIMG_HI in *; atop_facts; lia)
                ltac:(destruct full; [destruct FULL as (_ & _ & _ & _ & L0 & _); right | destruct FULL as [_ ->]; left]; unfold AIMG_HI in *; lia))
    as (DF1 & DF2 & DF3 & DF4 & DG0 & DG1 & DG2).
  cbn [ek_seps] in ES. destruct ES as (SB1 & SB2 & SB3 & SL).
  assert (PL2 : lst = 0 \/ 0x10007fff8000 <= lst) by (destruct full; [destruct FULL as (_ & _ & _ & _ & L0 & _); right; exact L0 | destruct FULL as [_ E0]; left; exact E0]).
  assert (PLB : lst + 8192 <= ATOP) by (destruct full; [destruct FULL as (_ & _ & _ & _ & _ & L1 & _); exact L1 | destruct FULL as [_ E0]; rewrite E0; atop_facts; lia]).
  pose proof (qsz_int lst ltac:(clear -PL2; lia) ltac:(clear -PLB; atop_facts; lia)) as (zq & QZ0 & QZ1 & QZ2 & QZ3).
  unfold AIMG_HI, AFREE_SYM, AFREE_PC in *.
  word_range sp SPR.
  box DHT. box DTN. box DTS. box DTB. box DTL. box DBL. box DHB. box DHL. box SB1. box SB2. box SB3. box DF1. box DF2. box DF3. box DF4. box DG2. box PL2.

  set (sp1 := Z_to_bv 64 (bv_unsigned sp + -2128)) in *.
  assert (Hsp : bv_unsigned sp1 = bv_unsigned sp + -2128) by (subst sp1; apply unsigned_lit; lia).
  replace (bv_unsigned sp + -2272) with (bv_unsigned sp1 + -144) in * by lia.
  replace (bv_unsigned sp + -2208) with (bv_unsigned sp1 + -80) in * by lia.

  eapply evtF_cut.
  { eapply (put_from_refill_spec full g t hm lst b RNG (Z_to_bv 64 0x5ef5c) sp1 gp tp sp (Z_to_bv 64 (hm + 16)) (Z_to_bv 64 (t + 208)) sp1
              (Z_to_bv 64 0x5eeec) (Z_to_bv 64 1) sp1 (Z_to_bv 64 (bv_unsigned sp + -81)) s6 s7 s8 s9 s10 s11
              ra0 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc m n nb fst0 qb b1 actx lo nx bsz cnt spacebeg maxc csz stj idxw chunks hs j0).
    all: try lazymatch goal with
         | |- stk _ _ _ _ => first [exact ST | exact IAS]
         | |- mem_inv _ _ => exact MI
         | |- if _ then _ else _ => exact FULL
         | |- dk_pre _ _ _ _ _ _ _ _ => exact DK
         | |- @eq word _ _ => reflexivity
         | |- @eq Z _ _ => first [exact HBE | lia]
         | |- ex _ => exact BJ
         | |- _ \/ _ => first [ub DHT; lia | ub DTB; lia | ub DTL; lia | ub DBL; lia | ub DHB; lia | ub DHL; lia]
         | |- rng _ _ _ => solve_rng
         | |- rw_cells _ _ _ [C1 _; C1 _; C2 _; C4 _; C8 _] => exact HD
         | |- rw_cells _ _ (shad _) _ => exact SH
         | |- rw_cells _ _ (_ + 80) _ => exact QC
         | |- rw_cells _ _ (_ + 2128) _ => exact CR
         | |- rw_cells _ _ (_ + 2784) _ => exact STS
         | |- rw_cells _ _ (_ + -80) _ => exact FRP
         | |- iclr _ _ => exact TI
         | |- rw_cells _ _ (_ + -144) _ => exact FRE
         | |- u32arr _ _ _ _ => exact CH
         | |- nth_error _ _ = _ => exact NTH
         end.
    all: try eassumption. all: try (unfold AIMG_HI, Q_MAX in *; lia).
    all: match goal with |- ?G => idtac "REMQ" G end. }
  cbv beta. intros ms2 PP. unfold put_tail_post in PP.
  destruct PP as (t0b & t1b & t2b & a0b & a1b & a2b & a3b & a4b & a5b & a6b & a7b & t3b & t4b & t5b & t6b & m2
                  & -> & MUp & WMp & MIp & STp & SH2 & HD2 & QC2 & EKP & DKP).
  replace (ret_pc (Z_to_bv 64 388956)) with (Z_to_bv 64 388956) by (symmetry; apply ret_pc_even; [lia|reflexivity]).

  cbn [ek_b] in MUp.
  xport FC MUp WMp ltac:(ub DHT; ub DHB; ub DHL; ub DF1; lia).
  xport STATS MUp WMp ltac:(rewrite LSJ; ub DTB; ub DTL; ub DF2; lia).
  xport UW MUp WMp ltac:(ub DTB; ub DTL; ub DF2; lia).
  xport FL MUp WMp ltac:(ub DG2; ub PL2; lia). xport IAS MUp WMp ltac:(ub DG2; ub PL2; lia).
  xport SS MUp WMp ltac:(lia). xport TB MUp WMp ltac:(rewrite LTB; lia). xport FRS MUp WMp ltac:(lia).
  assert (IAM2 : forall j, 0 <= j < 32768 -> bytes_at bsegs m2 (0xdce88 + 8 * j) (le8 (Z_to_bv 64 0))).
  { (intros j Hj; eapply bytes_at_agree; [exact (IAM j Hj)|];
    intros i Hi; apply MUp; cbn [outside]; rewrite length_le8 in Hi; rewrite wa_unsigned by lia; ub DG2; ub PL2; lia). }
  clear IAM.
  assert (DEP2 : ADEPOT DI L m2).
  { eapply (adi_frame DI); [exact DEP | exact MUp | exact WMp |].
    (repeat (apply Forall_cons; [cbn [fst snd]; intros q Hq;
      first [lia | ub DTN; ub DTS; lia | ub SB2; ub SB3; lia | ub DF3; ub DF4; ub DG2; lia
            | destruct full; [destruct (SL eq_refl) as (_ & S6 & S7); lia | destruct FULL as [_ LST0]; lia] ] |]); apply Forall_nil). }
  clear DEP.

  subst sp1. rewrite ?unsigned_lit in STp by lia. rewrite ?unsigned_lit in MUp by lia.
  apply rw_cells_of_u64arr in TB. rewrite LTB in TB.
  eapply evtF_mono.
  { (eapply (ficptD_spec RNG sp gp tp); [exact STp | atop_facts; lia | lia | exact MIp
      | eexists; split; [exact SS | reflexivity]
      | eexists; split; [replace (bv_unsigned sp + -2112) with (bv_unsigned sp + -2128 + 16) by lia; exact TB | reflexivity]
      | exact FRS | exact RIMG | solve_rng ]). }
  cbv beta. intros ms3 [-> ST3].

  assert (MU : munch (free_W L sp t hm n lst (EkNew full nx bsz cnt maxc csz stj idxw chunks spacebeg b hs) g) m m2).
  { eapply munch_weaken; [| exact MUp]. cbn [ek_b]. solve_sub_fp sp. }
  unfold free_fast_post. exists id. do 15 eexists. exists m2, sj.
  split; [reflexivity|].
  split; [exact MU|]. split; [exact WMp|]. split; [exact MIp|]. split; [exact ST3|]. split; [exact IDR|].
  split; [exact HD2|]. split; [exact FC|]. split; [exact SH2|]. split; [exact QC2|]. split; [exact EKP|]. split; [exact DKP|].
  split; [exact STATS|]. split; [exact LSJ|]. split; [exact UW|]. split; [exact FL|]. split; [exact IAS|]. split; [exact IAM2|].
  exact DEP2.
  Unshelve. all: try exact ST; try exact STp.
Qed.
End WithDepot.
End CANSEC1.
End F_afree_icptR.

Module F_afreeC_iface.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase. Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics. Import LinuxProcessSemantics.LinuxProcessSem.MemImageType. Import LinuxProcessSemantics.LinuxProcessSem.State. Import LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude. Import LinuxProcessSemantics.Riscv.Instr. Import LinuxProcessSemantics.Riscv.Decode. Import LinuxProcessSemantics.Riscv.DecodeC. Import LinuxProcessSemantics.Riscv.Sem. Import LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.ITree. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Nodes. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Decode. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Arr. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.InitMem.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.STree. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanCtrl. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanEmbed.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.BothW.BImg. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AProto.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ABase.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ABytes.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AQConst.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ADepot_iface.TwinB.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.StepF.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AKit.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AKit2.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AKitQ.TwinB.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_apoison.TwinB.F_apoison. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aalloc_s.TwinB.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aalloc1.TwinB.F_aalloc1. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_afree_iseg.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_afree_front.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_adrain.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_afree_tail.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_afree_icpt.TwinB.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aenqueue.TwinB.F_aenqueueR. Import F_afree_tailR. Import F_afree_icptR.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT}.
Definition drain_torec_post (gfull : bool) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a2 a3 : word) (F : bvmap 5 word) (fc : bv 32)
    (t nb fst lst qb gnb gfst glst gqb lo : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 AQUAR_Q) (Z_to_bv 64 Q_MIN) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x3f4c8) fc None m' (seg_rom bsegs)
    /\ munch [(bv_unsigned sp - 48, bv_unsigned sp); (t + 80, t + 112); (0xd8988, 0xd8988 + 4); (0xd8990, 0xd8990 + 32); (glst, glst + 8)]%Z m m'
    /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo (bv_unsigned sp)
    /\ rw_cells bsegs m' (t + 80) [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]
    /\ rw_cells bsegs m' 0xd8988 [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]
    /\ rw_cells bsegs m' 0xd8990 [C8 (Z_to_bv 64 (gnb + nb)); C8 (Z_to_bv 64 (if gfull then gfst else fst)); C8 (Z_to_bv 64 lst);
                                   C8 (Z_to_bv 64 (gqb + qb))]
    /\ (if gfull then rw_cells bsegs m' glst [C8 (Z_to_bv 64 fst)] else True).

Definition drain_torec_stmt : Prop := forall (gfull : bool) (t glst : Z) RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (nb fst lst qb gnb gfst gqb gnx lo : Z),
  stk bsegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - 48 ->
  mem_inv bsegs m ->
  a0 = Z_to_bv 64 AQUAR_Q -> a1 = Z_to_bv 64 (t + 80) ->
  rw_cells bsegs m (t + 80) [C8 (Z_to_bv 64 nb); C8 (Z_to_bv 64 fst); C8 (Z_to_bv 64 lst); C8 (Z_to_bv 64 qb)] ->
  0 < nb < 2^63 -> 0 <= qb -> 0 <= fst < 2^64 -> 0 <= lst < 2^64 ->
  rw_cells bsegs m AQ_MUTEX [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] ->
  rw_cells bsegs m AQ_GCACHE [C8 (Z_to_bv 64 gnb); C8 (Z_to_bv 64 gfst); C8 (Z_to_bv 64 glst); C8 (Z_to_bv 64 gqb)] ->
  0 <= gnb < 2^62 -> 0 <= gqb -> Q_MAX < gqb + qb -> gqb + qb < 2^63 -> 0 <= gfst < 2^64 -> 0 <= glst < 2^64 ->
  rw_cells bsegs m AQ_MAX [C8 (Z_to_bv 64 Q_MAX); C8 (Z_to_bv 64 Q_MIN); C8 (Z_to_bv 64 Q_CACHE)] ->
  (if gfull then 0 < gnb /\ rw_cells bsegs m glst [C8 (Z_to_bv 64 gnx)] /\ AIMG_HI <= glst /\ glst + Q_BATCH_BYTES <= ATOP
                 /\ (t + 4096 <= glst \/ glst + Q_BATCH_BYTES <= t)
   else gnb = 0) ->
  iclr t 4096 -> t + 4096 <= ATOP ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG t 4096 -> (if gfull then rng RNG glst Q_BATCH_BYTES else True) ->
  evtF bsegs RNG (drain_torec_post gfull ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a2 a3 F fc t nb fst lst qb gnb gfst glst gqb lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x3f324) fc None m (seg_rom bsegs)).

Definition dk_preC (ek : enq_kind) (g : gqd) (RNG : footprint) (t lst hm qb' : Z) (m : amem) : Prop :=
     g_drain g = true
  /\ rw_cells bsegs m 0xd8988 [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]
  /\ rw_cells bsegs m 0xd8990 [C8 (Z_to_bv 64 (g_nb g)); C8 (Z_to_bv 64 (g_fst g)); C8 (Z_to_bv 64 (g_lst g)); C8 (Z_to_bv 64 (g_qb g))]
  /\ 0 <= g_nb g < 2^62 /\ 0 <= g_qb g /\ 0 <= g_fst g < 2^64 /\ 0 <= g_lst g < 2^64
  /\ Q_CACHE < qb' /\ Q_MAX < g_qb g + qb' /\ g_qb g + qb' < 2^63
  /\ (if g_full g then 0 < g_nb g /\ rw_cells bsegs m (g_lst g) [C8 (Z_to_bv 64 (g_nx g))] /\ 0x10007fff8000 <= g_lst g /\ g_lst g + 8192 <= ATOP
                     /\ (t + 4096 <= g_lst g \/ g_lst g + 8192 <= t) /\ (hm + 16 <= g_lst g \/ g_lst g + 8 <= hm)
                     /\ (lst + 8192 <= g_lst g \/ g_lst g + 8192 <= lst) /\ (ek_b ek lst + 8192 <= g_lst g \/ g_lst g + 8192 <= ek_b ek lst)
                     /\ rng RNG (g_lst g) 8192
      else g_nb g = 0 /\ g_lst g = 0).

Definition dk_postC (g : gqd) (nb' fst' lst' qb' : Z) (m' : amem) : Prop :=
     rw_cells bsegs m' 0xd8988 [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]
  /\ rw_cells bsegs m' 0xd8990 [C8 (Z_to_bv 64 (g_nb g + nb')); C8 (Z_to_bv 64 (if g_full g then g_fst g else fst'));
                                 C8 (Z_to_bv 64 lst'); C8 (Z_to_bv 64 (g_qb g + qb'))]
  /\ (if g_full g then rw_cells bsegs m' (g_lst g) [C8 (Z_to_bv 64 fst')] else True).

Definition put_frame (cbc cbs s6 s5 s4 s3 s2 s1 s0 ra : word) : list cell :=
  [C8 cbc; C8 cbs; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

Definition put_torec_post (ek : enq_kind) (g : gqd)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a3 : word) (F : bvmap 5 word) (fc : bv 32)
    (t hm n nb fst0 lst qb b1 actx lo : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 xs0 xs1 xs2 xs3 xs4 xs5 xs6 a4 a5 a6 a7 t3 t4 t5 t6 : word) m',
    ms' = MS (mkR (Z_to_bv 64 0x41af8) (Z_to_bv 64 (bv_unsigned sp - 80)) gp tp t0 t1 t2 xs0 xs1
                  (Z_to_bv 64 AQUAR_Q) (Z_to_bv 64 Q_MIN) (Z_to_bv 64 (t + 208)) a3 a4 a5 a6 a7 xs2 xs3 xs4 xs5 xs6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x3f4c8) fc None m' (seg_rom bsegs)
    /\ munch [(bv_unsigned sp - 144, bv_unsigned sp); (shad (hm + 16), shad (hm + 16) + shlen (rup n 8));
              (t + 80, t + 112); (t + 2128, t + 2132); (t + 2784, t + 2792);
              (lst, lst + qsz lst); (ek_b ek lst, ek_b ek lst + 8192);
              (0xd8988, 0xd8988 + 4); (0xd8990, 0xd8990 + 32); (dk_glst g lst, dk_glst g lst + 8)]%Z m m'
    /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo (bv_unsigned sp - 80)
    /\ rw_cells bsegs m' (bv_unsigned sp - 80) (put_frame (Z_to_bv 64 (t + 208)) a3 s6 s5 s4 s3 s2 s1 s0 ra)
    /\ rw_cells bsegs m' (shad (hm + 16)) [CB (Z.to_nat (shlen (rup n 8))) (repeat (Z_to_bv 8 253) (Z.to_nat (shlen (rup n 8))))]
    /\ rw_cells bsegs m' hm [C1 (Z_to_bv 8 3); C1 (Z_to_bv 8 b1); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 (Z_to_bv 64 actx)]
    /\ rw_cells bsegs m' (t + 80) [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]
    /\ ek_post ek t lst hm n m'
    /\ dk_postC g (ek_nb ek nb) (ek_fst ek fst0) (ek_lst ek lst) (qb + ek_delta ek n) m'.

Definition put_torec_stmt : Prop := forall (ek : enq_kind) (g : gqd) (t hm lst : Z) RNG
    ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (n nb fst0 qb b1 actx lo : Z) (sjunk : list byte),
  stk bsegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - 144 ->
  mem_inv bsegs m ->
  a0 = Z_to_bv 64 0xd88f0 -> a1 = Z_to_bv 64 (t + 80) -> a2 = Z_to_bv 64 (t + 208) -> a4 = Z_to_bv 64 hm -> a5 = Z_to_bv 64 n ->
  rw_cells bsegs m 0xd8930 [C8 (Z_to_bv 64 Q_MAX); C8 (Z_to_bv 64 Q_MIN); C8 (Z_to_bv 64 Q_CACHE)] ->
  rw_cells bsegs m 0xd3628 [C8 (Z_to_bv 64 AFLAGS)] ->
  rw_cells bsegs m 0xd94a4 [C4 (Z_to_bv 64 0x1000); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0xbe)] ->
  poison_cells m ->
  rw_cells bsegs m hm [C1 (Z_to_bv 8 3); C1 (Z_to_bv 8 b1); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 (Z_to_bv 64 actx)] ->
  1 <= n <= Q_MAX -> 0 <= b1 < 256 -> hm mod 16 = 0 -> ablk hm (hm + 16 + rup n 8) -> hm + 16 + rup n 8 <= ATOP -> hm + 16 <= ATOP ->
  rw_cells bsegs m (shad (hm + 16)) [CB (Z.to_nat (shlen (rup n 8))) sjunk] ->
  rw_cells bsegs m (t + 80) [C8 (Z_to_bv 64 nb); C8 (Z_to_bv 64 fst0); C8 (Z_to_bv 64 lst); C8 (Z_to_bv 64 qb)] ->
  0 <= nb < 2^62 -> 0 <= qb -> qb + n + 8192 < 2^62 -> 0 <= fst0 < 2^64 -> 0 <= lst < 2^64 ->
  sclr t 4096 -> t + 4096 <= ATOP -> t mod 4096 = 0 -> (hm + 16 <= t \/ t + 4096 <= hm) ->
  ek_pre ek RNG t nb lst n hm m ->
  dk_preC ek g RNG t lst hm (qb + ek_delta ek n) m ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG t 4096 -> rng RNG hm 16 -> rng RNG (shad (hm + 16)) (shlen (rup n 8)) ->
  iclr t 4096 ->
  evtF bsegs RNG (put_torec_post ek g ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a3 F fc t hm n nb fst0 lst qb b1 actx lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x41a1c) fc None m (seg_rom bsegs)).

Definition put_from_refill_torec_stmt : Prop := forall (full : bool) (g : gqd) (t hm lst b : Z) RNG
    (ra sp gp tp s0 s1 a2 a3 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (ra0 t0 t1 t2 a1 a2' a3' a4 a5 a6 a7 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) fc (m : amem) (n nb fst0 qb b1 actx lo nx bsz cnt spacebeg : Z) (maxc csz stj idxw : word) (chunks hs : list word)
    (j0 : list byte),
  let ek := EkNew full nx bsz cnt maxc csz stj idxw chunks spacebeg b hs in
  stk bsegs m lo (bv_unsigned sp + -144) -> ATOP <= lo -> lo <= bv_unsigned sp - 144 ->
  mem_inv bsegs m ->
  a2 = Z_to_bv 64 (t + 208) ->

  rw_cells bsegs m (bv_unsigned sp + -80) [C8 a2; C8 a3; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  rw_cells bsegs m (bv_unsigned sp + -144)
     [CB 8 j0; C8 (Z_to_bv 64 hm); C8 a2; C8 a3; C8 (Z_to_bv 64 n); C8 (Z_to_bv 64 (t + 80)); C8 (Z_to_bv 64 0xd88f0); C8 (Z_to_bv 64 0x41bc0)] ->

  rw_cells bsegs m 0xd8930 [C8 (Z_to_bv 64 Q_MAX); C8 (Z_to_bv 64 Q_MIN); C8 (Z_to_bv 64 Q_CACHE)] ->

  rw_cells bsegs m hm [C1 (Z_to_bv 8 3); C1 (Z_to_bv 8 b1); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 (Z_to_bv 64 actx)] ->
  1 <= n <= Q_MAX -> hm mod 16 = 0 -> ablk hm (hm + 16 + rup n 8) -> hm + 16 + rup n 8 <= ATOP -> hm + 16 <= ATOP ->
  rw_cells bsegs m (shad (hm + 16)) [CB (Z.to_nat (shlen (rup n 8))) (repeat (Z_to_bv 8 253) (Z.to_nat (shlen (rup n 8))))] ->

  rw_cells bsegs m (t + 80) [C8 (Z_to_bv 64 nb); C8 (Z_to_bv 64 fst0); C8 (Z_to_bv 64 lst); C8 (Z_to_bv 64 qb)] ->
  0 <= nb < 2^62 -> 0 <= qb -> qb + n + 8192 < 2^62 -> 0 <= fst0 < 2^64 -> 0 <= lst < 2^64 ->
  sclr t 4096 -> t + 4096 <= ATOP -> t mod 4096 = 0 -> (hm + 16 <= t \/ t + 4096 <= hm) ->

  (if full then 0 < nb /\ rw_cells bsegs m lst [C8 (Z_to_bv 64 nx); C8 (Z_to_bv 64 bsz); C8 (Z_to_bv 64 1021)]
             /\ 0 <= nx < 2^64 /\ 0 <= bsz < 2^64 /\ 0x10007fff8000 <= lst /\ lst + 8192 <= ATOP
             /\ u64arr bsegs m (lst + 24) hs /\ length hs = 1021%nat
             /\ rng RNG lst 8192
   else nb = 0 /\ lst = 0) ->
  rw_cells bsegs m 0xd8638 [C8 (Z_to_bv 64 spacebeg)] ->
  rw_cells bsegs m (t + 2128) [C4 (Z_to_bv 64 cnt); C4 maxc; C8 csz] ->
  u32arr bsegs m (t + 2128 + 16) chunks -> length chunks = 16%nat ->
  0 < cnt <= 16 -> nth_error chunks (Z.to_nat (cnt - 1)) = Some idxw -> bv_unsigned idxw < 2^32 ->
  rw_cells bsegs m (t + 2784) [C8 stj] ->
  b = spacebeg + 24 * 2^32 + 16 * bv_unsigned idxw ->
  (exists bs, rw_cells bsegs m b [CB (Z.to_nat 8192) bs]) ->
  0 < spacebeg -> 0x10007fff8000 <= b -> b + 8192 <= ATOP ->
  (t + 4096 <= b \/ b + 8192 <= t) -> (t + 4096 <= lst \/ lst + 8192 <= t \/ lst = 0) -> (b + 8192 <= lst \/ lst + 8192 <= b) ->
  (hm + 16 <= b \/ b + 8192 <= hm) -> (hm + 16 <= lst \/ lst + 8192 <= hm) ->
  rng RNG b 8192 ->

  dk_preC ek g RNG t lst hm (qb + ek_delta ek n) m ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG t 4096 -> rng RNG hm 16 -> rng RNG (shad (hm + 16)) (shlen (rup n 8)) ->
  iclr t 4096 ->
  evtF bsegs RNG (put_torec_post ek g ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a3 F fc t hm n nb fst0 lst qb b1 actx lo m)
    (MS (mkR ra0 (Z_to_bv 64 (bv_unsigned sp + -144)) gp tp t0 t1 t2 (Z_to_bv 64 (t + 2128)) (Z_to_bv 64 (t + 208))
             (Z_to_bv 64 1) a1 a2' a3' a4 a5 a6 a7
             (Z_to_bv 64 hm) (Z_to_bv 64 (t + 80)) a3 (Z_to_bv 64 n) (Z_to_bv 64 Q_CACHE) s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x41d20) fc None m (seg_rom bsegs)).

Section WithDepot.
Variable DI : ADepotIface.

Definition free_torec_post (L : alayout) (ek : enq_kind) (g : gqd)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (t hm n nb fst0 lst qb b1 actx lo : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists (id : Z) (t0 t1 t2 xs0 xs1 xs2 xs3 xs4 xs5 xs6 ps0 ps1 ps2 ps3 ps4 ps5 spv a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) m' (sj' : list word)
                    (csA csT : list cell) (junk2 : list byte),
    let spP := bv_unsigned sp - 2128 in
    ms' = MS (mkR (Z_to_bv 64 0x41af8) (Z_to_bv 64 (spP - 80)) gp tp t0 t1 t2 xs0 xs1
                  (Z_to_bv 64 AQUAR_Q) (Z_to_bv 64 Q_MIN) (Z_to_bv 64 (t + 208)) a3 a4 a5 a6 a7 xs2 xs3 xs4 xs5 xs6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x3f4c8) fc None m' (seg_rom bsegs)
    /\ munch ([(bv_unsigned sp - 4096, bv_unsigned sp); (0xdce80, 0xdce80 + 0x81030); (0x16b708, 0x16b708 + 4);
               (t + 3168, t + 3169); (hm, hm + 4); (hm + 16, hm + 24); (t + 2800, t + 2800 + 368);
               (ADEPOT_LO, ADEPOT_HI); (al_nodes L, al_nodes L + 1048576); (al_store L, al_store L + 8388608);
               (shad (hm + 16), shad (hm + 16) + shlen (rup n 8)); (t + 80, t + 112); (t + 2128, t + 2132); (t + 2784, t + 2792);
               (lst, lst + qsz lst); (ek_b ek lst, ek_b ek lst + 8192);
               (0xd8988, 0xd8988 + 4); (0xd8990, 0xd8990 + 32); (dk_glst g lst, dk_glst g lst + 8)]%Z) m m'
    /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo (spP - 80)
    /\ 0 < id < 2^31

    /\ rw_cells bsegs m' (spP - 80) (put_frame (Z_to_bv 64 (t + 208)) a3 s6 ps5 ps4 ps3 ps2 ps1 ps0 (Z_to_bv 64 388956))

    /\ rw_cells bsegs m' spP csA /\ cells_size csA = 16%nat
    /\ rw_cells bsegs m' (spP + 16) csT /\ cells_size csT = 2040%nat
    /\ rw_cells bsegs m' (bv_unsigned sp - 72) [C8 spv; CB 8 junk2; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
    /\ rw_cells bsegs m' hm [C1 (Z_to_bv 8 3); C1 (Z_to_bv 8 b1); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 (Z_to_bv 64 actx)]
    /\ rw_cells bsegs m' (hm + 16) [C8 (Z_to_bv 64 id)]
    /\ rw_cells bsegs m' (shad (hm + 16)) [CB (Z.to_nat (shlen (rup n 8))) (repeat (Z_to_bv 8 253) (Z.to_nat (shlen (rup n 8))))]
    /\ rw_cells bsegs m' (t + 80) [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]
    /\ ek_post ek t lst hm n m'
    /\ dk_postC g (ek_nb ek nb) (ek_fst ek fst0) (ek_lst ek lst) (qb + ek_delta ek n) m'
    /\ u64arr bsegs m' (t + 2800) sj' /\ length sj' = 46%nat
    /\ rw_cells bsegs m' (t + 3168) [C1 (Z_to_bv 8 0)]
    /\ rw_cells bsegs m' 0x16b708 [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]
    /\ stk bsegs m' 0xdce80 (0xdce80 + 0x81030)
    /\ (forall j, 0 <= j < 32768 -> bytes_at bsegs m' (0xdce88 + 8 * j) (le8 (Z_to_bv 64 0)))
    /\ ADEPOT DI L m'.

Definition free_torec_stmt : Prop := forall (L : alayout) (ia : bool) (ek : enq_kind) (g : gqd) RNG
    ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem)
    (t ctx hm n b1 actx lo top bot nb fst0 lst qb : Z) (uw : word) (sj : list word) (sjunk : list byte) (trt : list Z),
  stk bsegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - 4096 ->
  mem_inv bsegs m ->
  tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 (hm + 16) ->
  bv_unsigned sp mod 16 = 0 ->
  allocA_cells m ctx t -> poison_cells m ->
  rw_cells bsegs m 0xdc97c [C4 (Z_to_bv 64 30)] ->
  rw_cells bsegs m 0x16d7ca [C1 (Z_to_bv 8 1)] ->
  rw_cells bsegs m 0xd3610 [C8 (Z_to_bv 64 0x16b720)] -> rw_cells bsegs m 0x16b720 [C8 (Z_to_bv 64 4096)] ->
  rw_cells bsegs m 0x16d748 [C8 (Z_to_bv 64 0)] ->
  rw_cells bsegs m 0xd8930 [C8 (Z_to_bv 64 Q_MAX); C8 (Z_to_bv 64 Q_MIN); C8 (Z_to_bv 64 Q_CACHE)] ->
  rw_cells bsegs m 0xd3628 [C8 (Z_to_bv 64 AFLAGS)] ->
  rw_cells bsegs m 0xd94a4 [C4 (Z_to_bv 64 0x1000); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0xbe)] ->
  rw_cells bsegs m 0x16b708 [C1 (Z_to_bv 8 (if ia then 1 else 0)); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] ->
  stk bsegs m 0xdce80 (0xdce80 + 0x81030) ->
  (ia = true -> forall j, 0 <= j < 32768 -> bytes_at bsegs m (0xdce88 + 8 * j) (le8 (Z_to_bv 64 0))) ->
  rw_cells bsegs m (ctx + 8) [C4 (Z_to_bv 64 0)] ->
  rw_cells bsegs m t [C8 (Z_to_bv 64 ctx); C8 (Z_to_bv 64 top); C8 (Z_to_bv 64 bot)] ->
  rw_cells bsegs m (t + 40) [C1 (Z_to_bv 8 0)] -> rw_cells bsegs m (t + 3168) [C1 (Z_to_bv 8 0)] ->
  u64arr bsegs m (t + 2800) sj -> length sj = 46%nat ->
  rw_cells bsegs m (t + 80) [C8 (Z_to_bv 64 nb); C8 (Z_to_bv 64 fst0); C8 (Z_to_bv 64 lst); C8 (Z_to_bv 64 qb)] ->
  0 <= nb < 2^62 -> 0 <= qb -> qb + n + 8192 < 2^62 -> 0 <= fst0 < 2^64 -> 0 <= lst < 2^64 ->
  0 < ctx -> sclr ctx 65536 -> ctx + 4096 <= ATOP ->
  sclr t 4096 -> t + 4096 <= ATOP -> t mod 4096 = 0 -> (ctx + 4096 <= t \/ t + 4096 <= ctx) ->
  rw_cells bsegs m hm [C1 (Z_to_bv 8 2); C1 (Z_to_bv 8 b1); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 (Z_to_bv 64 actx)] ->
  rw_cells bsegs m (hm + 16) [C8 uw] -> 0 <= b1 < 256 -> Z.land b1 3 = 1 -> 1 <= n <= Q_MAX -> hm mod 16 = 0 ->
  ablk hm (hm + 16 + rup n 8) -> hm + 16 + rup n 8 <= ATOP -> hm + 24 <= ATOP ->
  rw_cells bsegs m (shad (hm + 16)) [CB (Z.to_nat (shlen (rup n 8))) sjunk] ->
  (hm + 24 <= t \/ t + 4096 <= hm) -> (hm + 24 <= ctx \/ ctx + 4096 <= hm) ->
  ek_pre ek RNG t nb lst n hm m -> ek_seps ek L hm lst ->
  dk_preC ek g RNG t lst hm (qb + ek_delta ek n) m -> dk_seps g L hm ->
  ADEPOT DI L m ->
  sclr (al_nodes L) 1048576 -> al_nodes L + 1048576 <= ATOP -> sclr (al_store L) 8388608 -> al_store L + 8388608 <= ATOP ->
  (hm + 24 <= al_nodes L \/ al_nodes L + 1048576 <= hm) -> (hm + 24 <= al_store L \/ al_store L + 8388608 <= hm) ->
  (t + 4096 <= al_nodes L \/ al_nodes L + 1048576 <= t) -> (t + 4096 <= al_store L \/ al_store L + 8388608 <= t) ->
  (ctx + 4096 <= al_nodes L \/ al_nodes L + 1048576 <= ctx) -> (ctx + 4096 <= al_store L \/ al_store L + 8388608 <= ctx) ->
  afree_unw RNG lo m top sp s0 ra trt ->
  bv_unsigned s0 <> bv_unsigned sp + 8 ->
  In (AFREE_PC :: trt) (al_U L) ->
  0 <= bot -> bot < bv_unsigned sp -> bot < top -> 4096 <= top <= 2^47 -> 4096 <= bv_unsigned ra -> bv_unsigned ra <> AFREE_PC ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG ctx 4096 -> rng RNG t 4096 ->
  rng RNG (al_nodes L) 1048576 -> rng RNG (al_store L) 8388608 -> rng RNG hm 24 -> rng RNG (shad (hm + 16)) (shlen (rup n 8)) ->
  AIMG_HI <= ctx -> AIMG_HI <= al_nodes L -> AIMG_HI <= al_store L -> iclr t 4096 ->
  evtF bsegs RNG (free_torec_post L ek g ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc t hm n nb fst0 lst qb b1 actx lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 AFREE_SYM) fc None m (seg_rom bsegs)).

Definition free_from_refill_torec_stmt : Prop := forall (L : alayout) (full : bool) (g : gqd) RNG
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (ra0 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) fc (m : amem)
    (t hm n b1 actx lo nb fst0 lst qb nx bsz cnt spacebeg id b : Z) (maxc csz stj idxw : word) (sj tb chunks hs : list word)
    (junk2 j0 : list byte) (trt : list Z),
  let ek := EkNew full nx bsz cnt maxc csz stj idxw chunks spacebeg b hs in
  stk bsegs m lo (bv_unsigned sp + -2272) -> ATOP <= lo -> lo <= bv_unsigned sp - 4096 ->
  mem_inv bsegs m ->

  rw_cells bsegs m (bv_unsigned sp + -2128) [C8 (Z_to_bv 64 (bv_unsigned sp + -2128 + 16)); C4 (Z_to_bv 64 (1 + Z.of_nat (length trt))); C4 (Z_to_bv 64 0)] ->
  u64arr bsegs m (bv_unsigned sp + -2128 + 16) tb -> length tb = 255%nat ->
  rw_cells bsegs m (bv_unsigned sp + -72) [C8 sp; CB 8 junk2; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  rw_cells bsegs m (bv_unsigned sp + -2208)
     [C8 (Z_to_bv 64 (t + 208)); C8 (Z_to_bv 64 (bv_unsigned sp + -2128)); C8 s6; C8 (Z_to_bv 64 (bv_unsigned sp + -81));
      C8 (Z_to_bv 64 (bv_unsigned sp + -2128)); C8 (Z_to_bv 64 1); C8 (Z_to_bv 64 0x5eeec); C8 (Z_to_bv 64 (hm + 16)); C8 sp; C8 (Z_to_bv 64 0x5ef5c)] ->
  rw_cells bsegs m (bv_unsigned sp + -2272)
     [CB 8 j0; C8 (Z_to_bv 64 hm); C8 (Z_to_bv 64 (t + 208)); C8 (Z_to_bv 64 (bv_unsigned sp + -2128)); C8 (Z_to_bv 64 n);
      C8 (Z_to_bv 64 (t + 80)); C8 (Z_to_bv 64 0xd88f0); C8 (Z_to_bv 64 0x41bc0)] ->

  rw_cells bsegs m 0xd8930 [C8 (Z_to_bv 64 Q_MAX); C8 (Z_to_bv 64 Q_MIN); C8 (Z_to_bv 64 Q_CACHE)] ->

  rw_cells bsegs m hm [C1 (Z_to_bv 8 3); C1 (Z_to_bv 8 b1); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 (Z_to_bv 64 actx)] ->
  rw_cells bsegs m (hm + 16) [C8 (Z_to_bv 64 id)] -> 0 < id < 2^31 ->
  1 <= n <= Q_MAX -> hm mod 16 = 0 -> ablk hm (hm + 16 + rup n 8) -> hm + 16 + rup n 8 <= ATOP -> hm + 24 <= ATOP ->
  rw_cells bsegs m (shad (hm + 16)) [CB (Z.to_nat (shlen (rup n 8))) (repeat (Z_to_bv 8 253) (Z.to_nat (shlen (rup n 8))))] ->

  rw_cells bsegs m (t + 80) [C8 (Z_to_bv 64 nb); C8 (Z_to_bv 64 fst0); C8 (Z_to_bv 64 lst); C8 (Z_to_bv 64 qb)] ->
  0 <= nb < 2^62 -> 0 <= qb -> qb + n + 8192 < 2^62 -> 0 <= fst0 < 2^64 -> 0 <= lst < 2^64 ->
  sclr t 4096 -> t + 4096 <= ATOP -> t mod 4096 = 0 -> (hm + 24 <= t \/ t + 4096 <= hm) ->
  u64arr bsegs m (t + 2800) sj -> length sj = 46%nat -> rw_cells bsegs m (t + 3168) [C1 (Z_to_bv 8 0)] ->
  rw_cells bsegs m 0x16b708 [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] ->
  stk bsegs m 0xdce80 (0xdce80 + 0x81030) ->
  (forall j, 0 <= j < 32768 -> bytes_at bsegs m (0xdce88 + 8 * j) (le8 (Z_to_bv 64 0))) ->

  (if full then 0 < nb /\ rw_cells bsegs m lst [C8 (Z_to_bv 64 nx); C8 (Z_to_bv 64 bsz); C8 (Z_to_bv 64 1021)]
             /\ 0 <= nx < 2^64 /\ 0 <= bsz < 2^64 /\ 0x10007fff8000 <= lst /\ lst + 8192 <= ATOP
             /\ u64arr bsegs m (lst + 24) hs /\ length hs = 1021%nat
             /\ rng RNG lst 8192
   else nb = 0 /\ lst = 0) ->
  rw_cells bsegs m 0xd8638 [C8 (Z_to_bv 64 spacebeg)] ->
  rw_cells bsegs m (t + 2128) [C4 (Z_to_bv 64 cnt); C4 maxc; C8 csz] ->
  u32arr bsegs m (t + 2128 + 16) chunks -> length chunks = 16%nat ->
  0 < cnt <= 16 -> nth_error chunks (Z.to_nat (cnt - 1)) = Some idxw -> bv_unsigned idxw < 2^32 ->
  rw_cells bsegs m (t + 2784) [C8 stj] ->
  b = spacebeg + 24 * 2^32 + 16 * bv_unsigned idxw ->
  (exists bs, rw_cells bsegs m b [CB (Z.to_nat 8192) bs]) ->
  0 < spacebeg -> 0x10007fff8000 <= b -> b + 8192 <= ATOP ->
  (t + 4096 <= b \/ b + 8192 <= t) -> (t + 4096 <= lst \/ lst + 8192 <= t \/ lst = 0) -> (b + 8192 <= lst \/ lst + 8192 <= b) ->
  (hm + 24 <= b \/ b + 8192 <= hm) -> (hm + 24 <= lst \/ lst + 8192 <= hm) ->
  rng RNG b 8192 ->
  ek_seps ek L hm lst ->

  dk_preC ek g RNG t lst hm (qb + ek_delta ek n) m -> dk_seps g L hm ->

  ADEPOT DI L m ->
  sclr (al_nodes L) 1048576 -> al_nodes L + 1048576 <= ATOP -> sclr (al_store L) 8388608 -> al_store L + 8388608 <= ATOP ->
  (t + 4096 <= al_nodes L \/ al_nodes L + 1048576 <= t) -> (t + 4096 <= al_store L \/ al_store L + 8388608 <= t) ->
  bv_unsigned sp < 2^47 ->

  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG t 4096 -> rng RNG hm 24 -> rng RNG (shad (hm + 16)) (shlen (rup n 8)) ->
  AIMG_HI <= al_nodes L -> AIMG_HI <= al_store L -> iclr t 4096 ->
  evtF bsegs RNG (free_torec_post L ek g ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc t hm n nb fst0 lst qb b1 actx lo m)
    (MS (mkR ra0 (Z_to_bv 64 (bv_unsigned sp + -2272)) gp tp t0 t1 t2 (Z_to_bv 64 (t + 2128)) (Z_to_bv 64 (t + 208))
             (Z_to_bv 64 1) a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 hm) (Z_to_bv 64 (t + 80)) (Z_to_bv 64 (bv_unsigned sp + -2128)) (Z_to_bv 64 n) (Z_to_bv 64 Q_CACHE)
             s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x41d20) fc None m (seg_rom bsegs)).
End WithDepot.
End CANSEC1.
End F_afreeC_iface.

Module F_adrainC.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase. Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics. Import LinuxProcessSemantics.LinuxProcessSem.MemImageType. Import LinuxProcessSemantics.LinuxProcessSem.State. Import LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude. Import LinuxProcessSemantics.Riscv.Instr. Import LinuxProcessSemantics.Riscv.Decode. Import LinuxProcessSemantics.Riscv.DecodeC. Import LinuxProcessSemantics.Riscv.Sem. Import LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Arr. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.InitMem.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanCtrl.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.BothW.BImg. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ABase.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AQConst.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ABytes.TwinB.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.StepF.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AKit.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AKit2.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AKitQ.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_adrain.TwinB. Import F_afreeC_iface.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Local Ltac band_lin :=
  repeat match goal with H : iclr ?a ?n |- _ => unfold iclr, AIMG_LO, AIMG_HI in H end.

Local Ltac drain_tail MX FR ST sp :=
  step; step; zstep; step; step;
  step;
  apply (rw_C4_to_C1x4 _ _ 1 0 ltac:(lia) ltac:(lia)) in MX;
  step;
  let K3 := fresh "K3" in
  step; step; step; if_cases K3; zify_cond K3; [exfalso; unfold Q_MAX in *; lia|];
  zstep; step; step; zstep; zstep; zstep; zstep; zstep;
  apply (rw_C1x4_to_C4 _ _ 0 0 ltac:(lia) ltac:(lia)) in MX; change (0 + 256 * 0) with 0 in MX;
  amo_step; lits;
  do 4 zstep;
  amo_step;
  step; if_lit;
  zstep; zstep; step; if_lit;
  apply (rw_C4_to_C1x4 _ _ 0 1 ltac:(lia) ltac:(lia)) in MX;
  step;
  do 6 step;
  step;
  release_frame FR ST (bv_unsigned sp);
  unfold drain_torec_post; finish.

Section CANSEC1. Context {rc : runConstT}.
Theorem drain_torec : drain_torec_stmt.
Proof.
  unfold drain_torec_stmt.
  intros until lo. intros ST CEIL LO MI -> -> QC NB QB FST LST MX GC GNB GQB GQ GQ63 GFST GLST QM GFULL T0 T1 RIMG RSTK RT RGL. band_lin.
  unfold AIMG_HI, Q_BATCH_BYTES, Q_MAX, Q_MIN, Q_CACHE, AQUAR_Q, AQ_MUTEX, AQ_GCACHE, AQ_MAX, AINSTANCE in *.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (t + 80, t + 112); (0xd8988, 0xd8988 + 4);
                          (0xd8990, 0xd8990 + 32); (glst, glst + 8)]%Z m) as MU.
  pose proof (wmono_refl bsegs m) as WM.
  word_range sp SPR.
  carve_frame 48%nat ST.
  destruct gfull.
  - destruct GFULL as (GNB1 & GLB & GL0 & GL1 & DTG).
    do 6 step.
    zstep. step. zstep. step.
    apply (rw_C1x4_to_C4 _ _ 0 0 ltac:(lia) ltac:(lia)) in MX. change (0 + 256 * 0) with 0 in MX.
    amo_step. lits.
    do 4 zstep.
    amo_step.
    step. if_lit.
    zstep. step. if_lit.
    zstep. step. if_cases K0; zify_cond K0; [exfalso; lia|].
    step. step. if_cases K1; zify_cond K1; [exfalso; lia|].
    step. step. if_cases K2; zify_cond K2; [exfalso; lia|].
    step. step. step. zstep.
    step. step. step. step.
    step. step. step.
    drain_tail MX FR ST sp.
  - pose proof GFULL as GNB0. clear GFULL.
    do 6 step.
    zstep. step. zstep. step.
    apply (rw_C1x4_to_C4 _ _ 0 0 ltac:(lia) ltac:(lia)) in MX. change (0 + 256 * 0) with 0 in MX.
    amo_step. lits.
    do 4 zstep.
    amo_step.
    step. if_lit.
    zstep. step. if_lit.
    zstep. step. if_cases K0; zify_cond K0; [exfalso; lia|].
    step. step. if_cases K1; zify_cond K1; [exfalso; lia|].
    step. step. if_cases K2; zify_cond K2; [|exfalso; lia].
    step. step. step. step. step. step.
    step. step. step.
    drain_tail MX FR ST sp.
    subst gnb. exact GC.
Qed.
End CANSEC1.
End F_adrainC.

Module F_afree_tailC.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase. Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics. Import LinuxProcessSemantics.LinuxProcessSem.MemImageType. Import LinuxProcessSemantics.LinuxProcessSem.State. Import LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude. Import LinuxProcessSemantics.Riscv.Instr. Import LinuxProcessSemantics.Riscv.Decode. Import LinuxProcessSemantics.Riscv.DecodeC. Import LinuxProcessSemantics.Riscv.Sem. Import LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Arr. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.InitMem.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.StrFun.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanCtrl. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanEmbed.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.BothW.BImg. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ABase.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AQConst.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ABytes.TwinB.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.StepF.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AKit.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AKit2.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AKitQ.TwinB.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_apoison.TwinB.F_apoison.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aenqueue.TwinB.F_aenqueue. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_adrain.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aput.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_afree_tail.TwinB. Import F_afreeC_iface. Import F_adrainC.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Local Lemma outside_In8 : forall (W : list ivl) x lo hi, outside W x -> In (lo, hi) W -> ~ (lo <= x < hi)%Z.
Proof. induction W as [|[a b] W IH]; cbn; intros x lo hi H HI; [tauto|]. destruct HI as [E|HI]; [injection E; intros; subst; tauto| apply (IH x); tauto]. Qed.
Local Lemma sub_fp_cover8 : forall W W' : list ivl,
  Forall (fun iv : ivl => (snd iv <= fst iv)%Z \/ Exists (fun jv : ivl => (fst jv <= fst iv /\ snd iv <= snd jv)%Z) W') W -> sub_fp W W'.
Proof.
  intros W W' HF x HO. induction HF as [|[lo hi] W HP HF IH]; cbn; [exact I|]. split; [| exact IH].
  cbn in HP. destruct HP as [HE|HP]; [lia|]. apply Exists_exists in HP. destruct HP as ([lo' hi'] & HI & [H1 H2]). cbn in H1, H2.
  pose proof (outside_In8 _ _ _ _ HO HI). lia.
Qed.
Local Ltac fp_cheap8 := first [ match goal with Hs : bv_unsigned _ = (bv_unsigned _ + _)%Z |- _ => clear -Hs end | clear ]; Stdlib.micromega.Lia.lia.
Local Ltac fp_find8c := first [ apply Exists_cons_hd; cbn [fst snd]; split; fp_cheap8 | apply Exists_cons_tl; fp_find8c ].
Local Ltac fp_find8 := first [ apply Exists_cons_hd; cbn [fst snd]; split; lia | apply Exists_cons_tl; fp_find8 ].
Local Ltac fp_cover8 := apply sub_fp_cover8; repeat (apply Forall_cons; [ cbn [fst snd]; first [left; fp_cheap8 | right; fp_find8c | right; fp_find8] | ]); apply Forall_nil.

Local Ltac transport_after_call segs m m' MU WM ::=
  let W := lazymatch type of MU with munch ?W _ _ => W end in
  repeat match goal with
  | H : bytes_at segs m ?A2 ?bs2 |- _ =>
      first [ apply (bytes_at_transport segs W m m' A2 bs2) in H; [ | exact MU | cbn [disjoint_from]; simpl_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : wr_at segs m ?A2 ?n2 |- _ => apply (wr_at_transport segs m m' A2 n2) in H; [ | exact WM ]
  | H : rw_cells segs m ?A2 ?cs2 |- _ =>
      first [ apply (rw_cells_transport segs W m m' A2 cs2) in H; [ | exact MU | exact WM | cbn [disjoint_from]; simpl_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : ro_cells segs m ?A2 ?cs2 |- _ =>
      first [ apply (ro_cells_transport segs W m m' A2 cs2) in H; [ | exact MU | cbn [disjoint_from]; simpl_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : u8arr segs m ?A2 ?xs |- _ =>
      first [ apply (u8arr_transport segs W m m' A2 xs) in H; [ | exact MU | exact WM | cbn [disjoint_from]; simpl_sizes; simpl_arr_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : u32arr segs m ?A2 ?xs |- _ =>
      first [ apply (u32arr_transport segs W m m' A2 xs) in H; [ | exact MU | exact WM | cbn [disjoint_from]; simpl_sizes; simpl_arr_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : u64arr segs m ?A2 ?xs |- _ =>
      first [ apply (u64arr_transport segs W m m' A2 xs) in H; [ | exact MU | exact WM | cbn [disjoint_from]; simpl_sizes; simpl_arr_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : u8ro segs m ?A2 ?xs |- _ =>
      first [ apply (u8ro_transport segs W m m' A2 xs) in H; [ | exact MU | cbn [disjoint_from]; simpl_sizes; simpl_arr_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : stk segs m ?loq ?hiq |- _ =>
      first [ apply (stk_transport_disjoint segs W m m' loq hiq) in H; [ | exact MU | exact WM | cbn [disjoint_from]; slia ]
            | clear H ]
  | H : munch ?Wq ?mq m |- _ =>
      first [ apply (munch_trans Wq mq m m') in H; [ | eapply (munch_weaken W Wq m m'); [ first [ fp_cover8 | unfold sub_fp; cbn [outside]; first [ match goal with Hs : bv_unsigned _ = bv_unsigned _ + _ |- _ => clear -Hs; intros; lia end | clear; intros; lia | intros; slia ] ] | exact MU ] ]
            | fail 100 "callee footprint not inside caller footprint" ]
  | H : wmono segs ?mq m |- _ => apply (wmono_trans segs mq m m') in H; [ | exact WM ]
  end.

Ltac ub H := let X := fresh "Y" in pose proof H as X; unbox X.

Local Ltac band_lin :=
  repeat match goal with H : iclr ?a ?n |- _ => unfold iclr, AIMG_LO, AIMG_HI in H end.
Local Ltac with_band H tac :=
  let H' := fresh H in pose proof H as H'; unfold sclr, iclr, ablk, KLS, AIMG_LO, AIMG_HI in H'; tac; try clear H'.
Local Ltac with_sclr tac := idtac; match goal with H : sclr ?a ?n |- _ => with_band H tac | _ => tac end.
Local Ltac iclr_of H := clear -H; unfold iclr, AIMG_LO, AIMG_HI in *; lia.

Local Lemma sclr_int : forall a n, sclr a n -> 0 <= a -> a + n <= 18446744073709551616 ->
  exists k, 0 <= k <= 1 /\ a + n <= 2147446784 + k * 18446744073709551616 /\ 17594333495296 * k <= a.
Proof. intros a n H G1 G2. unfold sclr, KLS in H. destruct H; [exists 0 | exists 1]; lia. Qed.
Local Lemma iclr_int : forall a n, iclr a n -> a + n <= 18446744073709551616 ->
  exists k, 0 <= k <= 1 /\ 4096 <= a /\ a + n <= 65536 + k * 18446744073709551616 /\ 6492160 * k <= a.
Proof. intros a n H G2. unfold iclr, AIMG_LO, AIMG_HI in H. destruct H as [? [?|?]]; [exists 0 | exists 1]; lia. Qed.
Local Lemma ablk_int {rc : runConstT} : forall lo hi, ablk lo hi ->
  exists k, 0 <= k <= 1 /\ 6492160 <= lo /\ 17594333495296 * k <= lo /\ hi <= 2147446784 + k * 18446744073709551616 /\ hi <= ATOP.
Proof. intros lo hi H. unfold ablk, KLS, AIMG_HI in H. pose proof atop_range. destruct H as [[? ?]|[? ?]]; [exists 0 | exists 1]; lia. Qed.
Local Ltac band_int H :=
  let k := fresh "k" H in let A := fresh "KA" H in let B := fresh "KB" H in let C := fresh "KC" H in let D := fresh "KD" H in
  let G1 := fresh "G" in let G2 := fresh "G" in
  lazymatch type of H with
  | sclr ?a ?n =>
      assert (G1 : 0 <= a) by (atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia); assert (G2 : a + n <= 18446744073709551616) by (atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia);
      destruct (sclr_int a n H G1 G2) as (k & A & B & C); clear G1 G2
  | iclr ?a ?n =>
      assert (G2 : a + n <= 18446744073709551616) by (atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia);
      destruct (iclr_int a n H G2) as (k & A & B & C & D); clear G2
  | 4096 <= ?a /\ (?a + ?n <= _ \/ _ <= ?a) =>
      assert (G2 : a + n <= 18446744073709551616) by (atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia);
      destruct (iclr_int a n H G2) as (k & A & B & C & D); clear G2
  | ablk ?lo ?hi => let E := fresh "KE" H in destruct (ablk_int lo hi H) as (k & A & B & E & C & D)
  end.

Section CANSEC1. Context {rc : runConstT}.
Theorem put_torec : put_torec_stmt.
Proof.
  unfold put_torec_stmt.
  intros until sjunk. intros ST CEIL LO MI -> -> -> -> -> QK GF FLG PC HD N B1 AL HLO HHI HCE SH QC NB QB QBN FST LST T0 T1 TAL DHT EK DK RIMG RSTK RT RH RSH TI.
  band_int TI. pose proof (ablk_lin _ _ HLO) as (HL1 & HL2 & HL3 & HL4). unfold AIMG_HI in HL1. band_int HLO. band_lin. band_int T0.
  assert (SHB : 2148262400 <= shad (hm + 16) /\ shad (hm + 16) + shlen (rup n 8) <= 0x10007fff8000).
  { unfold shad, shlen, ASHOFF. rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8. unfold Q_MAX in N. Z.div_mod_to_equations. lia. }
  assert (RUP : n <= rup n 8 <= n + 7 /\ rup n 8 mod 8 = 0) by (unfold rup; Z.div_mod_to_equations; lia).
  assert (SHL : 0 < shlen (rup n 8) < 0x10000000) by (unfold shlen; rewrite Z.shiftr_div_pow2 by lia; unfold Q_MAX in N; Z.div_mod_to_equations; lia).
  word_range sp SPR.
  pose proof (munch_refl [(bv_unsigned sp - 144, bv_unsigned sp); (shad (hm + 16), shad (hm + 16) + shlen (rup n 8));
              (t + 80, t + 112); (t + 2128, t + 2132); (t + 2784, t + 2792);
              (lst, lst + qsz lst); (ek_b ek lst, ek_b ek lst + 8192);
              (0xd8988, 0xd8988 + 4); (0xd8990, 0xd8990 + 32); (dk_glst g lst, dk_glst g lst + 8)]%Z m) as MU.
  pose proof (wmono_refl bsegs m) as WM.
  destruct PC as (P1 & P2 & P3 & P4 & P5 & P6 & P7).
  box DHT.

  destruct ek as [nx bsz cnt hs cnt24' maxc' csz' stj' | full nx bsz cnt24 maxc csz stj idxw chunks spacebeg b hs0];
  [ destruct EK as (NB1 & LB & CNT & BSZ & BSZN & NX & LA & LEN & [junkt LJ] & L0 & L1 & DTL & DHL & CR' & STS' & RL); box DTL; box DHL
  | destruct EK as (FULL & SB & CR & CH & LCH & CNT & NTH & IXS & STS & HB & [junkb BJ] & SBP & B0 & BL1 & DTB & DTL & DBL & DHB & DHL & RB);
    box DTB; box DTL; box DBL; box DHB; box DHL;
    destruct full; [destruct FULL as (NB1 & LB & NX & BSZ & L0 & L1 & LA0 & LEN0 & RL) | destruct FULL as [NB0 LST0]] ];
  unfold dk_glst in *; cbn [ek_pre dk_preC ek_b ek_nb ek_fst ek_lst ek_delta] in *;
  destruct DK as (EGD & MX & GC & GNB & GQB & GFST & GLST & QB1 & GQ & GQ63 & GFULL);
  (destruct (g_full g) eqn:EGF;
     [destruct GFULL as (G1 & GLB & G3 & G4 & G5 & G6 & G7 & G8 & G9); box G5; box G6; box G7; box G8 | destruct GFULL as [GNB0 GLST0]]);
  rewrite ?EGD in *; cbn [ek_pre dk_preC ek_b ek_nb ek_fst ek_lst ek_delta dk_glst] in *; unfold AIMG_HI in *.
  all: first [assert (QZE : qsz lst = 8192) by (apply qsz_pos; generalize L0; clear; intros; lia) | assert (QZE : qsz lst = 8) by (apply qsz_eq0; exact LST0)]; rewrite QZE in *.
  -
    box ST.
    call (putA_spec t hm n); try unboxed ST; try eassumption; try reflexivity; try (unfold Q_MAX, AIMG_HI in *; lia).
    try clear ST.
    rename POST into FRP.
    match goal with H : stk bsegs ?mm lo _ |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename H into ST end. try rename MI0 into MI.
    box SH.
    box ST.
    step. call_sp (poison_shadow_spec RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ (hm + 16) (rup n 8) 253 lo sjunk);
      [unboxed ST| exact CEIL| lia| exact MI| repeat (split; [assumption|]); assumption| reflexivity| reflexivity| reflexivity
      | Z.div_mod_to_equations; lia| lia| lia| first [assumption | (eapply ablk_sub; [exact HLO| clear; lia| clear; lia]) | unfold ablk; right; lia | unfold ablk; left; lia]| lia| lia| lia| unboxed SH|].
    try clear ST.
    clear SH.
    try rename MI0 into MI. clear P1 P2 P3 P4 P5 P6 P7.
    match goal with H : stk bsegs ?mm lo _ |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename H into ST end.
    match goal with H : rw_cells bsegs ?mm (shad (hm + 16)) _ |- _ => rename H into SH' end.
    do 5 step.
    step.
    box HD. box SH'. box GLB. box CR'. box STS'.
    snapshot [(bv_unsigned sp + -80 - 64, bv_unsigned sp + -80); (t + 80 + 24, t + 80 + 32); (lst + 8, lst + 24); (lst + 24 + 8 * cnt, lst + 24 + 8 * cnt + 8)]%Z MUe WMe.
    box LJ. box LB. box QC. box LA.
    box ST.
    call_sp (enqueue_append_spec (t + 80) lst cnt RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ nb fst0 qb hm n nx bsz lo hs);
      [unboxed ST| exact CEIL| lia| exact MI| reflexivity| reflexivity| reflexivity| unboxed QC| lia| lia| unfold Q_MAX in *; lia| lia| lia| lia
      | unboxed LB| exact CNT| lia| unfold Q_MAX in *; lia| lia| unboxed LA| exact LEN| exists junkt; unboxed LJ
      | iclr_of TI| atop_facts; lia| unfold AIMG_HI; lia| unfold Q_BATCH_BYTES; lia| ub DTL; unfold Q_BATCH_BYTES; lia|].
    try clear ST.
    clear LJ LB QC LA.
    try rename MI0 into MI.
    match goal with H : stk bsegs ?mm lo _ |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename H into ST end.
    carry HD MUe WMe ltac:(ub DHT; ub DHL; lia). carry SH' MUe WMe ltac:(lia). carry GLB MUe WMe ltac:(ub G5; ub G7; lia). carry CR' MUe WMe ltac:(ub DTL; lia). carry STS' MUe WMe ltac:(ub DTL; lia). clear MUe WMe.
    rename POST into LJ'. rename PC1 into LB'. rename PC2 into LA'. rename PC0 into QC'. destruct LJ' as [junkt' LJ'].

    step.
    step. if_cases KD; zify_cond KD; [|exfalso; unfold Q_CACHE in *; lia].
    step. step. step. step.
    box HD.  box LB'. box LA'. box LJ'. box CR'. box STS'.
    snapshot [(bv_unsigned sp + -80 - 48, bv_unsigned sp + -80); (t + 80, t + 112); (0xd8988, 0xd8988 + 4); (0xd8990, 0xd8990 + 32); (g_lst g, g_lst g + 8)]%Z MUd WMd.
    box QC'. box GLB. box GC. box MX.
    box ST.
    step. call_sp (drain_torec true t (g_lst g) RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ nb fst0 lst (qb + n) (g_nb g) (g_fst g) (g_qb g) (g_nx g) lo);
      [unboxed ST| exact CEIL| lia| exact MI| reflexivity| reflexivity| unboxed QC'| lia| lia| lia| lia| unboxed MX| unboxed GC| lia| lia| unfold Q_MAX in *; lia| unfold Q_MAX in *; lia| lia| lia
      | exact QK| split; [lia|]; split; [unboxed GLB|]; unfold AIMG_HI, Q_BATCH_BYTES; repeat split; try lia; ub G5; lia| exact TI| atop_facts; lia|].
    try clear ST.
    clear QC' GLB GC MX.
    try rename MI0 into MI.
    match goal with H : stk bsegs ?mm lo _ |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename H into ST end.
    carry HD MUd WMd ltac:(ub DHT; ub G6; lia). carry LB' MUd WMd ltac:(ub DTL; first [ub G7 | pose proof GLST0]; lia). carry LA' MUd WMd ltac:(rewrite length_app, LEN; cbn [length]; ub DTL; first [ub G7 | pose proof GLST0]; lia). carry LJ' MUd WMd ltac:(ub DTL; first [ub G7 | pose proof GLST0]; lia). carry CR' MUd WMd ltac:(first [ub G5 | pose proof GLST0]; lia). carry STS' MUd WMd ltac:(first [ub G5 | pose proof GLST0]; lia). clear MUd WMd.
    unfold put_torec_post. rewrite ?QZE. unfold put_frame, dk_postC, dk_glst. rewrite ?EGD. rewrite ?EGF. cbn [ek_post ek_nb ek_fst ek_lst ek_delta ek_b]. finish.
    all: try assumption. all: try exact I. all: try (lazymatch goal with |- exists _, rw_cells _ ?mq ?Aq _ => match goal with Hq : rw_cells _ mq Aq _ |- _ => eexists; exact Hq end end).      all: try (eexists; eassumption).
  -
    box ST.
    call (putA_spec t hm n); try unboxed ST; try eassumption; try reflexivity; try (unfold Q_MAX, AIMG_HI in *; lia).
    try clear ST.
    rename POST into FRP.
    match goal with H : stk bsegs ?mm lo _ |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename H into ST end. try rename MI0 into MI.
    box SH.
    box ST.
    step. call_sp (poison_shadow_spec RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ (hm + 16) (rup n 8) 253 lo sjunk);
      [unboxed ST| exact CEIL| lia| exact MI| repeat (split; [assumption|]); assumption| reflexivity| reflexivity| reflexivity
      | Z.div_mod_to_equations; lia| lia| lia| first [assumption | (eapply ablk_sub; [exact HLO| clear; lia| clear; lia]) | unfold ablk; right; lia | unfold ablk; left; lia]| lia| lia| lia| unboxed SH|].
    try clear ST.
    clear SH.
    try rename MI0 into MI. clear P1 P2 P3 P4 P5 P6 P7.
    match goal with H : stk bsegs ?mm lo _ |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename H into ST end.
    match goal with H : rw_cells bsegs ?mm (shad (hm + 16)) _ |- _ => rename H into SH' end.
    do 5 step.
    step.
    box HD. box SH'. box CR'. box STS'.
    snapshot [(bv_unsigned sp + -80 - 64, bv_unsigned sp + -80); (t + 80 + 24, t + 80 + 32); (lst + 8, lst + 24); (lst + 24 + 8 * cnt, lst + 24 + 8 * cnt + 8)]%Z MUe WMe.
    box LJ. box LB. box QC. box LA.
    box ST.
    call_sp (enqueue_append_spec (t + 80) lst cnt RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ nb fst0 qb hm n nx bsz lo hs);
      [unboxed ST| exact CEIL| lia| exact MI| reflexivity| reflexivity| reflexivity| unboxed QC| lia| lia| unfold Q_MAX in *; lia| lia| lia| lia
      | unboxed LB| exact CNT| lia| unfold Q_MAX in *; lia| lia| unboxed LA| exact LEN| exists junkt; unboxed LJ
      | iclr_of TI| atop_facts; lia| unfold AIMG_HI; lia| unfold Q_BATCH_BYTES; lia| ub DTL; unfold Q_BATCH_BYTES; lia|].
    try clear ST.
    clear LJ LB QC LA.
    try rename MI0 into MI.
    match goal with H : stk bsegs ?mm lo _ |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename H into ST end.
    carry HD MUe WMe ltac:(ub DHT; ub DHL; lia). carry SH' MUe WMe ltac:(lia). carry CR' MUe WMe ltac:(ub DTL; lia). carry STS' MUe WMe ltac:(ub DTL; lia). clear MUe WMe.
    rename POST into LJ'. rename PC1 into LB'. rename PC2 into LA'. rename PC0 into QC'. destruct LJ' as [junkt' LJ'].

    step.
    step. if_cases KD; zify_cond KD; [|exfalso; unfold Q_CACHE in *; lia].
    step. step. step. step.
    box HD.  box LB'. box LA'. box LJ'. box CR'. box STS'.
    snapshot [(bv_unsigned sp + -80 - 48, bv_unsigned sp + -80); (t + 80, t + 112); (0xd8988, 0xd8988 + 4); (0xd8990, 0xd8990 + 32); (g_lst g, g_lst g + 8)]%Z MUd WMd.
    box QC'. box GC. box MX.
    box ST.
    step. call_sp (drain_torec false t (g_lst g) RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ nb fst0 lst (qb + n) (g_nb g) (g_fst g) (g_qb g) (g_nx g) lo);
      [unboxed ST| exact CEIL| lia| exact MI| reflexivity| reflexivity| unboxed QC'| lia| lia| lia| lia| unboxed MX| unboxed GC| lia| lia| unfold Q_MAX in *; lia| unfold Q_MAX in *; lia| lia| lia
      | exact QK| exact GNB0| exact TI| atop_facts; lia| exact I|].
    try clear ST.
    clear QC' GC MX.
    try rename MI0 into MI.
    match goal with H : stk bsegs ?mm lo _ |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename H into ST end.
    carry HD MUd WMd ltac:(ub DHT;  lia). carry LB' MUd WMd ltac:(ub DTL; first [ub G7 | pose proof GLST0]; lia). carry LA' MUd WMd ltac:(rewrite length_app, LEN; cbn [length]; ub DTL; first [ub G7 | pose proof GLST0]; lia). carry LJ' MUd WMd ltac:(ub DTL; first [ub G7 | pose proof GLST0]; lia). carry CR' MUd WMd ltac:(first [ub G5 | pose proof GLST0]; lia). carry STS' MUd WMd ltac:(first [ub G5 | pose proof GLST0]; lia). clear MUd WMd.
    unfold put_torec_post. rewrite ?QZE. unfold put_frame, dk_postC, dk_glst. rewrite ?EGD. rewrite ?EGF. cbn [ek_post ek_nb ek_fst ek_lst ek_delta ek_b]. finish.
    all: try assumption. all: try exact I. all: try (lazymatch goal with |- exists _, rw_cells _ ?mq ?Aq _ => match goal with Hq : rw_cells _ mq Aq _ |- _ => eexists; exact Hq end end).      all: try (eexists; eassumption).
  -
    box ST.
    call (putA_spec t hm n); try unboxed ST; try eassumption; try reflexivity; try (unfold Q_MAX, AIMG_HI in *; lia).
    try clear ST.
    rename POST into FRP.
    match goal with H : stk bsegs ?mm lo _ |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename H into ST end. try rename MI0 into MI.
    box SH.
    box ST.
    step. call_sp (poison_shadow_spec RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ (hm + 16) (rup n 8) 253 lo sjunk);
      [unboxed ST| exact CEIL| lia| exact MI| repeat (split; [assumption|]); assumption| reflexivity| reflexivity| reflexivity
      | Z.div_mod_to_equations; lia| lia| lia| first [assumption | (eapply ablk_sub; [exact HLO| clear; lia| clear; lia]) | unfold ablk; right; lia | unfold ablk; left; lia]| lia| lia| lia| unboxed SH|].
    try clear ST.
    clear SH.
    try rename MI0 into MI. clear P1 P2 P3 P4 P5 P6 P7.
    match goal with H : stk bsegs ?mm lo _ |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename H into ST end.
    match goal with H : rw_cells bsegs ?mm (shad (hm + 16)) _ |- _ => rename H into SH' end.
    do 5 step.
    step.
    box HD. box CH. box SH'. box GLB. box LA0.
    snapshot [(bv_unsigned sp + -80 - 64, bv_unsigned sp + -80); (t + 80, t + 112); (t + 2128, t + 2128 + 4); (t + 2784, t + 2784 + 8); (lst, lst + 8); (b, b + 8192)]%Z MUe WMe.
    box BJ. box STS. box CR. box LB. box QC.
    box ST.
    call_sp (enqueue_new_spec true t lst b RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ nb fst0 qb hm n nx bsz cnt24 spacebeg lo maxc csz stj idxw chunks);
      [unboxed ST| exact CEIL| lia| exact MI| reflexivity| reflexivity| reflexivity| reflexivity| unboxed QC| lia| lia| unfold Q_BATCH_BYTES, Q_MAX in *; lia
      | lia| lia| lia| lia
      | split; [lia|]; split; [unboxed LB|]; unfold AIMG_HI, Q_BATCH_BYTES; repeat split; try assumption; lia
      | exact SB| unboxed CR| ub CH; exact Y| exact LCH| exact CNT| exact NTH| exact IXS| unboxed STS| unfold K_BATCH_CLASS; lia| exists junkb; unboxed BJ
      | exact TI| atop_facts; lia| exact TAL| lia| unfold AIMG_HI; lia| unfold Q_BATCH_BYTES; lia
      | ub DTB; unfold Q_BATCH_BYTES; lia| ub DTL; unfold Q_BATCH_BYTES; lia| ub DBL; unfold Q_BATCH_BYTES; lia|].
    try clear ST.
    clear BJ STS CR LB QC.
    try rename MI0 into MI.
    match goal with H : stk bsegs ?mm lo _ |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename H into ST end.
    carry HD MUe WMe ltac:(ub DHT; ub DHL; ub DHB; lia). carry CH MUe WMe ltac:(rewrite LCH; ub DTL; ub DTB; lia). carry SH' MUe WMe ltac:(lia). carry LA0 MUe WMe ltac:(rewrite LEN0; ub DTL; ub DBL; lia). carry GLB MUe WMe ltac:(ub G5; ub G7; ub G8; lia). clear MUe WMe.
    rename PC0 into QC'. destruct PC2 as [stj' STS']. destruct PC5 as [junkb' PC5].

    step.
    step. if_cases KD; zify_cond KD; [|exfalso; unfold Q_CACHE in *; lia].
    step. step. step. step.
    box HD.  box PC3. box PC4. box PC5. box POST. box PC1. box STS'. box LA0.
    snapshot [(bv_unsigned sp + -80 - 48, bv_unsigned sp + -80); (t + 80, t + 112); (0xd8988, 0xd8988 + 4); (0xd8990, 0xd8990 + 32); (g_lst g, g_lst g + 8)]%Z MUd WMd.
    box QC'. box GLB. box GC. box MX. box CH.
    box ST.
    step. call_sp (drain_torec true t (g_lst g) RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ (nb + 1) fst0 b (qb + (n + 8192)) (g_nb g) (g_fst g) (g_qb g) (g_nx g) lo);
      [unboxed ST| exact CEIL| lia| exact MI| reflexivity| reflexivity| unboxed QC'| lia| lia| lia| lia| unboxed MX| unboxed GC| lia| lia| unfold Q_MAX in *; lia| unfold Q_MAX in *; lia| lia| lia
      | exact QK| split; [lia|]; split; [unboxed GLB|]; unfold AIMG_HI, Q_BATCH_BYTES; repeat split; try lia; ub G5; lia| exact TI| atop_facts; lia|].
    try clear ST.
    clear QC' GLB GC MX CH.
    try rename MI0 into MI.
    match goal with H : stk bsegs ?mm lo _ |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename H into ST end.
    carry HD MUd WMd ltac:(ub DHT; ub G6; lia). carry PC3 MUd WMd ltac:(ub DTB; first [ub G8 | pose proof GLST0]; lia). carry PC4 MUd WMd ltac:(cbn [length]; ub DTB; first [ub G8 | pose proof GLST0]; lia). carry PC5 MUd WMd ltac:(ub DTB; first [ub G8 | pose proof GLST0]; lia). carry POST MUd WMd ltac:(ub DTL; first [ub G7 | pose proof GLST0]; lia). carry PC1 MUd WMd ltac:(first [ub G5 | pose proof GLST0]; lia). carry STS' MUd WMd ltac:(first [ub G5 | pose proof GLST0]; lia). carry LA0 MUd WMd ltac:(rewrite LEN0; ub DTL; first [ub G7 | pose proof GLST0]; lia). clear MUd WMd.
    unfold put_torec_post. rewrite ?QZE. unfold put_frame, dk_postC, dk_glst. rewrite ?EGD. rewrite ?EGF. cbn [ek_post ek_nb ek_fst ek_lst ek_delta ek_b]. finish.
    all: try assumption. all: try exact I. all: try (lazymatch goal with |- exists _, rw_cells _ ?mq ?Aq _ => match goal with Hq : rw_cells _ mq Aq _ |- _ => eexists; exact Hq end end).      all: try (eexists; eassumption).
  -
    box ST.
    call (putA_spec t hm n); try unboxed ST; try eassumption; try reflexivity; try (unfold Q_MAX, AIMG_HI in *; lia).
    try clear ST.
    rename POST into FRP.
    match goal with H : stk bsegs ?mm lo _ |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename H into ST end. try rename MI0 into MI.
    box SH.
    box ST.
    step. call_sp (poison_shadow_spec RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ (hm + 16) (rup n 8) 253 lo sjunk);
      [unboxed ST| exact CEIL| lia| exact MI| repeat (split; [assumption|]); assumption| reflexivity| reflexivity| reflexivity
      | Z.div_mod_to_equations; lia| lia| lia| first [assumption | (eapply ablk_sub; [exact HLO| clear; lia| clear; lia]) | unfold ablk; right; lia | unfold ablk; left; lia]| lia| lia| lia| unboxed SH|].
    try clear ST.
    clear SH.
    try rename MI0 into MI. clear P1 P2 P3 P4 P5 P6 P7.
    match goal with H : stk bsegs ?mm lo _ |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename H into ST end.
    match goal with H : rw_cells bsegs ?mm (shad (hm + 16)) _ |- _ => rename H into SH' end.
    do 5 step.
    step.
    box HD. box CH. box SH'. box LA0.
    snapshot [(bv_unsigned sp + -80 - 64, bv_unsigned sp + -80); (t + 80, t + 112); (t + 2128, t + 2128 + 4); (t + 2784, t + 2784 + 8); (lst, lst + 8); (b, b + 8192)]%Z MUe WMe.
    box BJ. box STS. box CR. box LB. box QC.
    box ST.
    call_sp (enqueue_new_spec true t lst b RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ nb fst0 qb hm n nx bsz cnt24 spacebeg lo maxc csz stj idxw chunks);
      [unboxed ST| exact CEIL| lia| exact MI| reflexivity| reflexivity| reflexivity| reflexivity| unboxed QC| lia| lia| unfold Q_BATCH_BYTES, Q_MAX in *; lia
      | lia| lia| lia| lia
      | split; [lia|]; split; [unboxed LB|]; unfold AIMG_HI, Q_BATCH_BYTES; repeat split; try assumption; lia
      | exact SB| unboxed CR| ub CH; exact Y| exact LCH| exact CNT| exact NTH| exact IXS| unboxed STS| unfold K_BATCH_CLASS; lia| exists junkb; unboxed BJ
      | exact TI| atop_facts; lia| exact TAL| lia| unfold AIMG_HI; lia| unfold Q_BATCH_BYTES; lia
      | ub DTB; unfold Q_BATCH_BYTES; lia| ub DTL; unfold Q_BATCH_BYTES; lia| ub DBL; unfold Q_BATCH_BYTES; lia|].
    try clear ST.
    clear BJ STS CR LB QC.
    try rename MI0 into MI.
    match goal with H : stk bsegs ?mm lo _ |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename H into ST end.
    carry HD MUe WMe ltac:(ub DHT; ub DHL; ub DHB; lia). carry CH MUe WMe ltac:(rewrite LCH; ub DTL; ub DTB; lia). carry SH' MUe WMe ltac:(lia). carry LA0 MUe WMe ltac:(rewrite LEN0; ub DTL; ub DBL; lia). clear MUe WMe.
    rename PC0 into QC'. destruct PC2 as [stj' STS']. destruct PC5 as [junkb' PC5].

    step.
    step. if_cases KD; zify_cond KD; [|exfalso; unfold Q_CACHE in *; lia].
    step. step. step. step.
    box HD.  box PC3. box PC4. box PC5. box POST. box PC1. box STS'. box LA0.
    snapshot [(bv_unsigned sp + -80 - 48, bv_unsigned sp + -80); (t + 80, t + 112); (0xd8988, 0xd8988 + 4); (0xd8990, 0xd8990 + 32); (g_lst g, g_lst g + 8)]%Z MUd WMd.
    box QC'. box GC. box MX.
    box ST.
    step. call_sp (drain_torec false t (g_lst g) RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ (nb + 1) fst0 b (qb + (n + 8192)) (g_nb g) (g_fst g) (g_qb g) (g_nx g) lo);
      [unboxed ST| exact CEIL| lia| exact MI| reflexivity| reflexivity| unboxed QC'| lia| lia| lia| lia| unboxed MX| unboxed GC| lia| lia| unfold Q_MAX in *; lia| unfold Q_MAX in *; lia| lia| lia
      | exact QK| exact GNB0| exact TI| atop_facts; lia| exact I|].
    try clear ST.
    clear QC' GC MX.
    try rename MI0 into MI.
    match goal with H : stk bsegs ?mm lo _ |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename H into ST end.
    carry HD MUd WMd ltac:(ub DHT;  lia). carry PC3 MUd WMd ltac:(ub DTB; first [ub G8 | pose proof GLST0]; lia). carry PC4 MUd WMd ltac:(cbn [length]; ub DTB; first [ub G8 | pose proof GLST0]; lia). carry PC5 MUd WMd ltac:(ub DTB; first [ub G8 | pose proof GLST0]; lia). carry POST MUd WMd ltac:(ub DTL; first [ub G7 | pose proof GLST0]; lia). carry PC1 MUd WMd ltac:(first [ub G5 | pose proof GLST0]; lia). carry STS' MUd WMd ltac:(first [ub G5 | pose proof GLST0]; lia). carry LA0 MUd WMd ltac:(rewrite LEN0; ub DTL; first [ub G7 | pose proof GLST0]; lia). clear MUd WMd.
    unfold put_torec_post. rewrite ?QZE. unfold put_frame, dk_postC, dk_glst. rewrite ?EGD. rewrite ?EGF. cbn [ek_post ek_nb ek_fst ek_lst ek_delta ek_b]. finish.
    all: try assumption. all: try exact I. all: try (lazymatch goal with |- exists _, rw_cells _ ?mq ?Aq _ => match goal with Hq : rw_cells _ mq Aq _ |- _ => eexists; exact Hq end end).      all: try (eexists; eassumption).
  -
    box ST.
    call (putA_spec t hm n); try unboxed ST; try eassumption; try reflexivity; try (unfold Q_MAX, AIMG_HI in *; lia).
    try clear ST.
    rename POST into FRP.
    match goal with H : stk bsegs ?mm lo _ |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename H into ST end. try rename MI0 into MI.
    box SH.
    box ST.
    step. call_sp (poison_shadow_spec RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ (hm + 16) (rup n 8) 253 lo sjunk);
      [unboxed ST| exact CEIL| lia| exact MI| repeat (split; [assumption|]); assumption| reflexivity| reflexivity| reflexivity
      | Z.div_mod_to_equations; lia| lia| lia| first [assumption | (eapply ablk_sub; [exact HLO| clear; lia| clear; lia]) | unfold ablk; right; lia | unfold ablk; left; lia]| lia| lia| lia| unboxed SH|].
    try clear ST.
    clear SH.
    try rename MI0 into MI. clear P1 P2 P3 P4 P5 P6 P7.
    match goal with H : stk bsegs ?mm lo _ |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename H into ST end.
    match goal with H : rw_cells bsegs ?mm (shad (hm + 16)) _ |- _ => rename H into SH' end.
    do 5 step.
    step.
    box HD. box CH. box SH'. box GLB.
    snapshot [(bv_unsigned sp + -80 - 64, bv_unsigned sp + -80); (t + 80, t + 112); (t + 2128, t + 2128 + 4); (t + 2784, t + 2784 + 8); (lst, lst + 8); (b, b + 8192)]%Z MUe WMe.
    box BJ. box STS. box CR. box QC.
    box ST.
    call_sp (enqueue_new_spec false t lst b RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ nb fst0 qb hm n nx bsz cnt24 spacebeg lo maxc csz stj idxw chunks);
      [unboxed ST| exact CEIL| lia| exact MI| reflexivity| reflexivity| reflexivity| reflexivity| unboxed QC| lia| lia| unfold Q_BATCH_BYTES, Q_MAX in *; lia
      | lia| lia| lia| lia
      | exact NB0
      | exact SB| unboxed CR| ub CH; exact Y| exact LCH| exact CNT| exact NTH| exact IXS| unboxed STS| unfold K_BATCH_CLASS; lia| exists junkb; unboxed BJ
      | exact TI| atop_facts; lia| exact TAL| lia| unfold AIMG_HI; lia| unfold Q_BATCH_BYTES; lia
      | ub DTB; unfold Q_BATCH_BYTES; lia| ub DTL; unfold Q_BATCH_BYTES; lia| ub DBL; unfold Q_BATCH_BYTES; lia| exact I|].
    try clear ST.
    clear BJ STS CR QC.
    try rename MI0 into MI.
    match goal with H : stk bsegs ?mm lo _ |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename H into ST end.
    carry HD MUe WMe ltac:(ub DHT; ub DHL; ub DHB; lia). carry CH MUe WMe ltac:(rewrite LCH; ub DTL; ub DTB; lia). carry SH' MUe WMe ltac:(lia). carry GLB MUe WMe ltac:(ub G5; ub G7; ub G8; lia). clear MUe WMe.
    rename PC0 into QC'. destruct PC2 as [stj' STS']. destruct PC5 as [junkb' PC5].

    step.
    step. if_cases KD; zify_cond KD; [|exfalso; unfold Q_CACHE in *; lia].
    step. step. step. step.
    box HD.  box PC3. box PC4. box PC5. box PC1. box STS'.
    snapshot [(bv_unsigned sp + -80 - 48, bv_unsigned sp + -80); (t + 80, t + 112); (0xd8988, 0xd8988 + 4); (0xd8990, 0xd8990 + 32); (g_lst g, g_lst g + 8)]%Z MUd WMd.
    box QC'. box GLB. box GC. box MX. box CH.
    box ST.
    step. call_sp (drain_torec true t (g_lst g) RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ (nb + 1) b b (qb + (n + 8192)) (g_nb g) (g_fst g) (g_qb g) (g_nx g) lo);
      [unboxed ST| exact CEIL| lia| exact MI| reflexivity| reflexivity| unboxed QC'| lia| lia| lia| lia| unboxed MX| unboxed GC| lia| lia| unfold Q_MAX in *; lia| unfold Q_MAX in *; lia| lia| lia
      | exact QK| split; [lia|]; split; [unboxed GLB|]; unfold AIMG_HI, Q_BATCH_BYTES; repeat split; try lia; ub G5; lia| exact TI| atop_facts; lia|].
    try clear ST.
    clear QC' GLB GC MX CH.
    try rename MI0 into MI.
    match goal with H : stk bsegs ?mm lo _ |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename H into ST end.
    carry HD MUd WMd ltac:(ub DHT; ub G6; lia). carry PC3 MUd WMd ltac:(ub DTB; first [ub G8 | pose proof GLST0]; lia). carry PC4 MUd WMd ltac:(cbn [length]; ub DTB; first [ub G8 | pose proof GLST0]; lia). carry PC5 MUd WMd ltac:(ub DTB; first [ub G8 | pose proof GLST0]; lia). carry PC1 MUd WMd ltac:(first [ub G5 | pose proof GLST0]; lia). carry STS' MUd WMd ltac:(first [ub G5 | pose proof GLST0]; lia). clear MUd WMd.
    unfold put_torec_post. rewrite ?QZE. unfold put_frame, dk_postC, dk_glst. rewrite ?EGD. rewrite ?EGF. cbn [ek_post ek_nb ek_fst ek_lst ek_delta ek_b]. finish.
    all: try assumption. all: try exact I. all: try (lazymatch goal with |- exists _, rw_cells _ ?mq ?Aq _ => match goal with Hq : rw_cells _ mq Aq _ |- _ => eexists; exact Hq end end).      all: try (eexists; eassumption).
  -
    box ST.
    call (putA_spec t hm n); try unboxed ST; try eassumption; try reflexivity; try (unfold Q_MAX, AIMG_HI in *; lia).
    try clear ST.
    rename POST into FRP.
    match goal with H : stk bsegs ?mm lo _ |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename H into ST end. try rename MI0 into MI.
    box SH.
    box ST.
    step. call_sp (poison_shadow_spec RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ (hm + 16) (rup n 8) 253 lo sjunk);
      [unboxed ST| exact CEIL| lia| exact MI| repeat (split; [assumption|]); assumption| reflexivity| reflexivity| reflexivity
      | Z.div_mod_to_equations; lia| lia| lia| first [assumption | (eapply ablk_sub; [exact HLO| clear; lia| clear; lia]) | unfold ablk; right; lia | unfold ablk; left; lia]| lia| lia| lia| unboxed SH|].
    try clear ST.
    clear SH.
    try rename MI0 into MI. clear P1 P2 P3 P4 P5 P6 P7.
    match goal with H : stk bsegs ?mm lo _ |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename H into ST end.
    match goal with H : rw_cells bsegs ?mm (shad (hm + 16)) _ |- _ => rename H into SH' end.
    do 5 step.
    step.
    box HD. box CH. box SH'.
    snapshot [(bv_unsigned sp + -80 - 64, bv_unsigned sp + -80); (t + 80, t + 112); (t + 2128, t + 2128 + 4); (t + 2784, t + 2784 + 8); (lst, lst + 8); (b, b + 8192)]%Z MUe WMe.
    box BJ. box STS. box CR. box QC.
    box ST.
    call_sp (enqueue_new_spec false t lst b RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ nb fst0 qb hm n nx bsz cnt24 spacebeg lo maxc csz stj idxw chunks);
      [unboxed ST| exact CEIL| lia| exact MI| reflexivity| reflexivity| reflexivity| reflexivity| unboxed QC| lia| lia| unfold Q_BATCH_BYTES, Q_MAX in *; lia
      | lia| lia| lia| lia
      | exact NB0
      | exact SB| unboxed CR| ub CH; exact Y| exact LCH| exact CNT| exact NTH| exact IXS| unboxed STS| unfold K_BATCH_CLASS; lia| exists junkb; unboxed BJ
      | exact TI| atop_facts; lia| exact TAL| lia| unfold AIMG_HI; lia| unfold Q_BATCH_BYTES; lia
      | ub DTB; unfold Q_BATCH_BYTES; lia| ub DTL; unfold Q_BATCH_BYTES; lia| ub DBL; unfold Q_BATCH_BYTES; lia| exact I|].
    try clear ST.
    clear BJ STS CR QC.
    try rename MI0 into MI.
    match goal with H : stk bsegs ?mm lo _ |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename H into ST end.
    carry HD MUe WMe ltac:(ub DHT; ub DHL; ub DHB; lia). carry CH MUe WMe ltac:(rewrite LCH; ub DTL; ub DTB; lia). carry SH' MUe WMe ltac:(lia). clear MUe WMe.
    rename PC0 into QC'. destruct PC2 as [stj' STS']. destruct PC5 as [junkb' PC5].

    step.
    step. if_cases KD; zify_cond KD; [|exfalso; unfold Q_CACHE in *; lia].
    step. step. step. step.
    box HD.  box PC3. box PC4. box PC5. box PC1. box STS'.
    snapshot [(bv_unsigned sp + -80 - 48, bv_unsigned sp + -80); (t + 80, t + 112); (0xd8988, 0xd8988 + 4); (0xd8990, 0xd8990 + 32); (g_lst g, g_lst g + 8)]%Z MUd WMd.
    box QC'. box GC. box MX.
    box ST.
    step. call_sp (drain_torec false t (g_lst g) RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ (nb + 1) b b (qb + (n + 8192)) (g_nb g) (g_fst g) (g_qb g) (g_nx g) lo);
      [unboxed ST| exact CEIL| lia| exact MI| reflexivity| reflexivity| unboxed QC'| lia| lia| lia| lia| unboxed MX| unboxed GC| lia| lia| unfold Q_MAX in *; lia| unfold Q_MAX in *; lia| lia| lia
      | exact QK| exact GNB0| exact TI| atop_facts; lia| exact I|].
    try clear ST.
    clear QC' GC MX.
    try rename MI0 into MI.
    match goal with H : stk bsegs ?mm lo _ |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename H into ST end.
    carry HD MUd WMd ltac:(ub DHT;  lia). carry PC3 MUd WMd ltac:(ub DTB; first [ub G8 | pose proof GLST0]; lia). carry PC4 MUd WMd ltac:(cbn [length]; ub DTB; first [ub G8 | pose proof GLST0]; lia). carry PC5 MUd WMd ltac:(ub DTB; first [ub G8 | pose proof GLST0]; lia). carry PC1 MUd WMd ltac:(first [ub G5 | pose proof GLST0]; lia). carry STS' MUd WMd ltac:(first [ub G5 | pose proof GLST0]; lia). clear MUd WMd.
    unfold put_torec_post. rewrite ?QZE. unfold put_frame, dk_postC, dk_glst. rewrite ?EGD. rewrite ?EGF. cbn [ek_post ek_nb ek_fst ek_lst ek_delta ek_b]. finish.
    all: try assumption. all: try exact I. all: try (lazymatch goal with |- exists _, rw_cells _ ?mq ?Aq _ => match goal with Hq : rw_cells _ mq Aq _ |- _ => eexists; exact Hq end end).      all: try (eexists; eassumption).
Qed.
End CANSEC1.
End F_afree_tailC.

Module F_afree_tailRC.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase. Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics. Import LinuxProcessSemantics.LinuxProcessSem.MemImageType. Import LinuxProcessSemantics.LinuxProcessSem.State. Import LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude. Import LinuxProcessSemantics.Riscv.Instr. Import LinuxProcessSemantics.Riscv.Decode. Import LinuxProcessSemantics.Riscv.DecodeC. Import LinuxProcessSemantics.Riscv.Sem. Import LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Arr. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.InitMem.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.StrFun.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanCtrl. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanEmbed.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.BothW.BImg. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ABase.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AQConst.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ABytes.TwinB.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.StepF.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AKit.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AKit2.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AKitQ.TwinB.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_apoison.TwinB.F_apoison.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aenqueue.TwinB.F_aenqueue.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aenqueue.TwinB.F_aenqueueR. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_adrain.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aput.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_afree_tail.TwinB. Import F_afree_tailR. Import F_afreeC_iface. Import F_adrainC.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Local Lemma outside_In8 : forall (W : list ivl) x lo hi, outside W x -> In (lo, hi) W -> ~ (lo <= x < hi)%Z.
Proof. induction W as [|[a b] W IH]; cbn; intros x lo hi H HI; [tauto|]. destruct HI as [E|HI]; [injection E; intros; subst; tauto| apply (IH x); tauto]. Qed.
Local Lemma sub_fp_cover8 : forall W W' : list ivl,
  Forall (fun iv : ivl => (snd iv <= fst iv)%Z \/ Exists (fun jv : ivl => (fst jv <= fst iv /\ snd iv <= snd jv)%Z) W') W -> sub_fp W W'.
Proof.
  intros W W' HF x HO. induction HF as [|[lo hi] W HP HF IH]; cbn; [exact I|]. split; [| exact IH].
  cbn in HP. destruct HP as [HE|HP]; [lia|]. apply Exists_exists in HP. destruct HP as ([lo' hi'] & HI & [H1 H2]). cbn in H1, H2.
  pose proof (outside_In8 _ _ _ _ HO HI). lia.
Qed.
Local Ltac fp_cheap8 := first [ match goal with Hs : bv_unsigned _ = (bv_unsigned _ + _)%Z |- _ => clear -Hs end | clear ]; Stdlib.micromega.Lia.lia.
Local Ltac fp_find8c := first [ apply Exists_cons_hd; cbn [fst snd]; split; fp_cheap8 | apply Exists_cons_tl; fp_find8c ].
Local Ltac fp_find8 := first [ apply Exists_cons_hd; cbn [fst snd]; split; lia | apply Exists_cons_tl; fp_find8 ].
Local Ltac fp_cover8 := apply sub_fp_cover8; repeat (apply Forall_cons; [ cbn [fst snd]; first [left; fp_cheap8 | right; fp_find8c | right; fp_find8] | ]); apply Forall_nil.

Local Ltac transport_after_call segs m m' MU WM ::=
  let W := lazymatch type of MU with munch ?W _ _ => W end in
  repeat match goal with
  | H : bytes_at segs m ?A2 ?bs2 |- _ =>
      first [ apply (bytes_at_transport segs W m m' A2 bs2) in H; [ | exact MU | cbn [disjoint_from]; simpl_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : wr_at segs m ?A2 ?n2 |- _ => apply (wr_at_transport segs m m' A2 n2) in H; [ | exact WM ]
  | H : rw_cells segs m ?A2 ?cs2 |- _ =>
      first [ apply (rw_cells_transport segs W m m' A2 cs2) in H; [ | exact MU | exact WM | cbn [disjoint_from]; simpl_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : ro_cells segs m ?A2 ?cs2 |- _ =>
      first [ apply (ro_cells_transport segs W m m' A2 cs2) in H; [ | exact MU | cbn [disjoint_from]; simpl_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : u8arr segs m ?A2 ?xs |- _ =>
      first [ apply (u8arr_transport segs W m m' A2 xs) in H; [ | exact MU | exact WM | cbn [disjoint_from]; simpl_sizes; simpl_arr_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : u32arr segs m ?A2 ?xs |- _ =>
      first [ apply (u32arr_transport segs W m m' A2 xs) in H; [ | exact MU | exact WM | cbn [disjoint_from]; simpl_sizes; simpl_arr_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : u64arr segs m ?A2 ?xs |- _ =>
      first [ apply (u64arr_transport segs W m m' A2 xs) in H; [ | exact MU | exact WM | cbn [disjoint_from]; simpl_sizes; simpl_arr_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : u8ro segs m ?A2 ?xs |- _ =>
      first [ apply (u8ro_transport segs W m m' A2 xs) in H; [ | exact MU | cbn [disjoint_from]; simpl_sizes; simpl_arr_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : stk segs m ?loq ?hiq |- _ =>
      first [ apply (stk_transport_disjoint segs W m m' loq hiq) in H; [ | exact MU | exact WM | cbn [disjoint_from]; slia ]
            | clear H ]
  | H : munch ?Wq ?mq m |- _ =>
      first [ apply (munch_trans Wq mq m m') in H; [ | eapply (munch_weaken W Wq m m'); [ first [ fp_cover8 | unfold sub_fp; cbn [outside]; first [ match goal with Hs : bv_unsigned _ = bv_unsigned _ + _ |- _ => clear -Hs; intros; lia end | clear; intros; lia | intros; slia ] ] | exact MU ] ]
            | fail 100 "callee footprint not inside caller footprint" ]
  | H : wmono segs ?mq m |- _ => apply (wmono_trans segs mq m m') in H; [ | exact WM ]
  end.

Ltac ub H := let X := fresh "Y" in pose proof H as X; unbox X.

Local Ltac band_lin :=
  repeat match goal with H : iclr ?a ?n |- _ => unfold iclr, AIMG_LO, AIMG_HI in H end.
Local Ltac with_band H tac :=
  let H' := fresh H in pose proof H as H'; unfold sclr, iclr, ablk, KLS, AIMG_LO, AIMG_HI in H'; tac; try clear H'.
Local Ltac with_sclr tac := idtac; match goal with H : sclr ?a ?n |- _ => with_band H tac | _ => tac end.

Local Lemma sclr_int : forall a n, sclr a n -> 0 <= a -> a + n <= 18446744073709551616 ->
  exists k, 0 <= k <= 1 /\ a + n <= 2147446784 + k * 18446744073709551616 /\ 17594333495296 * k <= a.
Proof. intros a n H G1 G2. unfold sclr, KLS in H. destruct H; [exists 0 | exists 1]; lia. Qed.
Local Lemma iclr_int : forall a n, iclr a n -> a + n <= 18446744073709551616 ->
  exists k, 0 <= k <= 1 /\ 4096 <= a /\ a + n <= 65536 + k * 18446744073709551616 /\ 6492160 * k <= a.
Proof. intros a n H G2. unfold iclr, AIMG_LO, AIMG_HI in H. destruct H as [? [?|?]]; [exists 0 | exists 1]; lia. Qed.
Local Lemma ablk_int {rc : runConstT} : forall lo hi, ablk lo hi ->
  exists k, 0 <= k <= 1 /\ 6492160 <= lo /\ 17594333495296 * k <= lo /\ hi <= 2147446784 + k * 18446744073709551616 /\ hi <= ATOP.
Proof. intros lo hi H. unfold ablk, KLS, AIMG_HI in H. pose proof atop_range. destruct H as [[? ?]|[? ?]]; [exists 0 | exists 1]; lia. Qed.
Local Ltac band_int H :=
  let k := fresh "k" H in let A := fresh "KA" H in let B := fresh "KB" H in let C := fresh "KC" H in let D := fresh "KD" H in
  let G1 := fresh "G" in let G2 := fresh "G" in
  lazymatch type of H with
  | sclr ?a ?n =>
      assert (G1 : 0 <= a) by (atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia); assert (G2 : a + n <= 18446744073709551616) by (atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia);
      destruct (sclr_int a n H G1 G2) as (k & A & B & C); clear G1 G2
  | iclr ?a ?n =>
      assert (G2 : a + n <= 18446744073709551616) by (atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia);
      destruct (iclr_int a n H G2) as (k & A & B & C & D); clear G2
  | 4096 <= ?a /\ (?a + ?n <= _ \/ _ <= ?a) =>
      assert (G2 : a + n <= 18446744073709551616) by (atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia);
      destruct (iclr_int a n H G2) as (k & A & B & C & D); clear G2
  | ablk ?lo ?hi => let E := fresh "KE" H in destruct (ablk_int lo hi H) as (k & A & B & E & C & D)
  end.

Section CANSEC1. Context {rc : runConstT}.
Theorem put_from_refill_torec : put_from_refill_torec_stmt.
Proof.
  unfold put_from_refill_torec_stmt.
  intros until j0. cbv zeta. intros ST CEIL LO MI -> FRP FRE QK HD N AL HLO HHI HCE SH' QC NB QB QBN FST LST T0 T1 TAL DHT
    FULL SB CR CH LCH CNT NTH IXS STS HB BJ SBP B0 BL1 DTB DTL DBL DHB DHL RB DK RIMG RSTK RT RH RSH TI.
  band_int TI. pose proof (ablk_lin _ _ HLO) as (HL1 & HL2 & HL3 & HL4). unfold AIMG_HI in HL1. band_int HLO. band_lin. band_int T0.
  assert (SHB : 2148262400 <= shad (hm + 16) /\ shad (hm + 16) + shlen (rup n 8) <= 0x10007fff8000).
  { unfold shad, shlen, ASHOFF. rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8. unfold Q_MAX in N. Z.div_mod_to_equations. lia. }
  assert (RUP : n <= rup n 8 <= n + 7 /\ rup n 8 mod 8 = 0) by (unfold rup; Z.div_mod_to_equations; lia).
  assert (SHL : 0 < shlen (rup n 8) < 0x10000000) by (unfold shlen; rewrite Z.shiftr_div_pow2 by lia; unfold Q_MAX in N; Z.div_mod_to_equations; lia).
  word_range sp SPR.
  pose proof (munch_refl [(bv_unsigned sp - 144, bv_unsigned sp); (shad (hm + 16), shad (hm + 16) + shlen (rup n 8));
              (t + 80, t + 112); (t + 2128, t + 2132); (t + 2784, t + 2792);
              (lst, lst + qsz lst); (b, b + 8192);
              (0xd8988, 0xd8988 + 4); (0xd8990, 0xd8990 + 32); (dk_glst g lst, dk_glst g lst + 8)]%Z m) as MU.
  pose proof (wmono_refl bsegs m) as WM.
  box DHT. box DTB. box DTL. box DBL. box DHB. box DHL.
  destruct BJ as [junkb BJ].
  destruct full; [destruct FULL as (NB1 & LB & NX & BSZ & L0 & L1 & LA0 & LEN0 & RL) | destruct FULL as [NB0 LST0]];
  unfold dk_glst in *; cbn [ek_pre dk_preC ek_b ek_nb ek_fst ek_lst ek_delta] in *;
  destruct DK as (EGD & MX & GC & GNB & GQB & GFST & GLST & QB1 & GQ & GQ63 & GFULL);
  (destruct (g_full g) eqn:EGF;
     [destruct GFULL as (G1 & GLB & G3 & G4 & G5 & G6 & G7 & G8 & G9); box G5; box G6; box G7; box G8 | destruct GFULL as [GNB0 GLST0]]);
  rewrite ?EGD in *; cbn [ek_pre dk_preC ek_b ek_nb ek_fst ek_lst ek_delta dk_glst] in *; unfold AIMG_HI in *.
  all: first [assert (QZE : qsz lst = 8192) by (apply qsz_pos; generalize L0; clear; intros; lia) | assert (QZE : qsz lst = 8) by (apply qsz_eq0; exact LST0)]; rewrite QZE in *.
  -
    box HD. box CH. box SH'. box GLB. box LA0. box FRP.
    snapshot [(t + 80, t + 112); (t + 2128, t + 2128 + 4); (t + 2784, t + 2784 + 8); (lst, lst + 8); (b, b + 8192)]%Z MUe WMe.
    box BJ. box STS. box CR. box LB. box QC.
    box ST.
    call_sp (enqueue_from_refill_spec true t lst b RNG _ _ _ _ _ _ _
               (Z_to_bv 64 0x41bc0) (Z_to_bv 64 0xd88f0) (Z_to_bv 64 (t + 80)) (Z_to_bv 64 n) a3 (Z_to_bv 64 (t + 208)) (Z_to_bv 64 hm)
               _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ nb fst0 qb hm n nx bsz cnt spacebeg lo maxc csz stj idxw chunks j0);
      [unboxed ST| exact CEIL| lia| lia| exact MI| exact FRE| unboxed QC| lia| lia| unfold Q_BATCH_BYTES, Q_MAX in *; lia
      | lia| lia| lia| lia
      | split; [lia|]; split; [unboxed LB|]; unfold AIMG_HI, Q_BATCH_BYTES; repeat split; try assumption; lia
      | exact SB| unboxed CR| ub CH; exact Y| exact LCH| exact CNT| exact NTH| exact IXS| unboxed STS| unfold K_BATCH_CLASS; lia| exists junkb; unboxed BJ
      | exact TI| atop_facts; lia| exact TAL| lia| unfold AIMG_HI; lia| unfold Q_BATCH_BYTES; lia
      | ub DTB; unfold Q_BATCH_BYTES; lia| ub DTL; unfold Q_BATCH_BYTES; lia| ub DBL; unfold Q_BATCH_BYTES; lia|].
    clear BJ STS CR LB QC.
    try rename MI0 into MI.
    replace (bv_unsigned sp + -144 + 64) with (bv_unsigned sp + -80) in * by lia.
    clear ST. match goal with H : stk bsegs ?mm lo (bv_unsigned sp + -80) |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename H into ST end.
    carry HD MUe WMe ltac:(ub DHT; ub DHL; ub DHB; lia). carry CH MUe WMe ltac:(rewrite LCH; ub DTL; ub DTB; lia). carry SH' MUe WMe ltac:(lia). carry LA0 MUe WMe ltac:(rewrite LEN0; ub DTL; ub DBL; lia). carry GLB MUe WMe ltac:(ub G5; ub G7; ub G8; lia). carry FRP MUe WMe ltac:(lia). clear MUe WMe.
    rename PC0 into QC'. destruct PC2 as [stj' STS']. destruct PC5 as [junkb' PC5].

    step.
    step. if_cases KD; zify_cond KD; [|exfalso; unfold Q_CACHE in *; lia].
    step. step. step. step.
    box HD.  box PC3. box PC4. box PC5. box POST. box PC1. box STS'. box LA0.
    snapshot [(bv_unsigned sp + -80 - 48, bv_unsigned sp + -80); (t + 80, t + 112); (0xd8988, 0xd8988 + 4); (0xd8990, 0xd8990 + 32); (g_lst g, g_lst g + 8)]%Z MUd WMd.
    box QC'. box GLB. box GC. box MX. box FRE. box CH.
    box ST.
    step. call_sp (drain_torec true t (g_lst g) RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ (nb + 1) fst0 b (qb + (n + 8192)) (g_nb g) (g_fst g) (g_qb g) (g_nx g) lo);
      [unboxed ST| exact CEIL| lia| exact MI| reflexivity| reflexivity| unboxed QC'| lia| lia| lia| lia| unboxed MX| unboxed GC| lia| lia| unfold Q_MAX in *; lia| unfold Q_MAX in *; lia| lia| lia
      | exact QK| split; [lia|]; split; [unboxed GLB|]; unfold AIMG_HI, Q_BATCH_BYTES; repeat split; try lia; ub G5; lia| exact TI| atop_facts; lia|].
    try clear ST.
    clear QC' GLB GC MX FRE CH.
    try rename MI0 into MI.
    match goal with H : stk bsegs ?mm lo _ |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename H into ST end.
    carry HD MUd WMd ltac:(ub DHT; ub G6; lia). carry PC3 MUd WMd ltac:(ub DTB; first [ub G8 | pose proof GLST0]; lia). carry PC4 MUd WMd ltac:(cbn [length]; ub DTB; first [ub G8 | pose proof GLST0]; lia). carry PC5 MUd WMd ltac:(ub DTB; first [ub G8 | pose proof GLST0]; lia). carry POST MUd WMd ltac:(ub DTL; first [ub G7 | pose proof GLST0]; lia). carry PC1 MUd WMd ltac:(first [ub G5 | pose proof GLST0]; lia). carry STS' MUd WMd ltac:(first [ub G5 | pose proof GLST0]; lia). carry LA0 MUd WMd ltac:(rewrite LEN0; ub DTL; first [ub G7 | pose proof GLST0]; lia). clear MUd WMd.
    unfold put_torec_post. rewrite ?QZE. unfold put_frame, dk_postC, dk_glst. rewrite ?EGD. rewrite ?EGF. cbn [ek_post ek_nb ek_fst ek_lst ek_delta ek_b]. finish.
    all: try assumption. all: try exact I. all: try (lazymatch goal with |- exists _, rw_cells _ ?mq ?Aq _ => match goal with Hq : rw_cells _ mq Aq _ |- _ => eexists; exact Hq end end).      all: try (eexists; eassumption).
  -
    box HD. box CH. box SH'. box LA0. box FRP.
    snapshot [(t + 80, t + 112); (t + 2128, t + 2128 + 4); (t + 2784, t + 2784 + 8); (lst, lst + 8); (b, b + 8192)]%Z MUe WMe.
    box BJ. box STS. box CR. box LB. box QC.
    box ST.
    call_sp (enqueue_from_refill_spec true t lst b RNG _ _ _ _ _ _ _
               (Z_to_bv 64 0x41bc0) (Z_to_bv 64 0xd88f0) (Z_to_bv 64 (t + 80)) (Z_to_bv 64 n) a3 (Z_to_bv 64 (t + 208)) (Z_to_bv 64 hm)
               _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ nb fst0 qb hm n nx bsz cnt spacebeg lo maxc csz stj idxw chunks j0);
      [unboxed ST| exact CEIL| lia| lia| exact MI| exact FRE| unboxed QC| lia| lia| unfold Q_BATCH_BYTES, Q_MAX in *; lia
      | lia| lia| lia| lia
      | split; [lia|]; split; [unboxed LB|]; unfold AIMG_HI, Q_BATCH_BYTES; repeat split; try assumption; lia
      | exact SB| unboxed CR| ub CH; exact Y| exact LCH| exact CNT| exact NTH| exact IXS| unboxed STS| unfold K_BATCH_CLASS; lia| exists junkb; unboxed BJ
      | exact TI| atop_facts; lia| exact TAL| lia| unfold AIMG_HI; lia| unfold Q_BATCH_BYTES; lia
      | ub DTB; unfold Q_BATCH_BYTES; lia| ub DTL; unfold Q_BATCH_BYTES; lia| ub DBL; unfold Q_BATCH_BYTES; lia|].
    clear BJ STS CR LB QC.
    try rename MI0 into MI.
    replace (bv_unsigned sp + -144 + 64) with (bv_unsigned sp + -80) in * by lia.
    clear ST. match goal with H : stk bsegs ?mm lo (bv_unsigned sp + -80) |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename H into ST end.
    carry HD MUe WMe ltac:(ub DHT; ub DHL; ub DHB; lia). carry CH MUe WMe ltac:(rewrite LCH; ub DTL; ub DTB; lia). carry SH' MUe WMe ltac:(lia). carry LA0 MUe WMe ltac:(rewrite LEN0; ub DTL; ub DBL; lia). carry FRP MUe WMe ltac:(lia). clear MUe WMe.
    rename PC0 into QC'. destruct PC2 as [stj' STS']. destruct PC5 as [junkb' PC5].

    step.
    step. if_cases KD; zify_cond KD; [|exfalso; unfold Q_CACHE in *; lia].
    step. step. step. step.
    box HD.  box PC3. box PC4. box PC5. box POST. box PC1. box STS'. box LA0.
    snapshot [(bv_unsigned sp + -80 - 48, bv_unsigned sp + -80); (t + 80, t + 112); (0xd8988, 0xd8988 + 4); (0xd8990, 0xd8990 + 32); (g_lst g, g_lst g + 8)]%Z MUd WMd.
    box QC'. box GC. box MX. box FRE.
    box ST.
    step. call_sp (drain_torec false t (g_lst g) RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ (nb + 1) fst0 b (qb + (n + 8192)) (g_nb g) (g_fst g) (g_qb g) (g_nx g) lo);
      [unboxed ST| exact CEIL| lia| exact MI| reflexivity| reflexivity| unboxed QC'| lia| lia| lia| lia| unboxed MX| unboxed GC| lia| lia| unfold Q_MAX in *; lia| unfold Q_MAX in *; lia| lia| lia
      | exact QK| exact GNB0| exact TI| atop_facts; lia| exact I|].
    try clear ST.
    clear QC' GC MX FRE.
    try rename MI0 into MI.
    match goal with H : stk bsegs ?mm lo _ |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename H into ST end.
    carry HD MUd WMd ltac:(ub DHT;  lia). carry PC3 MUd WMd ltac:(ub DTB; first [ub G8 | pose proof GLST0]; lia). carry PC4 MUd WMd ltac:(cbn [length]; ub DTB; first [ub G8 | pose proof GLST0]; lia). carry PC5 MUd WMd ltac:(ub DTB; first [ub G8 | pose proof GLST0]; lia). carry POST MUd WMd ltac:(ub DTL; first [ub G7 | pose proof GLST0]; lia). carry PC1 MUd WMd ltac:(first [ub G5 | pose proof GLST0]; lia). carry STS' MUd WMd ltac:(first [ub G5 | pose proof GLST0]; lia). carry LA0 MUd WMd ltac:(rewrite LEN0; ub DTL; first [ub G7 | pose proof GLST0]; lia). clear MUd WMd.
    unfold put_torec_post. rewrite ?QZE. unfold put_frame, dk_postC, dk_glst. rewrite ?EGD. rewrite ?EGF. cbn [ek_post ek_nb ek_fst ek_lst ek_delta ek_b]. finish.
    all: try assumption. all: try exact I. all: try (lazymatch goal with |- exists _, rw_cells _ ?mq ?Aq _ => match goal with Hq : rw_cells _ mq Aq _ |- _ => eexists; exact Hq end end).      all: try (eexists; eassumption).
  -
    box HD. box CH. box SH'. box GLB. box FRP.
    snapshot [(t + 80, t + 112); (t + 2128, t + 2128 + 4); (t + 2784, t + 2784 + 8); (lst, lst + 8); (b, b + 8192)]%Z MUe WMe.
    box BJ. box STS. box CR. box QC.
    box ST.
    call_sp (enqueue_from_refill_spec false t lst b RNG _ _ _ _ _ _ _
               (Z_to_bv 64 0x41bc0) (Z_to_bv 64 0xd88f0) (Z_to_bv 64 (t + 80)) (Z_to_bv 64 n) a3 (Z_to_bv 64 (t + 208)) (Z_to_bv 64 hm)
               _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ nb fst0 qb hm n nx bsz cnt spacebeg lo maxc csz stj idxw chunks j0);
      [unboxed ST| exact CEIL| lia| lia| exact MI| exact FRE| unboxed QC| lia| lia| unfold Q_BATCH_BYTES, Q_MAX in *; lia
      | lia| lia| lia| lia
      | exact NB0
      | exact SB| unboxed CR| ub CH; exact Y| exact LCH| exact CNT| exact NTH| exact IXS| unboxed STS| unfold K_BATCH_CLASS; lia| exists junkb; unboxed BJ
      | exact TI| atop_facts; lia| exact TAL| lia| unfold AIMG_HI; lia| unfold Q_BATCH_BYTES; lia
      | ub DTB; unfold Q_BATCH_BYTES; lia| ub DTL; unfold Q_BATCH_BYTES; lia| ub DBL; unfold Q_BATCH_BYTES; lia| exact I|].
    clear BJ STS CR QC.
    try rename MI0 into MI.
    replace (bv_unsigned sp + -144 + 64) with (bv_unsigned sp + -80) in * by lia.
    clear ST. match goal with H : stk bsegs ?mm lo (bv_unsigned sp + -80) |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename H into ST end.
    carry HD MUe WMe ltac:(ub DHT; ub DHL; ub DHB; lia). carry CH MUe WMe ltac:(rewrite LCH; ub DTL; ub DTB; lia). carry SH' MUe WMe ltac:(lia). carry GLB MUe WMe ltac:(ub G5; ub G7; ub G8; lia). carry FRP MUe WMe ltac:(lia). clear MUe WMe.
    rename PC0 into QC'. destruct PC2 as [stj' STS']. destruct PC5 as [junkb' PC5].

    step.
    step. if_cases KD; zify_cond KD; [|exfalso; unfold Q_CACHE in *; lia].
    step. step. step. step.
    box HD.  box PC3. box PC4. box PC5. box PC1. box STS'.
    snapshot [(bv_unsigned sp + -80 - 48, bv_unsigned sp + -80); (t + 80, t + 112); (0xd8988, 0xd8988 + 4); (0xd8990, 0xd8990 + 32); (g_lst g, g_lst g + 8)]%Z MUd WMd.
    box QC'. box GLB. box GC. box MX. box FRE. box CH.
    box ST.
    step. call_sp (drain_torec true t (g_lst g) RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ (nb + 1) b b (qb + (n + 8192)) (g_nb g) (g_fst g) (g_qb g) (g_nx g) lo);
      [unboxed ST| exact CEIL| lia| exact MI| reflexivity| reflexivity| unboxed QC'| lia| lia| lia| lia| unboxed MX| unboxed GC| lia| lia| unfold Q_MAX in *; lia| unfold Q_MAX in *; lia| lia| lia
      | exact QK| split; [lia|]; split; [unboxed GLB|]; unfold AIMG_HI, Q_BATCH_BYTES; repeat split; try lia; ub G5; lia| exact TI| atop_facts; lia|].
    try clear ST.
    clear QC' GLB GC MX FRE CH.
    try rename MI0 into MI.
    match goal with H : stk bsegs ?mm lo _ |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename H into ST end.
    carry HD MUd WMd ltac:(ub DHT; ub G6; lia). carry PC3 MUd WMd ltac:(ub DTB; first [ub G8 | pose proof GLST0]; lia). carry PC4 MUd WMd ltac:(cbn [length]; ub DTB; first [ub G8 | pose proof GLST0]; lia). carry PC5 MUd WMd ltac:(ub DTB; first [ub G8 | pose proof GLST0]; lia). carry PC1 MUd WMd ltac:(first [ub G5 | pose proof GLST0]; lia). carry STS' MUd WMd ltac:(first [ub G5 | pose proof GLST0]; lia). clear MUd WMd.
    unfold put_torec_post. rewrite ?QZE. unfold put_frame, dk_postC, dk_glst. rewrite ?EGD. rewrite ?EGF. cbn [ek_post ek_nb ek_fst ek_lst ek_delta ek_b]. finish.
    all: try assumption. all: try exact I. all: try (lazymatch goal with |- exists _, rw_cells _ ?mq ?Aq _ => match goal with Hq : rw_cells _ mq Aq _ |- _ => eexists; exact Hq end end).      all: try (eexists; eassumption).
  -
    box HD. box CH. box SH'. box FRP.
    snapshot [(t + 80, t + 112); (t + 2128, t + 2128 + 4); (t + 2784, t + 2784 + 8); (lst, lst + 8); (b, b + 8192)]%Z MUe WMe.
    box BJ. box STS. box CR. box QC.
    box ST.
    call_sp (enqueue_from_refill_spec false t lst b RNG _ _ _ _ _ _ _
               (Z_to_bv 64 0x41bc0) (Z_to_bv 64 0xd88f0) (Z_to_bv 64 (t + 80)) (Z_to_bv 64 n) a3 (Z_to_bv 64 (t + 208)) (Z_to_bv 64 hm)
               _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ nb fst0 qb hm n nx bsz cnt spacebeg lo maxc csz stj idxw chunks j0);
      [unboxed ST| exact CEIL| lia| lia| exact MI| exact FRE| unboxed QC| lia| lia| unfold Q_BATCH_BYTES, Q_MAX in *; lia
      | lia| lia| lia| lia
      | exact NB0
      | exact SB| unboxed CR| ub CH; exact Y| exact LCH| exact CNT| exact NTH| exact IXS| unboxed STS| unfold K_BATCH_CLASS; lia| exists junkb; unboxed BJ
      | exact TI| atop_facts; lia| exact TAL| lia| unfold AIMG_HI; lia| unfold Q_BATCH_BYTES; lia
      | ub DTB; unfold Q_BATCH_BYTES; lia| ub DTL; unfold Q_BATCH_BYTES; lia| ub DBL; unfold Q_BATCH_BYTES; lia| exact I|].
    clear BJ STS CR QC.
    try rename MI0 into MI.
    replace (bv_unsigned sp + -144 + 64) with (bv_unsigned sp + -80) in * by lia.
    clear ST. match goal with H : stk bsegs ?mm lo (bv_unsigned sp + -80) |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename H into ST end.
    carry HD MUe WMe ltac:(ub DHT; ub DHL; ub DHB; lia). carry CH MUe WMe ltac:(rewrite LCH; ub DTL; ub DTB; lia). carry SH' MUe WMe ltac:(lia). carry FRP MUe WMe ltac:(lia). clear MUe WMe.
    rename PC0 into QC'. destruct PC2 as [stj' STS']. destruct PC5 as [junkb' PC5].

    step.
    step. if_cases KD; zify_cond KD; [|exfalso; unfold Q_CACHE in *; lia].
    step. step. step. step.
    box HD.  box PC3. box PC4. box PC5. box PC1. box STS'.
    snapshot [(bv_unsigned sp + -80 - 48, bv_unsigned sp + -80); (t + 80, t + 112); (0xd8988, 0xd8988 + 4); (0xd8990, 0xd8990 + 32); (g_lst g, g_lst g + 8)]%Z MUd WMd.
    box QC'. box GC. box MX. box FRE.
    box ST.
    step. call_sp (drain_torec false t (g_lst g) RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ (nb + 1) b b (qb + (n + 8192)) (g_nb g) (g_fst g) (g_qb g) (g_nx g) lo);
      [unboxed ST| exact CEIL| lia| exact MI| reflexivity| reflexivity| unboxed QC'| lia| lia| lia| lia| unboxed MX| unboxed GC| lia| lia| unfold Q_MAX in *; lia| unfold Q_MAX in *; lia| lia| lia
      | exact QK| exact GNB0| exact TI| atop_facts; lia| exact I|].
    try clear ST.
    clear QC' GC MX FRE.
    try rename MI0 into MI.
    match goal with H : stk bsegs ?mm lo _ |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename H into ST end.
    carry HD MUd WMd ltac:(ub DHT;  lia). carry PC3 MUd WMd ltac:(ub DTB; first [ub G8 | pose proof GLST0]; lia). carry PC4 MUd WMd ltac:(cbn [length]; ub DTB; first [ub G8 | pose proof GLST0]; lia). carry PC5 MUd WMd ltac:(ub DTB; first [ub G8 | pose proof GLST0]; lia). carry PC1 MUd WMd ltac:(first [ub G5 | pose proof GLST0]; lia). carry STS' MUd WMd ltac:(first [ub G5 | pose proof GLST0]; lia). clear MUd WMd.
    unfold put_torec_post. rewrite ?QZE. unfold put_frame, dk_postC, dk_glst. rewrite ?EGD. rewrite ?EGF. cbn [ek_post ek_nb ek_fst ek_lst ek_delta ek_b]. finish.
    all: try assumption. all: try exact I. all: try (lazymatch goal with |- exists _, rw_cells _ ?mq ?Aq _ => match goal with Hq : rw_cells _ mq Aq _ |- _ => eexists; exact Hq end end).      all: try (eexists; eassumption).
Qed.
End CANSEC1.
End F_afree_tailRC.
End TwinB.
