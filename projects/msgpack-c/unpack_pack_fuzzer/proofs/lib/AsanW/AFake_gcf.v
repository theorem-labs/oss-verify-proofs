(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib Require Import ITree Nodes Decode.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA Require Import Shadow.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require Import AImg RtCells AProto ABase F_tryinit. From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require F_aunwind. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aunwind.F_aunwind. From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require F_tlsga. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_tlsga.F_tlsga. From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require Import F_m2s_b.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA Require Import StepF.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require Import AKit AKit2 FsKit ABytes AFake_gc AFake_gcl.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac solve_load ::= first [ solve_load_g | solve_load_image ].
Local Ltac solve_store ::= solve_store_g.

Section CANSEC1. Context {rc : runConstT}.

Definition gc_ohead (pc : Z) (ra gp tp t0 t1 a0 a1 a2 a3 a4 a5 a6 a7 s3 s5 s8 s11 t4 t5 t6 : word) (FR : bvmap 5 word) (fc : bv 32)
    (spf fs bot cur c : Z) (m : amem) : machine_state :=
  MS (mkR ra (Z_to_bv 64 spf) gp tp t0 t1 (Z_to_bv 64 1) (Z_to_bv 64 (fs + 4096)) (Z_to_bv 64 cur)
          a0 a1 a2 a3 a4 a5 a6 a7
          (Z_to_bv 64 bot) s3 (Z_to_bv 64 c) s5 (Z_to_bv 64 0xd9ab8) (Z_to_bv 64 GCMAGIC)
          s8 (Z_to_bv 64 fs) (Z_to_bv 64 0) s11
          (Z_to_bv 64 6) t4 t5 t6) FR (Z_to_bv 64 pc) fc None m (seg_rom asegs).

Lemma gc_setup : forall RNG ra gp tp t0 t1 a0 a1 a2 a3 a4 a5 a6 a7 s3 s5 s8 s11 t4 t5 t6 (FR : bvmap 5 word) fc (m : amem)
    (spf fs bot cur c : Z) (v0 fsz : word),
  mem_inv asegs m -> 0 <= c < 11 -> 0 <= fs -> fs + 11571200 <= 2^47 ->
  rw_cells asegs m (fs + 88) [C8 (Z_to_bv 64 20)] ->
  rw_cells asegs m spf [C8 v0; C8 (Z_to_bv 64 0xda7a0); C8 (Z_to_bv 64 0xda7b0); C8 (Z_to_bv 64 0xda7a8); C8 fsz] ->
  ATOP <= spf -> spf + 40 <= 2^64 ->
  rng RNG spf 40 -> rng RNG fs 11571200 ->
  evtF asegs RNG (fun ms' => exists b0 b1 b2 b3 b4 b5 b6 b7 m',
       ms' = gc_head 0x47ff8 ra gp tp t0 t1 b0 b1 b2 b3 b4 b5 b6 b7 t4 t5 t6 FR fc spf fs bot cur c 0 m'
       /\ munch [(spf + 32, spf + 40)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
       /\ rw_cells asegs m' spf [C8 v0; C8 (Z_to_bv 64 0xda7a0); C8 (Z_to_bv 64 0xda7b0); C8 (Z_to_bv 64 0xda7a8); C8 (Z_to_bv 64 (2 ^ (6 + c)))])
    (gc_ohead 0x47f94 ra gp tp t0 t1 a0 a1 a2 a3 a4 a5 a6 a7 s3 s5 s8 s11 t4 t5 t6 FR fc spf fs bot cur c m).
Proof.
  intros until fsz. intros MI C F0 FB LOG FRM SPLO SPHI RSP RFS.
  unfold gc_ohead.
  pose proof (munch_refl [(spf + 32, spf + 40)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  zstep.
  zstep.
  zstep. zstep. zstep. zstep.
  zstep. zstep. zstep. zstep.
  zstep. zstep. zstep.
  zstep. zstep.
  zstep.
  zstep.
  assert (E8 : forall x, 0 <= x < 11 ->
     Z.shiftl (Z.land ((Z.shiftl 18446744073709551615 ((bv_swrap 32 (10 - x) mod 18446744073709551616) mod 64)) mod 18446744073709551616) 1023) 5 = 32768 - 2 ^ (15 - x)).
  { intros x X. assert (XX : x = 0 \/ x = 1 \/ x = 2 \/ x = 3 \/ x = 4 \/ x = 5 \/ x = 6 \/ x = 7 \/ x = 8 \/ x = 9 \/ x = 10) by lia.
    repeat (destruct XX as [->|XX]; [vm_compute; reflexivity|]). subst x. vm_compute. reflexivity. }
  assert (E6 : Z.shiftl 64 (c mod 64) = 2 ^ (6 + c)).
  { rewrite Z.mod_small by lia. rewrite Z.shiftl_mul_pow2 by lia. rewrite Z.pow_add_r by lia. reflexivity. }
  rewrite E8 in * by exact C. rewrite E6 in *.
  replace (20 - c + -6) with (14 - c) by lia.
  apply evtF_done. do 8 eexists. exists m0. split; [unfold gc_head, gflags; cbv delta [mkR]; reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [assumption| exact FRM].
Qed.

Lemma gc_exit : forall RNG ra gp tp t0 t1 a0 a1 a2 a3 a4 a5 a6 a7 t4 t5 t6 (FR : bvmap 5 word) fc (m : amem) (spf fs bot cur c i : Z),
  0 <= c < 11 ->
  evtF asegs RNG (fun ms' => exists b0 s3 s5 s8 s11,
       (c + 1 < 11 /\ ms' = gc_ohead 0x47f94 ra gp tp t0 t1 b0 a1 a2 a3 a4 a5 a6 a7 s3 s5 s8 s11 t4 t5 t6 FR fc spf fs bot cur (c + 1) m)
    \/ (c + 1 = 11 /\ ms' = gc_ohead 0x4816c ra gp tp t0 t1 b0 a1 a2 a3 a4 a5 a6 a7 s3 s5 s8 s11 t4 t5 t6 FR fc spf fs bot cur (c + 1) m))
    (gc_head 0x47f88 ra gp tp t0 t1 a0 a1 a2 a3 a4 a5 a6 a7 t4 t5 t6 FR fc spf fs bot cur c i m).
Proof.
  intros until i. intros C. unfold gc_head, gc_ohead.
  zstep. zstep.
  zstep. if_cases K; zify_cond K.
  - rewrite ?Z.mod_small in K by lia. apply evtF_done. do 5 eexists. right. split; [lia|]. cbv delta [mkR]. reflexivity.
  - rewrite ?Z.mod_small in K by lia. apply evtF_done. do 5 eexists. left. split; [lia|]. cbv delta [mkR]. reflexivity.
Qed.

Fixpoint gcWall (fs : Z) (fl : Z -> Z -> byte) (rs : Z -> Z -> Z) (bot cur : Z) (c : Z) (k : nat) : list (Z * Z) :=
  match k with
  | O => []
  | S k' => gcW fs c (fl c) (rs c) bot cur 0 (Z.to_nat (gcN c)) ++ gcWall fs fl rs bot cur (c + 1) k'
  end.

Lemma GC_NCLS_sig : {k : nat | Z.of_nat k = 11}. Proof. exists 11%nat. reflexivity. Qed.
Definition GC_NCLS : nat := proj1_sig GC_NCLS_sig.
Lemma GC_NCLS_eq : Z.of_nat GC_NCLS = 11. Proof. exact (proj2_sig GC_NCLS_sig). Qed.

Lemma gcWall_disjoint : forall fs fl rs bot cur A n k c,
  0 <= c -> c + Z.of_nat k <= 11 ->
  (forall c' q, c <= c' < c + Z.of_nat k -> 0 <= q < gcN c' -> gfreed bot cur (fl c' q) (rs c' q) = true ->
       disjoint_from (gcW1 fs c' q) A n) ->
  disjoint_from (gcWall fs fl rs bot cur c k) A n.
Proof.
  intros fs fl rs bot cur A n k. induction k as [|k IH]; intros c C0 CK H; cbn [gcWall]; [exact I|].
  apply gc_disjoint_from_app.
  - apply gcW_disjoint. intros p Hp GF. apply H; [lia| | exact GF].
    assert (0 < gcN c) by (unfold gcN; apply Z.pow_pos_nonneg; lia). rewrite Z2Nat.id in Hp by lia. lia.
  - apply IH; [lia| lia|]. intros c' q Hc' Hq GF. apply H; [lia| exact Hq| exact GF].
Qed.

Definition gc_outer_post (ra gp tp t1 t4 t5 t6 : word) (FR : bvmap 5 word) (fc : bv 32) (spf fs bot cur : Z)
    (fl : Z -> Z -> byte) (rs : Z -> Z -> Z) (c : Z) (k : nat) (v0 : word) (m : amem) : machine_state -> Prop :=
  fun ms' => exists t0' b0 b1 b2 b3 b4 b5 b6 b7 s3 s5 s8 s11 fsz' m',
    ms' = gc_ohead 0x4816c ra gp tp t0' t1 b0 b1 b2 b3 b4 b5 b6 b7 s3 s5 s8 s11 t4 t5 t6 FR fc spf fs bot cur 11 m'
    /\ munch ((spf + 32, spf + 40) :: gcWall fs fl rs bot cur c k) m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' spf [C8 v0; C8 (Z_to_bv 64 0xda7a0); C8 (Z_to_bv 64 0xda7b0); C8 (Z_to_bv 64 0xda7a8); C8 fsz']
    /\ (forall c' p, c <= c' < 11 -> 0 <= p < gcN c' ->
          rw_cells asegs m' (gflag fs c' p) [C1 (if gfreed bot cur (fl c' p) (rs c' p) then Z_to_bv 8 0 else fl c' p)]).

Lemma gc_outer : forall RNG (k : nat) (c : Z) ra gp tp t0 t1 a0 a1 a2 a3 a4 a5 a6 a7 s3 s5 s8 s11 t4 t5 t6 (FR : bvmap 5 word) fc (m : amem)
    (spf fs bot cur : Z) (fl : Z -> Z -> byte) (rs : Z -> Z -> Z) (v0 fsz : word),
  Z.of_nat k = 11 - c -> 0 <= c < 11 ->
  mem_inv asegs m ->
  ablk fs (fs + 11571200) -> fs + 11571200 <= ATOP -> fs mod 4096 = 0 ->
  0 <= bot < 2^64 -> 0 <= cur < 2^64 ->
  rw_cells asegs m (fs + 88) [C8 (Z_to_bv 64 20)] ->
  rt_shbase m -> rt_layout m ->
  rw_cells asegs m spf [C8 v0; C8 (Z_to_bv 64 0xda7a0); C8 (Z_to_bv 64 0xda7b0); C8 (Z_to_bv 64 0xda7a8); C8 fsz] ->
  (forall c' p, c <= c' < 11 -> 0 <= p < gcN c' -> rw_cells asegs m (gflag fs c' p) [C1 (fl c' p)]) ->
  (forall c' p, c <= c' < 11 -> 0 <= p < gcN c' -> bv_unsigned (fl c' p) <> 0 ->
       0 <= rs c' p < 2^64 /\ rw_cells asegs m (gframe fs c' p + 24) [C8 (Z_to_bv 64 (rs c' p))]) ->
  (forall c' p, c <= c' < 11 -> 0 <= p < gcN c' -> gfreed bot cur (fl c' p) (rs c' p) = true ->
       c' <= 2 /\ exists ws, length ws = Z.to_nat (2 ^ c') /\ rw_cells asegs m (shad (gframe fs c' p)) (map C8 ws)) ->
  ATOP <= spf -> spf + 40 <= 2^64 ->
  rng_aimg RNG -> rng RNG spf 40 -> rng RNG fs 11571200 -> rng RNG (shad fs) (shlen 11571200) ->
  evtF asegs RNG (gc_outer_post ra gp tp t1 t4 t5 t6 FR fc spf fs bot cur fl rs c k v0 m)
    (gc_ohead 0x47f94 ra gp tp t0 t1 a0 a1 a2 a3 a4 a5 a6 a7 s3 s5 s8 s11 t4 t5 t6 FR fc spf fs bot cur c m).
Proof.
  intros RNG k. induction k as [|k IH]; intros until fsz;
    intros HK C MI FLO FHI FAL BOT CUR LOG SHB LAY FRM FL RS SH SPLO SPHI RIMG RSP RFS RSH; [lia|].
  pose proof (ablk_lin _ _ FLO) as (FLOL & F0 & _ & FB). unfold AIMG_HI in FLOL.
  assert (NPOS : 0 < gcN c) by (unfold gcN; apply Z.pow_pos_nonneg; lia).
  pose proof atop_range as ATR.

  eapply evtF_cut.
  { eapply gc_setup; try eassumption; lia. }
  cbv beta. intros ms1 (b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & m1 & -> & MU1 & WM1 & MI1 & FRM1).
  assert (TR1 : forall A cs, rw_cells asegs m A cs -> A + Z.of_nat (cells_size cs) <= ATOP -> rw_cells asegs m1 A cs).
  { intros A cs H HA. eapply rw_cells_transport; [exact H| exact MU1| exact WM1|]. cbn [disjoint_from]. split; [lia| exact I]. }

  eapply evtF_cut.
  { eapply (gc_class_loop RNG (Z.to_nat (gcN c)) 0) with (fl := fl c) (rs := rs c) (m := m1); try eassumption; try lia.
    - apply TR1; [exact LOG| cbn; lia].
    - apply TR1; [exact SHB| cbn; lia].
    - apply TR1; [exact LAY| cbn; lia].
    - intros p Hp. pose proof (gc_geo fs c p C ltac:(lia) F0) as (G1 & _). apply TR1; [apply FL; lia| cbn; lia].
    - intros p Hp NZ. destruct (RS c p ltac:(lia) ltac:(lia) NZ) as (R1 & R2). split; [exact R1|].
      pose proof (gc_geo fs c p C ltac:(lia) F0) as (_ & _ & G3). pose proof (gc_pows c C) as (_ & _ & P6 & _).
      apply TR1; [exact R2| cbn; lia].
    - intros p Hp GF. destruct (SH c p ltac:(lia) ltac:(lia) GF) as (C2 & ws & LWS & CELL). split; [exact C2|]. exists ws. split; [exact LWS|].
      pose proof (gc_shad_off fs c p C ltac:(lia) FLO FHI) as (_ & _ & HI).
      apply TR1; [exact CELL|].
      assert (CS : forall l : list word, Z.of_nat (cells_size (map C8 l)) = 8 * Z.of_nat (length l)).
      { induction l as [|w l IHl]; [reflexivity|]. cbn [map cells_size csize length]. rewrite Nat2Z.inj_add, IHl. lia. }
      rewrite CS, LWS, Z2Nat.id by lia. lia. }
  cbv beta. intros ms2 (t0' & d0 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & m2 & -> & MU2 & WM2 & MI2 & FLS2).
  assert (TR2 : forall A cs, rw_cells asegs m1 A cs ->
             (forall q, 0 <= q < gcN c -> disjoint_from (gcW1 fs c q) A (Z.of_nat (cells_size cs))) -> rw_cells asegs m2 A cs).
  { intros A cs H HD. eapply rw_cells_transport; [exact H| exact MU2| exact WM2|]. apply gcW_disjoint. intros q Hq _. apply HD.
    rewrite Z2Nat.id in Hq by lia. lia. }

  eapply evtF_cut.
  { eapply gc_exit. exact C. }
  cbv beta. intros ms3 (e0 & s3' & s5' & s8' & s11' & [[LT ->] | [EQ ->]]).
  -
    eapply evtF_mono.
    { eapply (IH (c + 1)) with (m := m2) (fl := fl) (rs := rs); try eassumption; try lia.
      - apply TR2; [apply TR1; [exact LOG| cbn; lia]|]. intros q Hq. apply gcW1_disj_in_fs; try assumption; cbn; try lia.
        pose proof (gc_geo fs c q C Hq F0) as (G1 & _). lia.
      - apply TR2; [apply TR1; [exact SHB| cbn; lia]|]. intros q Hq. apply gcW1_disj_img; try assumption; cbn; lia.
      - apply TR2; [apply TR1; [exact LAY| cbn; lia]|]. intros q Hq. apply gcW1_disj_img; try assumption; cbn; lia.
      - apply TR2; [exact FRM1|]. intros q Hq. apply gcW1_disj_stack; assumption.
      - intros c' p Hc' Hp. pose proof (gc_geo fs c' p ltac:(lia) Hp F0) as (G1 & _).
        apply TR2; [apply TR1; [apply FL; lia| cbn; lia]|]. intros q Hq. apply gcW1_disj_flag2; try assumption; try lia. intros E; injection E; lia.
      - intros c' p Hc' Hp NZ. destruct (RS c' p ltac:(lia) Hp NZ) as (R1 & R2). split; [exact R1|].
        pose proof (gc_geo fs c' p ltac:(lia) Hp F0) as (_ & G2 & G3). pose proof (gc_pows c' ltac:(lia)) as (_ & _ & P6 & _).
        apply TR2; [apply TR1; [exact R2| cbn; lia]|]. intros q Hq. apply gcW1_disj_in_fs; try assumption; cbn; try lia.
        pose proof (gc_geo fs c q C Hq F0) as (G1 & _). lia.
      - intros c' p Hc' Hp GF. destruct (SH c' p ltac:(lia) Hp GF) as (C2 & ws & LWS & CELL). split; [exact C2|]. exists ws. split; [exact LWS|].
        pose proof (gc_shad_off fs c' p ltac:(lia) Hp FLO FHI) as (_ & _ & HI).
        assert (CS : forall l : list word, Z.of_nat (cells_size (map C8 l)) = 8 * Z.of_nat (length l)).
        { induction l as [|w l IHl]; [reflexivity|]. cbn [map cells_size csize length]. rewrite Nat2Z.inj_add, IHl. lia. }
        assert (PC' : 0 < 2 ^ c') by (apply Z.pow_pos_nonneg; lia).
        apply TR2; [apply TR1; [exact CELL| rewrite CS, LWS, Z2Nat.id by lia; lia]|].
        intros q Hq. rewrite CS, LWS, Z2Nat.id by lia. apply gcW1_disj_shadow2; try assumption; try lia. intros E; injection E; lia. }
    cbv beta. intros ms' (t0'' & g0 & g1 & g2 & g3 & g4 & g5 & g6 & g7 & h3 & h5 & h8 & h11 & fsz' & m' & -> & MU3 & WM3 & MI3 & FRM3 & FLS3).
    exists t0'', g0, g1, g2, g3, g4, g5, g6, g7, h3, h5, h8, h11, fsz', m'. split; [reflexivity|].
    split.
    { cbn [gcWall]. eapply munch_trans; [| eapply munch_trans].
      - eapply munch_weaken; [| exact MU1]. intros x Hx. cbn [outside] in Hx |- *. tauto.
      - eapply munch_weaken; [| exact MU2]. intros x Hx. cbn [outside] in Hx. destruct Hx as [_ Hx]. apply gc_outside_app in Hx. tauto.
      - eapply munch_weaken; [| exact MU3]. intros x Hx. cbn [outside] in Hx |- *. destruct Hx as [Hx1 Hx]. apply gc_outside_app in Hx. tauto. }
    split; [eapply wmono_trans; [exact WM1|]; eapply wmono_trans; [exact WM2| exact WM3]|]. split; [exact MI3|]. split; [exact FRM3|].
    intros c' p Hc' Hp. destruct (Z.eq_dec c' c) as [->|NE]; [| apply FLS3; [lia| exact Hp]].
    eapply rw_cells_transport; [apply FLS2; lia| exact MU3| exact WM3|].
    cbn [disjoint_from]. pose proof (gc_geo fs c p C Hp F0) as (G1 & _). split; [cbn; lia|].
    apply gcWall_disjoint; [lia| lia|]. intros c'' q Hc'' Hq _. apply gcW1_disj_flag2; try assumption; try lia. intros E; injection E; lia.
  -
    assert (k = 0)%nat by lia. subst k.
    apply evtF_done. exists t0', e0, d1, d2, d3, d4, d5, d6, d7, s3', s5', s8', s11'. eexists. exists m2. rewrite EQ. split; [reflexivity|].
    split.
    { cbn [gcWall]. rewrite app_nil_r. eapply munch_trans.
      - eapply munch_weaken; [| exact MU1]. intros x Hx. cbn [outside] in Hx |- *. tauto.
      - eapply munch_weaken; [| exact MU2]. intros x Hx. cbn [outside] in Hx. tauto. }
    split; [eapply wmono_trans; [exact WM1| exact WM2]|]. split; [exact MI2|].
    split; [apply TR2; [exact FRM1|]; intros q Hq; apply gcW1_disj_stack; assumption|].
    intros c' p Hc' Hp. assert (c' = c) by lia. subst c'. apply FLS2. lia.
Qed.
End CANSEC1.

Section CANSEC2. Context {rc : runConstT}.
Definition AGC : Z := 0x47ec4.

Definition gc_W (sp fs : Z) (fl : Z -> Z -> byte) (rs : Z -> Z -> Z) (bot cur : Z) : list (Z * Z) :=
  (sp - 208, sp) :: (fs + 96, fs + 97) :: gcWall fs fl rs bot cur 0 GC_NCLS.

Definition gc_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32)
    (lo fs bot cur : Z) (fl : Z -> Z -> byte) (rs : Z -> Z -> Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             FR (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch (gc_W (bv_unsigned sp) fs fl rs bot cur) m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp)
    /\ rw_cells asegs m' (fs + 96) [C1 (Z_to_bv 8 0)]
    /\ (forall c p, 0 <= c < 11 -> 0 <= p < gcN c ->
          rw_cells asegs m' (gflag fs c p) [C1 (if gfreed bot cur (fl c p) (rs c p) then Z_to_bv 8 0 else fl c p)]).

Definition gc_pro_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t4 t5 t6 : word) (FR : bvmap 5 word) (fc : bv 32)
    (lo fs bot cur : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists ra' t0' t1' b0 b1 b2 b3 b4 b5 b6 b7 q3 q5 q8 q11 wj m1,
    ms' = gc_ohead 0x47f94 ra' gp tp t0' t1' b0 b1 b2 b3 b4 b5 b6 b7 q3 q5 q8 q11 t4 t5 t6 FR fc (bv_unsigned sp + -144) fs bot cur 0 m1
    /\ munch [(bv_unsigned sp - 208, bv_unsigned sp)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
    /\ stk asegs m1 lo (bv_unsigned sp + -144)
    /\ rw_cells asegs m1 (bv_unsigned sp + -144)
         [C8 (Z_to_bv 64 881336); C8 (Z_to_bv 64 0xda7a0); C8 (Z_to_bv 64 0xda7b0); C8 (Z_to_bv 64 0xda7a8); C8 wj]
    /\ rw_cells asegs m1 (bv_unsigned sp + -104) [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

Lemma gc_prologue : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (FR : bvmap 5 word) fc (m : amem) (lo ctx t top bot fs cur : Z),
  mem_inv asegs m ->
  stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 208 -> ATOP <= lo ->
  tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 fs -> a1 = Z_to_bv 64 cur ->
  rw_cells asegs m ATSDI [C1 (Z_to_bv 8 1)] -> rw_cells asegs m ATSDK [C4 (Z_to_bv 64 0)] ->
  rw_cells asegs m ATP88 [C8 (Z_to_bv 64 ATSD)] -> rw_cells asegs m ATSD [C8 (Z_to_bv 64 ctx)] ->
  rw_cells asegs m (ctx + 152) [C8 (Z_to_bv 64 t)] ->
  rw_cells asegs m (t + 8) [C8 (Z_to_bv 64 top); C8 (Z_to_bv 64 bot)] -> rw_cells asegs m (t + 40) [C1 (Z_to_bv 8 0)] ->
  0 < ctx -> ctx + 4096 <= ATOP -> 0 < t -> t + 4096 <= ATOP -> 0 <= bot -> bot < top -> top <= 2^47 ->
  bot <= cur <= top ->
  rt_got m ->
  0 <= fs -> fs + 4096 < 2^64 ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG ctx 4096 -> rng RNG t 4096 ->
  evtF asegs RNG (gc_pro_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t4 t5 t6 FR fc lo fs bot cur m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        FR (Z_to_bv 64 AGC) fc None m (seg_rom asegs)).
Proof.
  intros until cur.
  intros MI ST LO CEIL TP A0 A1 TI TK T88 TSD CT TB SW CXa CXb T0 T1 B0 BT TT CURR GOT F0 FB RIMG RSTK RCTX RT.
  subst a0 a1.
  pose proof (munch_refl [(bv_unsigned sp - 208, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  unfold ATP, ATSDI, ATSDK, ATP88, ATSD, AGC in *.
  carve_frame 144%nat ST.
  do 14 zstep.
  zstep. zstep.
  zstep.
  box RCTX; box RT.
  call_sp get_current_thread_spec;
    first [ exact MI | exact ST | exact TP | reflexivity | exact TI | exact TK | exact T88 | exact TSD | exact CT
          | exact RIMG | (unbox RCTX; exact RCTX) | lia | solve_rng | idtac ].
  unbox RCTX.
  rename POST into ST.
  lazymatch goal with H : mem_inv asegs _ |- _ => rename H into MI2 end.
  zstep. if_cases Ka; zify_cond Ka; [exfalso; clear - Ka T0 T1; pose proof atop_range; lia|].
  zstep.
  zstep.
  unbox RT. callp stack_top_spec; [exact MI2 | reflexivity | exact TB | exact SW | lia | lia | lia | lia | exact T1 |].
  zstep. zstep.
  zstep.
  callp stack_bottom_spec; [exact MI2 | reflexivity | exact TB | exact SW | lia | lia | lia | lia | exact T1 |].
  zstep. if_cases Kt; zify_cond Kt; [exfalso; clear - Kt CURR B0 TT BT; rewrite ?Z.mod_small in Kt by lia; lia|].
  zstep.
  zstep. if_cases Kb; zify_cond Kb; [exfalso; clear - Kb CURR B0 TT BT; rewrite ?Z.mod_small in Kb by lia; lia|].
  zstep. zstep.
  do 6 zstep.
  zstep.
  zstep.
  zstep. zstep.
  zstep. zstep.
  zstep. zstep.
  zstep. zstep.
  zstep.
  zstep. zstep. zstep.
  zstep.

  lazymatch goal with FRx : rw_cells asegs ?mm (bv_unsigned sp + -144) (?c0 :: ?c1 :: ?c2 :: ?c3 :: CB 8 ?jb :: ?rest) |- _ =>
    pose proof (proj1 (rw_cells_app asegs mm (bv_unsigned sp + -144) [c0; c1; c2; c3] (CB 8 jb :: rest)) FRx) as [FRa FRb];
    pose proof (proj1 (rw_cells_app asegs mm _ [CB 8 jb] rest) FRb) as [FRc FRd];
    destruct (c8_of_CB mm _ jb FRc) as (wj & FRc8 & _);
    assert (FRM : rw_cells asegs mm (bv_unsigned sp + -144) ([c0; c1; c2; c3] ++ [C8 wj])) by (apply rw_cells_app; split; [exact FRa| exact FRc8]);
    clear FRx FRa FRb FRc FRc8
  end.
  cbn [app cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in FRM, FRd.
  replace (bv_unsigned sp + -144 + Z.of_nat 32 + Z.of_nat 8) with (bv_unsigned sp + -104) in FRd by lia.
  apply evtF_done. unfold gc_pro_post, gc_ohead. do 16 eexists. eexists. split; [cbv delta [mkR]; reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|]. split; [exact FRM| exact FRd].
Qed.

Lemma gc_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (FR : bvmap 5 word) fc (m : amem) (lo ctx t top bot fs cur : Z) (g : byte) (fl : Z -> Z -> byte) (rs : Z -> Z -> Z),
  mem_inv asegs m ->
  stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 208 -> ATOP <= lo ->
  tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 fs -> a1 = Z_to_bv 64 cur ->

  rw_cells asegs m ATSDI [C1 (Z_to_bv 8 1)] -> rw_cells asegs m ATSDK [C4 (Z_to_bv 64 0)] ->
  rw_cells asegs m ATP88 [C8 (Z_to_bv 64 ATSD)] -> rw_cells asegs m ATSD [C8 (Z_to_bv 64 ctx)] ->
  rw_cells asegs m (ctx + 152) [C8 (Z_to_bv 64 t)] ->
  rw_cells asegs m (t + 8) [C8 (Z_to_bv 64 top); C8 (Z_to_bv 64 bot)] -> rw_cells asegs m (t + 40) [C1 (Z_to_bv 8 0)] ->
  0 < ctx -> ctx + 4096 <= ATOP -> 0 < t -> t + 4096 <= ATOP -> 0 <= bot -> bot < top -> top <= 2^47 ->
  bot <= cur <= top ->
  rt_got m -> rt_shbase m -> rt_layout m ->

  ablk fs (fs + 11571200) -> fs + 11571200 <= ATOP -> fs mod 4096 = 0 ->
  rw_cells asegs m (fs + 88) [C8 (Z_to_bv 64 20)] -> rw_cells asegs m (fs + 96) [C1 g] ->
  (forall c p, 0 <= c < 11 -> 0 <= p < gcN c -> rw_cells asegs m (gflag fs c p) [C1 (fl c p)]) ->
  (forall c p, 0 <= c < 11 -> 0 <= p < gcN c -> bv_unsigned (fl c p) <> 0 ->
       0 <= rs c p < 2^64 /\ rw_cells asegs m (gframe fs c p + 24) [C8 (Z_to_bv 64 (rs c p))]) ->
  (forall c p, 0 <= c < 11 -> 0 <= p < gcN c -> gfreed bot cur (fl c p) (rs c p) = true ->
       c <= 2 /\ exists ws, length ws = Z.to_nat (2 ^ c) /\ rw_cells asegs m (shad (gframe fs c p)) (map C8 ws)) ->

  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG ctx 4096 -> rng RNG t 4096 ->
  rng RNG fs 11571200 -> rng RNG (shad fs) (shlen 11571200) ->
  evtF asegs RNG (gc_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc lo fs bot cur fl rs m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        FR (Z_to_bv 64 AGC) fc None m (seg_rom asegs)).
Proof.
  intros until rs.
  intros MI ST LO CEIL TP A0 A1 TI TK T88 TSD CT TB SW CXa CXb T0 T1 B0 BT TT CURR GOT SHB LAY
         FLO FHI FAL LOG NGC FL RS SH RIMG RSTK RCTX RT RFS RSH.
  pose proof (ablk_lin _ _ FLO) as (FLOL & F0 & _ & FB). unfold AIMG_HI in FLOL.
  eapply evtF_cut.
  { eapply gc_prologue with (lo := lo) (ctx := ctx) (t := t) (top := top) (bot := bot) (fs := fs) (cur := cur); try eassumption; lia. }
  cbv beta. intros ms1 (ra' & u0 & u1 & e0 & e1 & e2 & e3 & e4 & e5 & e6 & e7 & p3 & p5 & p8 & p11 & wj & m1 & -> & MU & WM & MI1 & ST1 & FRM & FRd).
  clear ST. rename ST1 into ST.
  assert (TRm : forall A cs, rw_cells asegs m A cs -> A + Z.of_nat (cells_size cs) <= ATOP -> rw_cells asegs m1 A cs)
    by (intros A cs H HA; eapply rw_cells_transport; [exact H| exact MU| exact WM|]; cbn [disjoint_from]; split; [lia| exact I]).
  pose proof atop_range as ATR0.
  apply TRm in LOG; [| cbn; lia]. apply TRm in NGC; [| cbn; lia]. apply TRm in SHB; [| cbn; lia]. apply TRm in LAY; [| cbn; lia].
  pose proof atop_range as ATR.
  assert (SPB : bv_unsigned sp < 2^64) by (pose proof (bv_unsigned_in_range 64 sp) as X; exact (proj2 X)).
  lazymatch goal with MUx : munch _ m ?mm |- _ =>
    assert (TR : forall A cs, rw_cells asegs m A cs -> A + Z.of_nat (cells_size cs) <= ATOP -> rw_cells asegs mm A cs)
      by (intros A cs H HA; eapply rw_cells_transport; [exact H| exact MUx| exact WM|]; cbn [disjoint_from]; split; [lia| exact I])
  end.

  pose proof GC_NCLS_eq as NCE.
  eapply evtF_cut.
  { eapply (gc_outer RNG GC_NCLS 0) with (fl := fl) (rs := rs); try eassumption; try lia.
    - intros c p Hc Hp. pose proof (gc_geo fs c p Hc Hp F0) as (G1 & _). apply TR; [apply FL; assumption| cbn; lia].
    - intros c p Hc Hp NZ. destruct (RS c p Hc Hp NZ) as (R1 & R2). split; [exact R1|].
      pose proof (gc_geo fs c p Hc Hp F0) as (_ & _ & G3). pose proof (gc_pows c Hc) as (_ & _ & P6 & _). apply TR; [exact R2| cbn; lia].
    - intros c p Hc Hp GF. destruct (SH c p Hc Hp GF) as (C2 & ws & LWS & CELL). split; [exact C2|]. exists ws. split; [exact LWS|].
      pose proof (gc_shad_off fs c p Hc Hp FLO FHI) as (_ & _ & HI).
      assert (CS : forall l : list word, Z.of_nat (cells_size (map C8 l)) = 8 * Z.of_nat (length l)).
      { induction l as [|w l IHl]; [reflexivity|]. cbn [map cells_size csize length]. rewrite Nat2Z.inj_add, IHl. lia. }
      assert (PC : 0 < 2 ^ c) by (apply Z.pow_pos_nonneg; lia).
      apply TR; [exact CELL| rewrite CS, LWS, Z2Nat.id by lia; lia].
    - eapply rng_sub'; [exact RSTK|]. lia. }
  cbv beta. intros ms' (t0' & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & q3 & q5 & q8 & q11 & fsz' & m' & -> & MUo & WMo & MIo & FRMo & FLSo).

  assert (WD1 : forall A n, ATOP <= A -> disjoint_from (gcWall fs fl rs bot cur 0 GC_NCLS) A n).
  { intros A n HA. apply gcWall_disjoint; [lia| lia|]. intros c q Hc Hq _. apply gcW1_disj_stack; try assumption; lia. }
  assert (WD2 : forall A n, fs <= A -> A + n <= fs + 4096 -> 0 <= n -> disjoint_from (gcWall fs fl rs bot cur 0 GC_NCLS) A n).
  { intros A n HA HB HN. apply gcWall_disjoint; [lia| lia|]. intros c q Hc Hq _.
    pose proof (gc_geo fs c q ltac:(lia) Hq F0) as (G1 & _). apply gcW1_disj_in_fs; try assumption; lia. }
  assert (DST : forall A n, ATOP <= A -> (A + n <= bv_unsigned sp + -144 + 32 \/ bv_unsigned sp + -144 + 40 <= A) ->
            disjoint_from ((bv_unsigned sp + -144 + 32, bv_unsigned sp + -144 + 40) :: gcWall fs fl rs bot cur 0 GC_NCLS) A n).
  { intros A n HA HD. cbn [disjoint_from]. split; [lia|]. apply WD1. exact HA. }
  lazymatch goal with MUx : munch _ m ?mm |- _ =>
    eapply (rw_cells_transport asegs _ mm m') in FRd; [| exact MUo| exact WMo| apply DST; cbn; lia];
    eapply (rw_cells_transport asegs _ mm m') in NGC; [| exact MUo| exact WMo|]
  end.
  2:{ cbn [disjoint_from]. split; [cbn; lia|]. apply WD2; cbn; lia. }
  lazymatch goal with MUx : munch _ m ?mm |- _ =>
    eapply (stk_transport_disjoint asegs ((bv_unsigned sp + -144 + 32, bv_unsigned sp + -144 + 40) :: gcWall fs fl rs bot cur 0 GC_NCLS) mm m') in ST; [| exact MUo| exact WMo| apply DST; lia];
    assert (MUf : munch ((bv_unsigned sp - 208, bv_unsigned sp) :: (fs + 96, fs + 97) :: gcWall fs fl rs bot cur 0 GC_NCLS) m m')
      by (eapply munch_trans;
          [ eapply munch_weaken; [| exact MUx]; intros xx Hxx; cbn [outside] in Hxx |- *; tauto
          | eapply munch_weaken; [| exact MUo]; intros xx Hxx; cbn [outside] in Hxx |- *;
            destruct Hxx as (Hx1 & Hx2 & Hx3); split; [lia| exact Hx3] ]);
    assert (WMf : wmono asegs m m') by (eapply wmono_trans; [exact WM| exact WMo]);
    clear MUx WM MUo WMo TR
  end.
  unfold gc_ohead.
  pose proof (munch_refl [(fs + 96, fs + 97)]%Z m') as MUg. pose proof (wmono_refl asegs m') as WMg.
  zstep.
  do 13 zstep.
  zstep. zstep.
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (FRall : rw_cells asegs mm (bv_unsigned sp + -144)
              ([C8 (Z_to_bv 64 881336); C8 (Z_to_bv 64 894880); C8 (Z_to_bv 64 894896); C8 (Z_to_bv 64 894888); C8 fsz'] ++
               [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]))
      by (apply rw_cells_app; split; [exact FRMo|]; cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ];
          replace (bv_unsigned sp + -144 + Z.of_nat 40) with (bv_unsigned sp + -104) by lia; exact FRd)
  end.
  cbn [app] in FRall.
  release_frame FRall ST (bv_unsigned sp).
  apply evtF_done. unfold gc_post. do 16 eexists. split; [cbv delta [mkR]; reflexivity|].
  split; [unfold gc_W; exact MUf|]. split; [exact WMf|]. split; [assumption|]. split; [exact ST|]. split; [exact NGC|].
  intros c p Hc Hp. pose proof (gc_geo fs c p Hc Hp F0) as (G1 & _).
  eapply rw_cells_transport; [apply FLSo; assumption| exact MUg| exact WMg|]. cbn [disjoint_from cells_size csize Nat.add]. split; [cbn; lia| exact I].
Qed.
End CANSEC2.

From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.BothW Require Import BImg.
Module TwinB.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.ITree OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Nodes OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Decode.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.STree OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanCtrl OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanEmbed.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.Shadow.
Import RtCells.TwinB AProto.TwinB ABase.TwinB F_tryinit.TwinB.

  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aunwind.TwinB.F_aunwind.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_tlsga.TwinB.F_tlsga. Import F_m2s_b.TwinB.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.StepF.
Import AKit.TwinB AKit2.TwinB FsKit.TwinB ABytes.TwinB AFake_gc.TwinB AFake_gcl.TwinB.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac solve_load ::= first [ solve_load_g | solve_load_image ].
Local Ltac solve_store ::= solve_store_g.

Section CANSEC1. Context {rc : runConstT}.

Definition gc_ohead (pc : Z) (ra gp tp t0 t1 a0 a1 a2 a3 a4 a5 a6 a7 s3 s5 s8 s11 t4 t5 t6 : word) (FR : bvmap 5 word) (fc : bv 32)
    (spf fs bot cur c : Z) (m : amem) : machine_state :=
  MS (mkR ra (Z_to_bv 64 spf) gp tp t0 t1 (Z_to_bv 64 1) (Z_to_bv 64 (fs + 4096)) (Z_to_bv 64 cur)
          a0 a1 a2 a3 a4 a5 a6 a7
          (Z_to_bv 64 bot) s3 (Z_to_bv 64 c) s5 (Z_to_bv 64 0xdbc78) (Z_to_bv 64 GCMAGIC)
          s8 (Z_to_bv 64 fs) (Z_to_bv 64 0) s11
          (Z_to_bv 64 6) t4 t5 t6) FR (Z_to_bv 64 pc) fc None m (seg_rom bsegs).

Lemma gc_setup : forall RNG ra gp tp t0 t1 a0 a1 a2 a3 a4 a5 a6 a7 s3 s5 s8 s11 t4 t5 t6 (FR : bvmap 5 word) fc (m : amem)
    (spf fs bot cur c : Z) (v0 fsz : word),
  mem_inv bsegs m -> 0 <= c < 11 -> 0 <= fs -> fs + 11571200 <= 2^47 ->
  rw_cells bsegs m (fs + 88) [C8 (Z_to_bv 64 20)] ->
  rw_cells bsegs m spf [C8 v0; C8 (Z_to_bv 64 0xdc960); C8 (Z_to_bv 64 0xdc970); C8 (Z_to_bv 64 0xdc968); C8 fsz] ->
  ATOP <= spf -> spf + 40 <= 2^64 ->
  rng RNG spf 40 -> rng RNG fs 11571200 ->
  evtF bsegs RNG (fun ms' => exists b0 b1 b2 b3 b4 b5 b6 b7 m',
       ms' = gc_head 0x48988 ra gp tp t0 t1 b0 b1 b2 b3 b4 b5 b6 b7 t4 t5 t6 FR fc spf fs bot cur c 0 m'
       /\ munch [(spf + 32, spf + 40)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
       /\ rw_cells bsegs m' spf [C8 v0; C8 (Z_to_bv 64 0xdc960); C8 (Z_to_bv 64 0xdc970); C8 (Z_to_bv 64 0xdc968); C8 (Z_to_bv 64 (2 ^ (6 + c)))])
    (gc_ohead 0x48924 ra gp tp t0 t1 a0 a1 a2 a3 a4 a5 a6 a7 s3 s5 s8 s11 t4 t5 t6 FR fc spf fs bot cur c m).
Proof.
  intros until fsz. intros MI C F0 FB LOG FRM SPLO SPHI RSP RFS.
  unfold gc_ohead.
  pose proof (munch_refl [(spf + 32, spf + 40)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  zstep.
  zstep.
  zstep. zstep. zstep. zstep.
  zstep. zstep. zstep. zstep.
  zstep. zstep. zstep.
  zstep. zstep.
  zstep.
  zstep.
  assert (E8 : forall x, 0 <= x < 11 ->
     Z.shiftl (Z.land ((Z.shiftl 18446744073709551615 ((bv_swrap 32 (10 - x) mod 18446744073709551616) mod 64)) mod 18446744073709551616) 1023) 5 = 32768 - 2 ^ (15 - x)).
  { intros x X. assert (XX : x = 0 \/ x = 1 \/ x = 2 \/ x = 3 \/ x = 4 \/ x = 5 \/ x = 6 \/ x = 7 \/ x = 8 \/ x = 9 \/ x = 10) by lia.
    repeat (destruct XX as [->|XX]; [vm_compute; reflexivity|]). subst x. vm_compute. reflexivity. }
  assert (E6 : Z.shiftl 64 (c mod 64) = 2 ^ (6 + c)).
  { rewrite Z.mod_small by lia. rewrite Z.shiftl_mul_pow2 by lia. rewrite Z.pow_add_r by lia. reflexivity. }
  rewrite E8 in * by exact C. rewrite E6 in *.
  replace (20 - c + -6) with (14 - c) by lia.
  apply evtF_done. do 8 eexists. exists m0. split; [unfold gc_head, gflags; cbv delta [mkR]; reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [assumption| exact FRM].
Qed.

Lemma gc_exit : forall RNG ra gp tp t0 t1 a0 a1 a2 a3 a4 a5 a6 a7 t4 t5 t6 (FR : bvmap 5 word) fc (m : amem) (spf fs bot cur c i : Z),
  0 <= c < 11 ->
  evtF bsegs RNG (fun ms' => exists b0 s3 s5 s8 s11,
       (c + 1 < 11 /\ ms' = gc_ohead 0x48924 ra gp tp t0 t1 b0 a1 a2 a3 a4 a5 a6 a7 s3 s5 s8 s11 t4 t5 t6 FR fc spf fs bot cur (c + 1) m)
    \/ (c + 1 = 11 /\ ms' = gc_ohead 0x48afc ra gp tp t0 t1 b0 a1 a2 a3 a4 a5 a6 a7 s3 s5 s8 s11 t4 t5 t6 FR fc spf fs bot cur (c + 1) m))
    (gc_head 0x48918 ra gp tp t0 t1 a0 a1 a2 a3 a4 a5 a6 a7 t4 t5 t6 FR fc spf fs bot cur c i m).
Proof.
  intros until i. intros C. unfold gc_head, gc_ohead.
  zstep. zstep.
  zstep. if_cases K; zify_cond K.
  - rewrite ?Z.mod_small in K by lia. apply evtF_done. do 5 eexists. right. split; [lia|]. cbv delta [mkR]. reflexivity.
  - rewrite ?Z.mod_small in K by lia. apply evtF_done. do 5 eexists. left. split; [lia|]. cbv delta [mkR]. reflexivity.
Qed.

Fixpoint gcWall (fs : Z) (fl : Z -> Z -> byte) (rs : Z -> Z -> Z) (bot cur : Z) (c : Z) (k : nat) : list (Z * Z) :=
  match k with
  | O => []
  | S k' => gcW fs c (fl c) (rs c) bot cur 0 (Z.to_nat (gcN c)) ++ gcWall fs fl rs bot cur (c + 1) k'
  end.

Lemma GC_NCLS_sig : {k : nat | Z.of_nat k = 11}. Proof. exists 11%nat. reflexivity. Qed.
Definition GC_NCLS : nat := proj1_sig GC_NCLS_sig.
Lemma GC_NCLS_eq : Z.of_nat GC_NCLS = 11. Proof. exact (proj2_sig GC_NCLS_sig). Qed.

Lemma gcWall_disjoint : forall fs fl rs bot cur A n k c,
  0 <= c -> c + Z.of_nat k <= 11 ->
  (forall c' q, c <= c' < c + Z.of_nat k -> 0 <= q < gcN c' -> gfreed bot cur (fl c' q) (rs c' q) = true ->
       disjoint_from (gcW1 fs c' q) A n) ->
  disjoint_from (gcWall fs fl rs bot cur c k) A n.
Proof.
  intros fs fl rs bot cur A n k. induction k as [|k IH]; intros c C0 CK H; cbn [gcWall]; [exact I|].
  apply gc_disjoint_from_app.
  - apply gcW_disjoint. intros p Hp GF. apply H; [lia| | exact GF].
    assert (0 < gcN c) by (unfold gcN; apply Z.pow_pos_nonneg; lia). rewrite Z2Nat.id in Hp by lia. lia.
  - apply IH; [lia| lia|]. intros c' q Hc' Hq GF. apply H; [lia| exact Hq| exact GF].
Qed.

Definition gc_outer_post (ra gp tp t1 t4 t5 t6 : word) (FR : bvmap 5 word) (fc : bv 32) (spf fs bot cur : Z)
    (fl : Z -> Z -> byte) (rs : Z -> Z -> Z) (c : Z) (k : nat) (v0 : word) (m : amem) : machine_state -> Prop :=
  fun ms' => exists t0' b0 b1 b2 b3 b4 b5 b6 b7 s3 s5 s8 s11 fsz' m',
    ms' = gc_ohead 0x48afc ra gp tp t0' t1 b0 b1 b2 b3 b4 b5 b6 b7 s3 s5 s8 s11 t4 t5 t6 FR fc spf fs bot cur 11 m'
    /\ munch ((spf + 32, spf + 40) :: gcWall fs fl rs bot cur c k) m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ rw_cells bsegs m' spf [C8 v0; C8 (Z_to_bv 64 0xdc960); C8 (Z_to_bv 64 0xdc970); C8 (Z_to_bv 64 0xdc968); C8 fsz']
    /\ (forall c' p, c <= c' < 11 -> 0 <= p < gcN c' ->
          rw_cells bsegs m' (gflag fs c' p) [C1 (if gfreed bot cur (fl c' p) (rs c' p) then Z_to_bv 8 0 else fl c' p)]).

Lemma gc_outer : forall RNG (k : nat) (c : Z) ra gp tp t0 t1 a0 a1 a2 a3 a4 a5 a6 a7 s3 s5 s8 s11 t4 t5 t6 (FR : bvmap 5 word) fc (m : amem)
    (spf fs bot cur : Z) (fl : Z -> Z -> byte) (rs : Z -> Z -> Z) (v0 fsz : word),
  Z.of_nat k = 11 - c -> 0 <= c < 11 ->
  mem_inv bsegs m ->
  ablk fs (fs + 11571200) -> fs + 11571200 <= ATOP -> fs mod 4096 = 0 ->
  0 <= bot < 2^64 -> 0 <= cur < 2^64 ->
  rw_cells bsegs m (fs + 88) [C8 (Z_to_bv 64 20)] ->
  rt_shbase m -> rt_layout m ->
  rw_cells bsegs m spf [C8 v0; C8 (Z_to_bv 64 0xdc960); C8 (Z_to_bv 64 0xdc970); C8 (Z_to_bv 64 0xdc968); C8 fsz] ->
  (forall c' p, c <= c' < 11 -> 0 <= p < gcN c' -> rw_cells bsegs m (gflag fs c' p) [C1 (fl c' p)]) ->
  (forall c' p, c <= c' < 11 -> 0 <= p < gcN c' -> bv_unsigned (fl c' p) <> 0 ->
       0 <= rs c' p < 2^64 /\ rw_cells bsegs m (gframe fs c' p + 24) [C8 (Z_to_bv 64 (rs c' p))]) ->
  (forall c' p, c <= c' < 11 -> 0 <= p < gcN c' -> gfreed bot cur (fl c' p) (rs c' p) = true ->
       c' <= 2 /\ exists ws, length ws = Z.to_nat (2 ^ c') /\ rw_cells bsegs m (shad (gframe fs c' p)) (map C8 ws)) ->
  ATOP <= spf -> spf + 40 <= 2^64 ->
  rng_aimg RNG -> rng RNG spf 40 -> rng RNG fs 11571200 -> rng RNG (shad fs) (shlen 11571200) ->
  evtF bsegs RNG (gc_outer_post ra gp tp t1 t4 t5 t6 FR fc spf fs bot cur fl rs c k v0 m)
    (gc_ohead 0x48924 ra gp tp t0 t1 a0 a1 a2 a3 a4 a5 a6 a7 s3 s5 s8 s11 t4 t5 t6 FR fc spf fs bot cur c m).
Proof.
  intros RNG k. induction k as [|k IH]; intros until fsz;
    intros HK C MI FLO FHI FAL BOT CUR LOG SHB LAY FRM FL RS SH SPLO SPHI RIMG RSP RFS RSH; [lia|].
  pose proof (ablk_lin _ _ FLO) as (FLOL & F0 & _ & FB). unfold AIMG_HI in FLOL.
  assert (NPOS : 0 < gcN c) by (unfold gcN; apply Z.pow_pos_nonneg; lia).
  pose proof atop_range as ATR.

  eapply evtF_cut.
  { eapply gc_setup; try eassumption; lia. }
  cbv beta. intros ms1 (b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & m1 & -> & MU1 & WM1 & MI1 & FRM1).
  assert (TR1 : forall A cs, rw_cells bsegs m A cs -> A + Z.of_nat (cells_size cs) <= ATOP -> rw_cells bsegs m1 A cs).
  { intros A cs H HA. eapply rw_cells_transport; [exact H| exact MU1| exact WM1|]. cbn [disjoint_from]. split; [lia| exact I]. }

  eapply evtF_cut.
  { eapply (gc_class_loop RNG (Z.to_nat (gcN c)) 0) with (fl := fl c) (rs := rs c) (m := m1); try eassumption; try lia.
    - apply TR1; [exact LOG| cbn; lia].
    - apply TR1; [exact SHB| cbn; lia].
    - apply TR1; [exact LAY| cbn; lia].
    - intros p Hp. pose proof (gc_geo fs c p C ltac:(lia) F0) as (G1 & _). apply TR1; [apply FL; lia| cbn; lia].
    - intros p Hp NZ. destruct (RS c p ltac:(lia) ltac:(lia) NZ) as (R1 & R2). split; [exact R1|].
      pose proof (gc_geo fs c p C ltac:(lia) F0) as (_ & _ & G3). pose proof (gc_pows c C) as (_ & _ & P6 & _).
      apply TR1; [exact R2| cbn; lia].
    - intros p Hp GF. destruct (SH c p ltac:(lia) ltac:(lia) GF) as (C2 & ws & LWS & CELL). split; [exact C2|]. exists ws. split; [exact LWS|].
      pose proof (gc_shad_off fs c p C ltac:(lia) FLO FHI) as (_ & _ & HI).
      apply TR1; [exact CELL|].
      assert (CS : forall l : list word, Z.of_nat (cells_size (map C8 l)) = 8 * Z.of_nat (length l)).
      { induction l as [|w l IHl]; [reflexivity|]. cbn [map cells_size csize length]. rewrite Nat2Z.inj_add, IHl. lia. }
      rewrite CS, LWS, Z2Nat.id by lia. lia. }
  cbv beta. intros ms2 (t0' & d0 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & m2 & -> & MU2 & WM2 & MI2 & FLS2).
  assert (TR2 : forall A cs, rw_cells bsegs m1 A cs ->
             (forall q, 0 <= q < gcN c -> disjoint_from (gcW1 fs c q) A (Z.of_nat (cells_size cs))) -> rw_cells bsegs m2 A cs).
  { intros A cs H HD. eapply rw_cells_transport; [exact H| exact MU2| exact WM2|]. apply gcW_disjoint. intros q Hq _. apply HD.
    rewrite Z2Nat.id in Hq by lia. lia. }

  eapply evtF_cut.
  { eapply gc_exit. exact C. }
  cbv beta. intros ms3 (e0 & s3' & s5' & s8' & s11' & [[LT ->] | [EQ ->]]).
  -
    eapply evtF_mono.
    { eapply (IH (c + 1)) with (m := m2) (fl := fl) (rs := rs); try eassumption; try lia.
      - apply TR2; [apply TR1; [exact LOG| cbn; lia]|]. intros q Hq. apply gcW1_disj_in_fs; try assumption; cbn; try lia.
        pose proof (gc_geo fs c q C Hq F0) as (G1 & _). lia.
      - apply TR2; [apply TR1; [exact SHB| cbn; lia]|]. intros q Hq. apply gcW1_disj_img; try assumption; cbn; lia.
      - apply TR2; [apply TR1; [exact LAY| cbn; lia]|]. intros q Hq. apply gcW1_disj_img; try assumption; cbn; lia.
      - apply TR2; [exact FRM1|]. intros q Hq. apply gcW1_disj_stack; assumption.
      - intros c' p Hc' Hp. pose proof (gc_geo fs c' p ltac:(lia) Hp F0) as (G1 & _).
        apply TR2; [apply TR1; [apply FL; lia| cbn; lia]|]. intros q Hq. apply gcW1_disj_flag2; try assumption; try lia. intros E; injection E; lia.
      - intros c' p Hc' Hp NZ. destruct (RS c' p ltac:(lia) Hp NZ) as (R1 & R2). split; [exact R1|].
        pose proof (gc_geo fs c' p ltac:(lia) Hp F0) as (_ & G2 & G3). pose proof (gc_pows c' ltac:(lia)) as (_ & _ & P6 & _).
        apply TR2; [apply TR1; [exact R2| cbn; lia]|]. intros q Hq. apply gcW1_disj_in_fs; try assumption; cbn; try lia.
        pose proof (gc_geo fs c q C Hq F0) as (G1 & _). lia.
      - intros c' p Hc' Hp GF. destruct (SH c' p ltac:(lia) Hp GF) as (C2 & ws & LWS & CELL). split; [exact C2|]. exists ws. split; [exact LWS|].
        pose proof (gc_shad_off fs c' p ltac:(lia) Hp FLO FHI) as (_ & _ & HI).
        assert (CS : forall l : list word, Z.of_nat (cells_size (map C8 l)) = 8 * Z.of_nat (length l)).
        { induction l as [|w l IHl]; [reflexivity|]. cbn [map cells_size csize length]. rewrite Nat2Z.inj_add, IHl. lia. }
        assert (PC' : 0 < 2 ^ c') by (apply Z.pow_pos_nonneg; lia).
        apply TR2; [apply TR1; [exact CELL| rewrite CS, LWS, Z2Nat.id by lia; lia]|].
        intros q Hq. rewrite CS, LWS, Z2Nat.id by lia. apply gcW1_disj_shadow2; try assumption; try lia. intros E; injection E; lia. }
    cbv beta. intros ms' (t0'' & g0 & g1 & g2 & g3 & g4 & g5 & g6 & g7 & h3 & h5 & h8 & h11 & fsz' & m' & -> & MU3 & WM3 & MI3 & FRM3 & FLS3).
    exists t0'', g0, g1, g2, g3, g4, g5, g6, g7, h3, h5, h8, h11, fsz', m'. split; [reflexivity|].
    split.
    { cbn [gcWall]. eapply munch_trans; [| eapply munch_trans].
      - eapply munch_weaken; [| exact MU1]. intros x Hx. cbn [outside] in Hx |- *. tauto.
      - eapply munch_weaken; [| exact MU2]. intros x Hx. cbn [outside] in Hx. destruct Hx as [_ Hx]. apply gc_outside_app in Hx. tauto.
      - eapply munch_weaken; [| exact MU3]. intros x Hx. cbn [outside] in Hx |- *. destruct Hx as [Hx1 Hx]. apply gc_outside_app in Hx. tauto. }
    split; [eapply wmono_trans; [exact WM1|]; eapply wmono_trans; [exact WM2| exact WM3]|]. split; [exact MI3|]. split; [exact FRM3|].
    intros c' p Hc' Hp. destruct (Z.eq_dec c' c) as [->|NE]; [| apply FLS3; [lia| exact Hp]].
    eapply rw_cells_transport; [apply FLS2; lia| exact MU3| exact WM3|].
    cbn [disjoint_from]. pose proof (gc_geo fs c p C Hp F0) as (G1 & _). split; [cbn; lia|].
    apply gcWall_disjoint; [lia| lia|]. intros c'' q Hc'' Hq _. apply gcW1_disj_flag2; try assumption; try lia. intros E; injection E; lia.
  -
    assert (k = 0)%nat by lia. subst k.
    apply evtF_done. exists t0', e0, d1, d2, d3, d4, d5, d6, d7, s3', s5', s8', s11'. eexists. exists m2. rewrite EQ. split; [reflexivity|].
    split.
    { cbn [gcWall]. rewrite app_nil_r. eapply munch_trans.
      - eapply munch_weaken; [| exact MU1]. intros x Hx. cbn [outside] in Hx |- *. tauto.
      - eapply munch_weaken; [| exact MU2]. intros x Hx. cbn [outside] in Hx. tauto. }
    split; [eapply wmono_trans; [exact WM1| exact WM2]|]. split; [exact MI2|].
    split; [apply TR2; [exact FRM1|]; intros q Hq; apply gcW1_disj_stack; assumption|].
    intros c' p Hc' Hp. assert (c' = c) by lia. subst c'. apply FLS2. lia.
Qed.
End CANSEC1.

Section CANSEC2. Context {rc : runConstT}.
Definition AGC : Z := 0x48854.

Definition gc_W (sp fs : Z) (fl : Z -> Z -> byte) (rs : Z -> Z -> Z) (bot cur : Z) : list (Z * Z) :=
  (sp - 208, sp) :: (fs + 96, fs + 97) :: gcWall fs fl rs bot cur 0 GC_NCLS.

Definition gc_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32)
    (lo fs bot cur : Z) (fl : Z -> Z -> byte) (rs : Z -> Z -> Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             FR (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch (gc_W (bv_unsigned sp) fs fl rs bot cur) m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo (bv_unsigned sp)
    /\ rw_cells bsegs m' (fs + 96) [C1 (Z_to_bv 8 0)]
    /\ (forall c p, 0 <= c < 11 -> 0 <= p < gcN c ->
          rw_cells bsegs m' (gflag fs c p) [C1 (if gfreed bot cur (fl c p) (rs c p) then Z_to_bv 8 0 else fl c p)]).

Definition gc_pro_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t4 t5 t6 : word) (FR : bvmap 5 word) (fc : bv 32)
    (lo fs bot cur : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists ra' t0' t1' b0 b1 b2 b3 b4 b5 b6 b7 q3 q5 q8 q11 wj m1,
    ms' = gc_ohead 0x48924 ra' gp tp t0' t1' b0 b1 b2 b3 b4 b5 b6 b7 q3 q5 q8 q11 t4 t5 t6 FR fc (bv_unsigned sp + -144) fs bot cur 0 m1
    /\ munch [(bv_unsigned sp - 208, bv_unsigned sp)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1
    /\ stk bsegs m1 lo (bv_unsigned sp + -144)
    /\ rw_cells bsegs m1 (bv_unsigned sp + -144)
         [C8 (Z_to_bv 64 889976); C8 (Z_to_bv 64 0xdc960); C8 (Z_to_bv 64 0xdc970); C8 (Z_to_bv 64 0xdc968); C8 wj]
    /\ rw_cells bsegs m1 (bv_unsigned sp + -104) [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

Lemma gc_prologue : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (FR : bvmap 5 word) fc (m : amem) (lo ctx t top bot fs cur : Z),
  mem_inv bsegs m ->
  stk bsegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 208 -> ATOP <= lo ->
  tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 fs -> a1 = Z_to_bv 64 cur ->
  rw_cells bsegs m ATSDI [C1 (Z_to_bv 8 1)] -> rw_cells bsegs m ATSDK [C4 (Z_to_bv 64 0)] ->
  rw_cells bsegs m ATP88 [C8 (Z_to_bv 64 ATSD)] -> rw_cells bsegs m ATSD [C8 (Z_to_bv 64 ctx)] ->
  rw_cells bsegs m (ctx + 152) [C8 (Z_to_bv 64 t)] ->
  rw_cells bsegs m (t + 8) [C8 (Z_to_bv 64 top); C8 (Z_to_bv 64 bot)] -> rw_cells bsegs m (t + 40) [C1 (Z_to_bv 8 0)] ->
  0 < ctx -> ctx + 4096 <= ATOP -> 0 < t -> t + 4096 <= ATOP -> 0 <= bot -> bot < top -> top <= 2^47 ->
  bot <= cur <= top ->
  rt_got m ->
  0 <= fs -> fs + 4096 < 2^64 ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG ctx 4096 -> rng RNG t 4096 ->
  evtF bsegs RNG (gc_pro_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t4 t5 t6 FR fc lo fs bot cur m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        FR (Z_to_bv 64 AGC) fc None m (seg_rom bsegs)).
Proof.
  intros until cur.
  intros MI ST LO CEIL TP A0 A1 TI TK T88 TSD CT TB SW CXa CXb T0 T1 B0 BT TT CURR GOT F0 FB RIMG RSTK RCTX RT.
  subst a0 a1.
  pose proof (munch_refl [(bv_unsigned sp - 208, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl bsegs m) as WM.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  unfold ATP, ATSDI, ATSDK, ATP88, ATSD, AGC in *.
  carve_frame 144%nat ST.
  do 14 zstep.
  zstep. zstep.
  zstep.
  box RCTX; box RT.
  call_sp get_current_thread_spec;
    first [ exact MI | exact ST | exact TP | reflexivity | exact TI | exact TK | exact T88 | exact TSD | exact CT
          | exact RIMG | (unbox RCTX; exact RCTX) | lia | solve_rng | idtac ].
  unbox RCTX.
  rename POST into ST.
  lazymatch goal with H : mem_inv bsegs _ |- _ => rename H into MI2 end.
  zstep. if_cases Ka; zify_cond Ka; [exfalso; clear - Ka T0 T1; pose proof atop_range; lia|].
  zstep.
  zstep.
  unbox RT. callp stack_top_spec; [exact MI2 | reflexivity | exact TB | exact SW | lia | lia | lia | lia | exact T1 |].
  zstep. zstep.
  zstep.
  callp stack_bottom_spec; [exact MI2 | reflexivity | exact TB | exact SW | lia | lia | lia | lia | exact T1 |].
  zstep. if_cases Kt; zify_cond Kt; [exfalso; clear - Kt CURR B0 TT BT; rewrite ?Z.mod_small in Kt by lia; lia|].
  zstep.
  zstep. if_cases Kb; zify_cond Kb; [exfalso; clear - Kb CURR B0 TT BT; rewrite ?Z.mod_small in Kb by lia; lia|].
  zstep. zstep.
  do 6 zstep.
  zstep.
  zstep.
  zstep. zstep.
  zstep. zstep.
  zstep. zstep.
  zstep. zstep.
  zstep.
  zstep. zstep. zstep.
  zstep.

  lazymatch goal with FRx : rw_cells bsegs ?mm (bv_unsigned sp + -144) (?c0 :: ?c1 :: ?c2 :: ?c3 :: CB 8 ?jb :: ?rest) |- _ =>
    pose proof (proj1 (rw_cells_app bsegs mm (bv_unsigned sp + -144) [c0; c1; c2; c3] (CB 8 jb :: rest)) FRx) as [FRa FRb];
    pose proof (proj1 (rw_cells_app bsegs mm _ [CB 8 jb] rest) FRb) as [FRc FRd];
    destruct (c8_of_CB mm _ jb FRc) as (wj & FRc8 & _);
    assert (FRM : rw_cells bsegs mm (bv_unsigned sp + -144) ([c0; c1; c2; c3] ++ [C8 wj])) by (apply rw_cells_app; split; [exact FRa| exact FRc8]);
    clear FRx FRa FRb FRc FRc8
  end.
  cbn [app cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in FRM, FRd.
  replace (bv_unsigned sp + -144 + Z.of_nat 32 + Z.of_nat 8) with (bv_unsigned sp + -104) in FRd by lia.
  apply evtF_done. unfold gc_pro_post, gc_ohead. do 16 eexists. eexists. split; [cbv delta [mkR]; reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|]. split; [exact FRM| exact FRd].
Qed.

Lemma gc_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (FR : bvmap 5 word) fc (m : amem) (lo ctx t top bot fs cur : Z) (g : byte) (fl : Z -> Z -> byte) (rs : Z -> Z -> Z),
  mem_inv bsegs m ->
  stk bsegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 208 -> ATOP <= lo ->
  tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 fs -> a1 = Z_to_bv 64 cur ->

  rw_cells bsegs m ATSDI [C1 (Z_to_bv 8 1)] -> rw_cells bsegs m ATSDK [C4 (Z_to_bv 64 0)] ->
  rw_cells bsegs m ATP88 [C8 (Z_to_bv 64 ATSD)] -> rw_cells bsegs m ATSD [C8 (Z_to_bv 64 ctx)] ->
  rw_cells bsegs m (ctx + 152) [C8 (Z_to_bv 64 t)] ->
  rw_cells bsegs m (t + 8) [C8 (Z_to_bv 64 top); C8 (Z_to_bv 64 bot)] -> rw_cells bsegs m (t + 40) [C1 (Z_to_bv 8 0)] ->
  0 < ctx -> ctx + 4096 <= ATOP -> 0 < t -> t + 4096 <= ATOP -> 0 <= bot -> bot < top -> top <= 2^47 ->
  bot <= cur <= top ->
  rt_got m -> rt_shbase m -> rt_layout m ->

  ablk fs (fs + 11571200) -> fs + 11571200 <= ATOP -> fs mod 4096 = 0 ->
  rw_cells bsegs m (fs + 88) [C8 (Z_to_bv 64 20)] -> rw_cells bsegs m (fs + 96) [C1 g] ->
  (forall c p, 0 <= c < 11 -> 0 <= p < gcN c -> rw_cells bsegs m (gflag fs c p) [C1 (fl c p)]) ->
  (forall c p, 0 <= c < 11 -> 0 <= p < gcN c -> bv_unsigned (fl c p) <> 0 ->
       0 <= rs c p < 2^64 /\ rw_cells bsegs m (gframe fs c p + 24) [C8 (Z_to_bv 64 (rs c p))]) ->
  (forall c p, 0 <= c < 11 -> 0 <= p < gcN c -> gfreed bot cur (fl c p) (rs c p) = true ->
       c <= 2 /\ exists ws, length ws = Z.to_nat (2 ^ c) /\ rw_cells bsegs m (shad (gframe fs c p)) (map C8 ws)) ->

  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG ctx 4096 -> rng RNG t 4096 ->
  rng RNG fs 11571200 -> rng RNG (shad fs) (shlen 11571200) ->
  evtF bsegs RNG (gc_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc lo fs bot cur fl rs m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        FR (Z_to_bv 64 AGC) fc None m (seg_rom bsegs)).
Proof.
  intros until rs.
  intros MI ST LO CEIL TP A0 A1 TI TK T88 TSD CT TB SW CXa CXb T0 T1 B0 BT TT CURR GOT SHB LAY
         FLO FHI FAL LOG NGC FL RS SH RIMG RSTK RCTX RT RFS RSH.
  pose proof (ablk_lin _ _ FLO) as (FLOL & F0 & _ & FB). unfold AIMG_HI in FLOL.
  eapply evtF_cut.
  { eapply gc_prologue with (lo := lo) (ctx := ctx) (t := t) (top := top) (bot := bot) (fs := fs) (cur := cur); try eassumption; lia. }
  cbv beta. intros ms1 (ra' & u0 & u1 & e0 & e1 & e2 & e3 & e4 & e5 & e6 & e7 & p3 & p5 & p8 & p11 & wj & m1 & -> & MU & WM & MI1 & ST1 & FRM & FRd).
  clear ST. rename ST1 into ST.
  assert (TRm : forall A cs, rw_cells bsegs m A cs -> A + Z.of_nat (cells_size cs) <= ATOP -> rw_cells bsegs m1 A cs)
    by (intros A cs H HA; eapply rw_cells_transport; [exact H| exact MU| exact WM|]; cbn [disjoint_from]; split; [lia| exact I]).
  pose proof atop_range as ATR0.
  apply TRm in LOG; [| cbn; lia]. apply TRm in NGC; [| cbn; lia]. apply TRm in SHB; [| cbn; lia]. apply TRm in LAY; [| cbn; lia].
  pose proof atop_range as ATR.
  assert (SPB : bv_unsigned sp < 2^64) by (pose proof (bv_unsigned_in_range 64 sp) as X; exact (proj2 X)).
  lazymatch goal with MUx : munch _ m ?mm |- _ =>
    assert (TR : forall A cs, rw_cells bsegs m A cs -> A + Z.of_nat (cells_size cs) <= ATOP -> rw_cells bsegs mm A cs)
      by (intros A cs H HA; eapply rw_cells_transport; [exact H| exact MUx| exact WM|]; cbn [disjoint_from]; split; [lia| exact I])
  end.

  pose proof GC_NCLS_eq as NCE.
  eapply evtF_cut.
  { eapply (gc_outer RNG GC_NCLS 0) with (fl := fl) (rs := rs); try eassumption; try lia.
    - intros c p Hc Hp. pose proof (gc_geo fs c p Hc Hp F0) as (G1 & _). apply TR; [apply FL; assumption| cbn; lia].
    - intros c p Hc Hp NZ. destruct (RS c p Hc Hp NZ) as (R1 & R2). split; [exact R1|].
      pose proof (gc_geo fs c p Hc Hp F0) as (_ & _ & G3). pose proof (gc_pows c Hc) as (_ & _ & P6 & _). apply TR; [exact R2| cbn; lia].
    - intros c p Hc Hp GF. destruct (SH c p Hc Hp GF) as (C2 & ws & LWS & CELL). split; [exact C2|]. exists ws. split; [exact LWS|].
      pose proof (gc_shad_off fs c p Hc Hp FLO FHI) as (_ & _ & HI).
      assert (CS : forall l : list word, Z.of_nat (cells_size (map C8 l)) = 8 * Z.of_nat (length l)).
      { induction l as [|w l IHl]; [reflexivity|]. cbn [map cells_size csize length]. rewrite Nat2Z.inj_add, IHl. lia. }
      assert (PC : 0 < 2 ^ c) by (apply Z.pow_pos_nonneg; lia).
      apply TR; [exact CELL| rewrite CS, LWS, Z2Nat.id by lia; lia].
    - eapply rng_sub'; [exact RSTK|]. lia. }
  cbv beta. intros ms' (t0' & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & q3 & q5 & q8 & q11 & fsz' & m' & -> & MUo & WMo & MIo & FRMo & FLSo).

  assert (WD1 : forall A n, ATOP <= A -> disjoint_from (gcWall fs fl rs bot cur 0 GC_NCLS) A n).
  { intros A n HA. apply gcWall_disjoint; [lia| lia|]. intros c q Hc Hq _. apply gcW1_disj_stack; try assumption; lia. }
  assert (WD2 : forall A n, fs <= A -> A + n <= fs + 4096 -> 0 <= n -> disjoint_from (gcWall fs fl rs bot cur 0 GC_NCLS) A n).
  { intros A n HA HB HN. apply gcWall_disjoint; [lia| lia|]. intros c q Hc Hq _.
    pose proof (gc_geo fs c q ltac:(lia) Hq F0) as (G1 & _). apply gcW1_disj_in_fs; try assumption; lia. }
  assert (DST : forall A n, ATOP <= A -> (A + n <= bv_unsigned sp + -144 + 32 \/ bv_unsigned sp + -144 + 40 <= A) ->
            disjoint_from ((bv_unsigned sp + -144 + 32, bv_unsigned sp + -144 + 40) :: gcWall fs fl rs bot cur 0 GC_NCLS) A n).
  { intros A n HA HD. cbn [disjoint_from]. split; [lia|]. apply WD1. exact HA. }
  lazymatch goal with MUx : munch _ m ?mm |- _ =>
    eapply (rw_cells_transport bsegs _ mm m') in FRd; [| exact MUo| exact WMo| apply DST; cbn; lia];
    eapply (rw_cells_transport bsegs _ mm m') in NGC; [| exact MUo| exact WMo|]
  end.
  2:{ cbn [disjoint_from]. split; [cbn; lia|]. apply WD2; cbn; lia. }
  lazymatch goal with MUx : munch _ m ?mm |- _ =>
    eapply (stk_transport_disjoint bsegs ((bv_unsigned sp + -144 + 32, bv_unsigned sp + -144 + 40) :: gcWall fs fl rs bot cur 0 GC_NCLS) mm m') in ST; [| exact MUo| exact WMo| apply DST; lia];
    assert (MUf : munch ((bv_unsigned sp - 208, bv_unsigned sp) :: (fs + 96, fs + 97) :: gcWall fs fl rs bot cur 0 GC_NCLS) m m')
      by (eapply munch_trans;
          [ eapply munch_weaken; [| exact MUx]; intros xx Hxx; cbn [outside] in Hxx |- *; tauto
          | eapply munch_weaken; [| exact MUo]; intros xx Hxx; cbn [outside] in Hxx |- *;
            destruct Hxx as (Hx1 & Hx2 & Hx3); split; [lia| exact Hx3] ]);
    assert (WMf : wmono bsegs m m') by (eapply wmono_trans; [exact WM| exact WMo]);
    clear MUx WM MUo WMo TR
  end.
  unfold gc_ohead.
  pose proof (munch_refl [(fs + 96, fs + 97)]%Z m') as MUg. pose proof (wmono_refl bsegs m') as WMg.
  zstep.
  do 13 zstep.
  zstep. zstep.
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (FRall : rw_cells bsegs mm (bv_unsigned sp + -144)
              ([C8 (Z_to_bv 64 889976); C8 (Z_to_bv 64 903520); C8 (Z_to_bv 64 903536); C8 (Z_to_bv 64 903528); C8 fsz'] ++
               [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]))
      by (apply rw_cells_app; split; [exact FRMo|]; cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ];
          replace (bv_unsigned sp + -144 + Z.of_nat 40) with (bv_unsigned sp + -104) by lia; exact FRd)
  end.
  cbn [app] in FRall.
  release_frame FRall ST (bv_unsigned sp).
  apply evtF_done. unfold gc_post. do 16 eexists. split; [cbv delta [mkR]; reflexivity|].
  split; [unfold gc_W; exact MUf|]. split; [exact WMf|]. split; [assumption|]. split; [exact ST|]. split; [exact NGC|].
  intros c p Hc Hp. pose proof (gc_geo fs c p Hc Hp F0) as (G1 & _).
  eapply rw_cells_transport; [apply FLSo; assumption| exact MUg| exact WMg|]. cbn [disjoint_from cells_size csize Nat.add]. split; [cbn; lia| exact I].
Qed.
End CANSEC2.
End TwinB.
