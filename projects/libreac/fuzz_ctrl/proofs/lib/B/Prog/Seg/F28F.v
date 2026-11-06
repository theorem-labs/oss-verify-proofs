(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libpcap/fuzz_pcap/lib/E2/Lib/Tac.v; 978 of its 1011 lines of code are new or changed and 2109 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/A4.v, with its module names changed; 615 of its 727 lines of code are new or changed and 899 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/F35.v, with its module names changed; 625 of its 686 lines of code are new or changed and 666 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/F28.v; 174 of its 338 lines of code are new or changed and 522 lines of the source are left out. *)
(* rule 24: no function proved. *)
(* Provenance (route (a) bridge input, lead 22:18Z; auditor a Theorem Labs lane):
   image fuzz_ctrl.asan-ubsan v1.9.0, pau-libreac-v190,
     sha256 12136677c5cf9891b3aed0c4821499bba9dde76b0e6baadb7ac66e07e6a62c17;
   source runs: lib/B/Prog/Seg/F28.v f28_loop (:560), f28_tail (:686) at a working branch
     3803efccea0 (blob f6be1c0fd181fbbf51f210c9487fea5a1f277ca7);
   tool: lib/Lib/StepF.v c97545265d26d5d39c131602ff95accd1bc78f07 (the blob this tree had at release c5e779efe8c),
         lib/Lib/ExecF.v 38b86b5d83a511566e396810e9b0b51804f48e22 (the blob this tree had at release c5e779efe8c);
   compare: split stretches, both calls-free.  f28_loop_F re-runs F28.v:584-679 (the 12-turn port-slot loop
     0x8292c -> 0x829cc) and f28_tail_F re-runs F28.v:713-759 (the tail 0x829cc -> 0x82aa4) on the lib.Lib
     engine with StepF in place of the UL engine's Step (the two step relations have the same body, as
     F22.f22_lu_msteps shows).  Neither run calls anything, so neither is split further. *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Reusable Require Import YK11 YM05 YK0o YK0s YK15 YP09 YO0f YO0d YO09
  YL00 YL0g YL0i YI14 YI16 YL01 YM06.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import Img0 AsanRT AsanRTInv AsanRTFacts PContract MemNorm AsanLift.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Contract FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcFrag.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require RcLeaf RcPorts.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import SlotModel SlotInv RcAsanFP RcAsanFPLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.Seg Require Import Tac_slot.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.Seg Require F28.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import ExecF StepF.
Import ListNotations.
Import OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Reusable.YK11.
Open Scope Z_scope.

(* The short name PropExec resolves to the UL engine's copy here (the Seg chain loads it last), but StepF steps
   the lib.Lib engine: name its value functions explicitly. *)
Module LPE := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.PropExec.

(* The value-function facts of F28's two runs, over the lib.Lib PropExec (F28's own speak the UL engine's). *)
Lemma f28f_seqz : forall x, - 2 ^ 63 <= x < 2 ^ 63 ->
  LPE.v_sltiu (Z_to_bv 64 x) 1 = Z_to_bv 64 (if x =? 0 then 1 else 0).
Proof.
  intros x Hx. assert (HP : 2 ^ 64 = 2 * 2 ^ 63) by reflexivity.
  unfold LPE.v_sltiu. change (bv_wrap 64 1) with 1.
  rewrite unsigned_lit_wrap.
  destruct (Z.eqb_spec x 0) as [E|E].
  - subst x. reflexivity.
  - replace (x mod 2 ^ 64 <? 1) with false; [reflexivity|].
    symmetry. apply Z.ltb_ge.
    destruct (Z.leb_spec 0 x) as [L|L].
    + rewrite Z.mod_small by lia. lia.
    + rewrite <- (Z.mod_add x 1 (2 ^ 64)) by lia. rewrite Z.mod_small by lia. lia.
Qed.
Lemma f28f_seqz_in : forall c, 0 <= c < 256 ->
  LPE.v_sltiu (Z_to_bv 64 (Z.land c 253)) 1 = Z_to_bv 64 (if RcLeaf.is_in c then 1 else 0).
Proof.
  intros c Hc.
  assert (E : forallb (fun z => ((0 <=? Z.land z 253) && (Z.land z 253 <=? 253))%bool)
                (map Z.of_nat (seq 0 256)) = true) by (vm_compute; reflexivity).
  rewrite forallb_forall in E.
  assert (Hin : In c (map Z.of_nat (seq 0 256))).
  { apply in_map_iff. exists (Z.to_nat c). split; [lia|]. apply in_seq. lia. }
  pose proof (E c Hin) as B. cbv beta in B. apply andb_prop in B as (B1 & B2).
  apply Z.leb_le in B1. apply Z.leb_le in B2.
  rewrite f28f_seqz by lia. rewrite (F28.f28_land253 c Hc). reflexivity.
Qed.
Lemma f28f_seqz_m1 : forall c, 0 <= c < 256 ->
  LPE.v_sltiu (Z_to_bv 64 (c + -1)) 1 = Z_to_bv 64 (if RcLeaf.is_out c then 1 else 0).
Proof.
  intros c Hc. rewrite f28f_seqz by lia. unfold RcLeaf.is_out.
  destruct (Z.eqb_spec (c + -1) 0); destruct (Z.eqb_spec c 1); try reflexivity; lia.
Qed.
Lemma f28f_seqz_m3 : forall c, 0 <= c < 256 ->
  LPE.v_sltiu (Z_to_bv 64 (c + -3)) 1 = Z_to_bv 64 (if c =? 3 then 1 else 0).
Proof.
  intros c Hc. rewrite f28f_seqz by lia.
  destruct (Z.eqb_spec (c + -3) 0); destruct (Z.eqb_spec c 3); try reflexivity; lia.
Qed.
Lemma f28f_sltiu4 : forall c, 0 <= c < 256 ->
  LPE.v_sltiu (Z_to_bv 64 c) 4 = Z_to_bv 64 (if c <? 4 then 1 else 0).
Proof.
  intros c Hc. unfold LPE.v_sltiu. change (bv_wrap 64 4) with 4.
  rewrite (unsigned_lit c) by lia. destruct (c <? 4); reflexivity.
Qed.
Lemma f28f_snez : forall f, 0 <= f < 256 ->
  LPE.v_sltu (Z_to_bv 64 0) (Z_to_bv 64 f) = Z_to_bv 64 (if f =? 0 then 0 else 1).
Proof.
  intros f Hf. unfold LPE.v_sltu, LPE.c_ltu, bv_ltu.
  rewrite (unsigned_lit f) by lia. change (bv_unsigned (Z_to_bv 64 0)) with 0.
  destruct (Z.eqb_spec f 0) as [E|E].
  - subst f. reflexivity.
  - replace (0 <? f) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
Qed.

Local Ltac acc_hint ::=
  lazymatch goal with
  | |- acc_in ?RNG (Z_to_bv 64 ?E, ?n) =>
      match goal with
      | H : rng RNG E _ |- _ =>
          eapply rng_acc_litZ; [exact H | reflexivity | lia | split; lia]
      end
  end.

(* ---- F28's read facts and value normalisations over the lib.Lib engine (its own copies speak the UL
   engine's Mem). ---- *)
Lemma f28f_rd1 : forall m a b, bytes_at rsegs m a [b] -> ov_read_bytes rsegs m (wa a) 1 = Some [b].
Proof.
  intros m a b H.
  pose proof (bytes_at_ov_read rsegs m a [b] 0 1 H ltac:(cbn; lia)) as HH.
  change (Z.of_nat 0) with 0%Z in HH. rewrite Z.add_0_r in HH. cbn [firstn skipn] in HH. exact HH.
Qed.
Lemma f28f_zxb_eq : forall b : byte, zxb b = Z_to_bv 64 (bv_unsigned b).
Proof. intros b. reflexivity. Qed.
Lemma f28f_zxb_lit : forall v, 0 <= v < 256 -> zxb (Z_to_bv 8 v) = Z_to_bv 64 v.
Proof.
  intros v Hv. rewrite f28f_zxb_eq. f_equal. rewrite Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_modulus 8) with 256. apply Z.mod_small. lia.
Qed.
Lemma f28f_sx32_small : forall v, 0 <= v < 2 ^ 31 -> sx32 (Z_to_bv 64 v) = Z_to_bv 64 v.
Proof.
  intros v Hv. unfold sx32. rewrite (unsigned_lit v) by lia. f_equal.
  unfold bv_swrap. change (bv_half_modulus 32) with (2 ^ 31). unfold bv_wrap.
  change (bv_modulus 32) with (2 ^ 32). rewrite Z.mod_small by lia. lia.
Qed.
Lemma f28f_shadow : forall m X, addressable m X 1 ->
  exists b : byte, ov_read_bytes rsegs m (wa (Z.shiftr X 3 + ASAN_K)) 1 = Some [b]
    /\ (bv_signed b = 0 \/ X mod 8 < bv_signed b) /\ -128 <= bv_signed b < 128.
Proof.
  intros m X HA. destruct (meta_byte m X 1 HA ltac:(lia)) as (b & RO & OK & IS).
  exists b. split; [| split].
  - pose proof (cells_at_read rsegs m (Z.shiftr X 3 + ASAN_K) [C1 b] 0%nat (C1 b) RO eq_refl) as H.
    cbn [csize cbytes] in H. rewrite Z.add_0_r in H. exact H.
  - destruct OK as [H|H]; [left; exact H | right; lia].
  - pose proof (sbyte_range b); lia.
Qed.

(* ---- F28's branch / normalisation tactics over the lib.Lib goal (its own use the UL engine's `evt` pattern
   and the UL Step's cbv_concl_iota). ---- *)
Ltac f28f_cbv_iota :=
  let g := lazymatch goal with |- ?g => g end in
  let g' := eval cbv iota in g in change_no_check g'.
Ltac f28f_norm :=
  repeat match goal with
  | |- context [bv_unsigned (Z_to_bv 64 ?x)] => rewrite (unsigned_lit x) by lia
  | |- context [bv_swrap 32 ?x] => rewrite (F28.f28_swrap_small x) by lia
  | |- context [Z.add ?x 0] => rewrite (Z.add_0_r x)
  | |- context [Z.shiftl ?x 2] => rewrite (F28.f28_shl2 x)
  | |- context [Z.shiftl ?x 4] => rewrite (F28.f28_shl4 x)
  end.
Ltac f28f_brc v :=
  lazymatch goal with
  | |- evtF _ _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      replace c with v by (vm_compute; reflexivity); f28f_cbv_iota
  end.
Ltac f28f_br v pf :=
  lazymatch goal with
  | |- evtF _ _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => replace c with v by (symmetry; pf); f28f_cbv_iota
  end.
Ltac f28f_nt := f28f_br false ltac:(rewrite F28.f28_eqb_true by lia; reflexivity).
Ltac f28f_fixmap :=
  lazymatch goal with
  | |- evtF _ _ _ (MS (bvmap_set ?k ?v ?R) _ _ _ _ _ _) =>
      let p := eval vm_compute in (bv_key k) in
      let R' := eval cbv beta iota delta [tset] in (tset p v R) in
      change (bvmap_set k v R) with R'
  end.
Ltac f28f_converge scratch Xe b OK BD :=
  match goal with
  | |- evtF ?segs ?RNG ?Q (MS ?R ?F (if _ then _ else ?cont) ?fc ?rv ?m ?ro) =>
      let Gc := fresh "Gc" in
      enough (Gc : forall rr, evtF segs RNG Q (MS (bvmap_set scratch rr R) F cont fc rv m ro)) by
        (let K0 := fresh "K0" in
         destruct (Z.eqb_spec (bv_signed b) 0) as [K0|K0];
         [ match goal with |- evtF _ _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
             replace c with false by (unfold sxb; rewrite K0; vm_compute; reflexivity) end;
           f28f_cbv_iota;
           match goal with |- evtF _ _ _ (MS ?R2 _ _ _ _ _ _) => exact (Gc (Sem.reg_get R2 scratch)) end
         | let Hmb := fresh "Hmb" in let Hlt := fresh "Hlt" in
           pose proof (Z.mod_pos_bound Xe 8 ltac:(lia)) as Hmb;
           assert (Hlt : Xe mod 8 < bv_signed b) by (destruct OK as [HH|HH]; [exfalso; apply K0; exact HH | lia]);
           match goal with |- evtF _ _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
             replace c with true by (unfold sxb; rewrite bv_eqb_lit by lia;
               replace (bv_signed b =? 0) with false by (symmetry; apply Z.eqb_neq; lia); reflexivity) end;
           f28f_cbv_iota; step; step;
           match goal with |- evtF _ _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
             replace c with false by (rewrite (unsigned_lit Xe) by lia;
               rewrite land7 by lia; rewrite lts_sxb by lia;
               replace (Xe mod 8 <? bv_signed b) with true by (symmetry; apply Z.ltb_lt; lia); reflexivity) end;
           f28f_cbv_iota; step;
           match goal with |- evtF _ _ _ (MS ?R2 _ _ _ _ _ _) => exact (Gc (Sem.reg_get R2 scratch)) end ])
  end; intro; f28f_fixmap.

(* The footprint twin of F28.f28_loop: the 12-turn port-slot loop 0x8292c -> 0x829cc, by the number k of turns
   left.  Each turn reads the byte Phi + 26 + i and its shadow byte ((Phi + 26 + i) >> 3) + 0x7fff8000; it
   writes no memory.  The regions are stated per turn, which is exactly what the run touches. *)
Lemma f28_loop_F : forall (RNG : footprint) (k i : nat) (Q : _ -> Prop)
  (ra sp gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s11 t4 t5 t6 : word)
  (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (phi : Z) (pbs : list byte),
  (i + k = 12)%nat -> (0 < k)%nat -> 0 < phi -> phi + 50 <= 2 ^ 64 ->
  (forall t, (t < 12)%nat ->
     bytes_at rsegs m (phi + 26 + Z.of_nat t) [nth (8 + t)%nat pbs (Z_to_bv 8 0)]) ->
  (forall t, (t < 12)%nat -> addressable m (phi + 26 + Z.of_nat t) 1) ->
  (forall t, (t < 12)%nat -> rng RNG (phi + 26 + Z.of_nat t) 1) ->
  (forall t, (t < 12)%nat -> rng RNG (Z.shiftr (phi + 26 + Z.of_nat t) 3 + ASAN_K) 1) ->
  (forall t1' t2' : word,
     evtF rsegs RNG Q (MS (mkR ra sp gp tp (Z_to_bv 64 (RcPorts.pu_first pbs 12)) t1' t2' s0 s1
          (Z_to_bv 64 (phi + 38)) (Z_to_bv 64 (RcLeaf.cnt RcLeaf.is_out pbs 12))
          (Z_to_bv 64 (RcLeaf.cnt RcLeaf.is_in pbs 12)) (Z_to_bv 64 (F28.f28_nemp pbs 12))
          (Z_to_bv 64 (phi + 38)) (Z_to_bv 64 (RcPorts.pu_first pbs 12))
          (Z_to_bv 64 (-8 - (phi + 18))) (Z_to_bv 64 0) s2 s3 s4 s5 s6 s7 s8 s9
          (Z_to_bv 64 ASAN_K) s11 (Z_to_bv 64 12) t4 t5 t6)
        F (Z_to_bv 64 0x829cc) fc None m (seg_rom rsegs))) ->
  evtF rsegs RNG Q
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1
       (Z_to_bv 64 (phi + 26 + Z.of_nat i)) (Z_to_bv 64 (RcLeaf.cnt RcLeaf.is_out pbs i))
       (Z_to_bv 64 (RcLeaf.cnt RcLeaf.is_in pbs i)) (Z_to_bv 64 (F28.f28_nemp pbs i))
       (Z_to_bv 64 (phi + 26 + Z.of_nat i)) (Z_to_bv 64 (RcPorts.pu_first pbs i))
       (Z_to_bv 64 (-8 - (phi + 18))) (Z_to_bv 64 (12 - Z.of_nat i)) s2 s3 s4 s5 s6 s7 s8 s9
       (Z_to_bv 64 ASAN_K) s11 (Z_to_bv 64 12) t4 t5 t6)
     F (Z_to_bv 64 0x8292c) fc None m (seg_rom rsegs)).
Proof.
  intros RNG k. induction k as [|k IH]; intros i Q ra sp gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s11 t4 t5 t6
    F fc m phi pbs Hik Hk Hphi0 Hphi50 HB HA RB' RS' HQ; [lia|].
  assert (HP64 : 2 ^ 64 = 18446744073709551616) by reflexivity.
  assert (HP63 : 2 ^ 63 = 9223372036854775808) by reflexivity.
  assert (HP31 : 2 ^ 31 = 2147483648) by reflexivity.
  assert (Hi : (i < 12)%nat) by lia.
  pose proof (f28f_rd1 m _ _ (HB i Hi)) as RB.
  destruct (f28f_shadow m (phi + 26 + Z.of_nat i) (HA i Hi)) as (b & RS & OK & BD).
  pose proof (RB' i Hi) as RGb.
  pose proof (RS' i Hi) as RGs.
  pose proof (F28.f28_cnt_bound RcLeaf.is_in pbs i) as Bin.
  pose proof (F28.f28_cnt_bound RcLeaf.is_out pbs i) as Bout.
  pose proof (F28.f28_nemp_bound pbs i) as Bemp.
  assert (Bfst : 0 <= RcPorts.pu_first pbs i < 256)
    by (destruct (F28.f28_first_nunk pbs i) as [(_ & E)|(_ & E)]; lia).
  (* 0x8292c add t0,a6,a7 ; 0x82930 beq t0,t3,82fa0 (trap T56): t0 = 2^64 - 14 - Phi - i is not 12 *)
  step. step. f28f_br false ltac:(apply F28.f28_eqb_ne; lia).
  (* 0x82934 srli t0,a0,3 ; add t0,t0,s10 ; lb t0,0(t0) ; 0x82940 bnez t0,829c0 *)
  step. step. rewrite (unsigned_lit (phi + 26 + Z.of_nat i)) by lia.
  step. step. f28f_converge (Z_to_bv 5 6) (phi + 26 + Z.of_nat i) b OK BD.
  (* 0x82944 lbu t0,0(a4): the code c = pbs[8 + i] *)
  step. rewrite f28f_zxb_eq.
  remember (bv_unsigned (nth (8 + i)%nat pbs (Z_to_bv 8 0))) as c eqn:Ec.
  assert (Bc : 0 <= c < 256) by (subst c; apply F28.f28_ubyte).
  pose proof (F28.f28_ite10 (RcLeaf.is_in c)) as B1.
  pose proof (F28.f28_ite10 (RcLeaf.is_out c)) as B2.
  pose proof (F28.f28_ite10 (c =? 3)) as B3.
  pose proof (F28.f28_ite10 (c <? 4)) as B4.
  pose proof (F28.f28_ite01 (RcPorts.pu_first pbs i =? 0)) as B5.
  step. f28f_norm. step. f28f_norm. step. rewrite (f28f_seqz_in c Bc).
  step. step. f28f_norm. step. f28f_nt.
  step. step. f28f_norm. step. rewrite (f28f_seqz_m1 c Bc).
  step. step. f28f_norm. step. f28f_nt.
  step. step. f28f_norm. step. rewrite (f28f_seqz_m3 c Bc).
  step. step. f28f_norm. step. f28f_nt.
  step. rewrite (f28f_sltiu4 c Bc).
  step. f28f_norm. rewrite (F28.f28_land255 (RcPorts.pu_first pbs i) Bfst).
  step. rewrite (f28f_snez (RcPorts.pu_first pbs i) Bfst).
  step. f28f_norm. rewrite F28.f28_or.
  step.
  destruct ((c <? 4) || negb (RcPorts.pu_first pbs i =? 0))%bool eqn:EB; f28f_cbv_iota.
  - f28f_brc false. step. f28f_norm.
    assert (Ef : RcPorts.pu_first pbs (S i) = RcPorts.pu_first pbs i).
    { rewrite F28.f28_first_step. unfold RcPorts.rc_u8. rewrite <- Ec, EB. reflexivity. }
    step. step. step. step. f28f_norm. step.
    rewrite <- Ef. subst c.
    change (RcLeaf.cnt RcLeaf.is_in pbs i +
              (if RcLeaf.is_in (bv_unsigned (nth (8 + i)%nat pbs (Z_to_bv 8 0))) then 1 else 0))
      with (RcLeaf.cnt RcLeaf.is_in pbs (S i)).
    change (RcLeaf.cnt RcLeaf.is_out pbs i +
              (if RcLeaf.is_out (bv_unsigned (nth (8 + i)%nat pbs (Z_to_bv 8 0))) then 1 else 0))
      with (RcLeaf.cnt RcLeaf.is_out pbs (S i)).
    change (F28.f28_nemp pbs i + (if bv_unsigned (nth (8 + i)%nat pbs (Z_to_bv 8 0)) =? 3 then 1 else 0))
      with (F28.f28_nemp pbs (S i)).
    replace (phi + 26 + Z.of_nat i + 1) with (phi + 26 + Z.of_nat (S i)) by lia.
    replace (12 - Z.of_nat i + -1) with (12 - Z.of_nat (S i)) by lia.
    destruct k as [|k].
    + assert (E11 : i = 11%nat) by lia. subst i.
      f28f_brc false. step.
      replace (phi + 26 + Z.of_nat 12) with (phi + 38) by lia.
      apply HQ.
    + f28f_br true ltac:(rewrite bv_eqb_lit by lia; apply Bool.negb_true_iff, Z.eqb_neq; lia).
      apply (IH (S i)); [lia | lia | exact Hphi0 | exact Hphi50 | exact HB | exact HA | exact RB' | exact RS'
                        | exact HQ].
  - f28f_brc true.
    assert (Ef : RcPorts.pu_first pbs (S i) = c).
    { rewrite F28.f28_first_step. unfold RcPorts.rc_u8. rewrite <- Ec, EB. reflexivity. }
    step. step. step. step. f28f_norm. step.
    replace (Z_to_bv 64 c) with (Z_to_bv 64 (RcPorts.pu_first pbs (S i))) by (rewrite Ef; reflexivity).
    clear Ef. subst c.
    change (RcLeaf.cnt RcLeaf.is_in pbs i +
              (if RcLeaf.is_in (bv_unsigned (nth (8 + i)%nat pbs (Z_to_bv 8 0))) then 1 else 0))
      with (RcLeaf.cnt RcLeaf.is_in pbs (S i)).
    change (RcLeaf.cnt RcLeaf.is_out pbs i +
              (if RcLeaf.is_out (bv_unsigned (nth (8 + i)%nat pbs (Z_to_bv 8 0))) then 1 else 0))
      with (RcLeaf.cnt RcLeaf.is_out pbs (S i)).
    change (F28.f28_nemp pbs i + (if bv_unsigned (nth (8 + i)%nat pbs (Z_to_bv 8 0)) =? 3 then 1 else 0))
      with (F28.f28_nemp pbs (S i)).
    replace (phi + 26 + Z.of_nat i + 1) with (phi + 26 + Z.of_nat (S i)) by lia.
    replace (12 - Z.of_nat i + -1) with (12 - Z.of_nat (S i)) by lia.
    destruct k as [|k].
    + assert (E11 : i = 11%nat) by lia. subst i.
      f28f_brc false. step.
      replace (phi + 26 + Z.of_nat 12) with (phi + 38) by lia.
      apply HQ.
    + f28f_br true ltac:(rewrite bv_eqb_lit by lia; apply Bool.negb_true_iff, Z.eqb_neq; lia).
      apply (IH (S i)); [lia | lia | exact Hphi0 | exact Hphi50 | exact HB | exact HA | exact RB' | exact RS'
                        | exact HQ].
Qed.

(* The footprint twin of F28.f28_tail: the tail 0x829cc -> 0x82aa4.  It reads the two spills [A + 136, A + 144)
   and [A + 312, A + 320), the three ports words [fr + 128, fr + 140), the first byte [fr + 160, fr + 161), the
   byte Phi + 25 and its shadow byte; it writes no memory. *)
Lemma f28_tail_F : forall (RNG : footprint) (Q : _ -> Prop)
  (ra sp gp tp t1 t2 s0 s2 s3 s4 s6 s8 s9 s11 t3 t4 t5 t6 a7 : word)
  (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
  (A fr phi nin nout nemp nunk first bt7 : Z),
  0 < phi -> phi + 50 <= 2 ^ 64 ->
  0 <= nin <= 12 -> 0 <= nout <= 12 -> 0 <= nemp <= 12 -> 0 <= nunk <= 12 ->
  nin + nout + nemp + nunk = 12 -> 0 <= first < 256 -> 0 <= bt7 < 256 ->
  ov_read_bytes rsegs m (wa (A + 136)) 8 = Some (le8 (Z_to_bv 64 (fr + 160))) ->
  ov_read_bytes rsegs m (wa (A + 312)) 8 = Some (le8 (Z_to_bv 64 (phi + 18))) ->
  ov_read_bytes rsegs m (wa (fr + 128)) 4 = Some (le4 (Z_to_bv 64 (4 * nin))) ->
  ov_read_bytes rsegs m (wa (fr + 132)) 4 = Some (le4 (Z_to_bv 64 (4 * nout))) ->
  ov_read_bytes rsegs m (wa (fr + 136)) 4 = Some (le4 (Z_to_bv 64 (16 * bt7))) ->
  ov_read_bytes rsegs m (wa (fr + 160)) 1 = Some [Z_to_bv 8 first] ->
  ov_read_bytes rsegs m (wa (phi + 25)) 1 = Some [Z_to_bv 8 bt7] ->
  addressable m (phi + 25) 1 ->
  rng RNG (A + 136) 8 -> rng RNG (A + 312) 8 -> rng RNG (fr + 128) 12 -> rng RNG (fr + 160) 1 ->
  rng RNG (phi + 25) 1 -> rng RNG (Z.shiftr (phi + 25) 3 + ASAN_K) 1 ->
  (forall a0' a1' a2' a3' a4' a5' a6' : word,
     Q (MS (mkR ra sp gp tp (Z_to_bv 64 first) t1 t2 s0 (Z_to_bv 64 A)
          a0' a1' a2' a3' a4' a5' a6' a7 s2 s3 s4 (Z_to_bv 64 (fr + 128)) s6 (Z_to_bv 64 (4 * nunk)) s8 s9
          (Z_to_bv 64 ASAN_K) s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x82aa4) fc None m (seg_rom rsegs))) ->
  evtF rsegs RNG Q
    (MS (mkR ra sp gp tp (Z_to_bv 64 first) t1 t2 s0 (Z_to_bv 64 A)
       (Z_to_bv 64 (phi + 38)) (Z_to_bv 64 nout) (Z_to_bv 64 nin) (Z_to_bv 64 nemp)
       (Z_to_bv 64 (phi + 38)) (Z_to_bv 64 first) (Z_to_bv 64 (-8 - (phi + 18))) a7
       s2 s3 s4 (Z_to_bv 64 (fr + 128)) s6 (Z_to_bv 64 (4 * nunk)) s8 s9 (Z_to_bv 64 ASAN_K) s11 t3 t4 t5 t6)
     F (Z_to_bv 64 0x829cc) fc None m (seg_rom rsegs)).
Proof.
  intros RNG Q ra sp gp tp t1 t2 s0 s2 s3 s4 s6 s8 s9 s11 t3 t4 t5 t6 a7 F fc m A fr phi nin nout nemp nunk
    first bt7 Hphi0 Hphi50 Bin Bout Bemp Bunk Btot Bfst Bb7 R136 R312 RP0 RP1 RP2 RF R7 HA7
    G136 G312 G128 G160 G25 G25s HQ.
  assert (HP64 : 2 ^ 64 = 18446744073709551616) by reflexivity.
  assert (HP63 : 2 ^ 63 = 9223372036854775808) by reflexivity.
  assert (HP31 : 2 ^ 31 = 2147483648) by reflexivity.
  assert (HP30 : 2 ^ 30 = 1073741824) by reflexivity.
  destruct (f28f_shadow m (phi + 25) HA7) as (b & RS & OK & BD).
  step. rewrite (f28f_sx32_small (4 * nin)) by lia.
  step. f28f_norm. rewrite F28.f28_land43. step. f28f_nt.
  step. rewrite (f28f_sx32_small (4 * nout)) by lia.
  destruct (F28.f28_lor44 nout nunk ltac:(lia) ltac:(lia)) as (Blor & Elor).
  step. f28f_norm. step. f28f_norm. rewrite Elor. step. f28f_nt.
  step. step. rewrite (f28f_zxb_lit first Bfst).
  step. f28f_norm. rewrite (F28.f28_land255 first Bfst). step. f28f_nt.
  step. step. f28f_norm. step. f28f_nt.
  step. f28f_norm. step. step. f28f_norm. step. f28f_nt.
  step. step. step. f28f_norm. rewrite (F28.f28_srliw30 (nemp + 536870912)) by lia. step. f28f_nt.
  step. f28f_norm. step. f28f_norm. step. step. f28f_norm. step. f28f_nt.
  step. f28f_norm. step. step. f28f_nt.
  step. step. step. f28f_norm. rewrite (F28.f28_srliw30 (nin + 536870912)) by lia. step. f28f_nt.
  step. f28f_norm. step. f28f_nt.
  step. step. step. f28f_norm. rewrite (F28.f28_srliw30 (nout + 536870912)) by lia. step. f28f_nt.
  step. f28f_norm. step. f28f_nt.
  step. step. step. step. f28f_br false ltac:(rewrite bv_ltu_lit by lia; apply Z.ltb_ge; lia).
  step. step. rewrite (unsigned_lit (phi + 25)) by lia.
  step. step. rewrite (f28f_sx32_small (16 * bt7)) by lia.
  step. f28f_converge (Z_to_bv 5 13) (phi + 25) b OK BD.
  step. rewrite (f28f_zxb_lit bt7 Bb7).
  step. f28f_norm. step. f28f_nt.
  apply evtF_done. apply HQ.
Qed.
