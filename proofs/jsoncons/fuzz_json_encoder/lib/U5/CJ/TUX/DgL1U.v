(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.Lib Require Import Tac ZBridge.
From OssFuzzTheorems.jsoncons.fuzz_json_encoder.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CJ.TUX Require Import DgBaseU.
Set Default Proof Mode "Classic".
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section DG.
Variables ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word.
Variable F : bvmap 5 word.
Variable fc : bv 32.
Variable m0 : word -> option byte.
Variables buf lenp kp : Z.
Local Notation SP0 := (DgBaseU.SP0 sp).
Hypothesis BUFR : (4096 <= buf /\ buf + 21 <= 2^47)%Z.
Hypothesis LENR : (4096 <= lenp /\ lenp + 4 <= 2^47)%Z.
Hypothesis KPR : (4096 <= kp /\ kp + 4 <= 2^47)%Z.
Hypothesis SPR0 : (2^40 <= SP0 /\ SP0 + 8 <= 2^47)%Z.
Hypothesis SEP_B : (buf + 21 <= SP0 - 64 \/ SP0 + 8 <= buf)%Z.
Hypothesis SEP_L : (lenp + 4 <= SP0 - 64 \/ SP0 + 8 <= lenp)%Z.
Hypothesis SEP_K : (kp + 4 <= SP0 - 64 \/ SP0 + 8 <= kp)%Z.
Hypothesis SEP_BL : (buf + 21 <= lenp \/ lenp + 4 <= buf)%Z.
Hypothesis SEP_BK : (buf + 21 <= kp \/ kp + 4 <= buf)%Z.
Hypothesis SEP_LK : (lenp + 4 <= kp \/ kp + 4 <= lenp)%Z.
Hypothesis LA : (lenp mod 4 = 0)%Z.
Hypothesis KA : (kp mod 4 = 0)%Z.
Local Notation DG_W := (DgBaseU.DG_W sp buf lenp kp).
Local Notation dg_post := (DgBaseU.dg_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 buf lenp kp).
Local Notation dg_mem := (DgBaseU.dg_mem ra sp s0 s1 s2 s3 s4 s5 s6 m0 buf lenp kp).
Local Notation dg_ret' := (DgBaseU.dg_ret' ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 buf lenp kp BUFR LENR KPR SPR0 SEP_B SEP_L SEP_K SEP_BL SEP_BK SEP_LK LA KA).
Ltac dg_mem_tac := unfold DgBaseU.dg_mem, DgBaseU.DG_W; dg_conjs; try eassumption; try (rewrite ?upd_length; assumption).
Ltac dg_mem_intro H := destruct H as (ST & FR & MU & WM & MI & BU & BL & LE & KC); unfold DgBaseU.DG_W in MU.

Hypothesis dg_loop2 : forall (n : nat) (i p2 len D U unit kap s Ks : Z) s0' s1' a4' s2' t4' s3' s4' s5' s6' (m : word -> option byte) (bs : list byte),
  Z.to_nat (17 - i) = n ->
  dg_mem m len Ks bs -> (1 <= len <= 3 + i)%Z -> (0 <= i <= 17)%Z -> (- 2 ^ 31 + 18 <= Ks <= 2 ^ 31 - 3)%Z ->
  (56 <= s <= 59)%Z -> (U <= p2 < 2 ^ s)%Z -> (2 * 10 ^ i <= U)%Z -> (0 <= D < 2 ^ 64)%Z -> unit = (10 ^ i)%Z -> kap = (- i)%Z ->
  evt rsegs (dg_post Ks) (MS (mkR ra (Z_to_bv 64 (SP0 - 64)) gp tp (Z_to_bv 64 kp) (Z_to_bv 64 s) (Z_to_bv 64 p2) s0' s1'
                                  (Z_to_bv 64 D) (Z_to_bv 64 U) (Z_to_bv 64 (2 ^ s)) (Z_to_bv 64 1) a4' (Z_to_bv 64 unit)
                                  (Z_to_bv 64 buf) (Z_to_bv 64 lenp) s2' s3' s4' s5' s6' s7 s8 s9 s10 s11
                                  (Z_to_bv 64 (2 ^ s - 1)) t4' (Z_to_bv 64 10) (Z_to_bv 64 kap))
                              F (Z_to_bv 64 0x44e6c) fc None m (seg_rom rsegs)).

Hypothesis dg_rw1_entry : forall (len D U r dv kc s Ks : Z) t2' s0' a2' a5' t3' t6' s2' s3' s4' s5' s6' (m : word -> option byte) (bs : list byte),
  dg_mem m len Ks bs -> (1 <= len <= 3)%Z -> (- 2 ^ 31 + 18 <= Ks <= 2 ^ 31 - 3)%Z -> (56 <= s <= 59)%Z ->
  (0 <= r < U)%Z -> (U < 2 ^ 64)%Z -> (0 <= D < 2 ^ 64)%Z -> (dv = 1 \/ dv = 10 \/ dv = 100)%Z -> (2 <= kc <= 4)%Z ->
  evt rsegs (dg_post Ks) (MS (mkR ra (Z_to_bv 64 (SP0 - 64)) gp tp (Z_to_bv 64 kp) (Z_to_bv 64 s) t2' s0' (Z_to_bv 64 r)
                                  (Z_to_bv 64 D) (Z_to_bv 64 U) a2' (Z_to_bv 64 1) (Z_to_bv 64 dv) a5' (Z_to_bv 64 buf) (Z_to_bv 64 lenp)
                                  s2' s3' s4' s5' s6' s7 s8 s9 s10 s11 t3' (Z_to_bv 64 kc) (Z_to_bv 64 1) t6')
                              F (Z_to_bv 64 0x44fb4) fc None m (seg_rom rsegs)).

Lemma dg_l1_k1 : forall (p1 p2 len D U Wp1 s Ks : Z) s1' a5' s2' s3' s4' s5' s6' (m : word -> option byte) (bs : list byte),
  dg_mem m len Ks bs -> (0 <= len <= 2)%Z -> (- 2 ^ 31 + 18 <= Ks <= 2 ^ 31 - 3)%Z -> (56 <= s <= 59)%Z ->
  (0 <= p1 < 10)%Z -> (0 <= p2 < 2 ^ s)%Z -> (p1 * 2 ^ s + p2 < 2 ^ 64)%Z -> (2 <= U < 2 ^ 64)%Z -> (0 <= D < 2 ^ 64)%Z ->
  (len = 0 -> p1 * 2 ^ s + p2 = Wp1 /\ U <= Wp1 /\ 8 <= p1)%Z ->
  evt rsegs (dg_post Ks) (MS (mkR ra (Z_to_bv 64 (SP0 - 64)) gp tp (Z_to_bv 64 kp) (Z_to_bv 64 s) (Z_to_bv 64 p2)
                                  (Z_to_bv 64 (0xcccccccd * 2 ^ 32)) s1' (Z_to_bv 64 D) (Z_to_bv 64 U) (Z_to_bv 64 (2 ^ s)) (Z_to_bv 64 1)
                                  (Z_to_bv 64 1) a5' (Z_to_bv 64 buf) (Z_to_bv 64 lenp) s2' s3' s4' s5' s6' s7 s8 s9 s10 s11
                                  (Z_to_bv 64 (2 ^ s - 1)) (Z_to_bv 64 2) (Z_to_bv 64 1) (Z_to_bv 64 p1))
                              F (Z_to_bv 64 0x44de4) fc None m (seg_rom rsegs)).
Proof using BUFR LENR KPR SPR0 SEP_B SEP_L SEP_K SEP_BL SEP_BK SEP_LK LA KA dg_loop2 dg_rw1_entry.
  intros p1 p2 len D U Wp1 s Ks s1' a5' s2' s3' s4' s5' s6' m bs DM Hlen HKs Hs Hp1 Hp2 Hlt HU HD Hinv.
  destruct DM as (ST & FR & MU & WM & MI & BU & BL & LE & KC). unfold DgBaseU.DG_W in MU. unfold DgBaseU.SP0 in *.
  assert (IDX : dg_idx buf len) by exact I.
  destruct (Z.eq_dec len 0) as [HL0 | HL0];
    [ destruct (Hinv HL0) as (HW & HUW & H8); subst len | ]; clear Hinv.
  all: assert (Hs4 : s = 56%Z \/ s = 57%Z \/ s = 58%Z \/ s = 59%Z) by lia.
  all: destruct Hs4 as [-> | [-> | [-> | ->]]].
  all: dg_solve 24%nat [0x44fb4; 0x44e6c]%Z.
  all: first
    [ dg_at [0x44fb4]%Z; eapply dg_rw1_entry;
      [ dg_mem_tac | lia | lia | lia | lia | lia | lia | lia | lia ]
    | dg_at [0x44e6c]%Z;
      let sv := dg_reg 6%Z in
      lazymatch sv with Z_to_bv 64 ?s0 =>
        eapply (dg_loop2 _ 0%Z _ _ _ _ _ _ s0);
        [ reflexivity | dg_mem_tac | lia | lia | lia | lia | lia | (cbn; lia) | lia | reflexivity | reflexivity ]
      end ].
Qed.

Lemma dg_l1_k2 : forall (p1 p2 len D U Wp1 s Ks : Z) s1' a5' s2' s3' s4' s5' s6' (m : word -> option byte) (bs : list byte),
  dg_mem m len Ks bs -> (0 <= len <= 1)%Z -> (- 2 ^ 31 + 18 <= Ks <= 2 ^ 31 - 3)%Z -> (56 <= s <= 59)%Z ->
  (0 <= p1 < 100)%Z -> (0 <= p2 < 2 ^ s)%Z -> (p1 * 2 ^ s + p2 < 2 ^ 64)%Z -> (2 <= U < 2 ^ 64)%Z -> (0 <= D < 2 ^ 64)%Z ->
  (len = 0 -> p1 * 2 ^ s + p2 = Wp1 /\ U <= Wp1 /\ 8 <= p1)%Z ->
  evt rsegs (dg_post Ks) (MS (mkR ra (Z_to_bv 64 (SP0 - 64)) gp tp (Z_to_bv 64 kp) (Z_to_bv 64 s) (Z_to_bv 64 p2)
                                  (Z_to_bv 64 (0xcccccccd * 2 ^ 32)) s1' (Z_to_bv 64 D) (Z_to_bv 64 U) (Z_to_bv 64 (2 ^ s)) (Z_to_bv 64 1)
                                  (Z_to_bv 64 10) a5' (Z_to_bv 64 buf) (Z_to_bv 64 lenp) s2' s3' s4' s5' s6' s7 s8 s9 s10 s11
                                  (Z_to_bv 64 (2 ^ s - 1)) (Z_to_bv 64 3) (Z_to_bv 64 1) (Z_to_bv 64 p1))
                              F (Z_to_bv 64 0x44de4) fc None m (seg_rom rsegs)).
Proof using BUFR LENR KPR SPR0 SEP_B SEP_L SEP_K SEP_BL SEP_BK SEP_LK LA KA dg_loop2 dg_rw1_entry.
  intros p1 p2 len D U Wp1 s Ks s1' a5' s2' s3' s4' s5' s6' m bs DM Hlen HKs Hs Hp1 Hp2 Hlt HU HD Hinv.
  destruct DM as (ST & FR & MU & WM & MI & BU & BL & LE & KC). unfold DgBaseU.DG_W in MU. unfold DgBaseU.SP0 in *.
  assert (IDX : dg_idx buf len) by exact I.
  destruct (Z.eq_dec len 0) as [HL0 | HL0];
    [ destruct (Hinv HL0) as (HW & HUW & H8); subst len | ]; clear Hinv.
  all: assert (Hs4 : s = 56%Z \/ s = 57%Z \/ s = 58%Z \/ s = 59%Z) by lia.
  all: destruct Hs4 as [-> | [-> | [-> | ->]]].
  all: dg_xstep; dg_solve 24%nat [0x44fb4; 0x44de4; 0x45114]%Z.
  all: lazymatch goal with
    | |- evt _ _ (MS _ _ (Z_to_bv 64 0x44fb4%Z) _ _ _ _) => eapply dg_rw1_entry
    | |- evt _ _ (MS _ _ (Z_to_bv 64 0x44de4%Z) _ _ _ _) =>
        let sv := dg_reg 6%Z in
        lazymatch sv with Z_to_bv 64 ?s0 => eapply (dg_l1_k1 _ _ _ _ _ Wp1 s0) end
    | |- evt _ _ (MS _ _ ?pc _ _ _ _) => fail 100 "dg_l1_k2: unexpected stop at" pc
    end.
  all: try dg_mem_tac.
  all: lia.
Qed.

Lemma dg_l1_k3 : forall (p1 p2 len D U Wp1 s Ks : Z) s1' a5' s2' s3' s4' s5' s6' (m : word -> option byte) (bs : list byte),
  dg_mem m len Ks bs -> (0 <= len <= 0)%Z -> (- 2 ^ 31 + 18 <= Ks <= 2 ^ 31 - 3)%Z -> (56 <= s <= 59)%Z ->
  (0 <= p1 < 256)%Z -> (0 <= p2 < 2 ^ s)%Z -> (p1 * 2 ^ s + p2 < 2 ^ 64)%Z -> (2 <= U < 2 ^ 64)%Z -> (0 <= D < 2 ^ 64)%Z ->
  (len = 0 -> p1 * 2 ^ s + p2 = Wp1 /\ U <= Wp1 /\ 8 <= p1)%Z ->
  evt rsegs (dg_post Ks) (MS (mkR ra (Z_to_bv 64 (SP0 - 64)) gp tp (Z_to_bv 64 kp) (Z_to_bv 64 s) (Z_to_bv 64 p2)
                                  (Z_to_bv 64 (0xcccccccd * 2 ^ 32)) s1' (Z_to_bv 64 D) (Z_to_bv 64 U) (Z_to_bv 64 (2 ^ s)) (Z_to_bv 64 1)
                                  (Z_to_bv 64 100) a5' (Z_to_bv 64 buf) (Z_to_bv 64 lenp) s2' s3' s4' s5' s6' s7 s8 s9 s10 s11
                                  (Z_to_bv 64 (2 ^ s - 1)) (Z_to_bv 64 4) (Z_to_bv 64 1) (Z_to_bv 64 p1))
                              F (Z_to_bv 64 0x44de4) fc None m (seg_rom rsegs)).
Proof using BUFR LENR KPR SPR0 SEP_B SEP_L SEP_K SEP_BL SEP_BK SEP_LK LA KA dg_loop2 dg_rw1_entry.
  intros p1 p2 len D U Wp1 s Ks s1' a5' s2' s3' s4' s5' s6' m bs DM Hlen HKs Hs Hp1 Hp2 Hlt HU HD Hinv.
  destruct DM as (ST & FR & MU & WM & MI & BU & BL & LE & KC). unfold DgBaseU.DG_W in MU. unfold DgBaseU.SP0 in *.
  assert (IDX : dg_idx buf len) by exact I.
  destruct (Z.eq_dec len 0) as [HL0 | HL0];
    [ destruct (Hinv HL0) as (HW & HUW & H8); subst len | ]; clear Hinv.
  all: try (exfalso; lia).
  all: assert (Hs4 : s = 56%Z \/ s = 57%Z \/ s = 58%Z \/ s = 59%Z) by lia.
  all: destruct Hs4 as [-> | [-> | [-> | ->]]].
  all: dg_xstep; dg_solve 24%nat [0x44fb4; 0x44de4; 0x45114]%Z.
  all: lazymatch goal with
    | |- evt _ _ (MS _ _ (Z_to_bv 64 0x44fb4%Z) _ _ _ _) => eapply dg_rw1_entry
    | |- evt _ _ (MS _ _ (Z_to_bv 64 0x44de4%Z) _ _ _ _) =>
        let sv := dg_reg 6%Z in
        lazymatch sv with Z_to_bv 64 ?s0 => eapply (dg_l1_k2 _ _ _ _ _ Wp1 s0) end
    | |- evt _ _ (MS _ _ ?pc _ _ _ _) => fail 100 "dg_l1_k3: unexpected stop at" pc
    end.
  all: try dg_mem_tac.
  all: lia.
Qed.

Lemma dg_spec : forall t0 t1 t2 t3 t4 t5 t6 (m : word -> option byte) (Wm dW dP s Ks : Z) (bs : list byte) lj,
  (56 <= s <= 59)%Z -> (1 <= Wm)%Z -> (0 <= dW)%Z -> (0 <= dP)%Z -> (Wm + dW + dP <= 2 ^ 64 - 2)%Z -> (2 ^ 62 <= Wm + dW + dP + 1)%Z ->
  (- 2 ^ 31 + 18 <= Ks <= 2 ^ 31 - 3)%Z ->
  stk rsegs m (SP0 - 64) SP0 -> rw_cells rsegs m SP0 [C8 (Z_to_bv 64 kp)] ->
  u8arr rsegs m buf bs -> length bs = 21%nat -> rw_cells rsegs m lenp [C4 lj] -> rw_cells rsegs m kp [C4 (Z_to_bv 64 Ks)] ->
  mem_inv rsegs m -> m = m0 ->
  evt rsegs (dg_post Ks) (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 Wm) (Z_to_bv 64 (2 ^ 32 - s)) (Z_to_bv 64 (Wm + dW)) (Z_to_bv 64 (2 ^ 32 - s))
                                  (Z_to_bv 64 (Wm + dW + dP)) (Z_to_bv 64 (2 ^ 32 - s)) (Z_to_bv 64 buf) (Z_to_bv 64 lenp)
                                  s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                              F (Z_to_bv 64 0x44d38) fc None m (seg_rom rsegs)).
Proof using BUFR LENR KPR SPR0 SEP_B SEP_L SEP_K SEP_BL SEP_BK SEP_LK LA KA dg_loop2 dg_rw1_entry.
  intros t0 t1 t2 t3 t4 t5 t6 m Wm dW dP s Ks bs lj Hs HWm HdW HdP Hsum Hbig HKs ST KPC BU BL LJ KC MI E.
  pose proof (munch_refl DG_W m) as MU. pose proof (wmono_refl rsegs m) as WM.
  subst m. unfold DgBaseU.DG_W in MU. unfold DgBaseU.SP0 in *.
  carve_frame 64%nat ST.
  assert (Hs4 : s = 56%Z \/ s = 57%Z \/ s = 58%Z \/ s = 59%Z) by lia.
  destruct Hs4 as [-> | [-> | [-> | ->]]].
  all: dg_solve 12%nat [0x44de4]%Z.
  all: dg_fold_R.
  all: lazymatch goal with |- evt _ _ (MS (mkR _ _ _ _ _ (Z_to_bv 64 ?sv) (Z_to_bv 64 ?p2) _ _ (Z_to_bv 64 ?D) (Z_to_bv 64 ?U) _ _ _ ?a5v _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 ?p1)) _ _ _ _ ?mm _) =>
         eapply evt_eq; [ | eapply (dg_l1_k3 p1 p2 0%Z D U (Wm + dW + dP + 1)%Z sv Ks s1 a5v s2 s3 s4 s5 s6 mm bs) ];
         [ unfold DgBaseU.SP0; reflexivity | .. ]
       end.
  all: try (lazymatch goal with |- dg_mem _ _ _ _ => dg_mem_tac end).
  all: repeat match goal with |- context [Z.land ?a ?b] =>
         first [ let n := eval vm_compute in (Z.log2 (a + 1)) in
                 rewrite (Z.land_comm a b); replace a with (Z.ones n) by (vm_compute; reflexivity);
                 rewrite (Z.land_ones b n) by lia
               | let n := eval vm_compute in (Z.log2 (b + 1)) in
                 replace b with (Z.ones n) by (vm_compute; reflexivity);
                 rewrite (Z.land_ones a n) by lia ] end.
  all: try (intros _; Z.div_mod_to_equations; repeat split; lia).
  all: try (Z.div_mod_to_equations; lia).
  all: try lia.
  all: lazymatch goal with |- ?G => fail 100 "open side goal" G end.
Qed.

End DG.
