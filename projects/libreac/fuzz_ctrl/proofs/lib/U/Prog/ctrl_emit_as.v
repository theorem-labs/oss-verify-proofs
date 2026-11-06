From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcModel RcLib RcPorts RcPortsLib RcBox RcSynth RcLay
  RcFin RcFinLib RcEmit RcEmitLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Prog Require Import memset_c memcpy_c ctrl_lay_block_c
  reac_braid_encode_ns0_c ctrl_finish_c ctrl_emit_as_c.
Local Ltac lia ::= em_lia.
Import ListNotations.
Open Scope Z_scope.

Local Ltac mem_after_store_opt ::=
  try rewrite em_le1;
  try fix_lit_store;
  lazymatch goal with
  | |- evt ?segs _ (MS _ _ _ _ _ (write_to_mem ?m (wa (?A + Z.of_nat _)) _) _) =>
      match goal with
      | H : rw_cells segs m A _ |- _ => mem_after_store
      | _ => idtac
      end
  | _ => idtac
  end.

Ltac fixret :=
  repeat match goal with
  | |- context [ret_pc (Z_to_bv 64 ?n)] =>
      replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [lia | reflexivity])
  end.

Ltac tac_call MUx WMx :=
  lazymatch type of MUx with munch _ ?ma ?mb => transport_after_call rsegs ma mb MUx WMx end.

(* A UBSan check branch: decide the unsigned comparison of two literals and take the branch it gives. *)
Ltac em_ub :=
  rewrite ?em_ltu_neg_r, ?em_ltu_neg_l, ?em_ltu_lit by lia;
  match goal with
  | |- context [?a <? ?b] =>
      first [ replace (a <? b) with true by (symmetry; apply Z.ltb_lt; lia)
            | replace (a <? b) with false by (symmetry; apply Z.ltb_ge; lia) ]
  end; cbn [negb]; cbv iota.

Section Emit.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a5 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : word -> option byte) (o f md d s g n ns : Z) (row tb mb nb gb db sb junk : list byte).

  Local Abbreviation SP0 := (bv_unsigned sp).
  Local Abbreviation LO := (bv_unsigned sp - 320).
  Local Abbreviation KB := (ly_k row).
  Local Abbreviation LL := (ubat row 21).
  Local Abbreviation GG := (ubat row 22).
  Local Abbreviation AA := (ubat row 23).
  Local Abbreviation CC := (ubat row 20).
  Local Abbreviation RO := (ubat row 18).
  Local Abbreviation RL := (ubat row 19).
  Local Abbreviation EE := (em_E (ubat row 21) (ubat row 22) n (em_hid mb)).
  Local Abbreviation LEN := (em_len (ubat row 21) n).
  Local Abbreviation LB := (ly_lay (ly_k row) tb (ly_Z md mb nb (ly_bb (ly_k row))) g (ly_ao row) (ly_al row) gb).
  Local Abbreviation BLK := (fin (ubat row 20) (ubat row 18) (ubat row 19)
                           (ly_lay (ly_k row) tb (ly_Z md mb nb (ly_bb (ly_k row))) g (ly_ao row) (ly_al row) gb)).
  Local Abbreviation NM := ((3 <= ly_k row <= 9 /\ (ly_bb (ly_k row) = 5 \/ ly_bb (ly_k row) = 6)) /\
                            has mb <> 0 /\ rname mb <> 0).

  Hypothesis HMS : memset_contract.
  Hypothesis HMC : memcpy_contract.
  Hypothesis HLB : ctrl_lay_block_contract.
  Hypothesis HBR : reac_braid_encode_ns0_contract.
  Hypothesis HFN : ctrl_finish_contract.
  Hypothesis Hn : -2^31 <= n < 2^31.
  Hypothesis Hns : -2^31 <= ns < 2^31.
  Hypothesis Hg : 0 <= g < 2^64.
  Hypothesis HS16 : SP0 mod 16 = 0.
  Hypothesis HST : em_stk rsegs m LO SP0.
  Hypothesis Dsf : ly_dj LO SP0 f (f + 24).
  Hypothesis Dst : KB = 2 -> ly_dj LO SP0 (ly_tm row) (ly_tm row + 32).
  Hypothesis Dsm : ly_dj LO SP0 md (md + 296).
  Hypothesis Dsn : NM -> ly_dj LO SP0 (rname mb) (rname mb + Z.of_nat (length nb)).
  Hypothesis Dsd : ly_dj LO SP0 d (d + 6).
  Hypothesis Dss : ly_dj LO SP0 s (s + 6).
  Hypothesis Dsg : g <> 0 -> ly_al row <> 0 -> ly_dj LO SP0 g (g + ly_al row).
  Hypothesis Hf0 : f <> 0.
  Hypothesis Hf8 : f mod 8 = 0.
  Hypothesis Hf24 : f + 24 <= 2^64.
  Hypothesis Hrl : length row = 24%nat.
  Hypothesis HR : em_at rsegs m f row.
  Hypothesis Hk : KB <= 9.
  Hypothesis Hc : CC <= 2.
  Hypothesis HL : LL <= 2.
  Hypothesis HG : GG <= 1.
  Hypothesis HA : AA <= 1.
  Hypothesis Hao : ly_ao row + ly_al row <= 32.
  Hypothesis Htm : KB = 2 -> ly_tm row + 32 <= 2^64 /\ length tb = 32%nat /\ ro_bytes rsegs (ly_tm row) tb.
  Hypothesis Hc2 : CC = 2 -> 2 <= RL /\ RO + RL <= 31.
  Hypothesis HLA : LL = 2 -> AA = 0.
  Hypothesis Hmd0 : md <> 0.
  Hypothesis Hmd8 : md mod 8 = 0.
  Hypothesis Hmd296 : md + 296 <= 2^64.
  Hypothesis Hml : length mb = 296%nat.
  Hypothesis HM : em_at rsegs m md mb.
  Hypothesis Hnm : NM -> name_ok nb /\ bytes_at rsegs m (rname mb) nb.
  Hypothesis Ho : 0 < o.
  Hypothesis Ho1492 : o + 1492 <= 2^64.
  Hypothesis HEo : EE = true ->
       rw_cells rsegs m o [CB (Z.to_nat LEN) junk] /\ ly_dj LO SP0 o (o + LEN) /\
       ly_dj o (o + LEN) f (f + 24) /\ (KB = 2 -> ly_dj o (o + LEN) (ly_tm row) (ly_tm row + 32)) /\
       ly_dj o (o + LEN) md (md + 296) /\
       (NM -> ly_dj o (o + LEN) (rname mb) (rname mb + Z.of_nat (length nb))) /\
       ly_dj o (o + LEN) d (d + 6) /\ ly_dj o (o + LEN) s (s + 6) /\
       (g <> 0 -> ly_al row <> 0 -> ly_dj o (o + LEN) g (g + ly_al row)).
  Hypothesis Hdb : length db = 6%nat.
  Hypothesis HD : em_at rsegs m d db.
  Hypothesis Hsb : length sb = 6%nat.
  Hypothesis HSb : em_at rsegs m s sb.
  Hypothesis Hgb : g <> 0 -> ly_al row <> 0 -> Z.of_nat (length gb) = ly_al row /\ bytes_at rsegs m g gb.
  Hypothesis Hns0 : AA = 1 -> ns <= 0.
  Hypothesis MI0 : em_mi rsegs m.

  Definition RES (m' : word -> option byte) : Prop :=
    bytes_at rsegs m' o
      (em_fr db sb (bv_unsigned a5 mod 65536) (nth 0 row (Z_to_bv 8 0)) (nth 1 row (Z_to_bv 8 0)) BLK LEN)
    /\ (LL <> 2 -> em_wok n = true)
    /\ (CC = 1 \/ CC = 2 -> closes CC RO RL BLK /\ (closes CC RO RL LB -> BLK = LB)).

  Definition Qp : machine_state -> Prop :=
    fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                      (m' : word -> option byte),
      ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (if EE then LEN else 0))
                    a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (ret_pc ra) fc None m' (seg_rom rsegs)
      /\ munch [(LO, SP0); (o, o + (if EE then LEN else 0))] m m'
      /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' LO SP0
      /\ (EE = true -> RES m').


  Local Abbreviation FRS := [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1;
                             C8 s0; C8 ra].
  Local Abbreviation HDR :=
    [Z_to_bv 8 136; Z_to_bv 8 25; Z_to_bv 8 ((bv_unsigned a5 mod 65536) mod 256);
     Z_to_bv 8 ((bv_unsigned a5 mod 65536) / 256); nth 0 row (Z_to_bv 8 0); nth 1 row (Z_to_bv 8 0)].

  Lemma rng_sp : 320 <= SP0 < 2^64.
  Proof. pose proof (zr_word sp) as R. unfold inr64 in R. destruct HST as (H1 & _). lia. Qed.

  Lemma row_at : forall mc W, munch ((LO, SP0) :: W) m mc -> disjoint_from W f 24 -> bytes_at rsegs mc f row.
  Proof.
    intros mc W MU DW. apply (bytes_at_transport rsegs _ m mc f row HR MU). rewrite Hrl. cbn [disjoint_from].
    pose proof Dsf as D. unfold ly_dj in D. split; [lia | exact DW].
  Qed.

  Lemma E_false_w : LL <> 2 -> em_wok n = false -> EE = false.
  Proof. intros H1 H2. unfold em_E. rewrite H2. replace (ubat row 21 =? 2) with false by (symmetry; apply Z.eqb_neq; exact H1). reflexivity. Qed.

  Lemma epi : forall (x1 u0 u1 u2 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x27
                      u3 u4 u5 u6 : word) (mc : word -> option byte) (j : list byte) (r : Z),
    r = (if EE then LEN else 0) -> 0 <= r < 2^64 ->
    rw_cells rsegs mc (SP0 + -128) (CB 24 j :: FRS) ->
    stk rsegs mc LO (SP0 + -128) ->
    munch [(LO, SP0); (o, o + r)] m mc -> wmono rsegs m mc -> mem_inv rsegs mc ->
    (EE = true -> RES mc) ->
    evt rsegs Qp
      (MS (mkR x1 (Z_to_bv 64 (SP0 + -128)) gp tp u0 u1 u2 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21
               x22 x23 x24 x25 (Z_to_bv 64 r) x27 u3 u4 u5 u6)
          F (Z_to_bv 64 0x151f8) fc None mc (seg_rom rsegs)).
  Proof.
    intros x1 u0 u1 u2 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x27 u3 u4 u5 u6
      mc j r Er Rr FR ST MU WM MI HRES.
    pose proof rng_sp as Rsp.
    pose proof ST as (Rlo & _ & _).
    do 16 step.
    apply evt_done. unfold Qp.
    do 14 eexists. exists mc. rewrite <- Er.
    split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [exact MI|].
    split; [|exact HRES].
    release_frame FR ST (bv_unsigned sp). exact ST.
  Qed.

  Lemma epi0 : forall (x1 u0 u1 u2 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x27
                      u3 u4 u5 u6 : word) (mc : word -> option byte) (j : list byte),
    EE = false ->
    rw_cells rsegs mc (SP0 + -128) (CB 24 j :: FRS) ->
    stk rsegs mc LO (SP0 + -128) ->
    munch [(LO, SP0)] m mc -> wmono rsegs m mc -> mem_inv rsegs mc ->
    evt rsegs Qp
      (MS (mkR x1 (Z_to_bv 64 (SP0 + -128)) gp tp u0 u1 u2 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21
               x22 x23 x24 x25 (Z_to_bv 64 0) x27 u3 u4 u5 u6)
          F (Z_to_bv 64 0x151f8) fc None mc (seg_rom rsegs)).
  Proof.
    intros x1 u0 u1 u2 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x27 u3 u4 u5 u6
      mc j HE FR ST MU WM MI.
    apply (epi x1 u0 u1 u2 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x27 u3 u4 u5 u6
             mc j 0); [rewrite HE; reflexivity | lia | exact FR | exact ST | | exact WM | exact MI |].
    - apply em_munch_add; exact MU.
    - rewrite HE. intros H. discriminate H.
  Qed.

  Lemma tail3 : forall (x1 u0 u1 u2 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x27
                        u3 u4 u5 u6 w1 w2 : word) (mc : word -> option byte) (j : list byte),
    EE = true ->
    rw_cells rsegs mc (SP0 + -128) (CB 8 j :: C8 w1 :: C8 w2 :: FRS) -> stk rsegs mc LO (SP0 + -128) ->
    munch [(LO, SP0); (o, o + LEN)] m mc -> wmono rsegs m mc -> mem_inv rsegs mc ->
    rw_cells rsegs mc o [CB 6 db] -> rw_cells rsegs mc (o + 6) [CB 6 sb] -> rw_cells rsegs mc (o + 12) [CB 6 HDR] ->
    rw_cells rsegs mc (o + 18) [CB 32 BLK] ->
    rw_cells rsegs mc (o + 50) [CB (Z.to_nat (LEN - 52)) (repeat (Z_to_bv 8 0) (Z.to_nat (LEN - 52)))] ->
    rw_cells rsegs mc (o + LEN + -2) [CB 2 (repeat (Z_to_bv 8 0) 2)] ->
    (CC = 1 \/ CC = 2 -> closes CC RO RL BLK /\ (closes CC RO RL LB -> BLK = LB)) ->
    evt rsegs Qp
      (MS (mkR x1 (Z_to_bv 64 (SP0 + -128)) gp tp u0 u1 u2 (Z_to_bv 64 o) x9 x10 x11 x12 x13 x14 x15 x16 x17
               x18 x19 x20 x21 x22 x23 x24 x25 (Z_to_bv 64 LEN) x27 u3 u4 u5 u6)
          F (Z_to_bv 64 0x151c0) fc None mc (seg_rom rsegs)).
  Proof.
    intros x1 u0 u1 u2 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x27 u3 u4 u5 u6 w1 w2 mc j
      HE FR ST MU WM MI P1 P2 P3 P4 P5 P6 CLS.
    pose proof rng_sp as Rsp. pose proof (em_len_rng _ _ _ _ HE) as RLN.
    destruct (HEo HE) as (_ & Dso & _). unfold ly_dj in Dso.
    destruct (em_rw_rep rsegs mc _ (Z_to_bv 8 0) 2 1 P6 ltac:(lia)) as [P6a P6b]. clear P6.
    replace (o + LEN + -2 + Z.of_nat 1) with (o + (LEN + -1)) in P6b by lia.
    change (2 - 1)%nat with 1%nat in P6b.
    (* out[len - 2] = 0xc2; out[len - 1] = 0xea, each address checked for overflow; the two addresses are
       named so that the store tactics match them against P6a and P6b *)
    step. step.
    set (q := LEN + -2 + o) in *. assert (Eq : q = LEN + -2 + o) by reflexivity. clearbody q.
    replace (o + LEN + -2) with q in P6a by lia.
    step.
    rewrite rc_eqb by lia. replace (q =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbv iota.
    step. em_ub.
    step. step. step.
    rewrite (unsigned_lit o) by lia. rewrite (zb_lxor_ones o) by lia.
    step. step. em_ub.
    step.
    set (q2 := o + (LEN + -1)) in *. assert (Eq2 : q2 = o + (LEN + -1)) by reflexivity. clearbody q2.
    step. step. step.
    apply em_merge3 in FR. destruct FR as [j' FR].
    eapply epi; [rewrite HE; reflexivity | lia | exact FR | exact ST | exact MU | exact WM | exact MI |].
    intros _. unfold RES. split; [|split; [intros HL2; exact (em_E_wok _ _ _ _ HE HL2) | exact CLS]].
    apply em_rw_cells_bytes in P6a. apply em_rw_cells_bytes in P6b.
    cbn [cells_bytes cbytes app] in P6a, P6b.
    rewrite (em_byte_lit 194) in P6a by lia. rewrite em_byte_m22 in P6b.
    eapply (em_fr_bytes rsegs _ o LEN db sb BLK); [exact P1 | exact P2 | exact P3 | exact P4 | exact P5 | | lia].
    change [Z_to_bv 8 194; Z_to_bv 8 234] with ([Z_to_bv 8 194] ++ [Z_to_bv 8 234]).
    apply bytes_at_app. split.
    - rewrite Eq in P6a. replace (o + LEN + -2) with (LEN + -2 + o) by lia. exact P6a.
    - rewrite Eq2 in P6b. cbn [length]. replace (o + LEN + -2 + Z.of_nat 1) with (o + (LEN + -1)) by lia.
      exact P6b.
  Qed.

  Lemma tail2 : forall (x1 u0 u1 u2 x9 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x23 x24 x25 x27
                        u3 u4 u5 u6 w1 w2 : word) (mc : word -> option byte) (j : list byte),
    EE = true ->
    rw_cells rsegs mc (SP0 + -128) (CB 8 j :: C8 w1 :: C8 w2 :: FRS) -> stk rsegs mc LO (SP0 + -128) ->
    munch [(LO, SP0); (o, o + LEN)] m mc -> wmono rsegs m mc -> mem_inv rsegs mc ->
    rw_cells rsegs mc o [CB 6 db] -> rw_cells rsegs mc (o + 6) [CB 6 sb] -> rw_cells rsegs mc (o + 12) [CB 6 HDR] ->
    rw_cells rsegs mc (o + 18) [CB 32 LB] ->
    rw_cells rsegs mc (o + 50) [CB (Z.to_nat (LEN - 52)) (repeat (Z_to_bv 8 0) (Z.to_nat (LEN - 52)))] ->
    rw_cells rsegs mc (o + LEN + -2) [CB 2 (repeat (Z_to_bv 8 0) 2)] ->
    evt rsegs Qp
      (MS (mkR x1 (Z_to_bv 64 (SP0 + -128)) gp tp u0 u1 u2 (Z_to_bv 64 o) x9 x10 x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 f) x19 x20 x21 x22 x23 x24 x25 (Z_to_bv 64 LEN) x27 u3 u4 u5 u6)
          F (Z_to_bv 64 0x151b4) fc None mc (seg_rom rsegs)).
  Proof.
    intros x1 u0 u1 u2 x9 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x23 x24 x25 x27 u3 u4 u5 u6 w1 w2 mc j
      HE FR ST MU WM MI P1 P2 P3 P4 P5 P6.
    pose proof rng_sp as Rsp. pose proof (em_len_rng _ _ _ _ HE) as RLN.
    pose proof (bytes_at_bound _ _ _ _ HR) as BR.
    destruct (HEo HE) as (_ & Dsof & Dof & _). pose proof Dsof as Dso. unfold ly_dj in Dso.
    pose proof (row_at mc [(o, o + LEN)] MU (em_df1 _ _ _ _ Dof)) as HRc.
    pose proof (byte_range (nth 18 row (Z_to_bv 8 0))) as R18.
    destruct (stk_split rsegs mc LO (SP0 + -128 - 16) (SP0 + -128) ST ltac:(lia)) as [STlo SThi]. clear ST.
    (* ctrl_finish(o, f) *)
    step. step. step.
    eapply evt_cut.
    { eapply HFN with (p := o) (f := f) (c := CC) (o := RO) (n := RL) (row := row) (B := LB);
        rewrite ?unsigned_lit by lia;
        [ reflexivity | reflexivity | exact SThi | apply (em_dj_raw _ _ _ _ _ _ _ _ Dsf); lia
        | apply (em_dj_raw _ _ _ _ _ _ _ _ Dsof); lia | exact Hf8 | exact Hf24 | exact Hrl | exact HRc
        | reflexivity | reflexivity | reflexivity | exact Hc | exact Hc2 | lia | lia | intros _; exact P4 ]. }
    intros ms' (y10 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & m1 & -> & MU1 & WM1 & MI1 & ST1 & HF).
    rewrite !unsigned_lit in MU1, ST1 by lia.
    fixret. specialize (MI1 MI).
    destruct (Z.eq_dec CC 0) as [C0|C0].
    - rewrite C0, em_fin_nil in MU1.
      tac_call MU1 WM1. clear MU1 WM1 MI.
      pose proof (stk_merge rsegs m1 LO (SP0 + -128 - 16) (SP0 + -128) STlo ST1 ltac:(lia)) as ST. clear STlo ST1.
      assert (P4' : rw_cells rsegs m1 (o + 18) [CB 32 BLK]) by (rewrite C0; exact P4).
      eapply tail3; [exact HE | eassumption .. | intros [H|H]; lia].
    - pose proof (byte_range (nth 20 row (Z_to_bv 8 0))) as R20.
      destruct (HF ltac:(unfold ubat in *; lia)) as (P4' & CL1 & CL2).
      apply (munch_weaken _ [(SP0 + -128 - 16, SP0 + -128); (o + 18, o + 50)] mc m1
               (em_fin_sub2 CC RO RL o _ Hc ltac:(unfold ubat; lia) Hc2)) in MU1.
      tac_call MU1 WM1. clear MU1 WM1 MI.
      pose proof (stk_merge rsegs m1 LO (SP0 + -128 - 16) (SP0 + -128) STlo ST1 ltac:(lia)) as ST. clear STlo ST1.
      eapply tail3; [exact HE | eassumption .. | intros _; split; [exact CL1 | exact CL2]].
  Qed.

  Lemma tail : forall (t0 t1 t2 t3 t5 t6 x10 x11 x12 x13 x14 x15 x16 x17 : word) (mc : word -> option byte)
                      (j : list byte),
    EE = true ->
    rw_cells rsegs mc (SP0 + -128) (CB 8 j :: C8 t3 :: C8 (Z_to_bv 64 ns) :: FRS) ->
    stk rsegs mc LO (SP0 + -128) ->
    munch [(LO, SP0)] m mc -> wmono rsegs m mc -> mem_inv rsegs mc ->
    evt rsegs Qp
      (MS (mkR ra (Z_to_bv 64 (SP0 + -128)) gp tp t0 t1 t2 (Z_to_bv 64 o) s1 x10 x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 f) s3 (Z_to_bv 64 n) (Z_to_bv 64 g) a5 (Z_to_bv 64 md) (Z_to_bv 64 s) (Z_to_bv 64 d)
               (Z_to_bv 64 LEN) s11 t3 (Z_to_bv 64 ns) t5 t6)
          F (Z_to_bv 64 0x150e4) fc None mc (seg_rom rsegs)).
  Proof.
    intros t0 t1 t2 t3 t5 t6 x10 x11 x12 x13 x14 x15 x16 x17 mc j HE FR ST MU0 WM MI.
    pose proof rng_sp as Rsp. pose proof (em_len_rng _ _ _ _ HE) as RLN.
    pose proof ST as (Rlo & _ & _).
    pose proof (bytes_at_bound _ _ _ _ HR) as BR. pose proof (bytes_at_bound _ _ _ _ HM) as BM.
    pose proof (bytes_at_bound _ _ _ _ HD) as BD. pose proof (bytes_at_bound _ _ _ _ HSb) as BS.
    destruct (HEo HE) as (HO & Dsof & Dof & Dot & Dom & Don & Dod & Dos & Dog).
    pose proof Dsof as Dso. unfold ly_dj in Dso.
    assert (HOc : rw_cells rsegs mc o [CB (Z.to_nat LEN) junk]).
    { apply (rw_cells_transport rsegs [(LO, SP0)] m mc o _ HO MU0 WM).
      cbn [disjoint_from cells_size csize]. lia. }
    assert (MU : munch [(LO, SP0); (o, o + LEN)] m mc) by (apply em_munch_add; exact MU0).
    clear MU0 HO.
    (* memset(o, 0, len) *)
    do 4 step.
    eapply evt_cut.
    { eapply HMS; [rewrite !unsigned_lit by lia; exact HOc | exact MI]. }
    intros ms' PO. unfold memset_post in PO.
    destruct PO as (u0 & u1 & u2 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & u3 & u4 & u5 & u6 & m1 & -> & MU1 & WM1
                    & MI1 & RW1).
    rewrite !unsigned_lit in MU1, RW1 by lia.
    change (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 0) mod 256)) with (Z_to_bv 8 0) in RW1.
    fixret.
    transport_after_call rsegs mc m1 MU1 WM1. clear MU1 WM1 MI.
    destruct (em_split_frame rsegs m1 o LEN _ RW1 ltac:(lia)) as (P1 & P2 & P3 & P4 & P5 & P6). clear RW1.
    pose proof (row_at m1 [(o, o + LEN)] MU (em_df1 _ _ _ _ Dof)) as HR1.
    pose proof (rd_byte rsegs m1 f row 0 HR1 ltac:(lia)) as RD0. replace (f + Z.of_nat 0) with f in RD0 by lia.
    pose proof (rd_byte rsegs m1 f row 1 HR1 ltac:(lia)) as RD1. change (Z.of_nat 1) with 1 in RD1.
    pose proof (em_obj rsegs m m1 _ _ o LEN d db 6 MU HD ltac:(rewrite Hdb; reflexivity) Dsd Dod) as HD1.
    (* the header: memcpy(o, d, 6), memcpy(o + 6, s, 6), then the six byte stores, each checked *)
    do 7 step.
    eapply evt_cut.
    { eapply HMC with (src := db) (junk := repeat (Z_to_bv 8 0) 6);
        [ rewrite unsigned_lit by lia; exact HD1
        | rewrite unsigned_lit by lia; rewrite Hdb; reflexivity
        | rewrite !unsigned_lit by lia; exact P1
        | rewrite !unsigned_lit by lia; apply (em_cpy_dj o LEN o d Dod); lia
        | exact MI1 ]. }
    intros ms' PO. unfold memcpy_post in PO.
    destruct PO as (u0' & u1' & u2' & y11' & y12' & y13' & y14' & y15' & y16' & y17' & u3' & u4' & u5' & u6' & m2 & ->
                    & MU2 & WM2 & MI2 & RW2 & BD2).
    rewrite !unsigned_lit in MU2, RW2 by lia. clear BD2. change (Z.to_nat 6) with 6%nat in RW2.
    fixret.
    transport_after_call rsegs m1 m2 MU2 WM2. clear MU2 WM2 MI1.
    pose proof (em_obj rsegs m m2 _ _ o LEN s sb 6 MU HSb ltac:(rewrite Hsb; reflexivity) Dss Dos) as HS2.
    step. step. em_ub. step. step. step.
    eapply evt_cut.
    { eapply HMC with (src := sb) (junk := repeat (Z_to_bv 8 0) 6);
        [ rewrite unsigned_lit by lia; exact HS2
        | rewrite unsigned_lit by lia; rewrite Hsb; reflexivity
        | rewrite !unsigned_lit by lia; exact P2
        | rewrite !unsigned_lit by lia; apply (em_cpy_dj o LEN (o + 6) s Dos); lia
        | exact MI2 ]. }
    intros ms' PO. unfold memcpy_post in PO.
    destruct PO as (v0 & v1 & v2 & z11 & z12 & z13 & z14 & z15 & z16 & z17 & v3 & v4 & v5 & v6 & m3 & ->
                    & MU3 & WM3 & MI3 & RW3 & BS3).
    rewrite !unsigned_lit in MU3, RW3 by lia. clear BS3. change (Z.to_nat 6) with 6%nat in RW3.
    fixret.
    transport_after_call rsegs m2 m3 MU3 WM3. clear MU3 WM3 MI2.
    step. step. em_ub.
    step. step. step. step. em_ub.
    step. step. step. step. em_ub.
    step. step. step. em_ub.
    step. step. step. step. em_ub.
    step. step. step. em_ub.
    step.
    match goal with H : rw_cells rsegs _ (o + 12) _ |- _ => apply em_merge in H; rename H into Q3 end.
    cbn [cells_size csize cells_bytes cbytes app Nat.add] in Q3.
    rewrite (em_byte_lit 136), (em_byte_lit 25), em_c16_hi, (em_c16_lo a5), !em_byte_zxb in Q3 by lia.
    (* ctrl_lay_block(o, f, md, g) *)
    do 5 step.
    eapply evt_cut.
    { eapply HLB with (p := o) (f := f) (md := md) (g := g) (fr := row) (ob := repeat (Z_to_bv 8 0) 32)
                      (tb := tb) (mb := mb) (nb := nb) (gb := gb).
      all: try unfold CTRL_LAY_BLOCK_K; rewrite ?unsigned_lit by lia.
      - reflexivity.
      - reflexivity.
      - reflexivity.
      - reflexivity.
      - lia.
      - lia.
      - lia.
      - exact Hg.
      - apply em_mod16; [exact HS16 | reflexivity].
      - replace (SP0 + -128 - 192) with LO by lia. assumption.
      - apply (em_dj_sub _ _ _ _ _ _ _ _ Dsof); lia.
      - apply (em_dj_sub _ _ _ _ _ _ _ _ Dsf); lia.
      - intros K. apply (em_dj_sub _ _ _ _ _ _ _ _ (Dst K)); lia.
      - intros G0 A0. apply (em_dj_sub _ _ _ _ _ _ _ _ (Dsg G0 A0)); lia.
      - intros K M0. split; [apply (em_dj_sub _ _ _ _ _ _ _ _ Dsm); lia|].
        intros B H1 H2. apply (em_dj_sub _ _ _ _ _ _ _ _ (Dsn (conj (conj K B) (conj H1 H2)))); lia.
      - exact Hf8.
      - exact Hf24.
      - exact Hrl.
      - eapply row_at; [exact MU | exact (em_df1 _ _ _ _ Dof)].
      - exact Hk.
      - exact Hao.
      - exact Htm.
      - lia.
      - lia.
      - exact P4.
      - apply (em_dj_sub _ _ _ _ _ _ _ _ Dof); lia.
      - intros K. apply (em_dj_sub _ _ _ _ _ _ _ _ (Dot K)); lia.
      - intros K M0. apply (em_dj_sub _ _ _ _ _ _ _ _ Dom); lia.
      - intros K M0 B H1 H2. apply (em_dj_sub _ _ _ _ _ _ _ _ (Don (conj (conj K B) (conj H1 H2)))); lia.
      - intros K M0. split; [exact Hmd8|]. split; [exact Hml|]. split.
        + exact (em_obj _ _ _ _ _ _ _ _ _ 296 MU HM ltac:(rewrite Hml; reflexivity) Dsm Dom).
        + intros B H1 H2. pose proof (conj (conj K B) (conj H1 H2)) as NMc.
          destruct (Hnm NMc) as [NO NB]. split; [exact NO|].
          exact (em_obj _ _ _ _ _ _ _ _ _ _ MU NB eq_refl (Dsn NMc) (Don NMc)).
      - intros G0 A0. destruct (Hgb G0 A0) as [GL GB]. split; [exact GL|]. split.
        + exact (em_obj _ _ _ _ _ _ _ _ _ _ MU GB GL (Dsg G0 A0) (Dog G0 A0)).
        + apply (em_dj_sub _ _ _ _ _ _ _ _ (Dog G0 A0)); lia.
      - assumption. }
    intros ms' (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m5 & -> &
                MU5 & WM5 & MI5 & ST5 & LB5).
    unfold CTRL_LAY_BLOCK_K in MU5, ST5. rewrite !unsigned_lit in MU5, ST5 by lia.
    replace (SP0 + -128 - 192) with LO in MU5, ST5 by lia.
    fixret.
    tac_call MU5 WM5. clear MU5 WM5 MI3.
    (* the audio: reac_braid_encode(o + 50, n, P, n, ns) when the row asks for it *)
    pose proof (row_at m5 [(o, o + LEN)] MU (em_df1 _ _ _ _ Dof)) as HR5.
    pose proof (rd_byte rsegs m5 f row 23 HR5 ltac:(lia)) as RD23. change (Z.of_nat 23) with 23 in RD23.
    pose proof (rc_u8_range row 23) as R23.
    step. step.
    rewrite (rc_u8_eqb row 23 0) by lia.
    destruct (Z.eqb_spec (rc_u8 row 23) 0) as [A0|A0]; cbv iota.
    - eapply tail2; [exact HE | eassumption ..].
    - assert (A1 : AA = 1) by (pose proof HA as HA'; unfold ubat in HA' |- *; unfold rc_u8 in A0, R23; lia).
      step. step. em_ub.
      do 6 step.
      destruct (stk_split rsegs m5 LO (SP0 + -128 - 112) (SP0 + -128) ST5 ltac:(lia)) as [STlo SThi]. clear ST5.
      eapply evt_cut.
      { eapply HBR with (ns := ns); try unfold REAC_BRAID_ENCODE_FRAME; rewrite ?unsigned_lit by lia;
          [pose proof (Hns0 A1); lia | reflexivity | exact SThi]. }
      intros ms' (m6 & -> & MU6 & WM6 & MI6 & ST6).
      specialize (MI6 MI5).
      unfold REAC_BRAID_ENCODE_FRAME in MU6, ST6. rewrite !unsigned_lit in MU6, ST6 by lia.
      fixret.
      tac_call MU6 WM6. clear MU6 WM6 MI5.
      pose proof (stk_merge rsegs m6 LO (SP0 + -128 - 112) (SP0 + -128) STlo ST6 ltac:(lia)) as ST. clear STlo ST6.
      eapply tail2; [exact HE | eassumption ..].
  Qed.

  Lemma gate2 : forall (t0 t1 t2 t3 t5 t6 x13 x14 x26 : word) (mc : word -> option byte) (j : list byte) (a1v : Z),
    EE = true ->
    (a1v = 1 /\ LL = 2) \/ (a1v = 0 /\ LL <> 2 /\ em_wok n = true) ->
    rw_cells rsegs mc (SP0 + -128) (CB 24 j :: FRS) ->
    stk rsegs mc LO (SP0 + -128) ->
    munch [(LO, SP0)] m mc -> wmono rsegs m mc -> mem_inv rsegs mc ->
    evt rsegs Qp
      (MS (mkR ra (Z_to_bv 64 (SP0 + -128)) gp tp t0 t1 t2 (Z_to_bv 64 o) s1 (zxb (nth 21 row (Z_to_bv 8 0)))
               (Z_to_bv 64 a1v) (Z_to_bv 64 0) x13 x14 a5 (Z_to_bv 64 n) (Z_to_bv 64 g)
               (Z_to_bv 64 f) s3 (Z_to_bv 64 n) s5 a5 (Z_to_bv 64 md) (Z_to_bv 64 s) (Z_to_bv 64 d) x26 s11 t3
               (Z_to_bv 64 ns) t5 t6)
          F (Z_to_bv 64 0x1509c) fc None mc (seg_rom rsegs)).
  Proof.
    intros t0 t1 t2 t3 t5 t6 x13 x14 x26 mc j a1v HE Ha1 FR ST MU WM MI.
    pose proof rng_sp as Rsp. pose proof ST as (Rlo & _ & _).
    step. step. if_true. step. step. step.
    destruct Ha1 as [(-> & L2) | (-> & L2 & W)].
    - if_false. do 3 step.
      replace (Z_to_bv 64 1492) with (Z_to_bv 64 LEN) by (unfold em_len; rewrite L2; reflexivity).
      eapply tail; eassumption.
    - if_true. step. step.
      pose proof (rc_u8_range row 21) as R21.
      rewrite (rc_u8_eqb row 21 1) by lia.
      destruct (Z.eqb_spec (rc_u8 row 21) 1); cbv iota; [|step]; do 4 step;
        rewrite (em_len_word n W);
        replace (Z_to_bv 64 (52 + 36 * n)) with (Z_to_bv 64 LEN)
          by (unfold em_len; replace (ubat row 21 =? 2) with false by (symmetry; apply Z.eqb_neq; exact L2);
              reflexivity);
        eapply tail; eassumption.
  Qed.

  Lemma gate : forall (t0 t1 t2 t3 t5 t6 x26 : word) (mc : word -> option byte) (j : list byte) (a1v : Z),
    (a1v = 1 /\ LL = 2) \/ (a1v = 0 /\ LL <> 2 /\ em_wok n = true) ->
    rw_cells rsegs mc (SP0 + -128) (CB 24 j :: FRS) ->
    stk rsegs mc LO (SP0 + -128) ->
    munch [(LO, SP0)] m mc -> wmono rsegs m mc -> mem_inv rsegs mc ->
    evt rsegs Qp
      (MS (mkR ra (Z_to_bv 64 (SP0 + -128)) gp tp t0 t1 t2 (Z_to_bv 64 o) s1 (zxb (nth 21 row (Z_to_bv 8 0)))
               (Z_to_bv 64 a1v) (Z_to_bv 64 0) (Z_to_bv 64 d) (Z_to_bv 64 s) a5 (Z_to_bv 64 n) (Z_to_bv 64 g)
               (Z_to_bv 64 f) s3 (Z_to_bv 64 n) s5 a5 (Z_to_bv 64 md) (Z_to_bv 64 s) (Z_to_bv 64 d) x26 s11 t3
               (Z_to_bv 64 ns) t5 t6)
          F (Z_to_bv 64 0x15080) fc None mc (seg_rom rsegs)).
  Proof.
    intros t0 t1 t2 t3 t5 t6 x26 mc j a1v Ha1 FR ST MU WM MI.
    pose proof rng_sp as Rsp. pose proof ST as (Rlo & _ & _).
    pose proof (bytes_at_bound _ _ _ _ HM) as BM. pose proof (bytes_at_bound _ _ _ _ HR) as BR.
    pose proof (row_at mc [] MU I) as HRc.
    pose proof (rd_byte rsegs mc f row 22 HRc ltac:(lia)) as RD22. change (Z.of_nat 22) with 22 in RD22.
    assert (WL : LL = 2 \/ em_wok n = true) by (destruct Ha1 as [(_ & H) | (_ & _ & H)]; [left | right]; exact H).
    step. step. step.
    pose proof (rc_u8_range row 22) as R22.
    rewrite (rc_u8_eqb row 22 1) by lia.
    destruct (Z.eqb_spec (rc_u8 row 22) 1) as [G1|G1]; cbn [negb]; cbv iota.
    - assert (L7 : Z.land md 7 = 0) by (change 7 with (Z.ones 3); rewrite Z.land_ones by lia; exact Hmd8).
      step. step.
      rewrite (unsigned_lit md) by lia. rewrite L7. rewrite bv_eqb_refl. cbn [negb]. cbv iota.
      pose proof (em_obj0 rsegs m mc _ _ md mb 296 MU HM ltac:(rewrite Hml; reflexivity) Dsm) as HMc.
      destruct (rc_rd4_opaque rsegs mc md mb 56 HMc ltac:(lia)) as (L4 & EL4 & RD56).
      change (Z.of_nat 56) with 56 in RD56.
      step. rewrite (em_lw_hid mb L4 EL4).
      step. pose proof (em_hid_range mb) as RH. rewrite em_eqb0 by lia.
      destruct (Z.eqb_spec (em_hid mb) 0) as [H0|H0]; cbv iota.
      + step. eapply epi0; [apply em_E_false_g; assumption | eassumption ..].
      + eapply gate2; [apply em_E_true; [exact WL | right; exact H0] | exact Ha1 | eassumption ..].
    - eapply gate2; [apply em_E_true; [exact WL | left; exact G1] | exact Ha1 | eassumption ..].
  Qed.

  Lemma chk2 : forall (t0 t1 t2 t3 t5 t6 x11 x12 x26 : word) (mc : word -> option byte) (j : list byte),
    LL <> 2 ->
    rw_cells rsegs mc (SP0 + -128) (CB 24 j :: FRS) ->
    stk rsegs mc LO (SP0 + -128) ->
    munch [(LO, SP0)] m mc -> wmono rsegs m mc -> mem_inv rsegs mc ->
    evt rsegs Qp
      (MS (mkR ra (Z_to_bv 64 (SP0 + -128)) gp tp t0 t1 t2 (Z_to_bv 64 o) s1 (zxb (nth 21 row (Z_to_bv 8 0)))
               x11 x12 (Z_to_bv 64 d) (Z_to_bv 64 s) a5 (Z_to_bv 64 n) (Z_to_bv 64 g)
               (Z_to_bv 64 f) s3 (Z_to_bv 64 n) s5 a5 (Z_to_bv 64 md) (Z_to_bv 64 s) (Z_to_bv 64 d) x26 s11 t3
               (Z_to_bv 64 ns) t5 t6)
          F (Z_to_bv 64 0x1501c) fc None mc (seg_rom rsegs)).
  Proof.
    intros t0 t1 t2 t3 t5 t6 x11 x12 x26 mc j L2 FR ST MU WM MI.
    pose proof rng_sp as Rsp. pose proof ST as (Rlo & _ & _).
    pose proof (bytes_at_bound _ _ _ _ HM) as BM.
    step. step. step. rewrite em_wok_ltu by lia.
    destruct (Z.leb_spec 2 n) as [W1|W1]; destruct (Z.leb_spec n 40) as [W2|W2]; cbn [andb negb]; cbv iota.
    - step. step. step. step. rewrite em_odd by lia.
      destruct (Z.even n) eqn:Ev; cbn [negb]; cbv iota.
      + step. rewrite rc_eqb by lia. replace (md =? 0) with false by (symmetry; apply Z.eqb_neq; exact Hmd0).
        cbv iota. step. step.
        eapply gate; [right; split; [reflexivity | split; [exact L2 |]] | eassumption ..].
        unfold em_wok. rewrite Ev. replace (2 <=? n) with true by (symmetry; apply Z.leb_le; lia).
        replace (n <=? 40) with true by (symmetry; apply Z.leb_le; lia). reflexivity.
      + eapply epi0; [apply em_E_false_w; [exact L2 | unfold em_wok; rewrite Ev; apply andb_false_r] | eassumption ..].
    - step. eapply epi0; [apply em_E_false_w; [exact L2 | unfold em_wok; replace (n <=? 40) with false
        by (symmetry; apply Z.leb_gt; lia); rewrite andb_false_r; reflexivity] | eassumption ..].
    - step. eapply epi0; [apply em_E_false_w; [exact L2 | unfold em_wok; replace (2 <=? n) with false
        by (symmetry; apply Z.leb_gt; lia); reflexivity] | eassumption ..].
    - step. eapply epi0; [apply em_E_false_w; [exact L2 | unfold em_wok; replace (2 <=? n) with false
        by (symmetry; apply Z.leb_gt; lia); reflexivity] | eassumption ..].
  Qed.

  Lemma main : forall (t0 t1 t2 t3 t5 t6 : word),
    evt rsegs Qp
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 o) (Z_to_bv 64 f) (Z_to_bv 64 md) (Z_to_bv 64 d)
               (Z_to_bv 64 s) a5 (Z_to_bv 64 n) (Z_to_bv 64 g) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3
               (Z_to_bv 64 ns) t5 t6)
          F (Z_to_bv 64 0x14f78) fc None m (seg_rom rsegs)).
  Proof.
    intros t0 t1 t2 t3 t5 t6.
    pose proof rng_sp as Rsp.
    pose proof (bytes_at_bound _ _ _ _ HM) as BM. pose proof (bytes_at_bound _ _ _ _ HR) as BR.
    pose proof (HST : stk rsegs m (bv_unsigned sp - 320) (bv_unsigned sp)) as ST. pose proof ST as (Rlo & _ & _).
    pose proof (MI0 : mem_inv rsegs m) as MI.
    pose proof (munch_refl [(bv_unsigned sp - 320, bv_unsigned sp)] m) as MU.
    pose proof (wmono_refl rsegs m) as WM.
    assert (L7 : Z.land f 7 = 0) by (change 7 with (Z.ones 3); rewrite Z.land_ones by lia; exact Hf8).
    step. carve_frame 128%nat ST. do 13 step.
    (* the UBSan checks of f: f <> 0, f mod 8 = 0 *)
    step. rewrite rc_eqb by lia. replace (f =? 0) with false by (symmetry; apply Z.eqb_neq; exact Hf0). cbv iota.
    step. step. step. step.
    rewrite (unsigned_lit f) by lia. rewrite L7. rewrite bv_eqb_refl. cbn [negb]. cbv iota.
    match goal with MU' : munch _ m ?mc |- _ =>
      pose proof (row_at mc [] MU' I) as HRc;
      pose proof (rd_byte rsegs mc f row 21 HRc ltac:(lia)) as RD21
    end.
    change (Z.of_nat 21) with 21 in RD21.
    do 8 step.
    pose proof (rc_u8_range row 21) as R21.
    rewrite (rc_u8_eqb row 21 2) by lia.
    destruct (Z.eqb_spec (rc_u8 row 21) 2) as [L2|L2]; cbv iota.
    - step. step. step. rewrite rc_eqb by lia. replace (md =? 0) with false by (symmetry; apply Z.eqb_neq; exact Hmd0).
      cbv iota. step. step.
      eapply gate; [left; split; [reflexivity | exact L2] | eassumption ..].
    - step. rewrite (rc_u8_eqb row 21 0) by lia.
      destruct (Z.eqb_spec (rc_u8 row 21) 0) as [L0|L0]; cbn [negb]; cbv iota.
      + step. step. step. step. rewrite em_wok_ltu by lia.
        destruct (Z.leb_spec 2 n) as [W1|W1]; destruct (Z.leb_spec n 40) as [W2|W2]; cbn [andb negb]; cbv iota.
        * step. step. rewrite em_odd by lia.
          destruct (Z.even n) eqn:Ev; cbn [negb]; cbv iota.
          -- step. rewrite rc_eqb by lia.
             replace (md =? 0) with false by (symmetry; apply Z.eqb_neq; exact Hmd0). cbn [negb]; cbv iota.
             eapply chk2; [exact L2 | eassumption ..].
          -- eapply epi0; [apply em_E_false_w; [exact L2 | unfold em_wok; rewrite Ev; apply andb_false_r]
                          | eassumption ..].
        * eapply epi0; [apply em_E_false_w; [exact L2 | unfold em_wok; replace (n <=? 40) with false
            by (symmetry; apply Z.leb_gt; lia); rewrite andb_false_r; reflexivity] | eassumption ..].
        * eapply epi0; [apply em_E_false_w; [exact L2 | unfold em_wok; replace (2 <=? n) with false
            by (symmetry; apply Z.leb_gt; lia); reflexivity] | eassumption ..].
        * eapply epi0; [apply em_E_false_w; [exact L2 | unfold em_wok; replace (2 <=? n) with false
            by (symmetry; apply Z.leb_gt; lia); reflexivity] | eassumption ..].
      + step. rewrite rc_eqb by lia.
        replace (md =? 0) with false by (symmetry; apply Z.eqb_neq; exact Hmd0). cbn [negb]; cbv iota.
        eapply chk2; [exact L2 | eassumption ..].
  Qed.

End Emit.

Theorem ctrl_emit_as_holds :
  memset_contract -> memcpy_contract -> ctrl_lay_block_contract -> reac_braid_encode_ns0_contract ->
  ctrl_finish_contract -> ctrl_emit_as_contract.
Proof.
  intros HMS HMC HLB HBR HFN. unfold ctrl_emit_as_contract, CTRL_EMIT_AS, CTRL_EMIT_AS_K.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m o f md d s g n ns row tb mb nb gb db sb junk.
  cbv zeta.
  intros -> -> -> -> -> -> -> ->.
  intros Hn Hns Hg HS16 HST Dsf Dst Dsm Dsn Dsd Dss Dsg Hf0 Hf8 Hf24 Hrl HR Hk Hc HL HG HA Hao Htm Hc2 HLA
    Hmd0 Hmd8 Hmd296 Hml HM Hnm Ho Ho1492 HEo Hdb HD Hsb HSb Hgb Hns0 MI0.
  eapply main; eassumption.
Qed.
