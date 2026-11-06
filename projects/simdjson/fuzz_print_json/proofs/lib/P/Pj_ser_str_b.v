(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.simdjson.fuzz_print_json.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP MonadX StoreFast.
From OSSVerify.Proofs.simdjson.fuzz_print_json.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OSSVerify.Proofs.simdjson.fuzz_print_json.lib.MallocP Require Import RMallocRep RMallocTree RMalloc_iface.
From OSSVerify.Proofs.simdjson.fuzz_print_json.lib.Spec Require Import Prelim STree Malloc Monad Stdio SjModel PjModel Target Prog PjImpl.
From OSSVerify.Proofs.simdjson.fuzz_print_json.lib.Sj Require Import SjS1Out SjAlloc SjTape SjTapeList SjTapeTile SjPjSer.
From OSSVerify.Proofs.simdjson.fuzz_print_json.lib.P Require Import Layout Exit Printf_wfile Sj_iface Sj_kit Sj_new Sj_h_kit F_memcpy F_memmove_t2.
From OSSVerify.Proofs.simdjson.fuzz_print_json.lib.P Require Import Pj_defs Pj_kit Pj_grow Pj_ser_defs Pj_ser_kit Pj_ser_calls Pj_ser_str_a.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
From OSSVerify.Proofs.simdjson.fuzz_print_json.lib.Lib Require Import Ceiling.
From OSSVerify.Proofs.simdjson.fuzz_print_json.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac solve_store ::= first [ pj_solve_store0 | pj_store_wr ].
Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof alloc_ceiling_range as CEIL_RANGE__); std_lia__].

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.
Section Proofs.
  Hypothesis HM : rmalloc_stmt.
  Hypothesis HF : rfree_stmt.

  Variable E : senv.
  Variable Q : @chst bptr -> PState -> machine_state -> Prop.
  Variable isobj : list byte.
  Variables (i dp c l A : Z).
  Variable F : bvmap 5 word.
  Variable fc : bv 32.
  Hypothesis FRM : frm0 fc.
  Hypothesis OK : senv_ok E.
  Hypothesis HSTR : str_at (e_S E) (e_sn E) c l.
  Hypothesis BUD : A + (2 + 6 * l) <= PJ_OUTMAX (e_len E).
  Hypothesis HK : av_K E Q (Z_to_bv 64 PJ_ESC_TAB) isobj 0x3e5e0 i dp (A + (2 + 6 * l)).

  Notation ESC := (Z_to_bv 64 PJ_ESC_TAB).
  Notation SPILL := (Z_to_bv 64 c).
  Notation DATA := (e_SBUF E + c + 4).

  Notation str_close := (Pj_ser_str_a.str_close HM HF E Q isobj i dp c l A F fc FRM OK HSTR BUD HK).
  Notation esc_head := (Pj_ser_str_a.esc_head HM HF E Q isobj i dp c l A F fc FRM OK HSTR BUD HK).

  Lemma str_copy : forall (k : Z) (st : sbst) (s : PState) (m : mem)
      (xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs5 xs8 xt3 xt4 xt5 xt6 : word),
    0 <= k <= l ->
    SERM E ESC SPILL isobj st s m -> sb_size st <= A + 1 ->
    evt psegs (sgoal E Q (sb_ch st) s)
        (SST E 0x3e004 xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 i) (Z_to_bv 64 DATA) (Z_to_bv 64 k) xs5
             (Z_to_bv 64 (e_q E + -200)) (Z_to_bv 64 l) xs8 (Z_to_bv 64 dp) (Z_to_bv 64 (e_SBUF E)) (Z_to_bv 64 34) xt3 xt4 xt5 xt6 F fc m).
  Proof using HM HF OK HSTR BUD HK FRM.
    intros k st s m xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs5 xs8 xt3 xt4 xt5 xt6 HKL HSM ACC.
    destruct st as [buf size cap blk fuel]. cbn [sb_size] in *.
    ser_env OK.
    pose proof HSTR as (C0 & L0 & CL & _).
    pose proof (ser_ranges _ _ _ _ _ _ _ OK HSM) as (_ & _ & SB0 & SB1).

    assert (FIN : forall (st5 : sbst) (s5 : PState) (m5 : mem) (yra yt0 yt1 yt2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt5 yt6 : word),
      SERM E ESC SPILL isobj st5 s5 m5 -> sb_size st5 = size -> size + k <= sb_cap st5 ->
      evt psegs (sgoal E Q (sb_ch st5) s5)
          (SST E 0x3e048 yra yt0 yt1 yt2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 (Z_to_bv 64 i) (Z_to_bv 64 DATA) (Z_to_bv 64 k) (Z_to_bv 64 (size + k))
               (Z_to_bv 64 (e_q E + -200)) (Z_to_bv 64 l) xs8 (Z_to_bv 64 dp) (Z_to_bv 64 (e_SBUF E)) (Z_to_bv 64 34) yt3 yt4 yt5 yt6 F fc m5)).
    { intros st5 s5 m5 yra yt0 yt1 yt2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt5 yt6 HSM5 ESZ ROOM.
      destruct st5 as [buf5 size5 cap5 blk5 fuel5]. cbn [sb_size sb_cap] in ESZ, ROOM. subst size5.
      ser_open HSM5 OK.

      step. step.
      if_cases K; zify_cond K.
      - pjnorm_in K. ser_close HSM6 OK.
        eapply (str_close (mkSb buf5 (size + k) cap5 blk5 fuel5)); [exact HSM6| cbn [sb_size]; lia].
      - pjnorm_in K.

        zstep. step. zstep. zstep. zstep. zstep. step.
        ser_close HSM6 OK.
        replace (Z_to_bv 64 (e_SBUF E + 4 + (k + c))) with (Z_to_bv 64 (DATA + k)) by (f_equal; lia).
        replace (Z_to_bv 64 (e_SBUF E + 4 + (l + c))) with (Z_to_bv 64 (DATA + l)) by (f_equal; lia).
        eapply (esc_head (Z.to_nat (l - k)) k (mkSb buf5 (size + k) cap5 blk5 fuel5)); [lia| lia| exact HSM6| cbn [sb_size]; lia]. }

    assert (TAIL : forall (st5 : sbst) (s5 : PState) (m5 : mem) (yra yt0 yt1 yt2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt5 yt6 : word),
      SERM E ESC SPILL isobj st5 s5 m5 -> sb_size st5 = size -> size + k <= sb_cap st5 ->
      evt psegs (sgoal E Q (sb_ch st5) s5)
          (SST E 0x3e02c yra yt0 yt1 yt2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 (Z_to_bv 64 i) (Z_to_bv 64 DATA) (Z_to_bv 64 k) (Z_to_bv 64 (size + k))
               (Z_to_bv 64 (e_q E + -200)) (Z_to_bv 64 l) xs8 (Z_to_bv 64 dp) (Z_to_bv 64 (e_SBUF E)) (Z_to_bv 64 34) yt3 yt4 yt5 yt6 F fc m5)).
    { intros st5 s5 m5 yra yt0 yt1 yt2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt5 yt6 HSM5 ESZ ROOM.
      pose proof HSM5 as HSM50. pose proof (ser_sep _ _ _ _ _ _ _ OK HSM5) as (_ & SEP).
      destruct st5 as [buf5 size5 cap5 blk5 fuel5]. cbn [sb_size sb_cap sb_buf] in ESZ, ROOM, SEP. subst size5.
      ser_open HSM5 OK.

      step. if_cases KZ; zify_cond KZ.
      - pjnorm_in KZ. eapply FIN; [exact HSM50| reflexivity| cbn [sb_cap]; lia].
      - pjnorm_in KZ.

        step. step. zstep. step. step. step.
        ser_close HSM6 OK.
        eapply (ser_copy E Q ESC SPILL isobj (mkSb buf5 size cap5 blk5 fuel5) s5 _ MEMMOVE_T2 DATA k 0x3e048);
          [right; reflexivity| exact OK| exact HSM6
          | replace DATA with (e_SBUF E + (c + 4)) by lia; eapply (sbuf_src E _ _ _ _ _ _ (c + 4) k OK HSM6); lia
          | lia| cbn [sb_size sb_cap]; lia| lia| lia| cbn [sb_buf sb_size]; lia| lia| reflexivity|].
        intros m7 zt0 zt1 zt2 za1 za2 za3 za4 za5 za6 za7 zt3 zt4 zt5 zt6 HSM7.
        eapply FIN; [exact HSM7| reflexivity| cbn [sb_cap]; lia]. }
    ser_open HSM OK.

    step. step. zstep. step.
    if_cases K; zify_cond K.
    - pjnorm_in K. ser_close HSM2 OK. eapply TAIL; [exact HSM2| reflexivity| cbn [sb_cap]; lia].
    - pjnorm_in K.

      zstep. pjnorm. step. step.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (GROWN : forall (z : Z) (ya0 : word), z = Z.max (2 * cap) (size + k) ->
        evt psegs (sgoal E Q (sb_ch (mkSb buf size cap blk fuel)) s)
          (SST E 0x3e024 xra xt0 xt1 xt2 ya0 (Z_to_bv 64 z) xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 i) (Z_to_bv 64 DATA) (Z_to_bv 64 k) (Z_to_bv 64 (size + k))
               (Z_to_bv 64 (e_q E + -200)) (Z_to_bv 64 l) xs8 (Z_to_bv 64 dp) (Z_to_bv 64 (e_SBUF E)) (Z_to_bv 64 34) xt3 xt4 xt5 xt6 F fc mm)) end.
      { intros z ya0 EZ.

        step. step.
        ser_close HSM3 OK.
        eapply (ser_grow HM HF) with (z := z) (rpc := 0x3e02c); [exact OK| exact HSM3| | lia| reflexivity|].
        { rewrite EZ. eapply (ser_req_ok E _ _ _ _ _ _ (size + k) OK HSM3); cbn [sb_cap]; lia. }
        intros s' m' b' NEW yt0 yt1 yt2 za0 za1 za2 za3 za4 za5 za6 za7 yt3 yt4 yt5 yt6 HSM4.
        eapply TAIL; [exact HSM4| reflexivity|].
        unfold sb_grown. cbn [sb_cap]. rewrite EZ. lia. }
      if_cases K2; zify_cond K2.
      + pjnorm_in K2. eapply (GROWN (size + k)). lia.
      + pjnorm_in K2.   step. eapply (GROWN (2 * cap)). lia.
  Qed.

  Definition tail_stmt (f : nat) : Prop :=
    forall (k : Z) (st : sbst) (s : PState) (m : mem)
           (xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs5 xt3 xt4 xt5 xt6 : word),
      l - k <= Z.of_nat f -> 0 <= k < l ->
      SERM E ESC SPILL isobj st s m -> sb_size st <= A + 1 ->
      evt psegs (sgoal E Q (sb_ch st) s)
          (SST E 0x3dfe4 xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 i) (Z_to_bv 64 DATA) (Z_to_bv 64 k) xs5
               (Z_to_bv 64 (e_q E + -200)) (Z_to_bv 64 l) (Z_to_bv 64 PJ_NE_TAB) (Z_to_bv 64 dp) (Z_to_bv 64 (e_SBUF E)) (Z_to_bv 64 34) xt3 xt4 xt5 xt6 F fc m).

  Lemma str_tail_loop : forall f, tail_stmt f.
  Proof using HM HF OK HSTR BUD HK FRM.
    induction f as [|f IH]; unfold tail_stmt;
      intros k st s m xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs5 xt3 xt4 xt5 xt6 HF0 HKL HSM ACC; [lia|].
    pose proof HSTR as (C0 & L0 & CL & _).
    pose proof (ser_ranges _ _ _ _ _ _ _ OK HSM) as (_ & _ & SB0 & SB1).
    pose proof (S_range E (c + 4 + k) OK) as BR. set (b := e_S E (c + 4 + k)) in *.
    pose proof (ne_val_range b) as VR.
    pose proof HSM as HSM0.
    destruct st as [buf size cap blk fuel]. cbn [sb_size] in *.
    ser_env OK. ser_open HSM OK. unfold PJ_NE_TAB in *.
    pose proof (sbuf_read_mu E _ _ _ _ (c + 4 + k) OK HREF MU WM ltac:(lia)) as RD. fold b in RD.
    replace (e_SBUF E + (c + 4 + k)) with (DATA + k) in RD by lia.
    pose proof (ne_read m b MI ltac:(lia)) as RT. unfold PJ_NE_TAB in RT.

    zstep. zstep. pjnorm. zstep. zstep. pjnorm. step.
    if_cases K1; zify_cond K1.
    - eapply (str_copy k (mkSb buf size cap blk fuel)); [lia| exact HSM0| cbn [sb_size]; lia].
    -
      zstep. step. if_cases K2; zify_cond K2.
      + pjnorm_in K2. eapply (IH (k + 1) (mkSb buf size cap blk fuel)); [lia| lia| exact HSM0| cbn [sb_size]; lia].
      + pjnorm_in K2.   step.
        eapply (str_copy l (mkSb buf size cap blk fuel)); [lia| exact HSM0| cbn [sb_size]; lia].
  Qed.

  Lemma str_tail : forall (k : Z) (st : sbst) (s : PState) (m : mem)
      (xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs5 xt3 xt4 xt5 xt6 : word),
    0 <= k <= l ->
    SERM E ESC SPILL isobj st s m -> sb_size st <= A + 1 ->
    evt psegs (sgoal E Q (sb_ch st) s)
        (SST E 0x3dfe0 xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 i) (Z_to_bv 64 DATA) (Z_to_bv 64 k) xs5
             (Z_to_bv 64 (e_q E + -200)) (Z_to_bv 64 l) (Z_to_bv 64 PJ_NE_TAB) (Z_to_bv 64 dp) (Z_to_bv 64 (e_SBUF E)) (Z_to_bv 64 34) xt3 xt4 xt5 xt6 F fc m).
  Proof using HM HF OK HSTR BUD HK FRM.
    intros k st s m xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs5 xt3 xt4 xt5 xt6 HKL HSM ACC.
    pose proof HSTR as (C0 & L0 & CL & _).
    pose proof (ser_ranges _ _ _ _ _ _ _ OK HSM) as (_ & _ & SB0 & SB1).

    step. if_cases K; zify_cond K.
    - pjnorm_in K. eapply str_copy; [lia| exact HSM| exact ACC].
    - pjnorm_in K. eapply (str_tail_loop (Z.to_nat (l - k))); [lia| lia| exact HSM| exact ACC].
  Qed.

  Definition scan8_stmt (f : nat) : Prop :=
    forall (r k8 : Z) (st : sbst) (s : PState) (m : mem)
           (xra xt0 xt1 xt2 xa2 xa3 xa4 xa5 xa6 xa7 xs5 xt3 xt4 xt5 xt6 : word),
      l - 8 * r < Z.of_nat f -> 0 <= r -> 8 * r <= l -> 0 <= k8 <= l ->
      SERM E ESC SPILL isobj st s m -> sb_size st <= A + 1 ->
      evt psegs (sgoal E Q (sb_ch st) s)
          (SST E 0x3df4c xra xt0 xt1 xt2 (Z_to_bv 64 (e_SBUF E + c + 5)) (Z_to_bv 64 (4 + 8 * r)) xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 i) (Z_to_bv 64 DATA) (Z_to_bv 64 k8) xs5
               (Z_to_bv 64 (e_q E + -200)) (Z_to_bv 64 l) (Z_to_bv 64 PJ_NE_TAB) (Z_to_bv 64 dp) (Z_to_bv 64 (e_SBUF E)) (Z_to_bv 64 34) xt3 xt4 xt5 xt6 F fc m).

  Lemma str_scan8 : forall f, scan8_stmt f.
  Proof using HM HF OK HSTR BUD HK FRM.
    induction f as [|f IH]; unfold scan8_stmt;
      intros r k8 st s m xra xt0 xt1 xt2 xa2 xa3 xa4 xa5 xa6 xa7 xs5 xt3 xt4 xt5 xt6 HF0 HR0 HRL HK8 HSM ACC; [lia|].
    pose proof HSTR as (C0 & L0 & CL & _).
    pose proof (ser_ranges _ _ _ _ _ _ _ OK HSM) as (_ & _ & SB0 & SB1).
    pose proof HSM as HSM0.
    destruct st as [buf size cap blk fuel]. cbn [sb_size] in *.

    zstep. step. if_cases K; zify_cond K.
    - pjnorm_in K. eapply (str_tail k8 (mkSb buf size cap blk fuel)); [lia| exact HSM0| cbn [sb_size]; lia].
    - pjnorm_in K.
      ser_env OK. ser_open HSM OK. unfold PJ_NE_TAB in *.
    pose proof (S_range E (c + 4 + 8 * r + 0) OK) as BR0. set (b0 := e_S E (c + 4 + 8 * r + 0)) in *. pose proof (ne_val_range b0) as VR0.
    pose proof (sbuf_read_mu E _ _ _ _ (c + 4 + 8 * r + 0) OK HREF MU WM ltac:(lia)) as RD0. fold b0 in RD0.
    pose proof (ne_read m b0 MI ltac:(lia)) as RT0. unfold PJ_NE_TAB in RT0.
    pose proof (S_range E (c + 4 + 8 * r + 1) OK) as BR1. set (b1 := e_S E (c + 4 + 8 * r + 1)) in *. pose proof (ne_val_range b1) as VR1.
    pose proof (sbuf_read_mu E _ _ _ _ (c + 4 + 8 * r + 1) OK HREF MU WM ltac:(lia)) as RD1. fold b1 in RD1.
    pose proof (ne_read m b1 MI ltac:(lia)) as RT1. unfold PJ_NE_TAB in RT1.
    pose proof (S_range E (c + 4 + 8 * r + 2) OK) as BR2. set (b2 := e_S E (c + 4 + 8 * r + 2)) in *. pose proof (ne_val_range b2) as VR2.
    pose proof (sbuf_read_mu E _ _ _ _ (c + 4 + 8 * r + 2) OK HREF MU WM ltac:(lia)) as RD2. fold b2 in RD2.
    pose proof (ne_read m b2 MI ltac:(lia)) as RT2. unfold PJ_NE_TAB in RT2.
    pose proof (S_range E (c + 4 + 8 * r + 3) OK) as BR3. set (b3 := e_S E (c + 4 + 8 * r + 3)) in *. pose proof (ne_val_range b3) as VR3.
    pose proof (sbuf_read_mu E _ _ _ _ (c + 4 + 8 * r + 3) OK HREF MU WM ltac:(lia)) as RD3. fold b3 in RD3.
    pose proof (ne_read m b3 MI ltac:(lia)) as RT3. unfold PJ_NE_TAB in RT3.
    pose proof (S_range E (c + 4 + 8 * r + 4) OK) as BR4. set (b4 := e_S E (c + 4 + 8 * r + 4)) in *. pose proof (ne_val_range b4) as VR4.
    pose proof (sbuf_read_mu E _ _ _ _ (c + 4 + 8 * r + 4) OK HREF MU WM ltac:(lia)) as RD4. fold b4 in RD4.
    pose proof (ne_read m b4 MI ltac:(lia)) as RT4. unfold PJ_NE_TAB in RT4.
    pose proof (S_range E (c + 4 + 8 * r + 5) OK) as BR5. set (b5 := e_S E (c + 4 + 8 * r + 5)) in *. pose proof (ne_val_range b5) as VR5.
    pose proof (sbuf_read_mu E _ _ _ _ (c + 4 + 8 * r + 5) OK HREF MU WM ltac:(lia)) as RD5. fold b5 in RD5.
    pose proof (ne_read m b5 MI ltac:(lia)) as RT5. unfold PJ_NE_TAB in RT5.
    pose proof (S_range E (c + 4 + 8 * r + 6) OK) as BR6. set (b6 := e_S E (c + 4 + 8 * r + 6)) in *. pose proof (ne_val_range b6) as VR6.
    pose proof (sbuf_read_mu E _ _ _ _ (c + 4 + 8 * r + 6) OK HREF MU WM ltac:(lia)) as RD6. fold b6 in RD6.
    pose proof (ne_read m b6 MI ltac:(lia)) as RT6. unfold PJ_NE_TAB in RT6.
    pose proof (S_range E (c + 4 + 8 * r + 7) OK) as BR7. set (b7 := e_S E (c + 4 + 8 * r + 7)) in *. pose proof (ne_val_range b7) as VR7.
    pose proof (sbuf_read_mu E _ _ _ _ (c + 4 + 8 * r + 7) OK HREF MU WM ltac:(lia)) as RD7. fold b7 in RD7.
    pose proof (ne_read m b7 MI ltac:(lia)) as RT7. unfold PJ_NE_TAB in RT7.

      zstep. zstep. zstep. zstep. zstep. pjnorm.

      zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. pjnorm.

      step. step. zstep. zstep. zstep. zstep. pjnorm.

      zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. pjnorm.

      step. step. step. step. step. zstep. step.
      if_cases K1; zify_cond K1.
      + replace (Z_to_bv 64 (4 + 8 * r + 8)) with (Z_to_bv 64 (4 + 8 * (r + 1))) by (f_equal; lia).
        eapply (IH (r + 1) k8 (mkSb buf size cap blk fuel)); [lia| lia| lia| lia| exact HSM0| cbn [sb_size]; lia].
      +
        zstep.
        eapply evt_eq; [| eapply (str_tail (8 * r) (mkSb buf size cap blk fuel))]; [pj_st_eq| lia| exact HSM0| cbn [sb_size]; lia].
  Qed.

End Proofs.
End WithCeiling0.
