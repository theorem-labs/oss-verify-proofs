(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP MonadX StoreFast.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.MallocU Require Import RMallocRep RMallocTree RMalloc_iface.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Spec Require Import Prelim STree Malloc Monad Stdio SjModel PjModel Target Prog PjImpl.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Sj Require Import SjS1Out SjAlloc SjTape SjTapeList SjTapeTile SjPjSer.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.U Require Import Layout Exit Printf_wfile Sj_iface Sj_kit Sj_new Sj_h_kit F_memcpy F_memmove_t2.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.U Require Import Pj_defs Pj_kit Pj_copy Pj_grow Pj_stmts Pj_ser_defs Pj_ser_kit Pj_ser_calls Pj_ser_loop_defs.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Lib Require SFModel.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac solve_store ::= first [ pj_solve_store0 | pj_store_wr ].
Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof alloc_ceiling_range as CEIL_RANGE__); std_lia__].

Local Ltac pj_st_eq_leaf ::=
  lazymatch goal with
  | |- Z_to_bv 64 _ = Z_to_bv 64 _ => first [reflexivity | f_equal; cbn [length]; lia]
  | |- _ => reflexivity
  end.

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.
Section Proofs.
  Hypothesis HM : rmalloc_stmt.
  Hypothesis HF : rfree_stmt.
  Variable E : senv.
  Variable Q : @chst bptr -> PState -> machine_state -> Prop.
  Variable D : nat.
  Variable f : nat.
  Hypothesis OK : senv_ok E.
  Hypothesis DISP : disp_stmt E Q D (S f).
  Hypothesis PKEY : key_stmt.

  Notation REST := (rest_ok (e_T E) (e_S E) (e_sn E)).

  Lemma head_mid : forall (d0 : nat) (ks : list bool) (i i2 c c2 : Z) (isobj : list byte) (st : sbst) (s : PState) (m : mem)
      (F : bvmap 5 word) (fc : bv 32) (e64 e72 e80 spill : word)
      (xs3 xs8 xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 : word),
    e_j E - i <= Z.of_nat (S f) -> (d0 + length ks = D)%nat -> (length ks <= 15)%nat -> kinds_rel ks isobj ->
    item_ok E ks d0 i i2 c c2 -> REST d0 ks i2 c2 (e_j E) (e_c' E) -> 1 <= i -> 0 <= c ->
    SERM E e64 e72 e80 spill isobj st s m -> frm0 fc -> sb_size st <= 41 * (i - 1) + 6 * c + 3 ->
    evt usegs (sgoal E Q (sb_ch st) s)
        (LST E 0x3dc6c i (Z.of_nat (length ks)) xs3 xs8 xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 F fc m).
  Proof using HM HF OK DISP PKEY.
    intros d0 ks i i2 c c2 isobj st s m F fc e64 e72 e80 spill xs3 xs8 xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6
           HF0 HD HL KR HIT HR HI HC HSM FRM ACC.
    pose proof OK as [WF _ _ _ _ _ _ _ _ _ _ _ _ [J1 J2] [CC1 CC2] _].
    pose proof WF as ((N1 & N2) & SN & _).
    pose proof (senv_out E OK) as OUTB.
    pose proof (rest_ok_le _ _ _ _ _ _ _ _ _ HR) as (LEJ & LEC & _).
    assert (KB : exists k : bool, nth_error isobj (Z.to_nat (Z.of_nat (length ks))) = Some (kbyte k)
                 /\ (k = false -> elemS (e_T E) (e_S E) (e_sn E) ck_any d0 i i2 c c2)
                 /\ (k = true -> fieldS (e_T E) (e_S E) (e_sn E) (elemS (e_T E) (e_S E) (e_sn E) ck_any d0) i i2 c c2)).
    { rewrite Nat2Z.id. destruct ks as [|k ks'].
      - exists false. split; [exact (proj1 KR)|]. split; [intros _; exact HIT| discriminate].
      - exists k. cbn [length]. replace (S (length ks')) with (length ks' + 1)%nat by lia.
        split; [eapply kinds_rel_top; exact KR|]. cbn [item_ok] in HIT. unfold itemS in HIT.
        destruct k; (split; [intros Hk; first [discriminate Hk | exact HIT]| intros Hk; first [discriminate Hk | exact HIT]]). }
    destruct KB as (k & KN & KF & KT).
    destruct st as [buf size cap blk fuel]. cbn [sb_size] in *.
    ser_env OK. ser_open HSM OK.
    pose proof (u8arr_read usegs _ _ isobj (Z.of_nat (length ks)) (kbyte k) _ FRI KN ltac:(lia) eq_refl) as RDK.
    assert (KB1 : 0 <= (if k then 1 else 0) <= 1) by (destruct k; lia).

    gfall. zstep. zstep. unfold kbyte. pjnorm. gfall. zstep.

    step. step. step. step. zstep. zstep. hstep. zstep. hstep. zstep. hstep.

    step.
    ser_close HSMC OK.
    destruct k; cbn [Z.b2z]; pjnorm.
    -
      if_cases K; zify_cond K; [exfalso; pjnorm_in K; lia| clear K].
      destruct (KT eq_refl) as (c1 & (l & HTW & HS & EC1) & HEL).
      pose proof (elemS_lt _ _ _ _ _ _ _ _ _ HEL) as LT. pose proof (elemS_cur _ _ _ _ _ _ _ _ _ HEL) as (CUR & _).
      pose proof HS as (_ & L0 & _).
      remember (41 * (i - 1) + 6 * c + 3) as A eqn:EA.
      eapply evt_eq; [| eapply (PKEY E Q spill isobj (mkSb buf size cap blk fuel) s _ F fc i c l (Z.of_nat (length ks)) A)];
        [pj_st_eq| exact OK| exact HSMC| exact FRM| lia| exact HTW| exact HS| cbn [sb_size]; lia| lia|].
      unfold disp_K. intros st' s' m' F' fc' spill' ys8 yra yt0 yt1 yt2 ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt5 yt6 HSM' FRM' ACC'.
      eapply (DISP d0 ks (i + 1) i2 c1 c2 isobj st'); try eassumption; lia.
    -
      if_cases K; zify_cond K; [clear K| exfalso; pjnorm_in K; lia].
      ser_open HSMC OK. step. step. ser_close HSMD OK.
      eapply evt_eq; [| eapply (DISP d0 ks i i2 c c2 isobj (mkSb buf size cap blk fuel))];
        [pj_st_eq| exact HF0| exact HD| exact HL| exact KR| exact (KF eq_refl)| exact HR| lia| lia| exact HSMD| exact FRM| cbn [sb_size]; lia].
  Qed.

  Lemma item_ok_lt : forall ks d0 i i2 c c2, item_ok E ks d0 i i2 c c2 -> i < i2.
  Proof. intros [|k ks] d0 i i2 c c2 H; cbn [item_ok] in H; [eapply elemS_lt; exact H| eapply itemS_lt; exact H]. Qed.

  Theorem head_proof : head_stmt E Q D (S f).
  Proof using HM HF OK DISP PKEY.
    unfold head_stmt.
    intros d0 ks i i2 c c2 after isobj st s m F fc e64 e72 e80 spill xs3 xs8 xra xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6
           HF0 HD HL KR HIT HR HAF HI HC HSM FRM ACC.
    pose proof OK as [_ _ _ _ _ _ _ _ _ _ _ _ _ [J1 J2] [CC1 CC2] _].
    pose proof (senv_out E OK) as OUTB.
    pose proof (rest_ok_le _ _ _ _ _ _ _ _ _ HR) as (LEJ & LEC & _).
    pose proof (item_ok_lt _ _ _ _ _ _ HIT) as LT.
    assert (CUR : c <= c2).
    { destruct ks as [|k ks']; cbn [item_ok] in HIT.
      - pose proof (elemS_cur _ _ _ _ _ _ _ _ _ HIT) as (X & _). exact X.
      - pose proof (ok_wf E OK) as (_ & SN & _). pose proof (itemS_cur _ _ _ _ _ _ _ _ _ HIT) as (X & _). exact X. }
    pose proof HSM as HSM0.
    destruct st as [buf size cap blk fuel]. cbn [sb_size] in *.
    ser_env OK.
    destruct after; cbn [Z.b2z] in *.
    2:{
        zstep. step. if_cases K; zify_cond K; [clear K| exfalso; cbn in K; lia].
        eapply (head_mid d0 ks i i2 c c2 isobj (mkSb buf size cap blk fuel)); try eassumption; cbn [sb_size]; lia. }
    assert (TAIL : forall (st5 : sbst) (s5 : PState) (m5 : mem) (yra yt0 yt1 yt2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt5 yt6 : word),
      SERM E e64 e72 e80 spill isobj st5 s5 m5 -> sb_size st5 = size -> size + 1 <= sb_cap st5 ->
      evt usegs (sgoal E Q (sb_ch st5) s5)
          (LST E 0x3dc2c i (Z.of_nat (length ks)) xs3 xs8 yra yt0 yt1 yt2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt5 yt6 F fc m5)).
    { intros st5 s5 m5 yra yt0 yt1 yt2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt5 yt6 HSM5 ESZ ROOM.
      destruct st5 as [buf5 size5 cap5 blk5 fuel5]. cbn [sb_size sb_cap] in ESZ, ROOM. subst size5.
      ser_open HSM5 OK.

      step. step. zstep. zstep. step. gfall.

      zstep. zstep. zstep. unz. change (Z.lxor 1 0) with 1%Z. gfall. gfall. step. step. pj_store_done.
      ser_close HSM6 OK.
      eapply (head_mid d0 ks i i2 c c2 isobj (mkSb buf5 (size + 1) cap5 blk5 fuel5)); try eassumption. cbn [sb_size]. lia. }

    - zstep. step. if_cases K; zify_cond K; [exfalso; cbn in K; lia| clear K].
      ser_open HSM OK.

      step. step. zstep. step.
      if_cases K; zify_cond K.
      + pjnorm_in K. ser_close HSM2 OK. eapply TAIL; [exact HSM2| reflexivity| cbn [sb_cap]; lia].
      + pjnorm_in K.

        zstep. pjnorm. step. step.
        ser_close HSM3 OK.
        eapply (ser_grow HM HF) with (z := 2 * cap) (rpc := 0x3dc2c); [exact OK| exact HSM3| | lia| reflexivity|].
        { eapply (ser_req_ok2 E _ _ _ _ _ _ _ _ OK HSM3). cbn [sb_cap]. lia. }
        intros s' m' b' NEW yt0 yt1 yt2 za0 za1 za2 za3 za4 za5 za6 za7 yt3 yt4 yt5 yt6 HSM4.
        eapply TAIL; [exact HSM4| reflexivity| unfold sb_grown; cbn [sb_cap]; lia].
  Qed.

End Proofs.
End WithCeiling0.
