(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP MonadX StoreFast.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.MallocP Require Import RMallocRep RMallocTree RMalloc_iface.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.Spec Require Import Prelim STree Malloc Monad Stdio StrFun SjModel AtpModel ElModel Target Prog AtpImpl.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.Sj Require Import SjTape SjTapeList.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.P Require Import Layout Exit Printf_wfile Sj_iface Sj_kit Sj_new Sj_new_t2 Sj_h_kit F_memcmp Atp_defs Atp_h_defs Atp_objl El_defs.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.Lib Require Import Ceiling.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof alloc_ceiling_range as CEIL_RANGE__); std_lia__].

Lemma a_shl8_shr8 : forall x, (0 <= x)%Z -> Z.shiftr (Z.shiftl x 8 mod 18446744073709551616) 8 = tval x.
Proof.
  intros x H. unfold tval. rewrite Z.shiftl_mul_pow2 by lia. rewrite Z.shiftr_div_pow2 by lia.
  change 18446744073709551616 with (2^56 * 2^8)%Z. rewrite Zmult_mod_distr_r.
  rewrite Z.div_mul by lia. reflexivity.
Qed.

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Definition cmp_post (ra : word) (sp : Z) (gp t0 t1 t2 s0 s1 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (r a1' a2' a3' a4' : word) (m' : mem),
    ms' = MS (mkR ra (Z_to_bv 64 sp) gp (Z_to_bv 64 RATP) t0 t1 t2 s0 s1 r a1' a2' a3' a4' a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom psegs)
    /\ munch [(sp - 48, sp)] m m' /\ wmono psegs m m' /\ mem_inv psegs m' /\ stk psegs m' lo sp.

Definition cmp_stmt (centry : Z) : Prop :=
  forall (ra gp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem)
         (sp lo p q : Z) (bp bq : list byte),
    length bq = length bp -> 0 <= p -> 0 <= q -> p + Z.of_nat (length bp) < 2 ^ 63 -> q + Z.of_nat (length bp) < 2 ^ 63 ->
    (length bp = 0%nat \/ (p + Z.of_nat (length bp) <= sp - 48 /\ q + Z.of_nat (length bp) <= sp - 48)) ->
    bytes_at psegs m p bp -> bytes_at psegs m q bq -> mem_inv psegs m -> stk psegs m lo sp -> lo + 48 <= sp -> sp < 2 ^ 63 -> sp mod 16 = 0 ->
    evt psegs (cmp_post ra sp gp t0 t1 t2 s0 s1 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc lo m)
      (MS (mkR ra (Z_to_bv 64 sp) gp (Z_to_bv 64 RATP) t0 t1 t2 s0 s1 (Z_to_bv 64 p) (Z_to_bv 64 q) (Z_to_bv 64 (Z.of_nat (length bp))) a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 centry) fc None m (seg_rom psegs)).

Lemma bcmp_cmp : cmp_stmt bcmp_entry.
Proof.
  unfold cmp_stmt. intros until bq. intros LEN P0 Q0 PH QH _ BP BQ MI ST _ _ _.
  eapply evt_cut; [eapply (bcmp_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m p q bp bq); try reflexivity; assumption|].
  cbv beta. intros ms' (r & a1' & a2' & a3' & a4' & -> & _).
  apply evt_done. exists r, a1', a2', a3', a4', m. split; [reflexivity|].
  split; [apply munch_refl|]. split; [apply wmono_refl|]. split; [exact MI| exact ST].
Qed.

Definition key_row (base centry : Z) : Prop :=
  (base = EL_ATKEY /\ centry = bcmp_entry) \/ (base = EL_ATKEY2 /\ centry = bcmp_entry) \/ (base = EL_ATKEYCI /\ centry = EL_STRNCASECMP).

Notation ae_T E := (Tf (ae_tws E)).
Notation ae_S E := (Tf (ae_sbs E)).
Notation ae_n E := (Z.of_nat (length (ae_tws E))).
Notation ae_sn E := (Z.of_nat (length (ae_sbs E))).

Section Key.
  Variable E : aenv.
  Hypothesis OK : aenv_ok E.
  Variables base centry : Z.
  Hypothesis ROW : key_row base centry.
  Hypothesis CMP : cmp_stmt centry.

  Definition kbytes : list byte := map (Z_to_bv 8) (ae_p1 E).
  Notation L := (zlength (ae_p1 E)).

  Definition kinv (mL : mem) (spv lo : Z) (m : mem) : Prop :=
    mem_inv psegs m /\ stk psegs m lo spv /\ munch [(spv - 48, spv)] mL m /\ wmono psegs mL m.

  Lemma kinv_agree : forall mL spv lo m, kinv mL spv lo m -> agree_on (fun a => outside [(spv - 48, spv)] a) mL m.
  Proof. intros mL spv lo m (_ & _ & MU & WM). exact (agree_on_of_munch _ _ _ MU WM). Qed.

  Ltac zlits_in H := repeat match type of H with context [Z.add ?a ?b] => is_Zlit a; is_Zlit b; let v := eval vm_compute in (Z.add a b) in change (Z.add a b) with v in H end.
  Ltac zlits := repeat match goal with |- context [Z.add ?a ?b] => is_Zlit a; is_Zlit b; let v := eval vm_compute in (Z.add a b) in change (Z.add a b) with v end.

  #[local] Set Default Goal Selector "all".

  Lemma key_tail : forall (K : machine_state -> Prop) (m : mem) (F : bvmap 5 word) (fc : bv 32) (d : nat) (e spv OUT Kp it j' : Z)
      (x1 x3 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
    bytes_at psegs m (ae_TAPE E) (u64s (map (Z_to_bv 64) (ae_tws E))) ->
    rw_cells psegs m (spv + 8) [C8 (Z_to_bv 64 (ae_DOC E)); C8 (Z_to_bv 64 4294967295)] -> mem_inv psegs m ->
    elem (ae_T E) (ae_S E) (ae_sn E) ck_any d (it + 1) j' -> 0 <= it -> it + 1 < j' <= e -> e + 1 <= ae_n E - 1 ->
    (forall (x10' x11' x12' : word), j' <> e ->
       evt psegs K (MS (mkR x1 (Z_to_bv 64 spv) x3 (Z_to_bv 64 RATP) x5 x6 x7 (Z_to_bv 64 OUT) (Z_to_bv 64 L) x10' x11' x12' x13 x14 x15 x16 x17
                          (Z_to_bv 64 Kp) (Z_to_bv 64 4294967297) (Z_to_bv 64 (ae_TAPE E)) (Z_to_bv 64 e) (Z_to_bv 64 (ae_TAPE E + 8 + 8 * it))
                          (Z_to_bv 64 (ae_TAPE E + 8)) (Z_to_bv 64 (ae_SBUF E)) (Z_to_bv 64 32) (Z_to_bv 64 j') (Z_to_bv 64 67240448) x28 x29 x30 x31)
                     F (Z_to_bv 64 (base + 0x104)) fc None m (seg_rom psegs))) ->
    (forall (x10' x11' x12' : word),
       evt psegs K (MS (mkR x1 (Z_to_bv 64 spv) x3 (Z_to_bv 64 RATP) x5 x6 x7 (Z_to_bv 64 OUT) (Z_to_bv 64 L) x10' x11' x12' x13 x14 x15 x16 x17
                          (Z_to_bv 64 Kp) (Z_to_bv 64 4294967297) (Z_to_bv 64 (ae_TAPE E)) (Z_to_bv 64 e) (Z_to_bv 64 (ae_TAPE E + 8 + 8 * it))
                          (Z_to_bv 64 (ae_TAPE E + 8)) (Z_to_bv 64 (ae_SBUF E)) (Z_to_bv 64 32) (Z_to_bv 64 e) (Z_to_bv 64 67240448) x28 x29 x30 x31)
                     F (Z_to_bv 64 (base + 0x80)) fc None m (seg_rom psegs))) ->
    evt psegs K (MS (mkR x1 (Z_to_bv 64 spv) x3 (Z_to_bv 64 RATP) x5 x6 x7 (Z_to_bv 64 OUT) (Z_to_bv 64 L) x10 x11 x12 x13 x14 x15 x16 x17
                       (Z_to_bv 64 Kp) (Z_to_bv 64 4294967297) (Z_to_bv 64 (ae_TAPE E)) (Z_to_bv 64 e) (Z_to_bv 64 (8 * it))
                       (Z_to_bv 64 (ae_TAPE E + 8)) (Z_to_bv 64 (ae_SBUF E)) (Z_to_bv 64 32) (Z_to_bv 64 it) (Z_to_bv 64 67240448) x28 x29 x30 x31)
                  F (Z_to_bv 64 (base + 0x15c)) fc None m (seg_rom psegs)).
  Proof.
    intros K m F fc d e spv OUT Kp it j' x1 x3 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 TAPEB FR8 MI EL I0 IJ EN HL HNF.
    pose proof OK as OK'. destruct OK' as [WF _ _ _ _ _ _ _ _ _ _].
    pose proof (tape_wf_root _ _ _ _ _ WF) as [_ NR].
    assert (HSN : ae_sn E < 2^56) by (destruct WF as (_ & ? & _); lia).
    pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl psegs m) as WM.
    pose proof (elem_lt _ _ _ _ _ _ _ EL) as IJ2.
    pose proof (tape_read _ (ae_TAPE E) (ae_tws E) (it + 1) TAPEB ltac:(lia)) as RDV.
    pose proof (elem_word_range _ _ _ _ _ _ EL ltac:(lia) ltac:(lia) HSN) as TIR.
    assert (TTR : 0 <= ttype (ae_T E (it + 1)) < 256) by (unfold ttype; lia).

    assert (LT : forall (pc : Z) (x10' x11' x12' : word), (pc = base + 0x180 \/ pc = base + 0x19c \/ pc = base + 0x1a8) ->
      evt psegs K (MS (mkR x1 (Z_to_bv 64 spv) x3 (Z_to_bv 64 RATP) x5 x6 x7 (Z_to_bv 64 OUT) (Z_to_bv 64 L) x10' x11' x12' x13 x14 x15 x16 x17
                         (Z_to_bv 64 Kp) (Z_to_bv 64 4294967297) (Z_to_bv 64 (ae_TAPE E)) (Z_to_bv 64 e) (Z_to_bv 64 (ae_TAPE E + 8 + 8 * it))
                         (Z_to_bv 64 (ae_TAPE E + 8)) (Z_to_bv 64 (ae_SBUF E)) (Z_to_bv 64 32) (Z_to_bv 64 j') (Z_to_bv 64 67240448) x28 x29 x30 x31)
                    F (Z_to_bv 64 pc) fc None m (seg_rom psegs))).
    { intros pc x10' x11' x12' HPC.
      destruct ROW as [[-> _]|[[-> _]|[-> _]]]; unfold EL_ATKEY, EL_ATKEY2, EL_ATKEYCI in HPC, HL, HNF; zlits_in HPC; zlits_in HL; zlits_in HNF;
        destruct HPC as [-> |[-> | ->]];
        (step; if_cases KLT; zify_cond KLT; [ apply HL; exact KLT | first [rewrite KLT | rewrite <- KLT]; step; apply HNF ]). }
    destruct ROW as [[-> _]|[[-> _]|[-> _]]]; unfold EL_ATKEY, EL_ATKEY2, EL_ATKEYCI in LT |- *; zlits_in LT; zlits.

    astep. step. astep. astep.
    destruct (elem_view_of (ae_T E) (ae_S E) (ae_sn E) ck_any (fun c cv H => H) HSN d (it + 1) j' EL ltac:(lia) ltac:(lia))
      as [TY Ej|TY Ej|TY Ej STR2|d' e2 c2 Ed TY Ej NXT CLOSE TILES|d' e2 c2 Ed TY Ej NXT CLOSE TILES]; unfold ty in TY;
    [
      unfold t_true, t_false, t_null in TY; destruct TY as [TY|[TY|TY]]; rewrite TY;
        (step; if_false; astep; astep; step; if_true; astep; astep; step; if_true; astep;
         eapply evt_eq; [| eapply LT]; [atp_st_eq| do 2 right; reflexivity])
    |
      unfold t_i64, t_u64, t_dbl in TY; destruct TY as [TY|[TY|TY]]; rewrite TY;
        (step; if_false; astep; astep; step; if_false; astep;
         eapply evt_eq; [| eapply LT]; [atp_st_eq| left; reflexivity])
    |
      unfold t_str in TY; rewrite TY;
        step; if_true; astep;
        eapply evt_eq; [| eapply LT]; [atp_st_eq| do 2 right; reflexivity]
    |
      unfold t_arr in TY; rewrite TY;
        step; if_false; astep; astep; step; if_true; astep; astep; step; if_false; step; astep;
        rewrite land32_tnext by lia; rewrite NXT, <- Ej;
        eapply evt_eq; [| eapply LT]; [atp_st_eq| right; left; reflexivity]
    |
      unfold t_obj in TY; rewrite TY;
        step; if_false; astep; astep; step; if_true; astep; astep; step; if_false; step; astep;
        rewrite land32_tnext by lia; rewrite NXT, <- Ej;
        eapply evt_eq; [| eapply LT]; [atp_st_eq| right; left; reflexivity] ].
  Qed.

  Lemma kinv_step : forall mL spv lo m m', kinv mL spv lo m ->
    munch [(spv - 48, spv)] m m' -> wmono psegs m m' -> mem_inv psegs m' -> stk psegs m' lo spv -> kinv mL spv lo m'.
  Proof.
    intros mL spv lo m m' (MI & ST & MU & WM) MU' WM' MI' ST'. split; [exact MI'|]. split; [exact ST'|].
    split; [eapply munch_trans; [exact MU| exact MU']| eapply wmono_trans; [exact WM| exact WM']].
  Qed.
  Lemma kinv_refl : forall mL spv lo, mem_inv psegs mL -> stk psegs mL lo spv -> kinv mL spv lo mL.
  Proof. intros mL spv lo MI ST. split; [exact MI|]. split; [exact ST|]. split; [apply munch_refl| apply wmono_refl]. Qed.

  Lemma kinv_facts : forall mL spv lo m,
    bytes_at psegs mL (ae_TAPE E) (u64s (map (Z_to_bv 64) (ae_tws E))) -> bytes_at psegs mL (ae_SBUF E) (map (Z_to_bv 8) (ae_sbs E)) ->
    bytes_at psegs mL (ae_PTR E) kbytes -> rw_cells psegs mL (spv + 8) [C8 (Z_to_bv 64 (ae_DOC E)); C8 (Z_to_bv 64 4294967295)] ->
    ae_TAPE E + 8 * ae_n E <= spv - 48 -> ae_SBUF E + ae_sn E <= spv - 48 -> (ae_p1 E = [] \/ ae_PTR E + L <= spv - 48) ->
    kinv mL spv lo m ->
    bytes_at psegs m (ae_TAPE E) (u64s (map (Z_to_bv 64) (ae_tws E))) /\ bytes_at psegs m (ae_SBUF E) (map (Z_to_bv 8) (ae_sbs E)) /\
    bytes_at psegs m (ae_PTR E) kbytes /\ rw_cells psegs m (spv + 8) [C8 (Z_to_bv 64 (ae_DOC E)); C8 (Z_to_bv 64 4294967295)] /\
    mem_inv psegs m /\ stk psegs m lo spv.
  Proof.
    intros mL spv lo m TB SB KB F8 TR SR KR KI. pose proof (kinv_agree _ _ _ _ KI) as AG. destruct KI as (MI & ST & _ & _).
    split; [| split; [| split; [| split; [| split; [exact MI| exact ST]]]]].
    - eapply bytes_at_agree; [exact AG| exact TB|]. rewrite u64s_length, length_map. intros a Ha. cbn [outside]. lia.
    - eapply bytes_at_agree; [exact AG| exact SB|]. rewrite length_map. intros a Ha. cbn [outside]. lia.
    - eapply bytes_at_agree; [exact AG| exact KB|]. unfold kbytes. rewrite length_map. intros a Ha. cbn [outside].
      destruct KR as [KR|KR]; [rewrite KR in Ha; cbn [length] in Ha; lia|]. unfold zlength in KR. lia.
    - eapply rw_cells_agree; [exact AG| exact F8|]. intros a Ha. cbn in Ha. cbn [outside]. lia.
  Qed.

  Lemma key_loop : forall (K : machine_state -> Prop) (mL : mem) (F : bvmap 5 word) (fc : bv 32) (d : nat) (e spv lo OUT : Z)
      (x3 x5 x6 x7 x15 x16 x17 x28 x29 x30 x31 : word),
    bytes_at psegs mL (ae_TAPE E) (u64s (map (Z_to_bv 64) (ae_tws E))) -> bytes_at psegs mL (ae_SBUF E) (map (Z_to_bv 8) (ae_sbs E)) ->
    bytes_at psegs mL (ae_PTR E) kbytes -> rw_cells psegs mL (spv + 8) [C8 (Z_to_bv 64 (ae_DOC E)); C8 (Z_to_bv 64 4294967295)] ->
    ae_TAPE E + 8 * ae_n E <= spv - 48 -> ae_SBUF E + ae_sn E <= spv - 48 -> (ae_p1 E = [] \/ ae_PTR E + L <= spv - 48) ->
    0 < ae_TAPE E -> 0 < ae_SBUF E -> 0 <= ae_PTR E -> ae_PTR E + L < 2 ^ 63 ->
    e + 1 <= ae_n E - 1 -> lo + 48 <= spv -> spv + 128 < 2 ^ 63 -> spv mod 16 = 0 ->
    (forall (it j' : Z) (m : mem) (x1 x10 x11 x12 x13 x14 x22 : word),
       is_str (ae_T E) (ae_S E) (ae_sn E) it -> elem (ae_T E) (ae_S E) (ae_sn E) ck_any d (it + 1) j' -> 0 <= it -> it + 1 < j' <= e -> kinv mL spv lo m ->
       evt psegs K (MS (mkR x1 (Z_to_bv 64 spv) x3 (Z_to_bv 64 RATP) x5 x6 x7 (Z_to_bv 64 OUT) (Z_to_bv 64 L) x10 x11 x12 x13 x14 x15 x16 x17
                          (Z_to_bv 64 (ae_PTR E)) (Z_to_bv 64 4294967297) (Z_to_bv 64 (ae_TAPE E)) (Z_to_bv 64 e) x22
                          (Z_to_bv 64 (ae_TAPE E + 8)) (Z_to_bv 64 (ae_SBUF E)) (Z_to_bv 64 32) (Z_to_bv 64 it) (Z_to_bv 64 67240448) x28 x29 x30 x31)
                     F (Z_to_bv 64 (base + 0x1b0)) fc None m (seg_rom psegs))) ->
    (forall (m : mem) (x1 x10 x11 x12 x13 x14 x22 : word), kinv mL spv lo m ->
       evt psegs K (MS (mkR x1 (Z_to_bv 64 spv) x3 (Z_to_bv 64 RATP) x5 x6 x7 (Z_to_bv 64 OUT) (Z_to_bv 64 L) x10 x11 x12 x13 x14 x15 x16 x17
                          (Z_to_bv 64 (ae_PTR E)) (Z_to_bv 64 4294967297) (Z_to_bv 64 (ae_TAPE E)) (Z_to_bv 64 e) x22
                          (Z_to_bv 64 (ae_TAPE E + 8)) (Z_to_bv 64 (ae_SBUF E)) (Z_to_bv 64 32) (Z_to_bv 64 e) (Z_to_bv 64 67240448) x28 x29 x30 x31)
                     F (Z_to_bv 64 (base + 0x80)) fc None m (seg_rom psegs))) ->
    forall (n : nat) (it c' : Z) (m : mem) (x1 x10 x11 x12 x13 x14 x22 : word),
      tiles (field (ae_T E) (ae_S E) (ae_sn E) (elem (ae_T E) (ae_S E) (ae_sn E) ck_any d)) it e c' -> it <> e -> 0 <= it -> e - it <= Z.of_nat n ->
      kinv mL spv lo m ->
      evt psegs K (MS (mkR x1 (Z_to_bv 64 spv) x3 (Z_to_bv 64 RATP) x5 x6 x7 (Z_to_bv 64 OUT) (Z_to_bv 64 L) x10 x11 x12 x13 x14 x15 x16 x17
                         (Z_to_bv 64 (ae_PTR E)) (Z_to_bv 64 4294967297) (Z_to_bv 64 (ae_TAPE E)) (Z_to_bv 64 e) x22
                         (Z_to_bv 64 (ae_TAPE E + 8)) (Z_to_bv 64 (ae_SBUF E)) (Z_to_bv 64 32) (Z_to_bv 64 it) (Z_to_bv 64 67240448) x28 x29 x30 x31)
                    F (Z_to_bv 64 (base + 0x104)) fc None m (seg_rom psegs)).
  Proof.
    intros K mL F fc d e spv lo OUT x3 x5 x6 x7 x15 x16 x17 x28 x29 x30 x31 TBL SBL KBL F8L TR SR KR T0 S0 KP0 KPL EN LOSP SPH AL16 XFOUND XNF.
    pose proof OK as OK'. destruct OK' as [WF SBS P1 _ _ _ _ _ _ _ _].
    pose proof (tape_wf_root _ _ _ _ _ WF) as [_ NR].
    assert (HSN : ae_sn E < 2^56) by (destruct WF as (_ & ? & _); lia).
    assert (KL : length kbytes = Z.to_nat L) by (unfold kbytes, zlength; rewrite length_map; lia).
    induction n as [|n IH]; intros it c' m x1 x10 x11 x12 x13 x14 x22 TI NE I0 FUEL KI.
    { pose proof (tiles_le _ (field_lt _ _ _ _ (elem_lt _ _ _ _ d)) _ _ _ TI). lia. }
    destruct (kinv_facts mL spv lo m TBL SBL KBL F8L TR SR KR KI) as (TAPEB & SBUFB & KB & FR8 & MI & ST).
    pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl psegs m) as WM.
    destruct (object_iter _ _ _ _ (fun c cv H => H) HSN d it e c' TI NE I0 ltac:(lia)) as (j' & STR & EL & IJ & AFT & TI').
    pose proof (key_word_range _ _ _ _ STR HSN) as (KWR & KM & KT).
    destruct (is_str_read _ _ _ HSN _ STR) as [_ (l & SA)].
    pose proof (str_at_bounds _ _ HSN _ _ SA) as (O0 & L0 & OL & LE & O56).
    set (o := tval (ae_T E it)) in *.
    pose proof (tape_read _ (ae_TAPE E) (ae_tws E) it TAPEB ltac:(lia)) as RDK.
    assert (KL' : Z.of_nat (length kbytes) = L) by (unfold kbytes, zlength; rewrite length_map; lia).
    destruct ROW as [[HB HC]|[[HB HC]|[HB HC]]]; rewrite HB; unfold EL_ATKEY, EL_ATKEY2, EL_ATKEYCI, bcmp_entry, EL_STRNCASECMP in HB, HC |- *; zlits.

    astep. astep. step. astep. astep. rewrite KM. astep.

    pose proof (sbuf_read1 m (ae_SBUF E) (ae_sbs E) o SBUFB ltac:(lia)) as RB0.
    pose proof (sbuf_read1 m (ae_SBUF E) (ae_sbs E) (o + 1) SBUFB ltac:(lia)) as RB1.
    pose proof (sbuf_read1 m (ae_SBUF E) (ae_sbs E) (o + 2) SBUFB ltac:(lia)) as RB2.
    pose proof (sbuf_read1 m (ae_SBUF E) (ae_sbs E) (o + 3) SBUFB ltac:(lia)) as RB3.
    pose proof (sbs_byte E OK o ltac:(lia)) as B0. pose proof (sbs_byte E OK (o + 1) ltac:(lia)) as B1.
    pose proof (sbs_byte E OK (o + 2) ltac:(lia)) as B2. pose proof (sbs_byte E OK (o + 3) ltac:(lia)) as B3.

    astep. astep. astep. astep. astep. astep. astep. astep. astep. astep.
    rewrite !land64_shl_small by lia. rewrite le32_of_lbu4 by lia.
    change (ae_S E o + 2 ^ 8 * ae_S E (o + 1) + 2 ^ 16 * ae_S E (o + 2) + 2 ^ 24 * ae_S E (o + 3)) with (le32 (ae_S E) o). rewrite LE.

    step. if_cases KEQ; zify_cond KEQ;
      [ eapply evt_eq; [| eapply (key_tail K m F fc d e spv OUT (ae_PTR E) it j')];
          [ atp_st_eq| exact TAPEB| exact FR8| exact MI| exact EL| lia| lia| lia
          | intros; eapply evt_eq; [| eapply (IH j' (c' - 1))]; [atp_st_eq| exact TI'| assumption| lia| lia| exact KI]
          | intros; eapply evt_eq; [| eapply XNF]; [atp_st_eq| exact KI] ] |].

    destruct (sbuf_bytes_at E m o l SBUFB ltac:(lia) ltac:(lia) ltac:(lia)) as [QB QL].
    astep. step. step. step.
    eapply evt_cut;
      [ eapply evt_eq; [| eapply (CMP _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m spv lo (ae_PTR E) (ae_SBUF E + o + 4) kbytes (sbuf_bytes E o l))];
          [ atp_st_eq| rewrite QL; lia| lia| lia| lia| lia
          | destruct KR as [KR'|KR']; [left; unfold kbytes; rewrite KR'; reflexivity| right; lia]
          | exact KB| exact QB| exact MI| exact ST| lia| lia| exact AL16 ] |].
    cbv beta. intros ms' (r & a1' & a2' & a3' & a4' & m' & -> & MU' & WM' & MI' & ST').
    lazymatch goal with |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?x)) _ _ _ _) =>
      replace (ret_pc (Z_to_bv 64 x)) with (Z_to_bv 64 x) by (symmetry; apply ret_pc_even; [lia| reflexivity]) end.
    pose proof (kinv_step _ _ _ _ _ KI MU' WM' MI' ST') as KI'.
    destruct (kinv_facts mL spv lo m' TBL SBL KBL F8L TR SR KR KI') as (TAPEB' & _ & _ & FR8' & _ & _).
    clear MU WM. pose proof (munch_refl ([] : list (Z * Z)) m') as MU. pose proof (wmono_refl psegs m') as WM.

    step. if_cases KF;
      [ eapply evt_eq; [| eapply (XFOUND it j' m')]; [atp_st_eq| exact STR| exact EL| lia| lia| exact KI']
      | eapply evt_eq; [| eapply (key_tail K m' F fc d e spv OUT (ae_PTR E) it j')];
          [ atp_st_eq| exact TAPEB'| exact FR8'| exact MI'| exact EL| lia| lia| lia
          | intros; eapply evt_eq; [| eapply (IH j' (c' - 1))]; [atp_st_eq| exact TI'| assumption| lia| lia| exact KI']
          | intros; eapply evt_eq; [| eapply XNF]; [atp_st_eq| exact KI'] ] ].
  Qed.

  Definition key_post (ra : word) (q : Z) (gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a5 a6 a7 t0 t1 t2 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
      (OUT lo : Z) (m : mem) : machine_state -> Prop :=
    fun ms' => exists (a0 a1 a2 a3 a4 : word) (m' : mem),
      ms' = MS (mkR ra (Z_to_bv 64 q) gp (Z_to_bv 64 RATP) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom psegs)
      /\ munch [(q - 176, q); (OUT, OUT + 24)] m m' /\ wmono psegs m m' /\ mem_inv psegs m' /\ stk psegs m' lo q
      /\ (exists (w0 w1 ew : word) od, rw_cells psegs m' OUT [C8 w0; C8 w1; C4 ew; CB 4 od]).

  Lemma key_exit : forall (ra : word) (q : Z) (gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a5 a6 a7 t0 t1 t2 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
      (OUT lo : Z) (m0 m : mem) (x1 x8 x9 a0 a1 a2 a3 a4 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 : word) (jl : list byte) (w0 w1 ew : word) (od : list byte),
    rw_cells psegs m (q + -128) [CB 24 jl] ->
    rw_cells psegs m (q + -104) [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    rw_cells psegs m OUT [C8 w0; C8 w1; C4 ew; CB 4 od] ->
    munch [(q - 176, q); (OUT, OUT + 24)] m0 m -> wmono psegs m0 m -> mem_inv psegs m -> stk psegs m lo (q + -128) -> lo <= q - 128 -> q < 2 ^ 63 ->
    evt psegs (key_post ra q gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a5 a6 a7 t0 t1 t2 t3 t4 t5 t6 F fc OUT lo m0)
      (MS (mkR x1 (Z_to_bv 64 (q + -128)) gp (Z_to_bv 64 RATP) t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6)
          F (Z_to_bv 64 (base + 0x98)) fc None m (seg_rom psegs)).
  Proof.
    intros until od. intros FRL FRS OUTC MU WM MI ST LOQ QH.
    pose proof (rw_cells_join _ _ _ _ _ FRL FRS ltac:(cbn [cells_size csize Nat.add]; lia)) as FR. cbn [app] in FR. clear FRL FRS.
    destruct ROW as [[HB HC]|[[HB HC]|[HB HC]]]; rewrite HB; unfold EL_ATKEY, EL_ATKEY2, EL_ATKEYCI in HB |- *; zlits.

    do 13 step. step. release_frame FR ST q. step.
    apply evt_done. unfold key_post. do 5 eexists. eexists. split; [cbv delta [mkR]; reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST| do 4 eexists; exact OUTC].
  Qed.

  Lemma key_store : forall (ra : word) (q : Z) (gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a5 a6 a7 t0 t1 t2 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
      (OUT lo : Z) (m0 m : mem) (x1 x9 a0 a1 a2 a3 a4 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 : word) (jl o0 o1 o2 od : list byte),
    rw_cells psegs m (q + -128) [CB 24 jl] ->
    rw_cells psegs m (q + -104) [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    rw_cells psegs m OUT [CB 8 o0; CB 8 o1; CB 4 o2; CB 4 od] -> q <= OUT -> OUT + 24 < 2 ^ 63 ->
    munch [(q - 176, q); (OUT, OUT + 24)] m0 m -> wmono psegs m0 m -> mem_inv psegs m -> stk psegs m lo (q + -128) -> lo <= q - 128 -> q < 2 ^ 63 ->
    evt psegs (key_post ra q gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a5 a6 a7 t0 t1 t2 t3 t4 t5 t6 F fc OUT lo m0)
      (MS (mkR x1 (Z_to_bv 64 (q + -128)) gp (Z_to_bv 64 RATP) t0 t1 t2 (Z_to_bv 64 OUT) x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6)
          F (Z_to_bv 64 (base + 0x8c)) fc None m (seg_rom psegs)).
  Proof.
    intros until od. intros FRL FRS OUTC QO OH MU WM MI ST LOQ QH.
    pose proof ROW as ROW'.
    destruct ROW' as [[HB HC]|[[HB HC]|[HB HC]]]; rewrite HB; unfold EL_ATKEY, EL_ATKEY2, EL_ATKEYCI in HB |- *; zlits.

    hstep. hstep. hstep.
    eapply evt_eq; [| eapply key_exit]; [atp_st_eq| eassumption| eassumption| eassumption| eassumption| eassumption| eassumption| eassumption| lia| lia].
  Qed.

  Lemma kinv_carry : forall (m0 mL m : mem) (q lo OUT : Z) (j0 : list byte) (wm : word) (s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra : word)
      (o0 o1 o2 od : list byte),
    kinv mL (q + -128) lo m -> q <= OUT -> OUT + 24 < 2 ^ 63 ->
    rw_cells psegs mL (q + -128) [CB 8 j0; C8 (Z_to_bv 64 (ae_DOC E)); C8 wm] ->
    rw_cells psegs mL (q + -104) [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    rw_cells psegs mL OUT [CB 8 o0; CB 8 o1; CB 4 o2; CB 4 od] ->
    munch [(q - 176, q); (OUT, OUT + 24)] m0 mL -> wmono psegs m0 mL ->
    rw_cells psegs m (q + -128) [CB 8 j0; C8 (Z_to_bv 64 (ae_DOC E)); C8 wm] /\
    rw_cells psegs m (q + -104) [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] /\
    rw_cells psegs m OUT [CB 8 o0; CB 8 o1; CB 4 o2; CB 4 od] /\
    munch [(q - 176, q); (OUT, OUT + 24)] m0 m /\ wmono psegs m0 m /\ mem_inv psegs m /\ stk psegs m lo (q + -128).
  Proof.
    intros until od. intros KI QO OH FR0 FRS OUTC MU WM. pose proof (kinv_agree _ _ _ _ KI) as AG. destruct KI as (MI & ST & MU' & WM').
    split; [| split; [| split; [| split; [| split; [| split; [exact MI| exact ST]]]]]].
    - eapply rw_cells_agree; [exact AG| exact FR0|]. intros a Ha. cbn in Ha. cbn [outside]. lia.
    - eapply rw_cells_agree; [exact AG| exact FRS|]. intros a Ha. cbn in Ha. cbn [outside]. lia.
    - eapply rw_cells_agree; [exact AG| exact OUTC|]. intros a Ha. cbn in Ha. cbn [outside]. lia.
    - eapply munch_trans; [exact MU|]. eapply munch_weaken; [| exact MU']. unfold sub_fp. cbn [outside]. intros x Hx. lia.
    - eapply wmono_trans; [exact WM| exact WM'].
  Qed.

  Lemma key_found : forall (ra : word) (q : Z) (gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a5 a6 a7 t0 t1 t2 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
      (OUT lo it : Z) (m0 m : mem) (x1 x9 a0 a1 a2 a3 a4 x18 x19 x20 x21 x22 x23 x24 x25 x27 : word) (j0 o0 o1 o2 od : list byte) (wm : word),
    rw_cells psegs m (q + -128) [CB 8 j0; C8 (Z_to_bv 64 (ae_DOC E)); C8 wm] ->
    rw_cells psegs m (q + -104) [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    rw_cells psegs m OUT [CB 8 o0; CB 8 o1; CB 4 o2; CB 4 od] -> q <= OUT -> OUT + 24 < 2 ^ 63 -> 0 <= it -> it + 1 < 2 ^ 63 ->
    munch [(q - 176, q); (OUT, OUT + 24)] m0 m -> wmono psegs m0 m -> mem_inv psegs m -> stk psegs m lo (q + -128) -> lo <= q - 128 -> q < 2 ^ 63 ->
    evt psegs (key_post ra q gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a5 a6 a7 t0 t1 t2 t3 t4 t5 t6 F fc OUT lo m0)
      (MS (mkR x1 (Z_to_bv 64 (q + -128)) gp (Z_to_bv 64 RATP) t0 t1 t2 (Z_to_bv 64 OUT) x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25
               (Z_to_bv 64 it) x27 t3 t4 t5 t6)
          F (Z_to_bv 64 (base + 0x1b0)) fc None m (seg_rom psegs)).
  Proof.
    intros until wm. intros FR0 FRS OUTC QO OH I0 IH MU WM MI ST LOQ QH.
    pose proof ROW as ROW'.
    destruct ROW' as [[HB HC]|[[HB HC]|[HB HC]]]; rewrite HB; unfold EL_ATKEY, EL_ATKEY2, EL_ATKEYCI in HB |- *; zlits.

    astep. step. hstep. hstep. hstep. step.
    destruct (rw_cells_forget _ _ _ _ FR0) as [jl FRL]. cbn [cells_size csize Nat.add] in FRL.
    eapply evt_eq; [| eapply key_exit]; [atp_st_eq| exact FRL| eassumption| eassumption| eassumption| eassumption| eassumption| eassumption| lia| lia].
  Qed.

  Ltac frame_parts FR FA FB q :=
    destruct (proj1 (rw_cells_app _ _ [_; _; _] _) FR) as [FA FB];
    lazymatch type of FB with rw_cells _ _ ?a _ => replace a with (q + -104) in FB by (cbn [cells_size csize length Nat.add]; lia) end.

  Ltac bufs_at mx TB SB KB TAPEB SBUFB PTRB MU WM PR2 :=
    pose proof (agree_on_of_munch _ _ _ MU WM) as AG; unhide TAPEB; unhide SBUFB; unhide PTRB;
    assert (TB : bytes_at psegs mx (ae_TAPE E) (u64s (map (Z_to_bv 64) (ae_tws E))))
      by (eapply bytes_at_agree; [exact AG| exact TAPEB|]; rewrite u64s_length, length_map; intros a Ha; cbn [outside]; lia);
    assert (SB : bytes_at psegs mx (ae_SBUF E) (map (Z_to_bv 8) (ae_sbs E)))
      by (eapply bytes_at_agree; [exact AG| exact SBUFB|]; rewrite length_map; intros a Ha; cbn [outside]; lia);
    assert (KB : bytes_at psegs mx (ae_PTR E) kbytes)
      by (eapply bytes_at_agree; [exact AG| exact PTRB|]; unfold kbytes; rewrite length_map; intros a Ha; cbn [outside];
          destruct PR2 as [PE|PC]; [rewrite PE in Ha; cbn [length] in Ha; lia| unfold zlength in PC; lia]);
    clear AG; hide TAPEB; hide SBUFB; hide PTRB.

  Lemma key_spec : forall (ra gp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (q node OUT lo : Z) (jo : list byte),
    AINV E m -> el_root E m node -> RHEAP s (ae_LB E) m -> mem_inv psegs m ->
    rw_cells psegs m OUT [CB 24 jo] -> q <= OUT -> OUT + 24 <= ae_B E -> (OUT + 24 <= node \/ node + 16 <= OUT) ->
    (OUT + 24 <= ae_DOC E \/ ae_DOC E + 16 <= OUT) -> q <= node -> node + 16 <= ae_B E -> q <= ae_DOC E ->
    stk psegs m lo q -> ae_lo E <= lo -> lo + 176 <= q -> q mod 16 = 0 ->
    evt psegs (key_post ra q gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a5 a6 a7 t0 t1 t2 t3 t4 t5 t6 F fc OUT lo m)
      (MS (mkR ra (Z_to_bv 64 q) gp (Z_to_bv 64 RATP) t0 t1 t2 s0 s1 (Z_to_bv 64 OUT) (Z_to_bv 64 node) (Z_to_bv 64 (ae_PTR E)) (Z_to_bv 64 L)
               a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 base) fc None m (seg_rom psegs)).
  Proof.
    intros until jo. intros AI ROOT HEAP MI OUTC QO O1 ONODE ODOC QN N1 QDOC ST LOLO LOQ Q16.
    pose proof OK as OK'. destruct OK' as [WF SBS P1 P1L BT BS BP P0 [CEIL GLO] B63 [DL DB]].
    assert (LO0 : 0 <= ae_lo E) by (unfold OSSVerify.Proofs.simdjson.fuzz_element.lib.Spec.Malloc.MCEIL in CEIL; try (pose proof alloc_ceiling_range as CEIL_RANGE__); lia).
    pose proof CEIL as CEIL'. unfold OSSVerify.Proofs.simdjson.fuzz_element.lib.Spec.Malloc.MCEIL in CEIL; try (pose proof alloc_ceiling_range as CEIL_RANGE__).
    pose proof (aenv_ranges E s m OK HEAP) as (TR & SR & PR0 & PR1 & PR2).
    pose proof (el_root_elem E OK) as [EL NR].
    assert (HSN : ae_sn E < 2^56) by (destruct WF as (_ & ? & _); lia).
    destruct AI as (TAPEB & SBUFB & PTRB & DOCC). unfold el_root in ROOT.
    pose proof (elem_word_range _ _ _ _ _ _ EL ltac:(lia) ltac:(lia) HSN) as TIR.
    assert (TTR : 0 <= ttype (ae_T E 1) < 256) by (unfold ttype; lia).
    pose proof (munch_refl [(q - 176, q); (OUT, OUT + 24)]%Z m) as MU. pose proof (wmono_refl psegs m) as WM.
    apply (rw_cells_split_CB psegs _ _ [] 24 jo [] [8;8;4;4]%nat) in OUTC; [|reflexivity]. cbn [mk_CB_cells app] in OUTC.
    pose proof ROW as ROW'.
    destruct ROW' as [[HB HC]|[[HB HC]|[HB HC]]]; rewrite HB; unfold EL_ATKEY, EL_ATKEY2, EL_ATKEYCI in HB |- *; zlits.

    hide TAPEB. hide SBUFB. hide PTRB.
    step. carve_frame 128%nat ST.
    apply (rw_cells_split_CB psegs _ _ [] 128 junk [] [8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8]%nat) in FR; [|reflexivity]. cbn [mk_CB_cells app] in FR.
    do 13 hstep.

    step. step. step. step. step.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      bufs_at mx TB0 SB0 KB0 TAPEB SBUFB PTRB MU WM PR2; clear SB0 KB0;
      pose proof (tape_read mx (ae_TAPE E) (ae_tws E) 1 TB0 ltac:(lia)) as RDT; clear TB0 end.
    rewrite Z.mul_1_r in RDT.

    astep. astep. step. astep. step. step.
    zstep. if_cases HK; zify_cond HK;
      [ astep; frame_parts FR FRa FRb q; destruct (rw_cells_forget _ _ _ _ FRa) as [jl FRL]; cbn [cells_size csize Nat.add] in FRL;
        eapply evt_eq; [| eapply key_store]; [atp_st_eq| exact FRL| exact FRb| exact OUTC| lia| lia| exact MU| exact WM| assumption| exact ST| lia| lia] |].

    destruct (elem_view_of (ae_T E) (ae_S E) (ae_sn E) ck_any (fun c cv H => H) HSN TAPE_MAX_DEPTH 1 (ae_n E - 1) EL ltac:(lia) ltac:(lia))
      as [TY Ej|TY Ej|TY Ej STR|d' e2 c2 Ed TY Ej NXT CLOSE TILES|d' e2 c2 Ed TY Ej NXT CLOSE TILES]; unfold ty in TY;
      unfold t_true, t_false, t_null, t_i64, t_u64, t_dbl, t_str, t_arr, t_obj in TY; try lia.
    pose proof (tiles_le _ (field_lt _ _ _ _ (elem_lt _ _ _ _ d')) _ _ _ TILES) as TLE.

    hstep. astep. astep. rewrite land32_tnext by lia. rewrite NXT. astep. astep.
    replace (e2 + 1 + -1) with e2 by lia.
    zstep. if_cases HK2; zify_cond HK2;
      [| astep; step; frame_parts FR FRa FRb q; destruct (rw_cells_forget _ _ _ _ FRa) as [jl FRL]; cbn [cells_size csize Nat.add] in FRL;
         eapply evt_eq; [| eapply key_store]; [atp_st_eq| exact FRL| exact FRb| exact OUTC| lia| lia| exact MU| exact WM| assumption| exact ST| lia| lia] ].

    astep. astep. step. step. astep. astep. astep. hstep. astep. astep. astep. astep.
    frame_parts FR FRa FRb q.
    destruct (proj1 (rw_cells_app _ _ [_] _) FRa) as [_ F8].
    lazymatch type of F8 with rw_cells _ _ ?a _ => replace a with (q + -128 + 8) in F8 by (cbn [cells_size csize length Nat.add]; lia) end.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
    bufs_at mx TB SB KB TAPEB SBUFB PTRB MU WM PR2;
    eapply evt_eq; [| eapply (key_loop _ mx F fc d' e2 (q + -128) lo OUT) with (n := (Z.to_nat (e2 - 2) + 1)%nat) (it := 2) (c' := c2) (m := mx)];
      [ atp_st_eq| exact TB| exact SB| exact KB| exact F8| lia| lia| destruct PR2 as [PE|PC]; [left; exact PE| right; lia]| lia| lia| lia| lia| lia| lia| lia
      | clear - Q16; replace (q + -128) with (q + (-8) * 16) by lia; rewrite Z.mod_add by lia; exact Q16
      |
        intros it j' mq y1 y10 y11 y12 y13 y14 y22 STR2 EL2 I02 IJ2 KI2;
        destruct (kinv_carry m mx mq q lo OUT _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KI2 QO ltac:(lia) FRa FRb OUTC MU WM) as (FRa2 & FRb2 & OUTC2 & MU2 & WM2 & MI2 & ST2);
        eapply evt_eq; [| eapply (key_found _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc OUT lo it m mq)];
          [atp_st_eq| exact FRa2| exact FRb2| exact OUTC2| lia| lia| lia| lia| exact MU2| exact WM2| exact MI2| exact ST2| lia| lia]
      |
        intros mq y1 y10 y11 y12 y13 y14 y22 KI2;
        destruct (kinv_carry m mx mq q lo OUT _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KI2 QO ltac:(lia) FRa FRb OUTC MU WM) as (FRa2 & FRb2 & OUTC2 & MU2 & WM2 & MI2 & ST2);
        clear MU WM; pose proof (munch_refl ([] : list (Z * Z)) mq) as MU; pose proof (wmono_refl psegs mq) as WM;
        rewrite HB; zlits;
        astep; step; destruct (rw_cells_forget _ _ _ _ FRa2) as [jl FRL]; cbn [cells_size csize Nat.add] in FRL;
        eapply evt_eq; [| eapply key_store]; [atp_st_eq| exact FRL| exact FRb2| exact OUTC2| lia| lia| exact MU2| exact WM2| exact MI2| exact ST2| lia| lia]
      | exact TILES| lia| lia| lia
      | apply kinv_refl; assumption ]
    end.
  Qed.
End Key.
End WithCeiling0.
