(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac ImageA Arr Walk Image.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require Import MallocKit_AB.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout R_small R_m2s R_cache_defs R_prim_defs R_asan_defs R_prim_kit R_glue_defs R_depot_defs R_quar_defs R_qrec_defs R_qput R_qdrain R_combfree R_qrecycle.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import StoreFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Open Scope bv_scope.
Notation mem := (word -> option byte).
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.

Definition qcbrec_entry : Z := 0x19d084.
Definition cdealloc_entry : Z := 0x19d488.

(* [comment removed for export] *)
Definition drec_frame (m : mem) (C : Z) (j : list byte) (cache stack : Z) (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 : word) : Prop :=
  rw_cells asegs m (C - 112) [CB 8 j] /\ rw_cells asegs m (C - 104) [C8 (Z_to_bv 64 cache); C8 (Z_to_bv 64 stack)]
  /\ rw_cells asegs m (C - 88) [C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

(* [comment removed for export] *)
Definition drec_mem (m : mem) (C SB : Z) (j : list byte) (cache stack : Z) (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 : word)
    (rest : list batch) : Prop :=
  drec_frame m C j cache stack ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 /\ rw_cells asegs m i_spacebeg [C8 (Z_to_bv 64 SB)]
  /\ qcache_rep m C rest.

(* [comment removed for export] *)
Definition drec_at_qcb (gp tp s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (C SB lo : Z) (j : list byte) (cache stack : Z)
    (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 : word) (W : list (Z * Z)) (rest : list batch) (b : Z) (ents : list (Z * Z)) (i : nat)
    (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0' t1' t2' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem),
    ms' = MS (mkR (Z_to_bv 64 0x19d010) (Z_to_bv 64 (C - 112)) gp tp t0' t1' t2' (Z_to_bv 64 C) (Z_to_bv 64 INST)
                  (Z_to_bv 64 (C - 104)) (Z_to_bv 64 (fst (nth i ents (0%Z, 0%Z)))) a2' a3' a4' a5' a6' a7'
                  (Z_to_bv 64 6722840) (Z_to_bv 64 6723464) (Z_to_bv 64 b) (Z_to_bv 64 (2^37)) (Z_to_bv 64 (Z.of_nat (length ents)))
                  (Z_to_bv 64 (b + 152 + 8 * Z.of_nat i)) (Z_to_bv 64 (Z.of_nat (length ents) + 16)) (Z_to_bv 64 (16 + Z.of_nat i))
                  s10 s11 t3' t4' t5' t6')
             F (Z_to_bv 64 qcbrec_entry) fc None m' (seg_rom asegs)
    /\ munch W m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ drec_mem m' C SB j cache stack ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 rest /\ qbatch m' b (qfirst rest) ents
    /\ stk asegs m' lo (C - 112).

(* [comment removed for export] *)
Definition drec_at_deal (gp tp s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (C SB lo : Z) (j : list byte) (cache stack : Z)
    (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 : word) (W : list (Z * Z)) (rest : list batch) (b : Z) (ents : list (Z * Z))
    (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0' t1' t2' a4' a5' a6' a7' s6' s7' s8' s9' t3' t4' t5' t6' : word) (m' : mem),
    ms' = MS (mkR (Z_to_bv 64 0x19d048) (Z_to_bv 64 (C - 112)) gp tp t0' t1' t2' (Z_to_bv 64 C) (Z_to_bv 64 INST)
                  (Z_to_bv 64 cache) (Z_to_bv 64 INST) (Z_to_bv 64 24) (Z_to_bv 64 b) a4' a5' a6' a7'
                  (Z_to_bv 64 6722840) (Z_to_bv 64 6723464) (Z_to_bv 64 b) (Z_to_bv 64 (2^37)) s6' s7' s8' s9'
                  s10 s11 t3' t4' t5' t6')
             F (Z_to_bv 64 cdealloc_entry) fc None m' (seg_rom asegs)
    /\ munch W m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ drec_mem m' C SB j cache stack ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 rest /\ qbatch m' b (qfirst rest) ents
    /\ stk asegs m' lo (C - 112).

(* [comment removed for export] *)
Definition drec_ret_post (gp tp s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (C lo : Z)
    (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 : word) (W : list (Z * Z)) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem),
    ms' = MS (mkR ra (Z_to_bv 64 C) gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                  t3' t4' t5' t6') F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch W m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ qcache_rep m' C [] /\ stk asegs m' lo C.

Lemma qlast_cons_ne : forall x rest, rest <> [] -> qlast (x :: rest) = qlast rest.
Proof.
  intros x rest H. unfold qlast. destruct rest as [|y rest]; [congruence|]. cbn [map]. reflexivity.
Qed.

Lemma qbytes_cons : forall b ents rest, qbytes ((b, ents) :: rest) = (8192 + bsum ents + qbytes rest)%Z.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma ent_word_nth : forall (ws : list word) (ents : list (Z * Z)) (i : nat),
  firstn (length ents) ws = map (fun e => Z_to_bv 64 (fst e)) ents -> (i < length ents)%nat ->
  nth_error ws i = Some (Z_to_bv 64 (fst (nth i ents (0%Z, 0%Z)))).
Proof.
  intros ws ents i H Hi.
  assert (E : nth_error (firstn (length ents) ws) i = nth_error (map (fun e => Z_to_bv 64 (fst e)) ents) i) by (rewrite H; reflexivity).
  rewrite nth_error_firstn in E. destruct (Nat.ltb_spec i (length ents)) as [_|]; [| lia].
  rewrite E, nth_error_map, (nth_error_nth' ents (0%Z, 0%Z) Hi). reflexivity.
Qed.

Lemma add_sub_cancel : forall a b, (a + b + - a = b)%Z.
Proof. intros. lia. Qed.

Lemma length_cons_pred : forall {X} (x : X) l, (Z.of_nat (length (x :: l)) + -1 = Z.of_nat (length l))%Z.
Proof. intros. cbn [length]. lia. Qed.

(* [comment removed for export] *)
Definition drec_popped (gp tp s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (C SB lo : Z) (j : list byte) (cache stack : Z)
    (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 : word) (rest : list batch) (b : Z) (ents : list (Z * Z)) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s7' s8' s9' t3' t4' t5' t6' : word) (m' : mem),
    ms' = MS (mkR ra' (Z_to_bv 64 (C - 112)) gp tp t0' t1' t2' (Z_to_bv 64 C) (Z_to_bv 64 INST) a0' a1' a2' a3' a4' a5' a6' a7'
                  (Z_to_bv 64 6722840) (Z_to_bv 64 6723464) (Z_to_bv 64 b) (Z_to_bv 64 (2^37)) (Z_to_bv 64 (Z.of_nat (length ents)))
                  s7' s8' s9' s10 s11 t3' t4' t5' t6')
             F (Z_to_bv 64 0x19cff4) fc None m' (seg_rom asegs)
    /\ munch [(C, C + 32)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ drec_mem m' C SB j cache stack ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 rest /\ qbatch m' b (qfirst rest) ents
    /\ stk asegs m' lo (C - 112).

(* [comment removed for export] *)
Lemma drec_pop : forall (ra0 gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s4r s6r s7r s8r s9r s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) fc (m : mem) (C SB lo cache stack : Z) (j : list byte) (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 : word)
    (b : Z) (ents : list (Z * Z)) (rest : list batch),
  qwf SB ((b, ents) :: rest) -> (qbytes ((b, ents) :: rest) < 2^63)%Z -> (0 < SB)%Z ->
  drec_mem m C SB j cache stack ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 ((b, ents) :: rest) ->
  stk asegs m lo (C - 112) -> (r24 SB + 2^32 <= lo)%Z -> (lo <= C - 112)%Z -> (C + 32 <= 2^47)%Z ->
  mem_inv asegs m ->
  evt asegs (drec_popped gp tp s10 s11 F fc C SB lo j cache stack ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 rest b ents m)
    (MS (mkR ra0 (Z_to_bv 64 (C - 112)) gp tp t0 t1 t2 (Z_to_bv 64 C) (Z_to_bv 64 INST)
             (Z_to_bv 64 (Z.of_nat (length ((b, ents) :: rest)))) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 6722840) (Z_to_bv 64 6723464) s4r
             (Z_to_bv 64 (2^37)) s6r s7r s8r s9r s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x19cfc4) fc None m (seg_rom asegs)).
Proof.
  intros until rest. intros WF HBY HSB DM ST HLO HCL HC MI.
  pose proof (qwf_region _ _ WF) as RG. apply box in RG.
  destruct WF as (ND & HF). inversion HF as [|? ? (Hb8 & Hb1 & Hb2 & Hbl & Hbp) HFr]; subst.
  destruct DM as (FRM & SBC & QR). apply box in FRM. apply box in SBC.
  apply (proj1 (qcache_rep_iff _ _ _)) in QR. destruct QR as (QH & QC).
  apply (proj1 (qchain_to_0 _ _)) in QC. cbn [qchain_to] in QC. destruct QC as (QB & QC). apply box in QC.
  apply (proj1 (qbatch_iff _ _ _ _)) in QB. destruct QB as (BH & BA & Ble). apply box in BA.
  change (qfirst ((b, ents) :: rest)) with b in QH.
  cbn [fst snd] in Hb8, Hb1, Hb2, Hbl, Hbp.
  assert (ENX : (match rest with [] => 0%Z | (b', _) :: _ => b' end) = qfirst rest) by (destruct rest as [|[? ?] ?]; reflexivity).
  rewrite ENX in BH.
  pose proof (qbytes_cons b ents rest) as EQB. pose proof (bsum_nonneg _ Hbp) as HBS.
  assert (QRN : (0 <= qbytes rest)%Z).
  { apply (qbytes_nonneg SB). split; [inversion ND; assumption| exact HFr]. }
  unfold r24 in *.
  pose proof (munch_refl [(C, C + 32)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
  do 3 zstep.
  destruct rest as [|[b' e'] rest'];
    [ (* [comment removed for export] *)
      change (qfirst []) with 0%Z in *; zstep; ifF; zstep; fix_lit_store
    | inversion HFr as [|? ? (Hb8' & Hb1' & Hb2' & _) _]; subst; cbn [fst] in Hb1', Hb2'; unfold r24 in Hb1', Hb2';
      change (qfirst ((b', e') :: rest')) with b' in *; zstep; ifT;
      rewrite (qlast_cons_ne (b, ents) ((b', e') :: rest')) in QH by discriminate ].
  all: do 6 zstep.
  all: rewrite EQB, add_sub_cancel, length_cons_pred in QH.
  all: zstep.
  all: apply evt_done; unfold drec_popped.
  all: do 20 eexists; split; [reflexivity|].
  all: split; [eassumption|]; split; [eassumption|]; split; [eassumption|].
  all: split; [| split; [apply (proj2 (qbatch_iff _ _ _ _)); split; [eassumption| split; [| exact Ble]]| eassumption]].
  2, 4: lazymatch goal with |- exists _, u64arr _ ?mm _ _ /\ _ =>
          destruct (unbox _ BA) as (ws & BA1 & BL & BP); exists ws; split; [| split; [exact BL| exact BP]];
          apply (u64arr_transport asegs _ m mm _ _ BA1 MU WM); rewrite BL; cbn [disjoint_from]; lia end.
  all: lazymatch goal with |- drec_mem ?mm _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => pose proof (unbox _ FRM) as (F1 & F2 & F3);
         split; [split; [| split]| split]; [apply (rw_cells_transport asegs _ m mm _ _ F1 MU WM)| apply (rw_cells_transport asegs _ m mm _ _ F2 MU WM)
                                          | apply (rw_cells_transport asegs _ m mm _ _ F3 MU WM)| apply (rw_cells_transport asegs _ m mm _ _ (unbox _ SBC) MU WM)|]
       end.
  all: try (cbn [disjoint_from cells_size csize Nat.add Z.of_nat length]; unfold i_spacebeg, g_instance; lia).
  all: apply (proj2 (qcache_rep_iff _ _ _)); split; [eassumption|].
  all: apply (proj2 (qchain_to_0 _ _)).
  all: lazymatch goal with |- qchain_to ?mm _ _ => apply (qchain_to_frame _ m mm _ _ (unbox _ QC) MU WM) end.
  all: apply Forall_forall; intros e He; pose proof (proj1 (Forall_forall _ _) (unbox _ RG) e ltac:(right; exact He)) as (E1 & E2).
  all: cbn [disjoint_from]; unfold r24 in *; lia.
Qed.

(* [comment removed for export] *)
Lemma drec_pop_qcb : forall (ra0 gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s4r s6r s7r s8r s9r s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) fc (m : mem) (C SB lo cache stack : Z) (j : list byte) (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 : word)
    (b : Z) (ents : list (Z * Z)) (rest : list batch),
  ents <> [] -> qwf SB ((b, ents) :: rest) -> (qbytes ((b, ents) :: rest) < 2^63)%Z -> (0 < SB)%Z ->
  drec_mem m C SB j cache stack ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 ((b, ents) :: rest) ->
  stk asegs m lo (C - 112) -> (r24 SB + 2^32 <= lo)%Z -> (lo <= C - 112)%Z -> (C + 32 <= 2^47)%Z ->
  mem_inv asegs m ->
  evt asegs (drec_at_qcb gp tp s10 s11 F fc C SB lo j cache stack ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 [(C, C + 32)]%Z rest b ents 0 m)
    (MS (mkR ra0 (Z_to_bv 64 (C - 112)) gp tp t0 t1 t2 (Z_to_bv 64 C) (Z_to_bv 64 INST)
             (Z_to_bv 64 (Z.of_nat (length ((b, ents) :: rest)))) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 6722840) (Z_to_bv 64 6723464) s4r
             (Z_to_bv 64 (2^37)) s6r s7r s8r s9r s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x19cfc4) fc None m (seg_rom asegs)).
Proof.
  intros until rest. intros Hne WF HBY HSB DM ST HLO HCL HC MI.
  pose proof (qwf_region _ _ WF) as RG. inversion RG as [|? ? (Hb1 & Hb2) _]; subst. cbn [fst] in Hb1, Hb2. clear RG.
  pose proof (proj2 WF) as HF. inversion HF as [|? ? (_ & _ & _ & Hbl & _) _]; subst. cbn [snd] in Hbl. clear HF.
  eapply evt_cut; [eapply drec_pop; eassumption|].
  intros ms1 (ra' & t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & s7' & s8' & s9' & t3' & t4' & t5' & t6' & m1
              & E1 & MU1 & WM1 & MI1 & DM1 & QB1 & ST1). subst ms1.
  apply (proj1 (qbatch_iff _ _ _ _)) in QB1. destruct QB1 as (BH & (ws & BA & BL & BP) & Ble).
  assert (HEL : (1 <= Z.of_nat (length ents) <= 1021)%Z) by (destruct ents as [|x ents']; [congruence| cbn [length] in *; lia]).
  unfold r24 in *.
  zstep. ifF.
  do 3 zstep.
  pose proof (u64arr_read asegs _ (b + 24) ws 0 _ (Z_to_bv 64 (b + 24)) BA (ent_word_nth ws ents 0 BP ltac:(lia)) ltac:(lia)
                ltac:(unfold wa; f_equal; lia)) as RD.
  zstep. clear RD. do 2 zstep.
  replace (C - 112 + 8)%Z with (C - 104)%Z by lia.
  apply evt_done. unfold drec_at_qcb, qcbrec_entry.
  replace (b + 152 + 8 * Z.of_nat 0)%Z with (b + 152)%Z by lia. replace (16 + Z.of_nat 0)%Z with 16%Z by lia.
  do 14 eexists. split; [reflexivity|].
  split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
  split; [| eassumption].
  apply (proj2 (qbatch_iff _ _ _ _)). split; [eassumption| split; [exists ws; split; [eassumption| split; [exact BL| exact BP]]| exact Ble]].
Qed.

(* [comment removed for export] *)
Lemma drec_pop_deal : forall (ra0 gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s4r s6r s7r s8r s9r s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) fc (m : mem) (ACEIL C SB lo cache stack : Z) (j : list byte) (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 : word)
    (b : Z) (rest : list batch),
  qwf SB ((b, []) :: rest) -> (qbytes ((b, []) :: rest) < 2^63)%Z -> SB_ok ACEIL SB -> (0 <= cache < 2^64)%Z ->
  drec_mem m C SB j cache stack ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 ((b, []) :: rest) ->
  stk asegs m lo (C - 112) -> (r24 SB + 2^32 <= lo)%Z -> (lo <= C - 112)%Z -> (C + 32 <= 2^47)%Z ->
  mem_inv asegs m ->
  evt asegs (drec_at_deal gp tp s10 s11 F fc C SB lo j cache stack ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 [(C, C + 32)]%Z rest b [] m)
    (MS (mkR ra0 (Z_to_bv 64 (C - 112)) gp tp t0 t1 t2 (Z_to_bv 64 C) (Z_to_bv 64 INST)
             (Z_to_bv 64 (Z.of_nat (length ((b, []) :: rest)))) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 6722840) (Z_to_bv 64 6723464) s4r
             (Z_to_bv 64 (2^37)) s6r s7r s8r s9r s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x19cfc4) fc None m (seg_rom asegs)).
Proof.
  intros until rest. intros WF HBY HSBo HCA DM ST HLO HCL HC MI.
  pose proof HSBo as HSBr. destruct HSBr as (HSB1 & _ & HSB3 & _). unfold kHighShadowEnd in HSB1.
  pose proof (qwf_region _ _ WF) as RG. inversion RG as [|? ? (Hb1 & Hb2) _]; subst. cbn [fst] in Hb1, Hb2. clear RG.
  eapply evt_cut; [eapply drec_pop; try eassumption; lia|].
  intros ms1 (ra' & t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & s7' & s8' & s9' & t3' & t4' & t5' & t6' & m1
              & E1 & MU1 & WM1 & MI1 & DM1 & QB1 & ST1). subst ms1.
  unfold r24 in *.
  zstep. first [ifT| dIf_closed].
  pose proof DM1 as (FR1 & SBC1 & _). destruct FR1 as (_ & F2 & _).
  apply (proj1 (rwc_app asegs m1 (C - 104) [C8 (Z_to_bv 64 cache)] [C8 (Z_to_bv 64 stack)])) in F2. destruct F2 as (F2 & _).
  assert (ESP : bv_unsigned (Z_to_bv 64 (C - 112)) = (C - 112)%Z) by (apply unsigned_lit; lia).
  replace (Z_to_bv 64 b) with (Z_to_bv 64 (SB + 24 * 2^32 + (b - SB - 24 * 2^32))) by (f_equal; lia).
  eapply evt_mono; [eapply (drdealloc_frag_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m1 ACEIL SB cache 24
                              (b - SB - 24 * 2^32)); try eassumption; try lia|].
  - qexact_addr.
  - intros ms' (t0'' & t1'' & t2'' & a4'' & a5'' & a6'' & a7'' & t3'' & t4'' & t5'' & t6'' & E).
    replace (SB + 24 * 2^32 + (b - SB - 24 * 2^32))%Z with b in E by lia.
    unfold drec_at_deal, cdealloc_entry.
    exists t0'', t1'', t2'', a4'', a5'', a6'', a7'', (Z_to_bv 64 (Z.of_nat (length (@nil (Z * Z))))), s7', s8', s9', t3'', t4'', t5'', t6'', m1.
    split; [exact E|]. split; [exact MU1|]. split; [exact WM1|]. split; [exact MI1|]. split; [exact DM1|]. split; [exact QB1| exact ST1].
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition drec_at_pop (gp tp s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (C SB lo cache stack : Z)
    (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 : word) (bs : list batch) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (j : list byte) (ra' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' s4' s6' s7' s8' s9' t3' t4' t5' t6' : word) (m' : mem),
    ms' = MS (mkR ra' (Z_to_bv 64 (C - 112)) gp tp t0' t1' t2' (Z_to_bv 64 C) (Z_to_bv 64 INST) (Z_to_bv 64 (Z.of_nat (length bs)))
                  a1' a2' a3' a4' a5' a6' a7' (Z_to_bv 64 6722840) (Z_to_bv 64 6723464) s4' (Z_to_bv 64 (2^37)) s6' s7' s8' s9'
                  s10 s11 t3' t4' t5' t6')
             F (Z_to_bv 64 0x19cfc4) fc None m' (seg_rom asegs)
    /\ munch [(C - 112, C)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ drec_mem m' C SB j cache stack ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 bs /\ stk asegs m' lo (C - 112).

(* [comment removed for export] *)
Lemma drec_prologue : forall ra gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (C SB lo cache stack : Z) (bs : list batch),
  bs <> [] -> (Z.of_nat (length bs) < 2^63)%Z -> qwf SB bs ->
  qcache_rep m C bs -> rw_cells asegs m i_spacebeg [C8 (Z_to_bv 64 SB)] ->
  stk asegs m lo C -> (lo <= C - 112)%Z -> (r24 SB + 2^32 <= lo)%Z -> (0xbc6000 <= lo)%Z -> (C + 32 <= 2^47)%Z ->
  (0 <= cache < 2^64)%Z -> (0 <= stack < 2^64)%Z ->
  mem_inv asegs m ->
  evt asegs (drec_at_pop gp tp s10 s11 F fc C SB lo cache stack ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 bs m)
    (MS (mkR ra (Z_to_bv 64 C) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 QUAR) (Z_to_bv 64 C) (Z_to_bv 64 cache) (Z_to_bv 64 stack) a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 qdorec_entry) fc None m (seg_rom asegs)).
Proof.
  intros until bs. intros Hne HLEN WF QR SBC ST HLO HRl HIMG HC HCA HST MI.
  assert (HL1 : (1 <= Z.of_nat (length bs))%Z) by (destruct bs as [|x bs']; [congruence| cbn [length]; lia]).
  pose proof QR as QR0. apply box in QR0. apply box in SBC.
  apply (proj1 (qcache_rep_iff _ _ _)) in QR. destruct QR as (QH & QC). apply box in QC.
  unfold qdorec_entry.
  pose proof (munch_refl [(C - 112, C)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
  carve_frame 88%nat ST. carve_frame 16%nat ST. carve_frame 8%nat ST.
  do 12 zstep.
  zstep. zstep. zstep. zstep. ifF.
  do 8 zstep.
  apply evt_done. unfold drec_at_pop.
  lazymatch goal with H : rw_cells asegs _ _ [CB 8 ?jk] |- _ => exists jk end.
  do 21 eexists. split; [reflexivity|].
  split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [| eassumption].
  split; [split; [eassumption| split; eassumption]|].
  pose proof (qwf_region _ _ WF) as RG.
  lazymatch goal with |- _ /\ qcache_rep ?mm _ _ =>
    split; [apply (rw_cells_transport asegs _ m mm _ _ (unbox _ SBC) MU WM); cbn [disjoint_from cells_size csize Nat.add Z.of_nat];
            unfold i_spacebeg, g_instance; lia|];
    apply (proj2 (qcache_rep_iff _ _ _)); split; [eassumption|];
    apply (proj2 (qchain_to_0 _ _)); apply (qchain_to_frame _ m mm _ _ (proj1 (qchain_to_0 _ _) (unbox _ QC)) MU WM) end.
  apply Forall_forall. intros e He. pose proof (proj1 (Forall_forall _ _) RG e He) as (E1 & E2).
  cbn [disjoint_from]. unfold r24 in *. lia.
Qed.

(* [comment removed for export] *)
Lemma drec_epi : forall (ra0 gp tp t0 t1 t2 s0r s1r a0 a1 a2 a3 a4 a5 a6 a7 s2r s3r s4r s5r s6r s7r s8r s9r s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) fc (m : mem) (C lo cache stack : Z) (j : list byte) (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 : word),
  drec_frame m C j cache stack ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 -> qcache_rep m C [] ->
  stk asegs m lo (C - 112) -> (lo <= C - 112)%Z -> (0xbc6000 <= lo)%Z -> (C + 32 <= 2^47)%Z ->
  mem_inv asegs m ->
  evt asegs (drec_ret_post gp tp s10 s11 F fc C lo ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 [] m)
    (MS (mkR ra0 (Z_to_bv 64 (C - 112)) gp tp t0 t1 t2 s0r s1r a0 a1 a2 a3 a4 a5 a6 a7 s2r s3r s4r s5r s6r s7r s8r s9r s10 s11
             t3 t4 t5 t6)
        F (Z_to_bv 64 0x19d050) fc None m (seg_rom asegs)).
Proof.
  intros until s9. intros (F1 & F2 & F3) QR ST HLO HIMG HC MI.
  apply box in QR.
  pose proof (munch_refl [] m) as MU. pose proof (wmono_refl asegs m) as WM.
  change (C - 112)%Z with (C + -112)%Z in *. change (C - 104)%Z with (C + -104)%Z in F2. change (C - 88)%Z with (C + -88)%Z in F3.
  do 12 zstep.
  release_frame F1 ST (C + -104)%Z. release_frame F2 ST (C + -88)%Z. release_frame F3 ST C.
  zstep.
  apply evt_done. unfold drec_ret_post.
  do 16 eexists. split; [reflexivity|].
  split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [exact (unbox _ QR)| eassumption].
Qed.

(* [comment removed for export] *)
Lemma drec_empty_spec : forall ra gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (C lo cache stack : Z),
  qcache_rep m C [] ->
  stk asegs m lo C -> (lo <= C - 112)%Z -> (0xbc6000 <= lo)%Z -> (C + 32 <= 2^47)%Z -> (0 <= cache < 2^64)%Z -> (0 <= stack < 2^64)%Z ->
  mem_inv asegs m ->
  evt asegs (drec_ret_post gp tp s10 s11 F fc C lo ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 [(C - 112, C)]%Z m)
    (MS (mkR ra (Z_to_bv 64 C) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 QUAR) (Z_to_bv 64 C) (Z_to_bv 64 cache) (Z_to_bv 64 stack) a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 qdorec_entry) fc None m (seg_rom asegs)).
Proof.
  intros until stack. intros QR ST HLO HIMG HC HCA HST MI.
  pose proof QR as QR0. apply box in QR0.
  apply (proj1 (qcache_rep_iff _ _ _)) in QR. destruct QR as (QH & _). cbn [length Z.of_nat qfirst qlast qbytes map last fold_right] in QH.
  unfold qdorec_entry.
  pose proof (munch_refl [(C - 112, C)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
  carve_frame 88%nat ST. carve_frame 16%nat ST. carve_frame 8%nat ST.
  do 12 zstep.
  zstep. zstep. zstep. zstep. first [ifT| dIf_closed].
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    eapply evt_mono; [eapply (drec_epi _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc mm C lo cache stack);
                      try eassumption; try lia|] end.
  - split; [eassumption| split; eassumption].
  - apply (qcache_rep_frame _ m _ _ _ (unbox _ QR0) MU WM); [cbn [disjoint_from]; lia| constructor].
  - intros ms' (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & E & MU' & WM' & P).
    exists t0', t1', t2', a0', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m'. split; [exact E|].
    split; [| split; [eapply wmono_trans; eassumption| exact P]].
    eapply munch_trans; [eassumption| eapply munch_weaken; [| exact MU']]. intros x _. exact I.
Qed.

(* [comment removed for export] *)
Lemma drec_first_qcb_spec : forall ra gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (C SB lo cache stack : Z) (b : Z) (ents : list (Z * Z)) (rest : list batch),
  ents <> [] -> qwf SB ((b, ents) :: rest) -> (qbytes ((b, ents) :: rest) < 2^56)%Z -> (0 < SB)%Z ->
  qcache_rep m C ((b, ents) :: rest) -> rw_cells asegs m i_spacebeg [C8 (Z_to_bv 64 SB)] ->
  stk asegs m lo C -> (lo <= C - 112)%Z -> (r24 SB + 2^32 <= lo)%Z -> (0xbc6000 <= lo)%Z -> (C + 32 <= 2^47)%Z ->
  (0 <= cache < 2^64)%Z -> (0 <= stack < 2^64)%Z ->
  mem_inv asegs m ->
  evt asegs (fun ms' => exists j, drec_at_qcb gp tp s10 s11 F fc C SB lo j cache stack ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9
                                    [(C - 112, C + 32)]%Z rest b ents 0 m ms')
    (MS (mkR ra (Z_to_bv 64 C) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 QUAR) (Z_to_bv 64 C) (Z_to_bv 64 cache) (Z_to_bv 64 stack) a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 qdorec_entry) fc None m (seg_rom asegs)).
Proof.
  intros until rest. intros Hne WF HBY HSB QR SBC ST HLO HRl HIMG HC HCA HST MI.
  pose proof (qbytes_ge _ _ WF) as QGE.
  eapply evt_cut; [eapply drec_prologue; try eassumption; try lia; discriminate|].
  intros ms1 (j & ra' & t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & s4' & s6' & s7' & s8' & s9' & t3' & t4' & t5' & t6'
              & m1 & E1 & MU1 & WM1 & MI1 & DM1 & ST1). subst ms1.
  eapply evt_mono; [eapply drec_pop_qcb with (cache := cache) (stack := stack); try eassumption; lia|].
  intros ms' P. exists j. destruct P as (t0'' & t1'' & t2'' & a2'' & a3'' & a4'' & a5'' & a6'' & a7'' & t3'' & t4'' & t5'' & t6'' & m'
                                      & E & MU' & WM' & P).
  exists t0'', t1'', t2'', a2'', a3'', a4'', a5'', a6'', a7'', t3'', t4'', t5'', t6'', m'. split; [exact E|].
  split; [| split; [eapply wmono_trans; eassumption| exact P]].
  eapply munch_trans; [eapply munch_weaken; [| exact MU1]| eapply munch_weaken; [| exact MU']]; intros x Hx; cbn [outside] in *; lia.
Qed.

(* [comment removed for export] *)
Lemma drec_first_deal_spec : forall ra gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (ACEIL C SB lo cache stack : Z) (b : Z) (rest : list batch),
  qwf SB ((b, []) :: rest) -> (qbytes ((b, []) :: rest) < 2^56)%Z -> SB_ok ACEIL SB ->
  qcache_rep m C ((b, []) :: rest) -> rw_cells asegs m i_spacebeg [C8 (Z_to_bv 64 SB)] ->
  stk asegs m lo C -> (lo <= C - 112)%Z -> (r24 SB + 2^32 <= lo)%Z -> (0xbc6000 <= lo)%Z -> (C + 32 <= 2^47)%Z ->
  (0 <= cache < 2^64)%Z -> (0 <= stack < 2^64)%Z ->
  mem_inv asegs m ->
  evt asegs (fun ms' => exists j, drec_at_deal gp tp s10 s11 F fc C SB lo j cache stack ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9
                                    [(C - 112, C + 32)]%Z rest b [] m ms')
    (MS (mkR ra (Z_to_bv 64 C) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 QUAR) (Z_to_bv 64 C) (Z_to_bv 64 cache) (Z_to_bv 64 stack) a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 qdorec_entry) fc None m (seg_rom asegs)).
Proof.
  intros until rest. intros WF HBY HSBo QR SBC ST HLO HRl HIMG HC HCA HST MI.
  pose proof (qbytes_ge _ _ WF) as QGE. pose proof HSBo as (HSB & _).
  eapply evt_cut; [eapply drec_prologue; try eassumption; try lia; discriminate|].
  intros ms1 (j & ra' & t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & s4' & s6' & s7' & s8' & s9' & t3' & t4' & t5' & t6'
              & m1 & E1 & MU1 & WM1 & MI1 & DM1 & ST1). subst ms1.
  eapply evt_mono; [eapply drec_pop_deal with (cache := cache) (stack := stack); try eassumption; lia|].
  intros ms' P. exists j. destruct P as (t0'' & t1'' & t2'' & a4'' & a5'' & a6'' & a7'' & s6'' & s7'' & s8'' & s9'' & t3'' & t4'' & t5''
                                      & t6'' & m' & E & MU' & WM' & P).
  exists t0'', t1'', t2'', a4'', a5'', a6'', a7'', s6'', s7'', s8'', s9'', t3'', t4'', t5'', t6'', m'. split; [exact E|].
  split; [| split; [eapply wmono_trans; eassumption| exact P]].
  eapply munch_trans; [eapply munch_weaken; [| exact MU1]| eapply munch_weaken; [| exact MU']]; intros x Hx; cbn [outside] in *; lia.
Qed.

(* [comment removed for export] *)
Lemma drec_next_qcb_spec : forall (ra0 gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) fc (m : mem) (C SB lo cache stack : Z) (j : list byte) (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 : word)
    (b : Z) (ents : list (Z * Z)) (rest : list batch) (i : nat),
  (S i < length ents)%nat -> (0 < b)%Z -> (b + 8192 <= lo)%Z ->
  drec_mem m C SB j cache stack ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 rest -> qbatch m b (qfirst rest) ents ->
  stk asegs m lo (C - 112) -> (lo <= C - 112)%Z -> (C + 32 <= 2^47)%Z ->
  mem_inv asegs m ->
  evt asegs (drec_at_qcb gp tp s10 s11 F fc C SB lo j cache stack ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 [] rest b ents (S i) m)
    (MS (mkR ra0 (Z_to_bv 64 (C - 112)) gp tp t0 t1 t2 (Z_to_bv 64 C) (Z_to_bv 64 INST) a0 a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 6722840) (Z_to_bv 64 6723464) (Z_to_bv 64 b) (Z_to_bv 64 (2^37)) (Z_to_bv 64 (Z.of_nat (length ents)))
             (Z_to_bv 64 (b + 152 + 8 * Z.of_nat i)) (Z_to_bv 64 (Z.of_nat (length ents) + 16)) (Z_to_bv 64 (16 + Z.of_nat i))
             s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x19d010) fc None m (seg_rom asegs)).
Proof.
  intros until i. intros HI Hb0 Hbl DM QB ST HLO HC MI.
  pose proof QB as QB0. apply (proj1 (qbatch_iff _ _ _ _)) in QB0. destruct QB0 as (_ & (ws & BA & BL & BP) & Ble).
  pose proof (munch_refl [] m) as MU. pose proof (wmono_refl asegs m) as WM.
  zstep. zstep. zstep. ifT.
  pose proof (u64arr_read asegs _ (b + 24) ws (Z.of_nat (S i)) _ (Z_to_bv 64 (b + 152 + 8 * Z.of_nat i + 8 + -128)) BA
                ltac:(rewrite Nat2Z.id; exact (ent_word_nth ws ents (S i) BP HI)) ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD.
  zstep. clear RD. do 2 zstep.
  replace (C - 112 + 8)%Z with (C - 104)%Z by lia.
  apply evt_done. unfold drec_at_qcb, qcbrec_entry.
  replace (b + 152 + 8 * Z.of_nat i + 8)%Z with (b + 152 + 8 * Z.of_nat (S i))%Z by lia.
  replace (16 + Z.of_nat i + 1)%Z with (16 + Z.of_nat (S i))%Z by lia.
  do 14 eexists. split; [reflexivity|].
  split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; eassumption.
Qed.

(* [comment removed for export] *)
Lemma drec_next_deal_spec : forall (ra0 gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) fc (m : mem) (ACEIL C SB lo cache stack : Z) (j : list byte) (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 : word)
    (b : Z) (ents : list (Z * Z)) (rest : list batch) (i : nat),
  (S i = length ents)%nat -> (r24 SB <= b)%Z -> (b + 8192 <= r24 SB + 2^32)%Z -> SB_ok ACEIL SB -> (0 <= cache < 2^64)%Z ->
  drec_mem m C SB j cache stack ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 rest -> qbatch m b (qfirst rest) ents ->
  stk asegs m lo (C - 112) -> (r24 SB + 2^32 <= lo)%Z -> (lo <= C - 112)%Z -> (C + 32 <= 2^47)%Z ->
  mem_inv asegs m ->
  evt asegs (drec_at_deal gp tp s10 s11 F fc C SB lo j cache stack ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 [] rest b ents m)
    (MS (mkR ra0 (Z_to_bv 64 (C - 112)) gp tp t0 t1 t2 (Z_to_bv 64 C) (Z_to_bv 64 INST) a0 a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 6722840) (Z_to_bv 64 6723464) (Z_to_bv 64 b) (Z_to_bv 64 (2^37)) (Z_to_bv 64 (Z.of_nat (length ents)))
             (Z_to_bv 64 (b + 152 + 8 * Z.of_nat i)) (Z_to_bv 64 (Z.of_nat (length ents) + 16)) (Z_to_bv 64 (16 + Z.of_nat i))
             s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x19d010) fc None m (seg_rom asegs)).
Proof.
  intros until i. intros HI Hb1 Hb2 HSBo HCA DM QB ST HRl HLO HC MI.
  pose proof HSBo as HSBr. destruct HSBr as (HSB1 & _ & HSB3 & _). unfold kHighShadowEnd, r24 in *.
  pose proof QB as QB0. apply (proj1 (qbatch_iff _ _ _ _)) in QB0. destruct QB0 as (_ & _ & Ble).
  zstep. zstep. zstep. ifF.
  pose proof DM as (FR1 & SBC1 & _). destruct FR1 as (_ & F2 & _).
  apply (proj1 (rwc_app asegs m (C - 104) [C8 (Z_to_bv 64 cache)] [C8 (Z_to_bv 64 stack)])) in F2. destruct F2 as (F2 & _).
  assert (ESP : bv_unsigned (Z_to_bv 64 (C - 112)) = (C - 112)%Z) by (apply unsigned_lit; lia).
  replace (Z_to_bv 64 b) with (Z_to_bv 64 (SB + 24 * 2^32 + (b - SB - 24 * 2^32))) by (f_equal; lia).
  eapply evt_mono; [eapply (drdealloc_frag_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m ACEIL SB cache 24
                              (b - SB - 24 * 2^32)); try eassumption; try lia|].
  - qexact_addr.
  - intros ms' (t0'' & t1'' & t2'' & a4'' & a5'' & a6'' & a7'' & t3'' & t4'' & t5'' & t6'' & E).
    replace (SB + 24 * 2^32 + (b - SB - 24 * 2^32))%Z with b in E by lia.
    unfold drec_at_deal, cdealloc_entry.
    do 15 eexists. exists m. split; [exact E|].
    split; [apply munch_refl|]. split; [apply wmono_refl|]. split; [exact MI|]. split; [exact DM|]. split; [exact QB| exact ST].
Qed.

(* [comment removed for export] *)
Lemma drec_loop_ret_spec : forall (ra0 gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4r s6r s7r s8r s9r s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) fc (m : mem) (C SB lo cache stack : Z) (j : list byte) (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 : word),
  drec_mem m C SB j cache stack ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 [] ->
  stk asegs m lo (C - 112) -> (lo <= C - 112)%Z -> (0xbc6000 <= lo)%Z -> (C + 32 <= 2^47)%Z ->
  mem_inv asegs m ->
  evt asegs (drec_ret_post gp tp s10 s11 F fc C lo ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 [] m)
    (MS (mkR ra0 (Z_to_bv 64 (C - 112)) gp tp t0 t1 t2 (Z_to_bv 64 C) (Z_to_bv 64 INST) a0 a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 6722840) (Z_to_bv 64 6723464) s4r (Z_to_bv 64 (2^37)) s6r s7r s8r s9r s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x19d048) fc None m (seg_rom asegs)).
Proof.
  intros until s9. intros DM ST HLO HIMG HC MI.
  destruct DM as (FR & SBC & QR). pose proof QR as QR0.
  apply (proj1 (qcache_rep_iff _ _ _)) in QR. destruct QR as (QH & _). cbn [length Z.of_nat qfirst qlast qbytes map last fold_right] in QH.
  zstep. zstep. first [ifF| dIf_closed].
  eapply drec_epi; eassumption.
Qed.

(* [comment removed for export] *)
Lemma drec_loop_qcb_spec : forall (ra0 gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4r s6r s7r s8r s9r s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) fc (m : mem) (C SB lo cache stack : Z) (j : list byte) (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 : word)
    (b : Z) (ents : list (Z * Z)) (rest : list batch),
  ents <> [] -> qwf SB ((b, ents) :: rest) -> (qbytes ((b, ents) :: rest) < 2^56)%Z -> (0 < SB)%Z ->
  drec_mem m C SB j cache stack ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 ((b, ents) :: rest) ->
  stk asegs m lo (C - 112) -> (r24 SB + 2^32 <= lo)%Z -> (lo <= C - 112)%Z -> (C + 32 <= 2^47)%Z ->
  mem_inv asegs m ->
  evt asegs (drec_at_qcb gp tp s10 s11 F fc C SB lo j cache stack ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 [(C, C + 32)]%Z rest b ents 0 m)
    (MS (mkR ra0 (Z_to_bv 64 (C - 112)) gp tp t0 t1 t2 (Z_to_bv 64 C) (Z_to_bv 64 INST) a0 a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 6722840) (Z_to_bv 64 6723464) s4r (Z_to_bv 64 (2^37)) s6r s7r s8r s9r s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x19d048) fc None m (seg_rom asegs)).
Proof.
  intros until rest. intros Hne WF HBY HSB DM ST HRl HLO HC MI.
  pose proof (qbytes_ge _ _ WF) as QGE.
  pose proof DM as (_ & _ & QR). apply (proj1 (qcache_rep_iff _ _ _)) in QR. destruct QR as (QH & _).
  zstep. zstep. ifT.
  eapply drec_pop_qcb with (cache := cache) (stack := stack); try eassumption; lia.
Qed.

(* [comment removed for export] *)
Lemma drec_loop_deal_spec : forall (ra0 gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4r s6r s7r s8r s9r s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) fc (m : mem) (ACEIL C SB lo cache stack : Z) (j : list byte) (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 : word)
    (b : Z) (rest : list batch),
  qwf SB ((b, []) :: rest) -> (qbytes ((b, []) :: rest) < 2^56)%Z -> SB_ok ACEIL SB -> (0 <= cache < 2^64)%Z ->
  drec_mem m C SB j cache stack ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 ((b, []) :: rest) ->
  stk asegs m lo (C - 112) -> (r24 SB + 2^32 <= lo)%Z -> (lo <= C - 112)%Z -> (C + 32 <= 2^47)%Z ->
  mem_inv asegs m ->
  evt asegs (drec_at_deal gp tp s10 s11 F fc C SB lo j cache stack ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 [(C, C + 32)]%Z rest b [] m)
    (MS (mkR ra0 (Z_to_bv 64 (C - 112)) gp tp t0 t1 t2 (Z_to_bv 64 C) (Z_to_bv 64 INST) a0 a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 6722840) (Z_to_bv 64 6723464) s4r (Z_to_bv 64 (2^37)) s6r s7r s8r s9r s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x19d048) fc None m (seg_rom asegs)).
Proof.
  intros until rest. intros WF HBY HSBo HCA DM ST HRl HLO HC MI.
  pose proof (qbytes_ge _ _ WF) as QGE.
  pose proof DM as (_ & _ & QR). apply (proj1 (qcache_rep_iff _ _ _)) in QR. destruct QR as (QH & _).
  zstep. zstep. ifT.
  eapply drec_pop_deal with (cache := cache) (stack := stack); try eassumption; lia.
Qed.
