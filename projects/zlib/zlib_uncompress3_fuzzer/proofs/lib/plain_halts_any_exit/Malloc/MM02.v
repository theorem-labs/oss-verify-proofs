(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require ZArith.
From Stdlib Require NArith.
From Stdlib Require List.
From Stdlib Require Lia.
From Stdlib Require Bool.
From stdpp Require gmap.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase.
From LinuxProcessSemantics.LinuxProcessSem Require RiscvSemantics.
From LinuxProcessSemantics.LinuxProcessSem Require MemImageType.
From LinuxProcessSemantics.LinuxProcessSem Require State.
From LinuxProcessSemantics.LinuxProcessSem Require Run.
From LinuxProcessSemantics.Riscv Require Prelude.
From LinuxProcessSemantics.Riscv Require Instr.
From LinuxProcessSemantics.Riscv Require Decode.
From LinuxProcessSemantics.Riscv Require DecodeC.
From LinuxProcessSemantics.Riscv Require Sem.
From LinuxProcessSemantics.Riscv Require Fpu.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit.Lib Require Tac.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit.Lib Require Image.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit.Lib Require ZBridge.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit.Lib Require SysStep.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit.Lib Require Walk.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit.Lib Require ITree.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit.Lib Require Nodes.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit.Lib Require Decode.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit.Lib Require Arr.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit.Common Require SFModel.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit.Malloc Require MM15.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit.Malloc Require F_malloc_entry.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit.Malloc Require MM11.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit.Malloc Require MallocTree.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit.Malloc Require MallocFacts_A.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit.Malloc Require MM12.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit.Malloc Require MallocKit_A.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit.Spec Require SM09. Import SM09.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit.Spec Require Malloc.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit.Spec Require SM08. Import SM08.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit.Spec Require SM01. Import SM01.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit.Malloc Require Malloc_fp.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit.Malloc Require MM14.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit.Malloc Require MM08.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit.Malloc Require MM07.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit.Malloc Require MallocNat.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit.Malloc Require MallocFacts_AS.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit.Malloc Require ASlot_W0.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit.Malloc Require ASlot_W1.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit.Malloc Require ASlot_W9.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit.Malloc Require MM01.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit.Malloc Require MM03.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit.Malloc Require MM05.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit.Malloc Require MM06.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit.Malloc Require ASlot_I.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit.Common Require RunDraw.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit.Malloc Require MM04.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit.Malloc Require MM13.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit.Malloc Require MallocFacts_B.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit.Malloc Require MallocFacts_Bpres.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit.Malloc Require MM10.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit.Malloc Require MM09.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit.Malloc Require F_am_P.
From Stdlib Require Permutation.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module ASlot_M4.
From Stdlib Require Import ZArith. From Stdlib Require Import NArith. From Stdlib Require Import List. From Stdlib Require Import Lia. From Stdlib Require Import Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase. From LinuxProcessSemantics.LinuxProcessSem Require Import RiscvSemantics. From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType. From LinuxProcessSemantics.LinuxProcessSem Require Import State. From LinuxProcessSemantics.LinuxProcessSem Require Import Run.
From LinuxProcessSemantics.Riscv Require Import Prelude. From LinuxProcessSemantics.Riscv Require Import Instr. From LinuxProcessSemantics.Riscv Require Import Decode. From LinuxProcessSemantics.Riscv Require Import DecodeC. From LinuxProcessSemantics.Riscv Require Import Sem. From LinuxProcessSemantics.Riscv Require Import Fpu.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit.Lib Require Import Tac. From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit.Lib Require Import Image. From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit.Lib Require Import ZBridge. From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit.Lib Require Import SysStep. From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit.Lib Require Import Walk. From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit.Lib Require Import ITree. From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit.Lib Require Import Nodes. From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit.Lib Require Import Decode. From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit.Lib Require Import Arr.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit.Common Require Import SFModel.
Import MM15. Import MM15.MallocRep. Import MM15.F_malloc_free. Import MM15.F_malloc_fast. From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit.Malloc Require Import F_malloc_entry. Import MM11. Import MM11.F_malloc_enframe. From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit.Malloc Require Import MallocTree. From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit.Malloc Require Import MallocFacts_A. Import MM12. Import MM12.MallocHINV. From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit.Malloc Require Import MallocKit_A. Import MM12.F_mm_syscalls.
Import MM11. Import MM11.MallocKit_AB.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit.Spec Require SM09. Import SM09. Import SM09.STree. From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit.Spec Require Import Malloc. From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit.Spec Require SM08. Import SM08. Import SM08.MallocCtrl. From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit.Spec Require SM01. Import SM01. Import SM01.Monad.
Import MM15. Import MM15.ProgDeps.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit.Malloc Require Import Malloc_fp. Import MM14. Import MM14.MallocKit_A2. Import MM08. Import MM08.AllocSlot_iface. Import MM08.F_malloc_join. Import MM12. Import MM12.Malloc_iface. Import MM08.F_malloc_bigw. Import MM07. Import MM07.F_malloc_big.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit.Malloc Require Import MallocNat. From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit.Malloc Require Import MallocFacts_AS. Import MM08. Import MM08.MallocKit_A3. From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit.Malloc Require Import ASlot_W0. From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit.Malloc Require Import ASlot_W1. From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit.Malloc Require Import ASlot_W9. Import MM08.ASlot_W10. Import MM01. Import MM01.ASlot_W11. Import MM03. Import MM03.ASlot_W14. Import MM05. Import MM05.ASlot_W15. Import MM01.ASlot_W16. Import MM01.ASlot_W17. Import MM06. Import MM06.ASlot_W18. From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit.Malloc Require Import ASlot_I. Import MM01.ASlot_M0. Import MM01.ASlot_M2. Import MM01.ASlot_M3. Import MM01.ASlot_M4P.
Import MM01.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT}.
Section MMEQ.
Context {R : Type}.
Variables (sc req : Z) (k : mstate -> Z -> Malloc.M R) (bail : Malloc.M R).

Definition mm_after (st2 : mstate) (m : aptr) (c nd : Z) : Z -> Malloc.M R :=
  let size := UNIT * size_class sc in
  let st1 := step_seq (account_bounce sc st2) in
  fun r =>
        if negb (mmap_answer_ok (s_atop st1) (live_ranges st1) nd r) then bad_answer bail else
        if is_err r then free_meta m st1 (fun st2 => as_kq sc k bail st2 None) bail
        else
          let '(st2, rid) := new_region RKGroup r nd st1 in
          let st3 := upd_meta m (m_set_maplen (Z.shiftr nd 12)) st2 in
          let st4 := upd_ctx (fun c => set_mmap_counter (u32 (c_mmap_counter c + 1)) c) st3 in
          let ai := (4096 - UNIT) / size - 1 in
          let ai := if c - 1 <? ai then c - 1 else ai in
          let ai := if ai <? 0 then 0 else ai in
          ag_tail full_lay st4 sc m (rid, 0) c ai (as_kq sc k bail).

Lemma ag_mmap_eq st2 m cnt :
  ag_mmap sc req k bail st2 m cnt =
  (let '(c, nd) := mm_final (UNIT * size_class sc) req (mm_usage1 (step_seq (account_bounce sc st2)) sc (usage st2 sc))
                              (mm_cnt_red sc (UNIT * size_class sc) cnt (mm_usage1 (step_seq (account_bounce sc st2)) sc (usage st2 sc)) (is_bouncing sc st2))
                              (is_bouncing sc st2) in
   SVis (EMmap 0 nd PROT_RW (MAP_PRIVATE + MAP_ANON)) (mm_after st2 m c nd)).
Proof. reflexivity. Qed.
End MMEQ.

Section TAILEQ.
Context {R : Type}.
Variables (sc : Z) (k : mstate -> Z -> Malloc.M R) (bail : Malloc.M R).
Lemma ag_tail_kq_eq stT mm p c ai :
  m_next (get_meta_rec stT mm) = None -> m_prev (get_meta_rec stT mm) = None -> active stT sc = None ->
  ag_tail full_lay stT sc mm p c ai (as_kq sc k bail) = k (st_model stT sc c ai mm p) 0.
Proof.
  intros HN HP HA. unfold ag_tail, as_kq. cbv zeta. cbn [lh_hdr full_lay].
  rewrite as_queue_eq.
  2:{ unfold upd_meta, add_slots. rewrite get_meta_rec_put_same. cbn [m_next m_set_avail].
      rewrite rec_set_slots, rec_put_group, get_meta_rec_put_same. cbn [m_next m_prev m_set_sizeclass m_set_freeable m_set_last_idx m_set_mem m_set_freed m_set_avail].
      rewrite rec_set_usage, rec_hdr_havoc. exact HN. }
  2:{ unfold upd_meta, add_slots. rewrite get_meta_rec_put_same. cbn [m_prev m_set_avail].
      rewrite rec_set_slots, rec_put_group, get_meta_rec_put_same. cbn [m_next m_prev m_set_sizeclass m_set_freeable m_set_last_idx m_set_mem m_set_freed m_set_avail].
      rewrite rec_set_usage, rec_hdr_havoc. exact HP. }
  unfold as_queue_st. cbn [get_head].
  match goal with |- context [active ?X sc] => replace (active X sc) with (active stT sc) by reflexivity end.
  rewrite HA. unfold as_fm_single, st_model. cbn [set_head]. reflexivity.
Qed.
End TAILEQ.

Lemma mm_cnt_red_range sc size cnt u1 nos : 1 <= cnt <= 32 -> 1 <= mm_cnt_red sc size cnt u1 nos <= 32.
Proof.
  intros H. unfold mm_cnt_red.
  destruct (_ && _); [|lia]. destruct (_ && _); [lia|]. destruct (_ && _); [lia|]. destruct (_ && _); [lia|]. destruct (_ && _); lia.
Qed.

Lemma round_up_pg_props x : 0 <= x -> x <= round_up_pg x < x + 4096 /\ round_up_pg x mod 4096 = 0.
Proof.
  intros Hx. unfold round_up_pg. change (PGSZ - 1) with (Z.ones 12). rewrite Z.land_ones by lia. change (2 ^ 12) with 4096.
  Z.div_mod_to_equations. lia.
Qed.

Lemma mm_final_props size req u1 cnt nos c nd :
  1 <= cnt <= 32 -> 16 <= size -> 0 <= req -> req + 4 <= size ->
  mm_final size req u1 cnt nos = (c, nd) ->
  1 <= c <= cnt /\ nd mod 4096 = 0 /\ req + 20 <= nd
  /\ (c = 1 /\ nd = round_up_pg (req + 20) \/ size * c + 16 <= nd /\ nd = round_up_pg (size * c + 16)).
Proof.
  intros HC HS HR HF E. unfold mm_final, mm_small in E. cbv zeta in E.
  pose proof (round_up_pg_props (req + 20) ltac:(lia)) as [R1 R2].
  pose proof (round_up_pg_props (size * cnt + 16) ltac:(nia)) as [N1 N2].
  change (req + IB + UNIT) with (req + 4 + 16) in E. replace (req + 4 + 16) with (req + 20) in E by lia.
  change (size * cnt + UNIT) with (size * cnt + 16) in E.
  destruct (negb nos && (cnt <=? 7)).
  - destruct (Z.ltb_spec (round_up_pg (req + 20)) (size + UNIT)) as [L|G]; cbn [orb] in E.
    + inversion E; subst. unfold UNIT in L. split; [lia|]. split; [lia|]. split; [lia|]. left; auto.
    + destruct ((4 * PGSZ <=? round_up_pg (req + 20)) && (u1 <? 2 * cnt)).
      * inversion E; subst. unfold UNIT in G. split; [lia|]. split; [lia|]. split; [lia|]. left; auto.
      * inversion E; subst. split; [lia|]. split; [lia|]. split; [nia|]. right; split; [nia| reflexivity].
  - inversion E; subst. split; [lia|]. split; [lia|]. split; [nia|]. right; split; [nia| reflexivity].
Qed.

Lemma pos_iter_slots (m p : aptr) (stride : Z) : forall n tb,
  0 < stride ->
  let F := fun acc : Z * gmap aptr (aptr * Z) => let (i, t) := acc in (i + 1, <[aadd p (UNIT + stride * i) := (m, i)]> t) in
  fst (Pos.iter F (0, tb) n) = Z.pos n
  /\ (snd (Pos.iter F (0, tb) n)) !! (aadd p UNIT) = Some (m, 0)
  /\ (forall q, (snd (Pos.iter F (0, tb) n)) !! q <> None -> tb !! q <> None \/ exists i, 0 <= i < Z.pos n /\ q = aadd p (UNIT + stride * i)).
Proof.
  intros n tb HS F. induction n as [|n IH] using Pos.peano_ind.
  - cbn [Pos.iter]. unfold F. rewrite Z.mul_0_r, Z.add_0_r. split; [reflexivity|]. split; [apply lookup_insert_eq|].
    intros q Hq. destruct (decide (q = aadd p UNIT)) as [->|NE]; [right; exists 0; rewrite Z.mul_0_r, Z.add_0_r; split; [lia| reflexivity]|].
    left. rewrite lookup_insert_ne in Hq by congruence. exact Hq.
  - rewrite Pos.iter_succ. destruct IH as (I1 & I2 & I3). fold F. destruct (Pos.iter F (0, tb) n) as [i t] eqn:EP. cbn [fst snd] in I1, I2, I3 |- *.
    unfold F at 1. unfold F at 1. unfold F at 1. cbn [fst snd]. subst i.
    split; [lia|]. split.
    + rewrite lookup_insert_ne; [exact I2|]. unfold aadd. intros E. apply (f_equal snd) in E. cbn in E. unfold UNIT in E. nia.
    + intros q Hq. destruct (decide (q = aadd p (UNIT + stride * Z.pos n))) as [->|NE].
      * right. exists (Z.pos n). split; [lia| reflexivity].
      * rewrite lookup_insert_ne in Hq by congruence. destruct (I3 q Hq) as [X|(i & Hi & ->)]; [left; exact X| right; exists i; split; [lia| reflexivity]].
Qed.

Lemma add_slots_first m p stride c st : 1 <= c -> 0 < stride ->
  (s_slots (add_slots m p stride c st)) !! (aadd p UNIT) = Some (m, 0)
  /\ (forall q, (s_slots (add_slots m p stride c st)) !! q <> None -> (s_slots st) !! q <> None \/ exists i, 0 <= i < c /\ q = aadd p (UNIT + stride * i)).
Proof.
  intros Hc HS. unfold add_slots. cbn [s_slots set_slots].
  destruct c as [|n|n]; [lia| |lia]. cbn [Z.iter].
  destruct (pos_iter_slots m p stride n (s_slots st) HS) as (_ & A & B). split; [exact A| exact B].
Qed.

Definition lowW (iv : Z * Z) : Prop :=
  0 <= fst iv /\ snd iv <= ATOP /\ (snd iv <= 0x19000 \/ 0x1b000 <= fst iv \/ (CTX <= fst iv /\ snd iv <= CTX + 928)).

Definition metaW (st : mstate) (iv : Z * Z) : Prop :=
  (exists q, meta_slot st q /\ fst iv = conc st q /\ snd iv = conc st q + 40) \/ iv = (CTX + 16, CTX + 24).

Lemma failW_shape st mt :
  meta_slot st mt ->
  (forall h, c_free_meta_head (ctx st) = Some h -> meta_slot st h /\ forall p, m_prev (get_meta_rec st h) = Some p -> meta_slot st p) ->
  Forall (metaW st) (failW st mt).
Proof.
  intros MS FL. unfold failW.
  constructor; [left; exists mt; auto|].
  constructor; [right; reflexivity|].
  destruct (c_free_meta_head (ctx st)) as [h|] eqn:FH; [|constructor].
  destruct (FL h eq_refl) as [MSh FP].
  constructor; [left; exists h; auto|].
  destruct (m_prev (get_meta_rec st h)) as [p|] eqn:HP; [|constructor].
  constructor; [left; exists p; auto| constructor].
Qed.

Lemma lowW_disjoint W a n : Forall lowW W -> ATOP <= a -> disjoint_from W a n.
Proof. intros FW Ha. eapply Forall_disjoint_from; [exact FW|]. intros lo hi (H1 & H2 & H3). cbn in *. lia. Qed.

Lemma lowW_disjoint_img W a n : Forall lowW W -> 0x19000 <= a -> a + n <= 0x1b000 -> (a + n <= CTX \/ CTX + 928 <= a) -> disjoint_from W a n.
Proof. intros FW H1 H2 H3. eapply Forall_disjoint_from; [exact FW|]. intros lo hi (X1 & X2 & X3). cbn in *. atop_facts. lia. Qed.

Lemma stS_shape sc st2 : exists f, step_seq (account_bounce sc st2) = upd_ctx f st2
  /\ forall c, c_active (f c) = c_active c /\ c_usage (f c) = c_usage c /\ c_brk (f c) = c_brk c
     /\ c_mmap_counter (f c) = c_mmap_counter c /\ c_free_meta_head (f c) = c_free_meta_head c
     /\ c_avail_meta (f c) = c_avail_meta c /\ c_secret (f c) = c_secret c /\ c_init_done (f c) = c_init_done c
     /\ c_avail_meta_count (f c) = c_avail_meta_count c /\ c_avail_meta_area_count (f c) = c_avail_meta_area_count c
     /\ c_meta_alloc_shift (f c) = c_meta_alloc_shift c /\ c_meta_area_head (f c) = c_meta_area_head c
     /\ c_meta_area_tail (f c) = c_meta_area_tail c /\ c_avail_meta_areas (f c) = c_avail_meta_areas c.
Proof.
  assert (AB : exists g, account_bounce sc st2 = upd_ctx g st2 /\ forall c, g c = c \/ exists v, g c = set_bounces_map (<[sc - 7 := v]> (c_bounces c)) c).
  { unfold account_bounce, set_bounce.
    destruct (sc_in_seq_range sc); [| exists (fun c => c); split; [destruct st2; reflexivity| intros; left; reflexivity]].
    destruct (negb _ && _); [| exists (fun c => c); split; [destruct st2; reflexivity| intros; left; reflexivity]].
    destruct (_ <? 100); (eexists; split; [reflexivity| intros c; right; eexists; reflexivity]). }
  destruct AB as (g & EG & HG).
  rewrite step_seq_eq. rewrite EG.
  destruct (c_seq (ctx (upd_ctx g st2)) =? 255).
  - exists (fun c => set_seq 1 (set_unmap_seq_map ∅ (g c))). split; [destruct st2; reflexivity|].
    intros c. destruct (HG c) as [E|[v E]]; rewrite E; repeat split; reflexivity.
  - exists (fun c => set_seq (c_seq (g c) + 1) (g c)). split; [destruct st2; reflexivity|].
    intros c. destruct (HG c) as [E|[v E]]; rewrite E; repeat split; reflexivity.
Qed.

Section LEVEL.
Context {R : Type}.
Variables (f : nat) (k : mstate -> Z -> Malloc.M R) (bail : Malloc.M R) (o : mem) (s : PState) (Q : R -> PState -> machine_state -> Prop).
Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (m : mem) (st0 st : mstate) (LB : list block) (lo sc req : Z) (errv : word).
Hypothesis AR : AREACH st0 LB.
Hypothesis IS : IST st0 st.
Hypothesis ER : ENTRY_REL st0 st.
Hypothesis AC : ALLC st.
Hypothesis SC : 0 <= sc < 48.
Hypothesis RQ : 0 <= req < 2^32.
Hypothesis FIT : req + 4 <= 16 * size_class sc.
Hypothesis TK : ticks_ok st.
Hypothesis UA : unk_agree st o m.
Hypothesis BL : brk_link_ps st s.
Hypothesis CLO : ATOP <= lo.
Hypothesis LO : lo <= bv_unsigned sp - AS_STACK (S f).
Hypothesis GP : gp = Z_to_bv 64 AGP.
Hypothesis TP : tp = Z_to_bv 64 0x1a620.
Hypothesis A0 : a0 = Z_to_bv 64 sc.
Hypothesis A1 : a1 = Z_to_bv 64 req.
Let F0 : ISTF st LB := MallocFacts_inv4.ist_facts_proof st0 LB st AR IS.

Variable am_pre : mstate -> Prop.
Hypothesis AMP : AMP_AS am_pre.

Lemma errno_lit4 : errno_addr tp = 107900.
Proof. rewrite TP. rewrite unsigned_lit by lia. reflexivity. Qed.
End LEVEL.


End CANSEC1.
End ASlot_M4.

Module ASlot_M5P.
From Stdlib Require Import ZArith. From Stdlib Require Import NArith. From Stdlib Require Import List. From Stdlib Require Import Lia. From Stdlib Require Import Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase. From LinuxProcessSemantics.LinuxProcessSem Require Import RiscvSemantics. From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType. From LinuxProcessSemantics.LinuxProcessSem Require Import State. From LinuxProcessSemantics.LinuxProcessSem Require Import Run.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit.Lib Require Import Tac. From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit.Lib Require Import Image. From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit.Lib Require Import ZBridge. From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit.Lib Require Import SysStep. From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit.Lib Require Import Walk. From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit.Lib Require Import ITree. From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit.Lib Require Import Nodes. From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit.Lib Require Import Decode. From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit.Lib Require Import Arr.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit.Common Require Import SFModel.
Import MM15. Import MM15.MallocRep. Import MM15.F_malloc_free. Import MM15.F_malloc_fast. Import MM11. Import MM11.F_malloc_enframe. From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit.Malloc Require Import MallocTree. From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit.Malloc Require Import MallocFacts_A. Import MM12. Import MM12.MallocHINV. From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit.Malloc Require Import MallocKit_A.
Import MM11. Import MM11.MallocKit_AB.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit.Spec Require SM09. Import SM09. Import SM09.STree. From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit.Spec Require Import Malloc. From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit.Spec Require SM08. Import SM08. Import SM08.MallocCtrl. From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit.Spec Require SM01. Import SM01. Import SM01.Monad.
Import MM15. Import MM15.ProgDeps.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit.Malloc Require Import Malloc_fp. Import MM14. Import MM14.MallocKit_A2. Import MM07. Import MM07.F_malloc_big.
Import MM08. Import MM08.MallocKit_A3. From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit.Malloc Require Import ASlot_W9. Import MM04. Import MM04.ASlot_W13. Import MM03. Import MM03.ASlot_W14. Import MM01. Import MM01.ASlot_M4P.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT}.
Lemma wr8_proj q v st :
  s_regions (wr8 q v st) = s_regions st /\ s_groups (wr8 q v st) = s_groups st /\ s_areas (wr8 q v st) = s_areas st
  /\ s_tick (wr8 q v st) = s_tick st /\ s_next_rid (wr8 q v st) = s_next_rid st /\ s_reserved (wr8 q v st) = s_reserved st
  /\ s_ctx (wr8 q v st) = s_ctx st /\ s_slots (wr8 q v st) = s_slots st /\ s_metas (wr8 q v st) = s_metas st.
Proof. repeat split; reflexivity. Qed.

Lemma cells_wr8_other st q v o : o <> snd q ->
  (r_cells (get_shadow (wr8 q v st) (fst q))) !! o = (r_cells (get_shadow st (fst q))) !! o.
Proof. intros NE. rewrite get_shadow_wr8_same. cbn [r_cells]. rewrite lookup_insert_ne by congruence. reflexivity. Qed.

Lemma cells_wr8_same st q v :
  (r_cells (get_shadow (wr8 q v st) (fst q))) !! (snd q) = Some (Z.land v 255, s_tick st).
Proof. rewrite get_shadow_wr8_same. cbn [r_cells]. apply lookup_insert_eq. Qed.

Lemma hav_wr8 st q v : r_hav (get_shadow (wr8 q v st) (fst q)) = r_hav (get_shadow st (fst q))
  /\ r_havp (get_shadow (wr8 q v st) (fst q)) = r_havp (get_shadow st (fst q)).
Proof. rewrite get_shadow_wr8_same. split; reflexivity. Qed.

Lemma cells_wr8_other' st rid off v o : o <> off ->
  (r_cells (get_shadow (wr8 (rid, off) v st) rid)) !! o = (r_cells (get_shadow st rid)) !! o.
Proof. intros NE. exact (cells_wr8_other st (rid, off) v o NE). Qed.

Lemma hav_wr8_any st q v rid : r_hav (get_shadow (wr8 q v st) rid) = r_hav (get_shadow st rid).
Proof. destruct (N.eq_dec rid (fst q)) as [->|NE]; [apply (proj1 (hav_wr8 st q v))| rewrite get_shadow_wr8_other by exact NE; reflexivity]. Qed.

Lemma havp_wr8_any st q v rid : r_havp (get_shadow (wr8 q v st) rid) = r_havp (get_shadow st rid).
Proof. destruct (N.eq_dec rid (fst q)) as [->|NE]; [apply (proj2 (hav_wr8 st q v))| rewrite get_shadow_wr8_other by exact NE; reflexivity]. Qed.

Lemma shadow_put_meta st m r rid : get_shadow (put_meta m r st) rid = get_shadow st rid.
Proof. reflexivity. Qed.

Lemma cell_read_wr8_other' st rid off v o : o <> off ->
  cell_read (get_shadow (wr8 (rid, off) v st) rid) o = cell_read (get_shadow st rid) o.
Proof. intros NE. exact (cell_read_wr8_other st (rid, off) v o NE). Qed.

Lemma cell_read_wr8_same' st rid off v : ticks_ok st -> 0 <= v < 256 ->
  cell_read (get_shadow (wr8 (rid, off) v st) rid) off = Known v.
Proof. intros TK Hv. exact (cell_read_wr8_same st (rid, off) v TK Hv). Qed.

Lemma cell_read_wr8_same_land st rid off v : ticks_ok st ->
  cell_read (get_shadow (wr8 (rid, off) v st) rid) off = Known (Z.land v 255).
Proof.
  intros TK. replace (wr8 (rid, off) v st) with (wr8 (rid, off) (Z.land v 255) st).
  - apply cell_read_wr8_same'; [exact TK|]. pose proof (Z.land_nonneg v 255). split; [lia|].
    change 255 with (Z.ones 8). rewrite Z.land_ones by lia. apply Z.mod_pos_bound. lia.
  - unfold wr8. cbn [fst snd]. rewrite <- Z.land_assoc. change (Z.land 255 255) with 255. reflexivity.
Qed.

Lemma ticks_ok_same2 st st1 : s_shadow st1 = s_shadow st -> s_tick st1 = s_tick st -> ticks_ok st -> ticks_ok st1.
Proof. intros HS HT [T1 T2]. split; rewrite HS, HT; assumption. Qed.

Section ZH.
Variables (p : aptr) (s : Z).

Lemma zh_proj : forall k i st,
  let st' := zero_hdrs p s i k st in
  s_regions st' = s_regions st /\ s_groups st' = s_groups st /\ s_areas st' = s_areas st
  /\ s_tick st' = s_tick st /\ s_next_rid st' = s_next_rid st /\ s_reserved st' = s_reserved st
  /\ s_ctx st' = s_ctx st /\ s_slots st' = s_slots st /\ s_metas st' = s_metas st.
Proof.
  induction k as [|k IH]; intros i st; cbn [zero_hdrs]; [repeat split; reflexivity|].
  destruct (IH (i + 1) (wr8 (aadd p (UNIT + i * s - 4)) 0 st)) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9).
  rewrite A1, A2, A3, A4, A5, A6, A7, A8, A9. repeat split; reflexivity.
Qed.

Lemma zh_shadow_other q : q <> fst p -> forall k i st, get_shadow (zero_hdrs p s i k st) q = get_shadow st q.
Proof.
  intros NE. induction k as [|k IH]; intros i st; cbn [zero_hdrs]; [reflexivity|].
  rewrite IH. apply get_shadow_wr8_other. exact NE.
Qed.

Lemma zh_hav : forall k i st,
  r_hav (get_shadow (zero_hdrs p s i k st) (fst p)) = r_hav (get_shadow st (fst p))
  /\ r_havp (get_shadow (zero_hdrs p s i k st) (fst p)) = r_havp (get_shadow st (fst p)).
Proof.
  induction k as [|k IH]; intros i st; cbn [zero_hdrs]; [split; reflexivity|].
  destruct (IH (i + 1) (wr8 (aadd p (UNIT + i * s - 4)) 0 st)) as [A B]. rewrite A, B.
  pose proof (hav_wr8 st (aadd p (UNIT + i * s - 4)) 0) as [C D]. cbn [fst aadd] in C, D. rewrite C, D. split; reflexivity.
Qed.

Lemma zh_cells_other o : forall k i st,
  (forall j, i <= j < i + Z.of_nat k -> o <> snd p + UNIT + j * s - 4) ->
  (r_cells (get_shadow (zero_hdrs p s i k st) (fst p))) !! o = (r_cells (get_shadow st (fst p))) !! o.
Proof.
  induction k as [|k IH]; intros i st Ho; cbn [zero_hdrs]; [reflexivity|].
  rewrite IH by (intros j Hj; apply Ho; lia).
  pose proof (cells_wr8_other st (aadd p (UNIT + i * s - 4)) 0 o) as C. cbn [fst snd aadd] in C. apply C. specialize (Ho i ltac:(lia)). lia.
Qed.

Lemma zh_cells_at : 0 < s -> forall k i st j, i <= j < i + Z.of_nat k ->
  (r_cells (get_shadow (zero_hdrs p s i k st) (fst p))) !! (snd p + UNIT + j * s - 4) = Some (0, s_tick st).
Proof.
  intros HS. induction k as [|k IH]; intros i st j Hj; cbn [zero_hdrs]; [lia|].
  destruct (Z.eq_dec j i) as [->|NE].
  - rewrite zh_cells_other by (intros j' Hj'; nia).
    pose proof (cells_wr8_same st (aadd p (UNIT + i * s - 4)) 0) as C. cbn [fst snd aadd] in C.
    replace (snd p + UNIT + i * s - 4) with (snd p + (UNIT + i * s - 4)) by lia. rewrite C. reflexivity.
  - rewrite (IH (i + 1) _ j) by lia. reflexivity.
Qed.

Lemma zh_cell_read_other o : forall k i st,
  (forall j, i <= j < i + Z.of_nat k -> o <> snd p + UNIT + j * s - 4) ->
  cell_read (get_shadow (zero_hdrs p s i k st) (fst p)) o = cell_read (get_shadow st (fst p)) o.
Proof.
  intros k i st Ho. unfold cell_read. rewrite (zh_cells_other o k i st Ho).
  destruct (zh_hav k i st) as [A B]. rewrite A, B. reflexivity.
Qed.

Lemma zh_ticks_ok : forall k i st, ticks_ok st -> ticks_ok (zero_hdrs p s i k st).
Proof. induction k as [|k IH]; intros i st TK; cbn [zero_hdrs]; [exact TK|]. apply IH. apply ticks_ok_wr8. exact TK. Qed.

Lemma zh_cell_read_at : 0 < s -> forall k i st j, ticks_ok st -> i <= j < i + Z.of_nat k ->
  cell_read (get_shadow (zero_hdrs p s i k st) (fst p)) (snd p + UNIT + j * s - 4) = Known 0.
Proof.
  intros HS. induction k as [|k IH]; intros i st j TK Hj; cbn [zero_hdrs]; [lia|].
  destruct (Z.eq_dec j i) as [->|NE].
  - rewrite zh_cell_read_other by (intros j' Hj'; nia).
    pose proof (cell_read_wr8_same st (aadd p (UNIT + i * s - 4)) 0 TK ltac:(lia)) as C. cbn [fst snd aadd] in C.
    replace (snd p + UNIT + i * s - 4) with (snd p + (UNIT + i * s - 4)) by lia. exact C.
  - apply IH; [apply ticks_ok_wr8; exact TK| lia].
Qed.
End ZH.

Lemma existsb_filter_gt12 (l : list (Z * N)) (f : Z * N -> bool) :
  (forall ch, f ch = true -> 12 < fst ch) ->
  existsb f (filter (fun ch : Z * N => Is_true (12 <? fst ch)) l) = existsb f l.
Proof.
  intros Hf. induction l as [|ch l IH]; [reflexivity|].
  rewrite filter_cons. destruct (decide _) as [D|D]; cbn [existsb]; rewrite IH; [reflexivity|].
  destruct (f ch) eqn:E; [|reflexivity]. exfalso. apply D. apply Is_true_true_2. apply Z.ltb_lt. exact (Hf ch E).
Qed.

Lemma stale_hav_add_ge hl bb T t : 12 <= bb -> stale (hav_add 12 T hl) bb t = stale hl bb t.
Proof.
  intros Hb. unfold hav_add, stale. cbn [existsb fst snd].
  replace (bb <? 12) with false by (symmetry; apply Z.ltb_ge; lia). cbn [andb orb].
  apply existsb_filter_gt12. intros [cov t'] H. cbn in H |- *. apply andb_prop in H. destruct H as [H _]. apply Z.ltb_lt in H. lia.
Qed.

Lemma cell_read_hdr_havoc_other st b o :
  snd b mod 16 = 0 -> ~ (snd b <= o < snd b + 12) ->
  cell_read (get_shadow (hdr_havoc b st) (fst b)) o = cell_read (get_shadow st (fst b)) o.
Proof.
  intros B16 Ho. unfold hdr_havoc, upd_shadow. unfold get_shadow at 1. cbn [s_shadow set_shadow].
  rewrite lookup_insert_eq. cbn [default from_option id].
  unfold cell_read. cbn [r_cells r_hav r_havp].
  destruct (Z.eq_dec (o / 16) (snd b / 16)) as [E|NE].
  - rewrite E, lookup_insert_eq. cbn [default from_option id].
    assert (HM : 12 <= o mod 16) by (Z.div_mod_to_equations; lia).
    fold (get_shadow st (fst b)).
    destruct (r_cells (get_shadow st (fst b)) !! o) as [[v t]|]; rewrite stale_hav_add_ge by exact HM; reflexivity.
  - rewrite lookup_insert_ne by congruence. reflexivity.
Qed.

Lemma hav_hdr_havoc_other st b u : u <> snd b / 16 ->
  (r_hav (get_shadow (hdr_havoc b st) (fst b))) !! u = (r_hav (get_shadow st (fst b))) !! u.
Proof.
  intros NE. unfold hdr_havoc, upd_shadow. unfold get_shadow at 1. cbn [s_shadow set_shadow].
  rewrite lookup_insert_eq. cbn [default from_option id r_hav]. rewrite lookup_insert_ne by congruence. reflexivity.
Qed.

Lemma cells_hdr_havoc st b : r_cells (get_shadow (hdr_havoc b st) (fst b)) = r_cells (get_shadow st (fst b))
  /\ r_havp (get_shadow (hdr_havoc b st) (fst b)) = r_havp (get_shadow st (fst b)).
Proof.
  unfold hdr_havoc, upd_shadow. split; rewrite (get_shadow_unfold (set_shadow _ _)); cbn [s_shadow set_shadow]; rewrite lookup_insert_eq; reflexivity.
Qed.

Section NEST.
Variables (st3 : mstate) (g b : aptr) (r : region) (idx jn sc cnt : Z) (mm : aptr).
Let strideg := get_stride (get_meta_rec st3 g).
Let szc := size_class sc.
Let X := snd b + (16 + strideg * idx).
Let p : aptr := (fst b, X).
Let N := UNIT * size_class jn - IB.

Definition nt_stW : mstate :=
  wr8 (fst b, snd b + (16 + strideg * idx) + -3) (Z.lor (Z.land idx 31) 192)
      (put_meta mm (m_set_maplen 0 (get_meta_rec st3 mm)) (enf0_st st3 g b idx)).
Definition nt_stT : mstate := zero_hdrs p (16 * szc) 0 (Z.to_nat (cnt + 1)) nt_stW.

Hypothesis SC : 0 <= sc < 48.
Hypothesis J : 0 <= jn < 48.
Hypothesis CNT : 1 <= cnt <= 32.
Hypothesis SO : slot_ok st3 g b r idx N.
Hypothesis STR : strideg = UNIT * size_class jn.
Hypothesis FITN : 16 * szc * cnt + 16 <= UNIT * size_class jn.
Hypothesis G0 : get_meta_rec st3 mm = meta0.
Hypothesis MSmm : meta_slot st3 mm.
Hypothesis TK3 : ticks_ok st3.
Hypothesis FRESH3 : forall o v t, X <= o < X + strideg - 4 ->
  (r_cells (get_shadow st3 (fst b))) !! o = Some (v, t) -> (t < s_tick st3)%N.

Lemma pp_eq : pp st3 g b idx = p.
Proof. reflexivity. Qed.

Lemma szc_range : 1 <= szc <= 8191.
Proof. unfold szc. apply size_class_range. exact SC. Qed.

Lemma nest_model_eq :
  upd_meta mm (m_set_maplen 0) (nest_layout st3 g idx jn (UNIT * size_class sc) cnt) = nt_stT.
Proof.
  unfold nest_layout. destruct (enf0_st_eq st3 g b r idx jn STR SO) as [E1 E2].
  rewrite (surjective_pairing (enframe_at st3 g idx (UNIT * size_class jn - IB) 0)), E1, E2.
  unfold upd_meta. rewrite rec_zero_hdrs.
  change (get_meta_rec (wr8 _ _ (enf0_st st3 g b idx)) mm) with (get_meta_rec st3 mm).
  rewrite put_meta_zero_hdrs_comm, put_meta_wr8_comm.
  unfold nt_stT, nt_stW, p, X, strideg, szc, aadd, UNIT. cbn [fst snd]. reflexivity.
Qed.

Lemma ntW_proj :
  s_regions nt_stW = s_regions st3 /\ s_groups nt_stW = s_groups st3 /\ s_areas nt_stW = s_areas st3
  /\ s_tick nt_stW = s_tick st3 /\ s_next_rid nt_stW = s_next_rid st3 /\ s_reserved nt_stW = s_reserved st3
  /\ s_ctx nt_stW = s_ctx st3 /\ s_slots nt_stW = s_slots st3.
Proof. repeat split; reflexivity. Qed.

Lemma ntT_proj :
  s_regions nt_stT = s_regions st3 /\ s_groups nt_stT = s_groups st3 /\ s_areas nt_stT = s_areas st3
  /\ s_tick nt_stT = s_tick st3 /\ s_next_rid nt_stT = s_next_rid st3 /\ s_reserved nt_stT = s_reserved st3
  /\ s_ctx nt_stT = s_ctx st3 /\ s_slots nt_stT = s_slots st3.
Proof.
  unfold nt_stT. destruct (zh_proj p (16 * szc) (Z.to_nat (cnt + 1)) 0 nt_stW) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & _).
  rewrite A1, A2, A3, A4, A5, A6, A7, A8. exact ntW_proj.
Qed.

Lemma ntT_rec q : get_meta_rec nt_stT q = if decide (q = mm) then mkMeta None None None 0 0 0 0 0 0 else get_meta_rec st3 q.
Proof.
  unfold nt_stT. rewrite rec_zero_hdrs. unfold nt_stW.
  change (get_meta_rec (wr8 _ _ (put_meta mm (m_set_maplen 0 (get_meta_rec st3 mm)) (enf0_st st3 g b idx))) q)
    with (get_meta_rec (put_meta mm (m_set_maplen 0 (get_meta_rec st3 mm)) (enf0_st st3 g b idx)) q).
  destruct (decide (q = mm)) as [->|NE].
  - rewrite get_meta_rec_put_same, G0. reflexivity.
  - rewrite get_meta_rec_put_other by exact NE. reflexivity.
Qed.

Lemma ntT_active c : active nt_stT c = active st3 c.
Proof. unfold active, ctx. rewrite (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 ntT_proj))))))). reflexivity. Qed.

Lemma ntT_usage i : usage nt_stT i = usage st3 i.
Proof. unfold usage, ctx. rewrite (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 ntT_proj))))))). reflexivity. Qed.

Lemma ntT_ctx : ctx nt_stT = ctx st3.
Proof. unfold ctx. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 ntT_proj))))))). Qed.

Lemma ntT_conc q : conc nt_stT q = conc st3 q.
Proof. unfold conc, get_region. rewrite (proj1 ntT_proj). reflexivity. Qed.

Lemma ntT_shadow_other q : q <> fst b -> get_shadow nt_stT q = get_shadow st3 q.
Proof.
  intros NE. unfold nt_stT. rewrite (zh_shadow_other p (16 * szc) q NE). unfold nt_stW.
  rewrite get_shadow_wr8_other by exact NE.
  change (get_shadow (put_meta mm (m_set_maplen 0 (get_meta_rec st3 mm)) (enf0_st st3 g b idx)) q) with (get_shadow (enf0_st st3 g b idx) q).
  unfold enf0_st, wr16. rewrite !get_shadow_wr8_other by exact NE. reflexivity.
Qed.

Lemma ntW_hav :
  r_hav (get_shadow nt_stW (fst b)) = r_hav (get_shadow st3 (fst b)) /\ r_havp (get_shadow nt_stW (fst b)) = r_havp (get_shadow st3 (fst b)).
Proof.
  unfold nt_stW, enf0_st, wr16.
  split; repeat first [rewrite hav_wr8_any | rewrite havp_wr8_any | rewrite shadow_put_meta]; reflexivity.
Qed.

Lemma ntT_hav :
  r_hav (get_shadow nt_stT (fst b)) = r_hav (get_shadow st3 (fst b)) /\ r_havp (get_shadow nt_stT (fst b)) = r_havp (get_shadow st3 (fst b)).
Proof.
  unfold nt_stT. destruct (zh_hav p (16 * szc) (Z.to_nat (cnt + 1)) 0 nt_stW) as [A B]. unfold p in A, B. cbn [fst] in A, B.
  rewrite A, B. exact ntW_hav.
Qed.

Definition nt_written (o : Z) : Prop :=
  o = X - 3 \/ o = X - 2 \/ o = X - 1 \/ exists j, 0 <= j <= cnt /\ o = X + 12 + j * (16 * szc).

Lemma ntW_cells_other o : o <> X - 3 -> o <> X - 2 -> o <> X - 1 ->
  (r_cells (get_shadow nt_stW (fst b))) !! o = (r_cells (get_shadow st3 (fst b))) !! o.
Proof.
  intros N3 N2 N1. unfold X in *. unfold nt_stW, enf0_st, wr16, aadd. cbn [fst snd]. fold strideg.
  rewrite cells_wr8_other' by lia. rewrite shadow_put_meta.
  rewrite !cells_wr8_other' by lia. reflexivity.
Qed.

Lemma ntW_cell_read_other o : o <> X - 3 -> o <> X - 2 -> o <> X - 1 ->
  cell_read (get_shadow nt_stW (fst b)) o = cell_read (get_shadow st3 (fst b)) o.
Proof.
  intros N3 N2 N1. unfold cell_read. rewrite (ntW_cells_other o N3 N2 N1). destruct ntW_hav as [A B]. rewrite A, B. reflexivity.
Qed.

Lemma ntT_cells_other o : ~ nt_written o ->
  (r_cells (get_shadow nt_stT (fst b))) !! o = (r_cells (get_shadow st3 (fst b))) !! o.
Proof.
  intros NW. unfold nt_stT. change (fst b) with (fst p) at 1.
  rewrite zh_cells_other.
  2:{ intros j Hj E. apply NW. right; right; right. exists j. split; [lia|]. unfold p, UNIT in E. cbn [snd] in E. lia. }
  unfold p. cbn [fst]. apply ntW_cells_other; intros E; apply NW; [left| right; left| right; right; left]; exact E.
Qed.

Lemma ntT_cell_read_other o : ~ nt_written o ->
  cell_read (get_shadow nt_stT (fst b)) o = cell_read (get_shadow st3 (fst b)) o.
Proof.
  intros NW. unfold cell_read. rewrite (ntT_cells_other o NW). destruct ntT_hav as [A B]. rewrite A, B. reflexivity.
Qed.

Lemma ntW_ticks_ok : ticks_ok nt_stW.
Proof.
  unfold nt_stW. apply ticks_ok_wr8.
  assert (TE : ticks_ok (enf0_st st3 g b idx)) by (unfold enf0_st, wr16; repeat apply ticks_ok_wr8; exact TK3).
  eapply ticks_ok_same2; [| | exact TE]; reflexivity.
Qed.

Lemma ntT_cell_read_zero j : 0 <= j <= cnt ->
  cell_read (get_shadow nt_stT (fst b)) (X + 12 + j * (16 * szc)) = Known 0.
Proof.
  intros Hj. pose proof szc_range as SZR. unfold nt_stT. change (fst b) with (fst p).
  replace (X + 12 + j * (16 * szc)) with (snd p + UNIT + j * (16 * szc) - 4) by (unfold p, UNIT; cbn; lia).
  apply zh_cell_read_at; [lia| exact ntW_ticks_ok| lia].
Qed.

Lemma ntT_cell_read_hdr k : 1 <= k <= 3 -> exists v, cell_read (get_shadow nt_stT (fst b)) (X - k) = Known v.
Proof.
  intros Hk. pose proof szc_range as SZR. unfold nt_stT. change (fst b) with (fst p).
  rewrite zh_cell_read_other by (intros j Hj; unfold p, UNIT; cbn; nia).
  unfold p. cbn [fst]. unfold X in *. unfold nt_stW, enf0_st, wr16, aadd. cbn [fst snd]. fold strideg.
  assert (T1 : ticks_ok (wr8 (fst b, snd b + (16 + strideg * idx) + -2) ((snd b + (16 + strideg * idx) - (snd b + 16)) / 16) st3)) by (apply ticks_ok_wr8; exact TK3).
  assert (T2 : ticks_ok (wr8 (fst b, snd b + (16 + strideg * idx) + -2 + 1) (Z.shiftr ((snd b + (16 + strideg * idx) - (snd b + 16)) / 16) 8)
                          (wr8 (fst b, snd b + (16 + strideg * idx) + -2) ((snd b + (16 + strideg * idx) - (snd b + 16)) / 16) st3))) by (apply ticks_ok_wr8; exact T1).
  assert (T3 : ticks_ok (wr8 (fst b, snd b + (16 + strideg * idx) + -3) idx
             (wr8 (fst b, snd b + (16 + strideg * idx) + -2 + 1) (Z.shiftr ((snd b + (16 + strideg * idx) - (snd b + 16)) / 16) 8)
             (wr8 (fst b, snd b + (16 + strideg * idx) + -2) ((snd b + (16 + strideg * idx) - (snd b + 16)) / 16) st3)))) by (apply ticks_ok_wr8; exact T2).
  assert (T4 : ticks_ok (wr8 (fst b, snd b + (16 + strideg * idx) + -3) (Z.land idx 31 + Z.shiftl 0 5)
             (wr8 (fst b, snd b + (16 + strideg * idx) + -3) idx
             (wr8 (fst b, snd b + (16 + strideg * idx) + -2 + 1) (Z.shiftr ((snd b + (16 + strideg * idx) - (snd b + 16)) / 16) 8)
             (wr8 (fst b, snd b + (16 + strideg * idx) + -2) ((snd b + (16 + strideg * idx) - (snd b + 16)) / 16) st3))))) by (apply ticks_ok_wr8; exact T3).
  assert (T5 : ticks_ok (put_meta mm (m_set_maplen 0 (get_meta_rec st3 mm)) (wr8 (fst b, snd b + (16 + strideg * idx) + -3) (Z.land idx 31 + Z.shiftl 0 5)
             (wr8 (fst b, snd b + (16 + strideg * idx) + -3) idx
             (wr8 (fst b, snd b + (16 + strideg * idx) + -2 + 1) (Z.shiftr ((snd b + (16 + strideg * idx) - (snd b + 16)) / 16) 8)
             (wr8 (fst b, snd b + (16 + strideg * idx) + -2) ((snd b + (16 + strideg * idx) - (snd b + 16)) / 16) st3)))))) by (eapply ticks_ok_same2; [| | exact T4]; reflexivity).
  destruct (Z.eq_dec k 3) as [->|N3].
  { eexists. replace (snd b + (16 + strideg * idx) - 3) with (snd b + (16 + strideg * idx) + -3) by lia. apply cell_read_wr8_same_land. exact T5. }
  rewrite cell_read_wr8_other' by lia. rewrite shadow_put_meta.
  rewrite 2 cell_read_wr8_other' by lia.
  destruct (Z.eq_dec k 1) as [->|N1].
  { eexists. replace (snd b + (16 + strideg * idx) - 1) with (snd b + (16 + strideg * idx) + -2 + 1) by lia. apply cell_read_wr8_same_land. exact T1. }
  assert (k = 2) by lia. subst k.
  rewrite cell_read_wr8_other' by lia.
  eexists. replace (snd b + (16 + strideg * idx) - 2) with (snd b + (16 + strideg * idx) + -2) by lia. apply cell_read_wr8_same_land. exact TK3.
Qed.
Lemma slot_geom :
  m_mem (get_meta_rec st3 g) = Some b /\ (s_regions st3) !! (fst b) = Some r /\ r_kind r = RKGroup
  /\ 0 <= snd b /\ snd b mod 16 = 0 /\ 0 <= idx /\ 16 <= strideg /\ strideg mod 16 = 0
  /\ X + strideg <= round_up_pg (r_len r) /\ 0 <= strideg * idx
  /\ (forall b' gh, (s_groups st3) !! b' = Some gh -> fst b' = fst b -> snd b' + 9 <= X - 4 \/ X + strideg - 4 <= snd b').
Proof.
  destruct SO as [Smem Sreg Skind Sb0 Sb16 Sidx Sli Sspan Ss16 Ssmod _ _ _ Snogrp _ _ _ _ _ _ _ _ _].
  fold strideg in Sspan, Ss16, Ssmod, Snogrp.
  assert (SK : 0 <= strideg * idx) by (apply Z.mul_nonneg_nonneg; lia).
  assert (SPAN1 : snd b + 16 + strideg * (idx + 1) <= round_up_pg (r_len r)).
  { eapply Z.le_trans; [|exact Sspan]. apply Z.add_le_mono_l. apply Z.mul_le_mono_nonneg_l; lia. }
  rewrite Z.mul_add_distr_l, Z.mul_1_r in SPAN1.
  repeat (split; [first [assumption | unfold X; lia] |]).
  intros b' gh Hb' Hf. unfold X. destruct (Snogrp b' gh Hb' Hf); lia.
Qed.

Lemma X_mod16 : X mod 16 = 0.
Proof.
  destruct slot_geom as (_ & _ & _ & B0 & B16 & IDX & S16 & SMOD & _).
  unfold X. rewrite Z.add_assoc, <- Z.add_mod_idemp_l, <- (Z.add_mod_idemp_l (snd b)), B16 by lia. cbn [Z.add].
  rewrite <- Z.mul_mod_idemp_l, SMOD by lia. reflexivity.
Qed.

Lemma nt_tail_hyps :
  meta_slot nt_stT mm
  /\ get_meta_rec nt_stT mm = mkMeta None None None 0 0 0 0 0 0
  /\ (s_regions nt_stT) !! (fst p) = Some r
  /\ 0 <= snd p /\ snd p mod 16 = 0 /\ snd p + 16 <= round_up_pg (r_len r)
  /\ (s_groups nt_stT) !! p = None
  /\ (forall b' gh, (s_groups nt_stT) !! b' = Some gh -> fst b' = fst p -> snd b' + 9 <= snd p \/ snd p + 9 <= snd b')
  /\ (forall o v t, snd p <= o < snd p + 12 -> (r_cells (get_shadow nt_stT (fst p))) !! o = Some (v, t) -> (t < s_tick nt_stT)%N)
  /\ s_tick nt_stT = s_tick st3.
Proof.
  destruct slot_geom as (Smem & Sreg & Skind & B0 & B16 & IDX & S16 & SMOD & SPAN & SK & NOG).
  destruct ntT_proj as (PR & PG & PA & PT & _).
  split. { eapply meta_slot_same_areas; [| exact MSmm]. rewrite PA. reflexivity. }
  split. { rewrite ntT_rec. destruct (decide (mm = mm)); [reflexivity| congruence]. }
  split. { rewrite PR. exact Sreg. }
  split. { unfold p, X. cbn. lia. }
  split. { exact X_mod16. }
  split. { unfold p. cbn [snd]. lia. }
  split. { rewrite PG. destruct ((s_groups st3) !! p) as [gh|] eqn:E; [|reflexivity]. exfalso.
           destruct (NOG p gh E eq_refl); unfold p in *; cbn in *; lia. }
  split. { intros b' gh Hb' Hf. rewrite PG in Hb'. unfold p in Hf |- *. cbn in Hf |- *. destruct (NOG b' gh Hb' Hf); lia. }
  split. { intros o v t Ho Hc. rewrite PT. unfold p in Ho, Hc. cbn [fst snd] in Ho, Hc.
           rewrite ntT_cells_other in Hc. 2:{ pose proof szc_range. intros [E|[E|[E|(j & Hj & E)]]]; nia. }
           eapply FRESH3; [| exact Hc]. lia. }
  exact PT.
Qed.

Let stF := st_model nt_stT sc cnt (cnt - 1) mm p.

Lemma ntF_rec_mt : get_meta_rec stF mm = sm_rec sc cnt (cnt - 1) 0 mm p.
Proof.
  apply smg_rec_mt; [exact SC| exact CNT| apply (proj1 (proj2 nt_tail_hyps))| apply (proj1 (proj2 (proj2 (proj2 nt_tail_hyps))))].
Qed.

Lemma ntF_stride : get_stride (get_meta_rec stF mm) = 16 * szc.
Proof. rewrite ntF_rec_mt, smg_stride by (exact SC || exact CNT). rewrite andb_false_r. reflexivity. Qed.

Lemma ntF_shadow_eq : s_shadow stF = s_shadow (hdr_havoc p nt_stT).
Proof. exact (proj1 (proj2 (smg_proj nt_stT sc cnt (cnt - 1) mm p))). Qed.

Lemma ntF_cell_read_other o : ~ (X <= o < X + 12) ->
  cell_read (get_shadow stF (fst b)) o = cell_read (get_shadow nt_stT (fst b)) o.
Proof.
  intros Ho. unfold get_shadow at 1. rewrite ntF_shadow_eq. fold (get_shadow (hdr_havoc p nt_stT) (fst b)).
  change (fst b) with (fst p). apply cell_read_hdr_havoc_other; [exact X_mod16| exact Ho].
Qed.

Lemma ntF_cells o : (r_cells (get_shadow stF (fst b))) !! o = (r_cells (get_shadow nt_stT (fst b))) !! o.
Proof.
  unfold get_shadow at 1. rewrite ntF_shadow_eq. fold (get_shadow (hdr_havoc p nt_stT) (fst b)).
  change (fst b) with (fst p). rewrite (proj1 (cells_hdr_havoc nt_stT p)). reflexivity.
Qed.

Lemma ntF_havp : r_havp (get_shadow stF (fst b)) = r_havp (get_shadow st3 (fst b)).
Proof.
  unfold get_shadow at 1. rewrite ntF_shadow_eq. fold (get_shadow (hdr_havoc p nt_stT) (fst b)).
  change (fst b) with (fst p) at 1. rewrite (proj2 (cells_hdr_havoc nt_stT p)). unfold p. cbn [fst]. apply (proj2 ntT_hav).
Qed.

Lemma ntF_hav u : u <> X / 16 -> (r_hav (get_shadow stF (fst b))) !! u = (r_hav (get_shadow st3 (fst b))) !! u.
Proof.
  intros NE. unfold get_shadow at 1. rewrite ntF_shadow_eq. fold (get_shadow (hdr_havoc p nt_stT) (fst b)).
  change (fst b) with (fst p) at 1. rewrite hav_hdr_havoc_other by exact NE. unfold p. cbn [fst]. rewrite (proj1 ntT_hav). reflexivity.
Qed.

Lemma nt_slot_ok (req : Z) : 0 <= req -> req + 4 <= 16 * szc -> slot_ok stF mm p r 0 req.
Proof.
  intros RQ FIT. pose proof szc_range as SZR.
  destruct slot_geom as (Smem & Sreg & Skind & B0 & B16 & IDX & S16 & SMOD & SPAN & SK & NOG).
  destruct nt_tail_hyps as (TMS & TREC & TREG & TP0 & TP16 & TPEND & TGN & TNOG & TOLD & TTK).
  pose proof ntF_stride as STF.
  pose proof (mask_upto_range' (cnt - 1) ltac:(lia)) as [C1 C2].
  destruct (smg_proj nt_stT sc cnt (cnt - 1) mm p) as (PF1 & PF2 & PF3 & PF4 & _). fold stF in PF1, PF2, PF3, PF4.
  destruct ntT_proj as (PR & PG & PA & PT & _).
  constructor; rewrite ?STF.
  - rewrite ntF_rec_mt. reflexivity.
  - rewrite PF1, PR. exact Sreg.
  - exact Skind.
  - exact TP0.
  - exact TP16.
  - rewrite ntF_rec_mt. cbn [m_last_idx sm_rec]. lia.
  - rewrite ntF_rec_mt. cbn [m_last_idx sm_rec]. lia.
  - rewrite ntF_rec_mt. cbn [m_last_idx sm_rec snd]. replace (cnt - 1 + 1) with cnt by lia. unfold p, X. cbn [snd]. unfold X in SPAN. nia.
  - lia.
  - rewrite Z.mul_comm. apply Z_mod_mult.
  - lia.
  - exact RQ.
  - exact FIT.
  - intros b' gh Hb' Hf. destruct (smg_groups_inv nt_stT sc cnt (cnt - 1) mm p b' gh Hb') as [[-> _]|[NE Hb3]].
    + left. unfold p. cbn [snd]. lia.
    + rewrite PG in Hb3. unfold p in Hf |- *. cbn [fst snd] in Hf |- *. destruct (NOG b' gh Hb3 Hf); [left; lia| right]. clear - CNT STR FITN RQ FIT H; nia.
  - unfold p at 1 2. cbn [fst snd]. replace (X + 16 + 16 * szc * 0 - 4) with (X + 12) by lia.
    rewrite ntF_cell_read_other by lia. replace (X + 12) with (X + 12 + 0 * (16 * szc)) by lia. apply ntT_cell_read_zero. lia.
  - intros off O0 OF. rewrite Z.mul_0_r, Z.add_0_l. rewrite Z.mul_comm, Z_div_mult by lia. lia.
  - unfold p at 2. cbn [fst snd]. replace (X + 16 + 16 * szc * 0) with (snd p + 16) by (unfold p; cbn; lia). change (fst b) with (fst p).
    apply (smg_slot0 nt_stT sc cnt (cnt - 1) 0 mm p SC CNT TREC). rewrite <- ntF_rec_mt, STF. lia.
  - apply (proj1 (smg_meta_slot nt_stT sc cnt (cnt - 1) mm p mm)). exact TMS.
  - rewrite ntF_rec_mt. cbn [m_avail sm_rec]. lia.
  - rewrite ntF_rec_mt. cbn [m_freed sm_rec]. lia.
  - rewrite ntF_rec_mt. cbn [m_freeable sm_rec]. lia.
  - rewrite ntF_rec_mt. cbn [m_maplen sm_rec]. lia.
  - rewrite ntF_rec_mt. cbn [m_sizeclass sm_rec]. lia.
Qed.

Lemma ntF_span_cells o : X + 16 <= o < X + 16 + 16 * szc - 4 ->
  (r_cells (get_shadow stF (fst b))) !! o = (r_cells (get_shadow st3 (fst b))) !! o.
Proof.
  intros Ho. pose proof szc_range. rewrite ntF_cells. apply ntT_cells_other.
  intros [E|[E|[E|(j & Hj & E)]]]; try lia. assert (j = 0 \/ 1 <= j) as [->|J1] by lia; nia.
Qed.

Lemma ntF_span_hav o : X + 16 <= o -> (r_hav (get_shadow stF (fst b))) !! (o / 16) = (r_hav (get_shadow st3 (fst b))) !! (o / 16).
Proof. intros Ho. apply ntF_hav. pose proof X_mod16. Z.div_mod_to_equations. lia. Qed.

Lemma ntF_rdv13 o :
  (r_cells (get_shadow st3 (fst b))) !! (X + 13) = None ->
  (r_hav (get_shadow st3 (fst b))) !! ((X + 13) / 16) = None ->
  (r_havp (get_shadow st3 (fst b))) !! ((X + 13) / 4096) = None ->
  rdv pans_mem o stF (fst b, X + 13) = 0.
Proof.
  intros HC HH HP. pose proof szc_range. unfold rdv. cbn [fst snd]. rewrite ntF_cell_read_other by lia.
  rewrite ntT_cell_read_other. 2:{ intros [E|[E|[E|(j & Hj & E)]]]; nia. }
  unfold cell_read. rewrite HC, HH, HP. cbn. reflexivity.
Qed.

Lemma ntF_unknown off h : 0 <= off ->
  cell_read (get_shadow stF (fst b)) off = Unknown h ->
  grp_hdr_cov stF (fst b) off
  \/ (cell_read (get_shadow st3 (fst b)) off = Unknown h /\ ~ (X - 3 <= off < X) /\ ~ (exists j, 0 <= j <= cnt /\ off = X + 12 + j * (16 * szc))).
Proof.
  intros Ho Hc. pose proof szc_range as SZR.
  destruct (Z_lt_le_dec off X) as [L|GE]; [| destruct (Z_lt_le_dec off (X + 12)) as [L2|GE2]].
  2:{ left. change (fst b) with (fst p). apply smg_grp_hdr_cov; [exact SC|]. unfold p. cbn [snd]. lia. }
  all: right; rewrite ntF_cell_read_other in Hc by lia.
  - destruct (Z_lt_le_dec off (X - 3)) as [L3|GE3].
    + rewrite ntT_cell_read_other in Hc. 2:{ intros [E|[E|[E|(j & Hj & E)]]]; first [lia | nia]. }
      split; [exact Hc|]. split; [lia|]. intros (j & Hj & E). nia.
    + exfalso. destruct (ntT_cell_read_hdr (X - off) ltac:(lia)) as [v Hv]. replace (X - (X - off)) with off in Hv by lia. rewrite Hv in Hc. discriminate.
  - destruct (Z.eq_dec ((off - X - 12) mod (16 * szc)) 0) as [M0|M1];
      [destruct (Z_lt_le_dec cnt ((off - X - 12) / (16 * szc))) as [QB|QS]|].
    + rewrite ntT_cell_read_other in Hc. 2:{ intros [E|[E|[E|(j & Hj & E)]]]; try lia.
        assert (j = (off - X - 12) / (16 * szc)) by (subst off; replace (X + 12 + j * (16 * szc) - X - 12) with (j * (16 * szc)) by lia; rewrite Z_div_mult by lia; reflexivity). lia. }
      split; [exact Hc|]. split; [lia|]. intros (j & Hj & E).
      assert (j = (off - X - 12) / (16 * szc)) by (subst off; replace (X + 12 + j * (16 * szc) - X - 12) with (j * (16 * szc)) by lia; rewrite Z_div_mult by lia; reflexivity). lia.
    + exfalso. pose proof (Z.div_mod (off - X - 12) (16 * szc) ltac:(lia)) as DM. rewrite M0, Z.add_0_r in DM.
      pose proof (Z.div_pos (off - X - 12) (16 * szc) ltac:(lia) ltac:(lia)) as QP.
      pose proof (ntT_cell_read_zero ((off - X - 12) / (16 * szc)) ltac:(lia)) as Hz.
      replace (X + 12 + (off - X - 12) / (16 * szc) * (16 * szc)) with off in Hz by lia. rewrite Hz in Hc. discriminate.
    + rewrite ntT_cell_read_other in Hc. 2:{ intros [E|[E|[E|(j & Hj & E)]]]; try lia.
        apply M1. subst off. replace (X + 12 + j * (16 * szc) - X - 12) with (j * (16 * szc)) by lia. apply Z_mod_mult. }
      split; [exact Hc|]. split; [lia|]. intros (j & Hj & E).
      apply M1. subst off. replace (X + 12 + j * (16 * szc) - X - 12) with (j * (16 * szc)) by lia. apply Z_mod_mult.
Qed.

Lemma ntF_shadow_other q : q <> fst b -> get_shadow stF q = get_shadow st3 q.
Proof.
  intros NE. unfold stF. rewrite (smg_shadow_other nt_stT sc cnt (cnt - 1) mm p q) by exact NE. apply ntT_shadow_other. exact NE.
Qed.
End NEST.


End CANSEC1.
End ASlot_M5P.

Module ASlot_M5D.
From Stdlib Require Import ZArith. From Stdlib Require Import NArith. From Stdlib Require Import List. From Stdlib Require Import Lia. From Stdlib Require Import Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase. From LinuxProcessSemantics.LinuxProcessSem Require Import RiscvSemantics. From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType. From LinuxProcessSemantics.LinuxProcessSem Require Import State. From LinuxProcessSemantics.LinuxProcessSem Require Import Run.
From LinuxProcessSemantics.Riscv Require Import Prelude. From LinuxProcessSemantics.Riscv Require Import Instr. From LinuxProcessSemantics.Riscv Require Import Decode. From LinuxProcessSemantics.Riscv Require Import DecodeC. From LinuxProcessSemantics.Riscv Require Import Sem. From LinuxProcessSemantics.Riscv Require Import Fpu.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit.Lib Require Import Tac. From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit.Lib Require Import Image. From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit.Lib Require Import ZBridge. From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit.Lib Require Import SysStep. From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit.Lib Require Import Walk. From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit.Lib Require Import ITree. From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit.Lib Require Import Nodes. From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit.Lib Require Import Decode. From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit.Lib Require Import Arr.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit.Common Require Import SFModel.
Import MM15. Import MM15.MallocRep. Import MM15.F_malloc_free. Import MM15.F_malloc_fast. From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit.Malloc Require Import F_malloc_entry. Import MM11. Import MM11.F_malloc_enframe. From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit.Malloc Require Import MallocTree. From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit.Malloc Require Import MallocFacts_A. Import MM12. Import MM12.MallocHINV. From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit.Malloc Require Import MallocKit_A. Import MM12.F_mm_syscalls.
Import MM11. Import MM11.MallocKit_AB.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit.Spec Require SM09. Import SM09. Import SM09.STree. From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit.Spec Require Import Malloc. From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit.Spec Require SM08. Import SM08. Import SM08.MallocCtrl. From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit.Spec Require SM01. Import SM01. Import SM01.Monad.
Import MM15. Import MM15.ProgDeps.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit.Malloc Require Import Malloc_fp. Import MM14. Import MM14.MallocKit_A2. Import MM08. Import MM08.AllocSlot_iface. Import MM08.F_malloc_join. Import MM12. Import MM12.Malloc_iface. Import MM08.F_malloc_bigw. Import MM07. Import MM07.F_malloc_big.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit.Malloc Require Import MallocNat. From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit.Malloc Require Import MallocFacts_AS. Import MM08. Import MM08.MallocKit_A3. From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit.Malloc Require Import ASlot_W0. From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit.Malloc Require Import ASlot_W1. From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit.Malloc Require Import ASlot_W9. Import MM08.ASlot_W10. Import MM03. Import MM03.ASlot_W12. Import MM04. Import MM04.ASlot_W13. Import MM03.ASlot_W14. Import MM06. Import MM06.ASlot_W18. From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit.Malloc Require Import ASlot_I. Import MM01. Import MM01.ASlot_M0. Import MM01.ASlot_M2. Import MM01.ASlot_M3. Import MM01.ASlot_M4P. Import ASlot_M4. Import ASlot_M5P.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT}.
Lemma malloc_fp_widen st0 stA stB lo sp sp' a :
  sp' <= sp ->
  (forall rid r, (s_regions stA) !! rid = Some r ->
     exists r', (s_regions stB) !! rid = Some r' /\ r_kind r' = r_kind r /\ r_base r' = r_base r /\ r_len r <= r_len r') ->
  malloc_fp st0 stA lo sp' a -> malloc_fp st0 stB lo sp a.
Proof.
  intros LE HR H. apply (malloc_fp_mono st0 stA stB lo sp a HR).
  destruct H as [[X|X]|X]; [left; left; lia| left; right; exact X| right; exact X].
Qed.

Lemma slot_ok_N st g b r idx n N :
  slot_ok st g b r idx n -> get_stride (get_meta_rec st g) = N + 4 -> 0 <= N -> slot_ok st g b r idx N.
Proof.
  intros SO STR N0. destruct SO. constructor; try assumption; try lia.
  intros off O0 OF. apply so_q16; lia.
Qed.

Lemma outside_app' W1 W2 a : outside (W1 ++ W2) a <-> outside W1 a /\ outside W2 a.
Proof. induction W1 as [|[lo hi] W1 IH]; cbn; [tauto|]. rewrite IH. tauto. Qed.

Lemma arith_prog_dec a c s n : 0 < s ->
  (exists j, 0 <= j <= n /\ a = c + s * j) \/ (forall j, 0 <= j <= n -> a <> c + s * j).
Proof.
  intros Hs. destruct (Z.eq_dec ((a - c) mod s) 0) as [M0|M1].
  - pose proof (Z.div_mod (a - c) s ltac:(lia)) as DM. rewrite M0, Z.add_0_r in DM.
    destruct (Z_le_dec 0 ((a - c) / s)) as [L0|L0]; [destruct (Z_le_dec ((a - c) / s) n) as [L1|L1]|].
    + left. exists ((a - c) / s). split; [lia|]. lia.
    + right. intros j Hj E. assert ((a - c) / s = j) by (subst a; replace (c + s * j - c) with (j * s) by lia; rewrite Z_div_mult by lia; lia). lia.
    + right. intros j Hj E. assert ((a - c) / s = j) by (subst a; replace (c + s * j - c) with (j * s) by lia; rewrite Z_div_mult by lia; lia). lia.
  - right. intros j Hj E. apply M1. subst a. replace (c + s * j - c) with (j * s) by lia. apply Z_mod_mult.
Qed.

Lemma errno_lit5 (tp : word) : tp = Z_to_bv 64 0x1a620 -> errno_addr tp = 107900.
Proof. intros ->. rewrite unsigned_lit by lia. reflexivity. Qed.

Lemma meta_slot_mono stA stB g :
  (forall a, is_Some ((s_areas stA) !! a) -> is_Some ((s_areas stB) !! a)) -> meta_slot stA g -> meta_slot stB g.
Proof.
  intros HA (ar & arr & kk & Ha & Hk & E). destruct (HA ar ltac:(rewrite Ha; eexists; reflexivity)) as [arr' Ha'].
  exists ar, arr', kk. auto.
Qed.

Definition nreq (sc cnt1 : Z) : Z := UNIT + cnt1 * (UNIT * size_class sc) - IB.
Definition ncls (sc cnt1 : Z) : Z := size_to_class (nreq sc cnt1).

Lemma nest_class sc (SC : 0 <= sc < 48) cnt1 : 1 <= cnt1 <= 32 -> size_class sc * UNIT * cnt1 + UNIT <= 2048 ->
  nreq sc cnt1 = size_class sc * 16 * cnt1 + 12 /\ 0 <= ncls sc cnt1 <= 26 /\ 16 * size_class sc * cnt1 + 16 <= UNIT * size_class (ncls sc cnt1)
  /\ sc < ncls sc cnt1 /\ 0 <= nreq sc cnt1 < 2^32 /\ nreq sc cnt1 + 4 <= 16 * size_class (ncls sc cnt1).
Proof.
  intros C1 SM. pose proof (size_class_range sc SC) as SZR.
  assert (E : nreq sc cnt1 = size_class sc * 16 * cnt1 + 12) by (unfold nreq, UNIT, IB; lia).
  assert (QR : 1 <= size_class sc * cnt1 <= 127) by (unfold UNIT in SM; nia).
  pose proof (stc_q_eq (size_class sc) cnt1 SZR C1 ltac:(unfold UNIT in SM; lia)) as EJ.
  assert (EJ' : ncls sc cnt1 = stc_q (size_class sc * cnt1)) by (unfold ncls; rewrite E; exact EJ).
  destruct (nest_class_props (size_class sc * cnt1) QR) as [J1 J2]. rewrite <- EJ' in J1, J2.
  split; [exact E|]. split; [exact J1|]. split; [unfold UNIT; nia|].
  split.
  { destruct (Z_lt_le_dec sc (ncls sc cnt1)) as [L|GE]; [exact L|]. exfalso.
    destruct (Z.eq_dec (ncls sc cnt1) sc) as [EQ|NE]; [rewrite EQ in J2; nia|].
    pose proof (size_class_mono (ncls sc cnt1) sc ltac:(lia) ltac:(lia)). nia. }
  split; [lia|]. nia.
Qed.

Section LEVEL.
Context {R : Type}.
Variables (f : nat) (k : mstate -> Z -> Malloc.M R) (bail : Malloc.M R) (o : mem) (s : PState) (Q : R -> PState -> machine_state -> Prop).
Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (m : mem) (st0 st : mstate) (LB : list block) (lo sc req : Z) (errv : word).
Hypothesis AR : AREACH st0 LB.
Hypothesis IS : IST st0 st.
Hypothesis ER : ENTRY_REL st0 st.
Hypothesis AC : ALLC st.
Hypothesis SC : 0 <= sc < 48.
Hypothesis RQ : 0 <= req < 2^32.
Hypothesis FIT : req + 4 <= 16 * size_class sc.
Hypothesis TK : ticks_ok st.
Hypothesis UA : unk_agree st o m.
Hypothesis BL : brk_link_ps st s.
Hypothesis CLO : ATOP <= lo.
Hypothesis LO : lo <= bv_unsigned sp - AS_STACK (S f).
Hypothesis GP : gp = Z_to_bv 64 AGP.
Hypothesis TP : tp = Z_to_bv 64 0x1a620.
Hypothesis A0 : a0 = Z_to_bv 64 sc.
Hypothesis A1 : a1 = Z_to_bv 64 req.


End LEVEL.


End CANSEC1.
End ASlot_M5D.

Module F_am_K2.
From Stdlib Require Import ZArith. From Stdlib Require Import NArith. From Stdlib Require Import List. From Stdlib Require Import Lia. From Stdlib Require Import Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase. From LinuxProcessSemantics.LinuxProcessSem Require Import RiscvSemantics. From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType. From LinuxProcessSemantics.LinuxProcessSem Require Import State. From LinuxProcessSemantics.LinuxProcessSem Require Import Run.
From LinuxProcessSemantics.Riscv Require Import Prelude. From LinuxProcessSemantics.Riscv Require Import Instr. From LinuxProcessSemantics.Riscv Require Import Decode. From LinuxProcessSemantics.Riscv Require Import DecodeC. From LinuxProcessSemantics.Riscv Require Import Sem. From LinuxProcessSemantics.Riscv Require Import Fpu.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit.Lib Require Import Tac. From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit.Lib Require Import Image. From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit.Lib Require Import ZBridge. From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit.Lib Require Import SysStep. From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit.Lib Require Import Walk. From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit.Lib Require Import Arr. From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit.Lib Require Import ITree. From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit.Lib Require Import Nodes.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit.Common Require Import SFModel.
Import MM14. Import MM14.MallocKit_A2.
Import MM15. Import MM15.MallocRep. Import MM15.F_malloc_free. From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit.Malloc Require Import MallocTree.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit.Spec Require SM09. Import SM09. Import SM09.STree. From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit.Spec Require Import Malloc. From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit.Spec Require SM08. Import SM08. Import SM08.MallocCtrl.
Import MM13. Import MM13.MallocKit_B. Import MM12. Import MM12.MallocModel_B. Import MM07. Import MM07.MallocKit_B2. Import MM14. Import MM14.MallocKit_B3. Import MM07.F_ntf_B.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.

Module A2 := MallocKit_A2.


Section CANSEC1. Context {rc : runConstT}.
Lemma area_in_live : forall st a ar r x, regions_wf st -> (s_areas st) !! a = Some ar -> (s_regions st) !! (fst a) = Some r ->
  conc st a <= x < conc st a + 4096 -> lr_lo r <= x < r_base r + round_up_pg (r_len r).
Proof.
  intros st a ar r x WF Ha Hr Hx. destruct (area_conc st a ar WF Ha) as (ra & Hra & Ca & Sa0 & Sa1 & _).
  rewrite Hr in Hra. assert (ra = r) by congruence. subst ra.
  pose proof (area_lr_lo st a ar r WF Ha Hr). lia.
Qed.

Lemma group_in_live : forall st b gh r x, regions_wf st -> (s_groups st) !! b = Some gh -> (s_regions st) !! (fst b) = Some r ->
  conc st b <= x < conc st b + 9 -> lr_lo r <= x < r_base r + round_up_pg (r_len r).
Proof.
  intros st b gh r x WF Hb Hr Hx. destruct (group_conc st b gh WF Hb) as (rb & Hrb & Cb & Krb & Sb0 & Sb1 & _).
  rewrite Hr in Hrb. assert (rb = r) by congruence. subst rb. rewrite (lr_lo_group r Krb). lia.
Qed.

Definition clear_range (st : mstate) (lo n : Z) : Prop :=
  forall rid r x, (s_regions st) !! rid = Some r -> lr_lo r <= x < r_base r + round_up_pg (r_len r) -> ~ (lo <= x < lo + n).

Lemma clear_range_of_ranges_free st lo n : ranges_free (live_ranges st) lo n = true -> clear_range st lo n.
Proof.
  intros RF rid r x Hr Hx Hin. pose proof (In_live_ranges st rid r Hr) as HI.
  unfold region_live_range in HI. unfold lr_lo in Hx. unfold PGSZ in HI.
  destruct (r_kind r); (pose proof (ranges_free_In _ _ _ _ _ RF HI); lia).
Qed.

Lemma image_clear_of_ranges_free st lo n x : s_reserved st = agent_reserved -> ranges_free (live_ranges st) lo n = true ->
  0x10000 <= x < 0x1b000 -> ~ (lo <= x < lo + n).
Proof.
  intros RS RF Hx Hin. unfold live_ranges in RF. rewrite RS in RF.
  pose proof (ranges_free_In _ _ _ _ _ RF ltac:(apply in_or_app; left; left; reflexivity)).
  pose proof (ranges_free_In _ _ _ _ _ RF ltac:(apply in_or_app; left; right; left; reflexivity)). cbn in *. lia.
Qed.

Lemma round_up_pg_aligned x : x mod 4096 = 0 -> round_up_pg x = x.
Proof. intros H. unfold round_up_pg, PGSZ. change (4096 - 1) with (Z.ones 12). rewrite Z.land_ones by lia. change (2^12) with 4096. Z.div_mod_to_equations. lia. Qed.

Section GROW.
Variables (st : mstate) (m : mem) (rid : N) (r : region) (off : Z).
Hypothesis Hr : (s_regions st) !! rid = Some r.
Hypothesis NK : r_kind r <> RKGroup.
Hypothesis LEN : r_len r = off.
Hypothesis OFF : 0 <= off.
Hypothesis OAL : off mod 4096 = 0.
Hypothesis RF : ranges_free (live_ranges st) (r_base r + off) 4096 = true.
Hypothesis CEIL : r_base r + off + 4096 <= ATOP.
Hypothesis RPOS : forall q rq, (s_regions st) !! q = Some rq -> 0 < r_len rq.
Hypothesis UNIQ : forall q rq, (s_regions st) !! q = Some rq -> q <> rid -> r_kind rq <> RKBrk.

Let r' := mkRegion (r_kind r) (r_base r) (off + 4096).
Let st' := set_regions (<[rid := r']> (s_regions st)) st.

Lemma gr_eq : upd_region rid (fun rg => mkRegion (r_kind rg) (r_base rg) (off + 4096)) st = st'.
Proof. unfold st', upd_region, get_region. rewrite Hr. reflexivity. Qed.
Lemma gr_regions : s_regions st' = <[rid := r']> (s_regions st).
Proof. reflexivity. Qed.
Lemma gr_lookup_inv q rq : (s_regions st') !! q = Some rq -> (q = rid /\ rq = r') \/ (q <> rid /\ (s_regions st) !! q = Some rq).
Proof.
  rewrite gr_regions. intros H. destruct (decide (q = rid)) as [->|NE].
  - rewrite lookup_insert_eq in H. left. split; congruence.
  - rewrite lookup_insert_ne in H by congruence. right. auto.
Qed.
Lemma gr_lookup_old q : q <> rid -> (s_regions st') !! q = (s_regions st) !! q.
Proof. intros. rewrite gr_regions, lookup_insert_ne by congruence. reflexivity. Qed.
Lemma gr_lookup_new : (s_regions st') !! rid = Some r'.
Proof. rewrite gr_regions, lookup_insert_eq. reflexivity. Qed.
Lemma gr_conc q : conc st' q = conc st q.
Proof.
  unfold conc, get_region. destruct (decide (fst q = rid)) as [E|NE].
  - rewrite E, gr_lookup_new, Hr. reflexivity.
  - rewrite gr_lookup_old by exact NE. reflexivity.
Qed.
Lemma gr_ru : round_up_pg (off + 4096) = round_up_pg off + 4096.
Proof. rewrite !round_up_pg_aligned; [lia| exact OAL|]. Z.div_mod_to_equations. lia. Qed.

Lemma ptrs_in_grow P : ptrs_in P st -> ptrs_in P st'.
Proof. intros H. exact H. Qed.
End GROW.

End CANSEC1.
End F_am_K2.

Module F_alloc_meta.
From Stdlib Require Import ZArith. From Stdlib Require Import NArith. From Stdlib Require Import List. From Stdlib Require Import Lia. From Stdlib Require Import Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase. From LinuxProcessSemantics.LinuxProcessSem Require Import RiscvSemantics. From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType. From LinuxProcessSemantics.LinuxProcessSem Require Import State. From LinuxProcessSemantics.LinuxProcessSem Require Import Run.
From LinuxProcessSemantics.Riscv Require Import Prelude. From LinuxProcessSemantics.Riscv Require Import Instr. From LinuxProcessSemantics.Riscv Require Import Decode. From LinuxProcessSemantics.Riscv Require Import DecodeC. From LinuxProcessSemantics.Riscv Require Import Sem. From LinuxProcessSemantics.Riscv Require Import Fpu.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit.Lib Require Import Tac. From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit.Lib Require Import Image. From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit.Lib Require Import ZBridge. From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit.Lib Require Import SysStep. From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit.Lib Require Import Walk. From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit.Lib Require Import Arr. From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit.Lib Require Import ITree. From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit.Lib Require Import Nodes. From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit.Lib Require Import Decode.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit.Common Require Import SFModel.
Import MM14.
Import MM12. Import MM12.F_mm_syscalls. Import MM15. Import MM15.MallocRep. Import MM15.F_malloc_free. From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit.Malloc Require Import MallocTree. From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit.Malloc Require Import MallocFacts_B. From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit.Malloc Require Import MallocFacts_Bpres.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit.Spec Require SM09. Import SM09. Import SM09.STree. From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit.Spec Require Import Malloc. From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit.Spec Require SM08. Import SM08. Import SM08.MallocCtrl. From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit.Spec Require SM01. Import SM01. Import SM01.Monad.
Import MM15. Import MM15.ProgDeps.
Import MM13. Import MM13.MallocKit_B. Import MM12. Import MM12.MallocModel_B. Import MM07. Import MM07.MallocKit_B2. Import MM14. Import MM14.MallocKit_B3. Import MM07.F_ntf_B.
Import MM07. Import MM07.F_am_A. Import MM07.F_am_K. Import F_am_K2. Import MM10. Import MM10.F_am_C. Import MM09. Import MM09.F_am_D. Import MM10.F_am_E. Import MM10.F_am_F. Import MM09.F_am_G. Import MM01. Import MM01.F_am_H. From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit.Malloc Require Import F_am_P.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.

Module A2 := MallocKit_A2.


Section CANSEC1. Context {rc : runConstT}.
Definition magree (C : Z -> Prop) (m m' : mem) : Prop := forall a, 0 <= a < 2^64 -> ~ C a -> m' (wa a) = m (wa a).

Lemma magree_refl C m : magree C m m. Proof. intros a _ _; reflexivity. Qed.
Lemma magree_trans (C1 C2 C3 : Z -> Prop) m1 m2 m3 :
  magree C1 m1 m2 -> magree C2 m2 m3 -> (forall a, C1 a -> C3 a) -> (forall a, C2 a -> C3 a) -> magree C3 m1 m3.
Proof. intros A B I1 I2 a Ha Hc. rewrite (B a Ha) by (intros X; apply Hc, I2, X). apply A; [exact Ha|]. intros X; apply Hc, I1, X. Qed.
Lemma magree_of_munch C W m m' : munch W m m' -> ivs_covered C W -> magree C m m'.
Proof.
  intros MU COV a Ha Hc. apply MU. rewrite wa_unsigned by lia.
  revert COV Hc. clear. induction W as [|[lo hi] W IH]; cbn; intros COV Hc; [exact I|].
  destruct COV as [C1 COV]. split; [| apply IH; assumption]. intros Hin. apply Hc. apply C1. exact Hin.
Qed.

Section ASM.
Variables (R : Type) (k : mstate -> optr -> Malloc.M R) (bail : Malloc.M R) (o : mem) (s : PState) (Q : R -> PState -> machine_state -> Prop).
Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (st : mstate) (lo : Z) (errv : word).
Hypothesis AMP : AMpre st.
Hypothesis TK : ticks_ok st.
Hypothesis BL : brk_link_ps st s.
Hypothesis LO : ATOP <= lo.
Hypothesis LOLE : lo <= bv_unsigned sp - AM_STACK.
Hypothesis GP : gp = Z_to_bv 64 0x1a800.
Hypothesis TP : tp = Z_to_bv 64 0x1a620.

Definition FP (stX : mstate) (a : Z) : Prop := alloc_fp (fun k => k <> RKGroup) stX lo (bv_unsigned sp) a \/ fresh_addr st a.

Lemma FP_am stX a : am_fp stX lo (bv_unsigned sp) a -> FP stX a.
Proof. intros H. left. apply am_fp_alloc_fp. exact H. Qed.

Lemma ETP : errno_addr tp = 0x1a620 - 164.
Proof. rewrite TP, unsigned_lit by lia. reflexivity. Qed.

Lemma FP_mono stX stY a :
  (forall rid r, (s_regions stX) !! rid = Some r -> exists r', (s_regions stY) !! rid = Some r' /\ r_kind r' = r_kind r /\ r_base r' = r_base r /\ r_len r <= r_len r') ->
  FP stX a -> FP stY a.
Proof.
  intros HR [[X|[X|[X|(rid & r & Hr & K & X)]]]|X]; [left; left; exact X| left; right; left; exact X| left; right; right; left; exact X| | right; exact X].
  destruct (HR rid r Hr) as (r' & Hr' & K' & B' & L'). left. right. right. right. exists rid, r'. split; [exact Hr'|]. split; [rewrite K'; exact K|].
  assert (RU : round_up_pg (r_len r) <= round_up_pg (r_len r')).
  { unfold round_up_pg, PGSZ. change (4096 - 1) with (Z.ones 12). rewrite !Z.land_ones by lia. Z.div_mod_to_equations. lia. }
  unfold lr_lo in *. rewrite K', B'. lia.
Qed.

Lemma FP_same stX stY a : s_regions stY = s_regions stX -> FP stX a -> FP stY a.
Proof. intros E. apply FP_mono. intros rid r Hr. exists r. rewrite E. repeat split; auto; lia. Qed.

Lemma FP_below stX a : regions_wf stX -> FP stX a -> a < bv_unsigned sp /\ ~ (AUXV_CELL <= a < AUXV_CELL + 8).
Proof.
  intros (_ & WR & _) [[X|[X|[X|(rid & r & Hr & K & X)]]]|X]; rewrite ?TP in X; unfold AUXV_CELL, LIBC, CTX, AM_STACK in *;
    rewrite ?unsigned_lit in X by lia; [lia| lia| lia| |].
  - destruct (WR _ _ Hr) as (_ & _ & _ & RBC & RF). destruct (reserved_disjoint _ _ RF) as [D1 D2]. pose proof (lr_lo_ge r). atop_facts. lia.
  - pose proof (fresh_image st a X (amp_reserved st AMP)). destruct X as [C _]. atop_facts. lia.
Qed.

Lemma errno_not_amfp stX a : regions_wf stX -> am_fp stX lo (bv_unsigned sp) a -> ~ (errno_addr tp <= a < errno_addr tp + 4).
Proof. intros WF X. rewrite TP. eapply am_fp_not_errno; [exact X| exact WF| exact LO]. Qed.

Lemma brk_am_took X q c : c_brk (ctx (am_took X q c)) = c_brk (ctx X). Proof. reflexivity. Qed.
Lemma am_take_took {RR} (Xst : mstate) (pp : aptr) (kk : mstate -> optr -> Malloc.M RR) (bl : Malloc.M RR) :
  am_take (upd_ctx (fun c => set_avail_meta (Some (aadd pp AREA_HDR)) (set_avail_meta_count NSLOTS c)) Xst) kk bl
  = kk (am_took Xst (aadd pp AREA_HDR) 100) (Some (aadd pp AREA_HDR)).
Proof. reflexivity. Qed.
Lemma conc_am_took X q c y : conc (am_took X q c) y = conc X y. Proof. reflexivity. Qed.
Lemma brk_carve stY p : c_brk (ctx (carve_st stY p)) = c_brk (ctx stY).
Proof.
  unfold carve_st. cbn [ctx upd_ctx s_ctx set_avail_meta_areas set_avail_meta_area_count c_meta_area_tail].
  destruct (c_meta_area_tail (s_ctx stY)); reflexivity.
Qed.
Lemma conc_carve stY p y : conc (carve_st stY p) y = conc stY y.
Proof. unfold conc, get_region. rewrite carve_st_regions. reflexivity. Qed.

Lemma repfoot_low stY a : regions_wf stY -> repfoot stY a -> a < ATOP /\ ~ (errno_addr tp <= a < errno_addr tp + 4).
Proof.
  intros WF H. rewrite ETP. pose proof WF as (_ & WR & _ & WA & WG). atop_facts.
  destruct H as [C|[C|[C|[C|[C|[C|C]]]]]]; unfold CTX, MLOCK, NEED_LOCKS, MallocRep.PAGE_SIZE_A in *; try lia.
  - destruct C as (ak & ar & Hak & Hin). destruct (area_conc stY ak ar WF Hak) as (rra & Hra & Ca & Sa0 & Sa1 & SaL & NKa & RB0 & RBAL & RBC).
    destruct (WR _ _ Hra) as (_ & _ & _ & _ & RF). destruct (reserved_disjoint _ _ RF) as [D1 D2]. atop_facts. lia.
  - destruct C as (b & gh & Hb & Hin). destruct (group_conc stY b gh WF Hb) as (rb & Hrb & Cb & Krb & Sb0 & Sb1 & Al & RB0 & RBC).
    destruct (WR _ _ Hrb) as (_ & _ & _ & _ & RF). destruct (reserved_disjoint _ _ RF) as [D1 D2]. atop_facts. lia.
  - destruct C as (rid & rg & v & Hrg & Krg & Hin & _). destruct (WR _ _ Hrg) as (_ & _ & _ & RBC & RF). destruct (reserved_disjoint _ _ RF) as [D1 D2]. atop_facts. lia.
Qed.

Lemma live_ranges_same stA stB : s_regions stB = s_regions stA -> s_reserved stB = s_reserved stA -> live_ranges stB = live_ranges stA.
Proof. intros E1 E2. unfold live_ranges. rewrite E1, E2. reflexivity. Qed.

Lemma fresh_of_ranges_free stY x L a :
  s_regions stY = s_regions st -> s_reserved stY = s_reserved st ->
  ranges_free (live_ranges stY) x L = true -> x + L <= ATOP -> x <= a < x + L -> fresh_addr st a.
Proof.
  intros E1 E2 RF XC Ha. split; [lia|]. rewrite (live_ranges_same st stY E1 E2) in RF.
  eapply ranges_free_sub; [exact RF| lia| lia| lia].
Qed.

Lemma image_range_clear stY x L : s_reserved stY = agent_reserved -> ranges_free (live_ranges stY) x L = true -> 0 < L ->
  x + L <= 0x10000 \/ 0x1b000 <= x.
Proof.
  intros RS RF HL. unfold live_ranges in RF. rewrite RS in RF.
  pose proof (ranges_free_In _ _ _ _ _ RF ltac:(apply in_or_app; left; left; reflexivity)).
  pose proof (ranges_free_In _ _ _ _ _ RF ltac:(apply in_or_app; left; right; left; reflexivity)). cbn in *. lia.
Qed.
End ASM.

End CANSEC1.
End F_alloc_meta.

Module F_free_spec.
From Stdlib Require Import ZArith. From Stdlib Require Import NArith. From Stdlib Require Import List. From Stdlib Require Import Lia. From Stdlib Require Import Bool. From Stdlib Require Import Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase. From LinuxProcessSemantics.LinuxProcessSem Require Import RiscvSemantics. From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType. From LinuxProcessSemantics.LinuxProcessSem Require Import State. From LinuxProcessSemantics.LinuxProcessSem Require Import Run.
From LinuxProcessSemantics.Riscv Require Import Prelude. From LinuxProcessSemantics.Riscv Require Import Instr. From LinuxProcessSemantics.Riscv Require Import Decode. From LinuxProcessSemantics.Riscv Require Import DecodeC. From LinuxProcessSemantics.Riscv Require Import Sem. From LinuxProcessSemantics.Riscv Require Import Fpu.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit.Lib Require Import Tac. From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit.Lib Require Import Image. From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit.Lib Require Import ZBridge. From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit.Lib Require Import SysStep. From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit.Lib Require Import Walk. From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit.Lib Require Import Arr. From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit.Lib Require Import ITree. From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit.Lib Require Import Nodes. From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit.Lib Require Import Decode.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit.Common Require Import SFModel.
Import MM15. Import MM15.MallocRep. Import MM15.F_malloc_free. From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit.Malloc Require Import MallocTree. Import MM13. Import MM13.MallocBlocks. Import MM12. Import MM12.MallocHINV. From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit.Malloc Require Import MallocFacts_B. Import MM12.MallocFacts_B_reach. Import MM12.Malloc_iface.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit.Spec Require SM09. Import SM09. Import SM09.STree. From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit.Spec Require Import Malloc. From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit.Spec Require SM08. Import SM08. Import SM08.MallocCtrl. From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit.Spec Require SM01. Import SM01. Import SM01.Monad.
Import MM15. Import MM15.ProgDeps.
Import MM13. Import MM13.MallocKit_B. Import MM07. Import MM07.MallocKit_B2. From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit.Malloc Require Import MallocFacts_Bpres. Import MM04. Import MM04.F_ntf. Import MM09. Import MM09.F_free_K. Import MM01. Import MM01.F_free.
Import MM09.
Import MM01.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit.Common Require Import RunDraw.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT}.
Lemma lb_remove_lbrm LB (p : bptr) A n : List.NoDup (map blk_slot LB) -> In (p, A, n) LB ->
  lb_remove p LB = lbrm LB (p, A, n).
Proof.
  intros ND Hin. unfold lb_remove, lbrm. apply filter_ext_in. intros x Hx.
  unfold bptr_eqb, blk_id, blk_slot. cbn [fst snd].
  destruct (aptr_eqb_spec' (fst (fst (fst x))) (fst p)) as [E|NE]; cbn [andb negb].
  - pose proof (NoDup_map_inj_in blk_slot LB ND x (p, A, n) Hx Hin E) as ->. cbn. rewrite Z.eqb_refl. cbn. tauto.
  - tauto.
Qed.

Lemma NoDup_map_perm {A B} (f : A -> B) (l l' : list A) : Permutation l l' -> List.NoDup (map f l) -> List.NoDup (map f l').
Proof. intros P ND. eapply Permutation_NoDup; [apply Permutation_map; exact P| exact ND]. Qed.

Lemma lbrm_perm LB LB' blk : Permutation LB LB' -> Permutation (lbrm LB blk) (lbrm LB' blk).
Proof. intros P. unfold lbrm. apply filter_Permutation. exact P. Qed.

Lemma In_lbrm_perm LB LB' blk b : Permutation LB LB' -> In b (lbrm LB blk) -> In b (lbrm LB' blk).
Proof. intros P H. eapply Permutation_in; [apply lbrm_perm; exact P| exact H]. Qed.

Section FP.
Variables (st st' : mstate) (LB0 : list block) (blk : block) (lo sp : Z) (m m' : mem).
Hypothesis C : CINV st LB0.
Hypothesis LO : ATOP <= lo.
Hypothesis LS : lo <= sp.
Hypothesis BLKR : forall blk', In blk' (lbrm LB0 blk) -> exists r', (s_regions st') !! fst (blk_slot blk') = Some r'.
Hypothesis SHR : forall rid r', (s_regions st') !! rid = Some r' -> (s_regions st) !! rid = Some r'.

Let FPT := fun a => free_fp st lo sp a \/ DROPPED st st' a \/ 107900 <= a < 107904.
End FP.

End CANSEC1.
End F_free_spec.

Module Malloc_ifaceP.
From Stdlib Require Import ZArith. From Stdlib Require Import NArith. From Stdlib Require Import List. From Stdlib Require Import Lia. From Stdlib Require Import Bool. From Stdlib Require Import Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase. From LinuxProcessSemantics.LinuxProcessSem Require Import RiscvSemantics. From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType. From LinuxProcessSemantics.LinuxProcessSem Require Import State. From LinuxProcessSemantics.LinuxProcessSem Require Import Run.
From LinuxProcessSemantics.Riscv Require Import Prelude. From LinuxProcessSemantics.Riscv Require Import Instr. From LinuxProcessSemantics.Riscv Require Import Decode. From LinuxProcessSemantics.Riscv Require Import DecodeC. From LinuxProcessSemantics.Riscv Require Import Sem. From LinuxProcessSemantics.Riscv Require Import Fpu.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit.Lib Require Import Tac. From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit.Lib Require Import Image. From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit.Lib Require Import ZBridge. From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit.Lib Require Import SysStep. From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit.Lib Require Import Walk. From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit.Lib Require Import ITree. From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit.Lib Require Import Nodes. From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit.Lib Require Import Decode. From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit.Lib Require Import Arr.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit.Common Require Import SFModel.
Import MM15. Import MM15.MallocRep. From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit.Malloc Require Import MallocTree. From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit.Malloc Require Import MallocFacts_A. From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit.Malloc Require Import MallocKit_A. Import MM12. Import MM12.Malloc_iface. Import MM11. Import MM11.MallocKit_AB. Import MM15.InitMem.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit.Spec Require SM09. Import SM09. Import SM09.STree. From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit.Spec Require Import Malloc. From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit.Spec Require SM08. Import SM08. Import SM08.MallocCtrl. From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit.Spec Require SM01. Import SM01. Import SM01.Monad.
Import MM15. Import MM15.ProgDeps.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit.Malloc Require Import Malloc_fp. Import MM01. Import MM01.F_malloc_top. Import MM07. Import MM07.F_malloc_big.
Import MM01.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT}.
Lemma rw_cells_app : forall segs m A cs1 cs2,
  rw_cells segs m A (cs1 ++ cs2) <->
  rw_cells segs m A cs1 /\ rw_cells segs m (A + Z.of_nat (cells_size cs1)) cs2.
Proof.
  intros segs m A cs1 cs2. unfold rw_cells, cells_at.
  rewrite cells_wf_app, cells_bytes_app, cells_size_app, bytes_at_app.
  split.
  - intros [[[W1 W2] [B1 B2]] WR].
    pose proof (cells_bytes_length cs1 W1) as L1. rewrite L1 in B2.
    destruct WR as (HA & HN & HW).
    split; [split; [split; assumption|] | split; [split; assumption|]].
    + split; [lia|]. split; [lia|]. intros i Hi. apply HW. lia.
    + split; [lia|]. split; [lia|]. intros i Hi.
      replace (A + Z.of_nat (cells_size cs1) + i)%Z with (A + (Z.of_nat (cells_size cs1) + i))%Z by lia. apply HW. lia.
  - intros [[[W1 B1] (HA1 & HN1 & HW1)] [[W2 B2] (HA2 & HN2 & HW2)]].
    pose proof (cells_bytes_length cs1 W1) as L1.
    split; [split; [split; assumption|] |].
    + split; [exact B1|]. rewrite L1. exact B2.
    + split; [lia|]. split; [lia|]. intros i Hi. destruct (Z_lt_dec i (Z.of_nat (cells_size cs1))).
      * apply HW1. lia.
      * replace (A + i)%Z with (A + Z.of_nat (cells_size cs1) + (i - Z.of_nat (cells_size cs1)))%Z by lia. apply HW2. lia.
Qed.

End CANSEC1.
End Malloc_ifaceP.
