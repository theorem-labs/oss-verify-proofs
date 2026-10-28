(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP Frame.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.MallocU Require Import RMallocRep RMallocTree RMalloc_iface.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec Require Import Prelim STree Malloc Monad Stdio SjModel Target Prog.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Sj Require Import SjS1Out SjAlloc SjStage2 SjLeaves SjNumber SjTape SjTapeInv SjTapeList.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.P Require Import Sj_stage1_kit.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.U Require Import Layout Sj_iface Sj_kit Sj_h_kit Sj_stage2_iface.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.P Require Import Rnd.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.U Require Import Sj_num_iface Sj_stage2_defs Sj_stage2_numkitr.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Ceiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Definition s2_rebase (E : s2env) (m : mem) : s2env :=
  mkS2Env (e_ra E) (e_sp E) (e_gp E) (e_tp E) (e_s0 E) (e_s1 E) (e_s2 E) (e_s3 E) (e_s4 E) (e_s5 E) (e_s6 E) (e_s7 E) (e_s8 E)
          (e_s9 E) (e_s10 E) (e_s11 E) (e_lo E) (e_THIS E) (e_DOC E) (e_IDX E) (e_BUF E) (e_TAPE E) (e_SBUF E) (e_OC E) (e_IA E)
          (e_bs E) (e_idxs E) (e_iws E) (e_tcap E) (e_scap E) (e_vptr E) (e_p12 E) (e_nxt0 E) (e_p28 E) (e_capv E) (e_p50 E)
          (e_dcap E) (e_j80 E) m (e_tws E) (e_sbs E).

Lemma env_ok_rebase : forall E m, env_ok E -> env_ok (s2_rebase E m).
Proof. intros E m []. constructor; assumption. Qed.

Definition s2_region (E : s2env) (a : Z) : Prop :=
  (e_SP E <= a < bv_unsigned (e_sp E)) \/ (e_THIS E <= a < e_THIS E + 96) \/ (e_DOC E <= a < e_DOC E + 24)
  \/ (e_IDX E <= a < e_IDX E + 4 * Z.of_nat (length (e_iws E))) \/ (e_BUF E <= a < e_BUF E + e_len E + 64)
  \/ (e_TAPE E <= a < e_TAPE E + 8 * e_tcap E) \/ (e_SBUF E <= a < e_SBUF E + e_scap E)
  \/ (e_OC E <= a < e_OC E + 8192) \/ (e_IA E <= a < e_IA E + 1024).

Lemma MEMI_rebase_agree : forall (P : Z -> Prop) E nxt sl sc fc m m',
  agree_on P m m' -> (forall a, s2_region E a -> P a) -> cells_size sl = 80%nat ->
  MEMI E nxt sl sc fc m -> mem_inv usegs m' -> stk usegs m' (e_lo E) (e_SP E) ->
  MEMI (s2_rebase E m') nxt sl sc fc m'.
Proof.
  intros P E nxt sl sc fc m m' AG HR HSL (FRM & FR & IMPL & DOCC & IDXA & BUFRO & TAPEW & SBUFW & (ocs & OCA & OCL & OCR) & (ias & IAA & IAL & IAR) & MI & MU & WM & ST & TIMG) MI' ST'.
  unfold MEMI. change (e_SP (s2_rebase E m')) with (e_SP E). change (frame_hi (s2_rebase E m')) with (frame_hi E).
  change (impl_cells (s2_rebase E m') nxt) with (impl_cells E nxt). change (doc_cells (s2_rebase E m')) with (doc_cells E).
  cbn [s2_rebase e_THIS e_DOC e_IDX e_BUF e_TAPE e_SBUF e_OC e_IA e_iws e_bs e_tcap e_scap e_lo e_m0].
  split; [exact FRM|].
  split. { eapply rw_cells_agree; [exact AG| exact FR|]. intros a Ha. apply HR. left.
           rewrite cells_size_app, HSL in Ha. unfold frame_hi in Ha. cbn [cells_size csize Nat.add] in Ha. lia. }
  split. { eapply rw_cells_agree; [exact AG| exact IMPL|]. intros a Ha. apply HR. right; left.
           unfold impl_cells in Ha. cbn [cells_size csize Nat.add] in Ha. lia. }
  split. { eapply rw_cells_agree; [exact AG| exact DOCC|]. intros a Ha. apply HR. right; right; left.
           unfold doc_cells in Ha. cbn [cells_size csize Nat.add] in Ha. lia. }
  split. { eapply u32arr_agree; [exact AG| exact IDXA|]. intros a Ha. apply HR. do 3 right; left. lia. }
  split. { eapply bytes_at_agree; [exact AG| exact BUFRO|]. intros a Ha. apply HR. do 4 right; left.
           rewrite padded_bytes_blen in Ha. lia. }
  split. { eapply wr_at_agree; [exact AG| exact TAPEW|]. intros a Ha. apply HR. do 5 right; left. lia. }
  split. { eapply wr_at_agree; [exact AG| exact SBUFW|]. intros a Ha. apply HR. do 6 right; left. lia. }
  split. { exists ocs. split; [|split; assumption]. eapply u32arr_agree; [exact AG| exact OCA|]. intros a Ha. apply HR. do 7 right; left. lia. }
  split. { exists ias. split; [|split; assumption]. eapply u8arr_agree; [exact AG| exact IAA|]. intros a Ha. apply HR. do 8 right. lia. }
  split; [exact MI'|]. split; [apply munch_refl|]. split; [apply wmono_refl|]. split; [exact ST'|].
  destruct TIMG as (T1 & T2 & T3 & T4 & S1 & S2 & SB). unfold tape_img. cbn [s2_rebase e_tws e_sbs e_TAPE e_SBUF e_tcap e_scap].
  split. { eapply bytes_at_agree; [exact AG| exact T1|]. intros a Ha. apply HR. do 5 right; left. rewrite twords_length in Ha. lia. }
  split. { eapply bytes_at_agree; [exact AG| exact T2|]. intros a Ha. apply HR. do 6 right; left. rewrite zbytes_length in Ha. lia. }
  split; [exact T3|]. split; [exact T4|].
  split. { eapply stk_agree; [exact AG| exact S1|]. intros a Ha. apply HR. do 5 right; left. lia. }
  split. { eapply stk_agree; [exact AG| exact S2|]. intros a Ha. apply HR. do 6 right; left. lia. }
  exact SB.
Qed.

Lemma rk_CB_split2 : forall m A (n1 n2 : nat) (bs : list byte), rw_cells usegs m A [CB (n1 + n2) bs] ->
  rw_cells usegs m A [CB n1 (firstn n1 bs)] /\ rw_cells usegs m (A + Z.of_nat n1) [CB n2 (skipn n1 bs)].
Proof.
  intros m A n1 n2 bs H.
  assert (L : length bs = (n1 + n2)%nat) by (destruct H as [[[HL _] _] _]; exact HL).
  assert (H2 : rw_cells usegs m A ([CB n1 (firstn n1 bs)] ++ [CB n2 (skipn n1 bs)])).
  { eapply rw_cells_recast; [exact H| | |].
    - cbn. rewrite firstn_length, skipn_length. repeat split; lia.
    - cbn [app cells_bytes cbytes]. rewrite !app_nil_r. apply firstn_skipn.
    - cbn. lia. }
  apply (proj1 (rw_cells_app usegs m A _ _)) in H2. cbn [cells_size csize Nat.add] in H2. rewrite Nat.add_0_r in H2. exact H2.
Qed.

Lemma zbytes_skipn : forall k l, skipn k (zbytes l) = zbytes (skipn k l).
Proof. intros k l. unfold zbytes. apply skipn_map. Qed.

Lemma padded_src : forall (m : mem) A bs o, bytes_at usegs m A (padded_bytes bs) -> 0 <= o <= blen bs ->
  bytes_at usegs m (A + o) (zbytes (skipn (Z.to_nat o) bs)).
Proof.
  intros m A bs o H Ho. unfold padded_bytes in H. apply bytes_at_app in H. destruct H as [H _].
  apply (bytes_at_skipn m A (zbytes bs) (Z.to_nat o)) in H; [| rewrite zbytes_length; unfold blen in Ho; lia].
  rewrite Z2Nat.id in H by lia. rewrite zbytes_skipn in H. exact H.
Qed.

Lemma blen_skipn : forall bs o, 0 <= o <= blen bs -> blen (skipn (Z.to_nat o) bs) = blen bs - o.
Proof. intros bs o Ho. unfold blen in *. rewrite length_skipn. lia. Qed.

Lemma bytes_ok_skipn : forall bs k, bytes_ok bs -> bytes_ok (skipn k bs).
Proof.
  intros bs k H. unfold bytes_ok in *. rewrite <- (firstn_skipn k bs) in H. apply Forall_app in H. exact (proj2 H).
Qed.

Lemma crs_assemble : forall (m : mem) CP t,
  rw_cells usegs m CP [CB (Z.to_nat (blen t)) (zbytes t)] ->
  rw_cells usegs m (CP + blen t) [CB 64 (repeat (Z_to_bv 8 (32 mod 256)) 64)] ->
  bytes_at usegs m CP (zbytes (Sj_stage2_numkitr.crs t)).
Proof.
  intros m CP t [[_ H1] _] [[_ H2] _]. cbn [cells_bytes cbytes] in H1, H2. rewrite app_nil_r in H1, H2.
  unfold Sj_stage2_numkitr.crs, zbytes. rewrite map_app, map_repeat. apply bytes_at_app. split; [exact H1|].
  rewrite length_map. unfold blen in H2. exact H2.
Qed.

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Record env_heap (E : s2env) (LB : list block) (B cap : Z) : Prop := mkEnvHeap {
  eh_tp : e_tp E = Z_to_bv 64 RATP;
  eh_vptr : e_vptr E = Z_to_bv 64 SJ_DPI_VPTR;
  eh_capv : e_capv E = Z_to_bv 64 cap;
  eh_ceil : alloc_ceiling <= e_lo E;
  eh_B : bv_unsigned (e_sp E) <= B /\ B < 2^63 /\ e_DOC E + 24 <= B;
  eh_blocks : forall a, in_block LB a -> a < alloc_ceiling;
  eh_this : region_in LB (e_THIS E) 96;
  eh_idx : region_in LB (e_IDX E) (4 * Z.of_nat (length (e_iws E)));
  eh_buf : region_in LB (e_BUF E) (e_len E + 64);
  eh_tape : region_in LB (e_TAPE E) (8 * e_tcap E);
  eh_sbuf : region_in LB (e_SBUF E) (e_scap E);
  eh_oc : region_in LB (e_OC E) 8192;
  eh_ia : region_in LB (e_IA E) 1024;

  eh_st_this : e_THIS E + 96 <= 0x10000 \/ 0x111000 <= e_THIS E;
  eh_st_tape : e_TAPE E + 8 * e_tcap E <= 0x10000 \/ 0x111000 <= e_TAPE E;
  eh_st_sbuf : e_SBUF E + e_scap E <= 0x10000 \/ 0x111000 <= e_SBUF E;
  eh_st_oc : e_OC E + 8192 <= 0x10000 \/ 0x111000 <= e_OC E;
  eh_st_ia : e_IA E + 1024 <= 0x10000 \/ 0x111000 <= e_IA E }.

Lemma env_heap_ghost : forall E LB B cap tws sbs, env_heap E LB B cap -> env_heap (s2_ghost E tws sbs) LB B cap.
Proof. intros E LB B cap tws sbs []. constructor; assumption. Qed.
Lemma env_heap_rebase : forall E LB B cap m, env_heap E LB B cap -> env_heap (s2_rebase E m) LB B cap.
Proof. intros E LB B cap m []. constructor; assumption. Qed.

Lemma region_in_cons : forall b LB X n, region_in LB X n -> region_in (b :: LB) X n.
Proof. intros b LB X n (b' & Hb & H). exists b'. split; [right; exact Hb| exact H]. Qed.

Lemma env_heap_cons : forall E LB B cap b, env_heap E LB B cap ->
  (forall a, blk_addr b <= a < blk_addr b + blk_size b -> a < alloc_ceiling) -> env_heap E (b :: LB) B cap.
Proof.
  intros E LB B cap b [] Hb. constructor; try assumption; try (apply region_in_cons; assumption).
  intros a (b' & [Eb|Hb'] & Hr); [subst b'; apply Hb; exact Hr|].
  match goal with H : forall a, in_block LB a -> _ |- _ => apply H end. exists b'. split; assumption.
Qed.

Lemma region_in_block : forall LB X n a, region_in LB X n -> X <= a < X + n -> in_block LB a.
Proof. intros LB X n a (b & Hb & H1 & H2) Ha. exists b. split; [exact Hb| lia]. Qed.

Lemma s2_region_client : forall E LB B cap, env_ok E -> env_heap E LB B cap ->
  forall a, s2_region E a -> rclient_addr LB (e_SP E) a.
Proof.
  intros E LB B cap OK EH a HR. pose proof (ok_doc _ OK) as HD. pose proof (ok_room _ OK) as HRM. unfold S2_STACK in HRM.
  destruct HR as [H|[H|[H|[H|[H|[H|[H|[H|H]]]]]]]].
  - left. lia.
  - right; right. eapply region_in_block; [exact (eh_this _ _ _ _ EH)| lia].
  - left. lia.
  - right; right. eapply region_in_block; [exact (eh_idx _ _ _ _ EH)| lia].
  - right; right. eapply region_in_block; [exact (eh_buf _ _ _ _ EH)| lia].
  - right; right. eapply region_in_block; [exact (eh_tape _ _ _ _ EH)| lia].
  - right; right. eapply region_in_block; [exact (eh_sbuf _ _ _ _ EH)| lia].
  - right; right. eapply region_in_block; [exact (eh_oc _ _ _ _ EH)| lia].
  - right; right. eapply region_in_block; [exact (eh_ia _ _ _ _ EH)| lia].
Qed.

Lemma s2_W_write_ok : forall E LB B cap, env_heap E LB B cap -> Forall (rclient_write_ok LB) (s2_W E).
Proof.
  intros E LB B cap EH. unfold s2_W.
  destruct (eh_this _ _ _ _ EH) as (b1 & Hb1 & R11 & R12). destruct (eh_tape _ _ _ _ EH) as (b4 & Hb4 & R41 & R42).
  destruct (eh_sbuf _ _ _ _ EH) as (b5 & Hb5 & R51 & R52). destruct (eh_oc _ _ _ _ EH) as (b6 & Hb6 & R61 & R62).
  destruct (eh_ia _ _ _ _ EH) as (b7 & Hb7 & R71 & R72).
  constructor; [apply W_ok_stack; exact (eh_ceil _ _ _ _ EH)|].
  constructor; [eapply W_ok_block; [exact Hb1 | exact R11 | exact R12]|].
  constructor; [eapply W_ok_block; [exact Hb4 | exact R41 | exact R42]|].
  constructor; [eapply W_ok_block; [exact Hb5 | exact R51 | exact R52]|].
  constructor; [eapply W_ok_block; [exact Hb6 | exact R61 | exact R62]|].
  constructor; [eapply W_ok_block; [exact Hb7 | exact R71 | exact R72]| constructor].
Qed.

Lemma s2_heap_frame : forall E LB B cap s m m', env_heap E LB B cap ->
  RHEAP s LB m -> munch (s2_W E) m m' -> wmono usegs m m' -> RHEAP s LB m'.
Proof. intros E LB B cap s m m' EH H MU WM. eapply LH_frame; [exact H| exact MU| exact WM| eapply s2_W_write_ok; exact EH]. Qed.

Lemma s2_auxv_frame : forall E LB B cap m m', env_ok E -> env_heap E LB B cap ->
  rauxv_ok m B -> munch (s2_W E) m m' -> wmono usegs m m' -> rauxv_ok m' B.
Proof.
  intros E LB B cap m m' OK EH AUX MU WM.
  pose proof (ok_glo _ OK) as G. pose proof (ok_room _ OK) as HRM. unfold S2_STACK in HRM. destruct (eh_B _ _ _ _ EH) as (B1 & _ & _).
  pose proof (ok_this _ OK) as T1. pose proof (ok_tape _ OK) as T2. pose proof (ok_sbuf _ OK) as T3. pose proof (ok_oc _ OK) as T4. pose proof (ok_ia _ OK) as T5.
  pose proof (eh_st_this _ _ _ _ EH) as S1. pose proof (eh_st_tape _ _ _ _ EH) as S2. pose proof (eh_st_sbuf _ _ _ _ EH) as S3.
  pose proof (eh_st_oc _ _ _ _ EH) as S4. pose proof (eh_st_ia _ _ _ _ EH) as S5.
  eapply rauxv_ok_frame; [exact AUX | exact MU | exact WM |]. unfold s2_W, RAUXV_CELL.
  constructor; [cbn [fst snd]; clear - G HRM B1; lia|].
  constructor; [cbn [fst snd]; clear - T1 S1 HRM B1; lia|].
  constructor; [cbn [fst snd]; clear - T2 S2 HRM B1; lia|].
  constructor; [cbn [fst snd]; clear - T3 S3 HRM B1; lia|].
  constructor; [cbn [fst snd]; clear - T4 S4 HRM B1; lia|].
  constructor; [cbn [fst snd]; clear - T5 S5 HRM B1; lia| constructor].
Qed.

Lemma s2_static_frame : forall E LB B cap m m' A cs, env_ok E -> env_heap E LB B cap ->
  0x10000 <= A -> A + Z.of_nat (cells_size cs) <= 0x111000 ->
  rw_cells usegs m A cs -> munch (s2_W E) m m' -> wmono usegs m m' -> rw_cells usegs m' A cs.
Proof.
  intros E LB B cap m m' A cs OK EH HA1 HA2 H MU WM.
  pose proof (ok_glo _ OK) as G.
  pose proof (eh_st_this _ _ _ _ EH) as S1. pose proof (eh_st_tape _ _ _ _ EH) as S2. pose proof (eh_st_sbuf _ _ _ _ EH) as S3.
  pose proof (eh_st_oc _ _ _ _ EH) as S4. pose proof (eh_st_ia _ _ _ _ EH) as S5.
  eapply rw_cells_transport; [exact H | exact MU | exact WM |].
  unfold s2_W. cbn [disjoint_from].
  split; [clear - G HA2; lia|]. split; [clear - S1 HA1 HA2; lia|]. split; [clear - S2 HA1 HA2; lia|].
  split; [clear - S3 HA1 HA2; lia|]. split; [clear - S4 HA1 HA2; lia|]. split; [clear - S5 HA1 HA2; lia| exact I].
Qed.

Lemma s2_lx_pres_munch : forall E LB B cap m m', env_ok E -> env_heap E LB B cap ->
  munch (s2_W E) m m' -> wmono usegs m m' ->
  lx_pres LB (bv_unsigned (e_sp E)) (s2_X (e_THIS E) (e_TAPE E) (e_SBUF E) (e_OC E) (e_IA E) (e_tcap E) (e_scap E)) m m'.
Proof.
  intros E LB B cap m m' OK EH MU WM.
  pose proof (ok_glo _ OK) as G. pose proof (eh_ceil _ _ _ _ EH) as HC0.
  eapply lx_pres_of_munch; [exact MU | exact WM |].
  intros a Ha (HX & HC). unfold s2_X in HX. cbn [rin_ivs fst snd] in HX. unfold s2_W. cbn [outside].
  assert (HA : ~ (e_lo E <= a < bv_unsigned (e_sp E))).
  { destruct HC as [HC | [HC | (HC & _)]]; [clear - HC; lia | | clear - HC G; lia].
    pose proof (eh_blocks _ _ _ _ EH a HC) as P3. clear - P3 HC0. lia. }
  split; [exact HA|].
  split; [intros HI; apply HX; left; exact HI|].
  split; [intros HI; apply HX; right; left; exact HI|].
  split; [intros HI; apply HX; right; right; left; exact HI|].
  split; [intros HI; apply HX; right; right; right; left; exact HI|].
  split; [intros HI; apply HX; right; right; right; right; left; exact HI| exact I].
Qed.

Definition flat_post (E : s2env) (LB : list block) (B cap : Z) (s : PState) (m : mem) (r : unit) (s' : PState) : machine_state -> Prop :=
  stage2t_post (e_ra E) (e_sp E) (e_gp E) (e_s0 E) (e_s1 E) (e_s2 E) (e_s3 E) (e_s4 E) (e_s5 E) (e_s6 E) (e_s7 E) (e_s8 E) (e_s9 E)
              (e_s10 E) (e_s11 E) s LB (e_lo E) B m
              (e_THIS E) (e_DOC E) (e_IDX E) (e_BUF E) (e_TAPE E) (e_SBUF E) (e_OC E) (e_IA E)
              (e_n E) cap (e_len E) (e_tcap E) (e_scap E) (e_p12 E) (e_p28 E) (e_p50 E) r s'.

Lemma s2_post_conv : forall E LB B cap s s' m errv ms',
  env_ok E -> env_heap E LB B cap ->
  RHEAP s' LB (e_m0 E) -> rauxv_ok (e_m0 E) B -> rw_cells usegs (e_m0 E) LX_ERRNO [C4 errv] ->
  lx_pres LB (bv_unsigned (e_sp E)) (s2_X (e_THIS E) (e_TAPE E) (e_SBUF E) (e_OC E) (e_IA E) (e_tcap E) (e_scap E)) m (e_m0 E) ->
  ps_fa s' = ps_fa s -> ps_so s' = ps_so s ->
  s2_post E ms' -> flat_post E LB B cap s m tt s' ms'.
Proof.
  intros E LB B cap s s' m errv ms' OK EH HEAP AUX ERR PRES FA SO HP.
  unfold s2_post in HP.
  destruct HP as (q5 & q6 & q7 & q10 & q11 & q12 & q13 & q14 & q15 & q16 & q17 & q28 & q29 & q30 & q31 & F' & fc' & m'
                  & -> & A64 & MU & WM & MI' & FRM' & (nxt' & IMPL') & _ & _ & _ & _ & _ & _ & _ & ST2 & RES).
  unfold flat_post, stage2t_post.
  exists q5, q6, q7, q10, q11, q12, q13, q14, q15, q16, q17, q28, q29, q30, q31, F', fc', m', errv, nxt'.
  split; [rewrite (eh_tp _ _ _ _ EH); reflexivity|]. split; [exact FRM'|].
  split; [eapply s2_heap_frame; [exact EH| exact HEAP| exact MU| exact WM]|].
  split; [eapply s2_auxv_frame; [exact OK| exact EH| exact AUX| exact MU| exact WM]|].
  split; [exact ST2|].
  split; [eapply (s2_static_frame E LB B cap _ _ LX_ERRNO); [exact OK| exact EH| | | exact ERR| exact MU| exact WM];
          unfold LX_ERRNO, RATP; cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; lia|].
  split; [exact MI'|]. split; [exact FA|]. split; [exact SO|].
  split; [eapply lx_pres_trans; [exact PRES| eapply s2_lx_pres_munch; [exact OK| exact EH| exact MU| exact WM]]|].
  split; [| unfold s2_result, s2_fail, tape_ok, twords, zbytes in RES; exact RES].
  unfold impl_cells in IMPL'. unfold s2_impl_cells. rewrite (eh_vptr _ _ _ _ EH), (eh_capv _ _ _ _ EH) in IMPL'. exact IMPL'.
Qed.
End WithCeiling0.
