(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import PropExec ShapeAlg MmapSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import MState Mem Cells Frame Step Arr Tac Bytes.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc Require Import SpinAlg Ledger Hull Restrict EvtAcct.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo Asan12c Asanqj4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import ARt_u2d.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import ARtStmts ARtSscs ARtSf1m.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AIface AState ADepotM LayoutPA AInv ALogic1 ALogic2 ALogic3 ALogic AMTac
     AMallocI AMallocA AMallocH AMalmys ABudget ANodeA7 ASecComb ASecO1 ASecImg.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.

Notation wz z := (Z_to_bv 64 z) (only parsing).
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma LMA7_eq : ARtSf1m.LMA = ASecComb.LMA. Proof. reflexivity. Qed.
Lemma CF_eq : ANodeA7.CF = 0x146ee8. Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma CB8_bytes : forall ws, cells_bytes (map C8 ws) = u64s ws.
Proof. induction ws as [|w ws IH]; [reflexivity|]. cbn [map cells_bytes cbytes u64s]. rewrite IH. reflexivity. Qed.
Lemma CB8_size : forall ws, cells_size (map C8 ws) = (8 * length ws)%nat.
Proof. induction ws as [|w ws IH]; [reflexivity|]. cbn [map cells_size csize length]. rewrite IH. lia. Qed.
Lemma CB8_wf : forall ws, cells_wf (map C8 ws).
Proof. induction ws as [|w ws IH]; [exact I|]. cbn. split; [exact I| exact IH]. Qed.

(* [comment removed for export] *)
Lemma img_wr_at0 : forall (m : mem) a n, 0xa8000 <= a -> a + n <= 0x60a000 -> wr_at rsegs m a n.
Proof.
  intros m a n Ha Hb. split; [lia|]. split; [lia|]. intros i Hi.
  pose proof (img_mrd_some m (wz (a + i)) ltac:(rewrite unsigned_lit by lia; lia)) as R.
  unfold wa, wview, mrd in *. destruct (m (wz (a + i))); [discriminate|].
  destruct (ro_addr rsegs (wz (a + i))) eqn:RO.
  - exfalso. apply (proj1 (pa_ro_addr_iff _)) in RO. rewrite unsigned_lit in RO by lia. lia.
  - unfold ro_addr in RO. unfold seg_rom, memory_read in R. change (Z.of_N 1) with 1 in R.
    destruct (find_segment rsegs (bv_unsigned (wz (a + i))) 1) as [seg|]; [| exact R].
    cbn [negb] in RO. destruct (seg_writable seg); [| discriminate].
    destruct (seg_readable seg); [| exfalso; exact (R eq_refl)].
    change (N.to_nat 1) with 1%nat in R. cbn [segment_read_bytes] in R.
    destruct (segment_byte_at (seg_bytes seg) (Z.to_N (bv_unsigned (wz (a + i)) - Z.of_N (seg_base seg)))); [discriminate| exact R].
Qed.
Lemma img_rw_words : forall (m : mem) a (k : nat), 0xa8000 <= a -> a + 8 * Z.of_nat k <= 0x60a000 ->
  exists ws, length ws = k /\ rw_cells rsegs m a (map C8 ws).
Proof.
  intros m a k H1 H2. (first [ pose proof ((img_junk m a (8 * Z.of_nat k) H1 H2 ltac:(lia))) as dR_1; dex1 dR_1 as bs; destruct dR_1 as [L B] | pose proof ((img_junk m a (8 * Z.of_nat k) H1 H2 ltac:(lia))) as dR_1; dand3 dR_1 as bs L B | destruct (img_junk m a (8 * Z.of_nat k) H1 H2 ltac:(lia)) as (bs & L & B) ]).
  exists (words8 bs k). split; [apply words8_length|].
  split; [split; [apply CB8_wf| rewrite CB8_bytes, u64s_words8 by lia; exact B]|].
  rewrite CB8_size, words8_length. apply img_wr_at0; lia.
Qed.
Lemma img_rw_bytes : forall (m : mem) a (k : nat), 0xa8000 <= a -> a + Z.of_nat k <= 0x60a000 ->
  exists bs, length bs = k /\ rw_cells rsegs m a [CB k bs].
Proof.
  intros m a k H1 H2. (first [ pose proof ((img_junk m a (Z.of_nat k) H1 H2 ltac:(lia))) as dR_2; dex1 dR_2 as bs; destruct dR_2 as [L B] | pose proof ((img_junk m a (Z.of_nat k) H1 H2 ltac:(lia))) as dR_2; dand3 dR_2 as bs L B | destruct (img_junk m a (Z.of_nat k) H1 H2 ltac:(lia)) as (bs & L & B) ]).
  exists bs. split; [lia|]. split; [split; [cbn; split; [lia| exact I]| cbn [cells_bytes cbytes]; rewrite app_nil_r; exact B]|].
  cbn [cells_size csize]. rewrite Nat.add_0_r. apply img_wr_at0; lia.
Qed.

Ltac ulma := unfold ASecComb.LMA, ASecComb.LSTAT in *.

Section Cells.
Context {Clg : Ceiling}.
  Variables (A : AState) (m : mem) (md : Model).
  Hypothesis AI : @pa_ainv _ DepotRepL A m md.
  Let v := aview_of (pa_hull A) m.
  Let P := a_pl A.
  Let W : WF AL_pasan A. Proof. exact (ai_wf _ _ _ _ _ _ _ AI). Qed.
  Let CFA : Forall (fun c => bytes_at rsegs v (fst c) (snd c)) (cl_consts LPA).
  Proof. exact (proj1 (ar_consts _ _ _ _ _ (ai_repr _ _ _ _ _ _ _ AI))). Qed.
  Ltac cell H a bs := pose proof (consts_cell v a bs CFA eq_refl) as H.
  Let CR : consts_repr_ LPA AL_pasan (a_pl A) v.
  Proof. exact (ar_consts _ _ _ _ _ (ai_repr _ _ _ _ _ _ _ AI)). Qed.
  Let SR : sec_repr_ LPA AL_pasan (a_pl A) (a_sec A) v.
  Proof. exact (ar_sec _ _ _ _ _ (ai_repr _ _ _ _ _ _ _ AI)). Qed.
  Let LK : locks_repr_ LPA AL_pasan (a_pl A) [] v.
  Proof. exact (ar_locks _ _ _ _ _ (ai_repr _ _ _ _ _ _ _ AI)). Qed.

  (* [comment removed for export] *)
  Lemma sec_LMA0 : ro_cells rsegs v ASecComb.LMA [C8 (wz 4096)].
  Proof.
    pose proof CR as C. unfold consts_repr_ in C. cbv zeta in C. cbn [al_instance AL_pasan] in C.
    assert (X : u64_at rsegs v (728408 + off_sec_page_size) 4096) by tauto. apply u64_ro. exact X.
  Qed.
  Lemma sec_LPA8 : ro_cells rsegs v (ASecComb.LMA + 8) [C8 (wz (p_pa P))].
  Proof.
    pose proof CR as C. unfold consts_repr_ in C. cbv zeta in C. cbn [al_instance AL_pasan] in C.
    assert (X : u64_at rsegs v (728408 + off_sec_chunks) (p_pa (a_pl A))) by tauto. apply u64_ro. exact X.
  Qed.
  Lemma sec_LPA16 : ro_cells rsegs v (ASecComb.LMA + 16) [C8 (wz (p_pa P))].
  Proof.
    pose proof CR as C. unfold consts_repr_ in C. cbv zeta in C. cbn [al_instance AL_pasan] in C.
    assert (X : u64_at rsegs v (728408 + off_sec_ptr_array_base) (p_pa (a_pl A))) by tauto. apply u64_ro. exact X.
  Qed.

  (* [comment removed for export] *)
  Lemma sec_PN : ro_cells rsegs v 0xa9178 [C8 (wz 0xab070)].
  Proof. cell H 0xa9178 (le8 (Z_to_bv 64 0xab070)). apply bytes_ro_C8. exact H. Qed.
  Lemma sec_NAME : ro_cells rsegs v 0xab070 [C8 (wz lma_name)].
  Proof. cell H 0xab070 (le8 (Z_to_bv 64 0x19805)). apply bytes_ro_C8. exact H. Qed.
  Lemma sec_CF260 : ro_cells rsegs v (ANodeA7.CF + 260) [C1 (Z_to_bv 8 0)].
  Proof.
    cell H 0x146ee8 pa_common_flags_bytes. rewrite CF_eq. apply bytes_ro_C1.
    apply (bytes_at_as v _ _ _ (bytes_at_mid v 0x146ee8 pa_common_flags_bytes 260 1 H ltac:(cbn; lia))). byteseq.
  Qed.
  Lemma sec_CF144 : ro_cells rsegs v (ANodeA7.CF + 144) [C8 (wz 0)].
  Proof.
    cell H 0x146ee8 pa_common_flags_bytes. rewrite CF_eq. apply bytes_ro_C8.
    apply (bytes_at_as v _ _ _ (bytes_at_mid v 0x146ee8 pa_common_flags_bytes 144 8 H ltac:(cbn; lia))). byteseq.
  Qed.
  Lemma sec_LC : lma_consts v 0xab070.
  Proof.
    unfold lma_consts. split; [first [exact sec_LMA0 | rewrite LMA7_eq; exact sec_LMA0]|]. split; [exact sec_PN|]. split; [exact sec_NAME|].
    split; [lia|]. split; [lia|].
    split; [exact (proj1 (proj2 (hit_PCo A m md AI)))|]. split; [exact sec_CF260| exact sec_CF144].
  Qed.
  Lemma sec_MRN : ro_cells rsegs v 0x137621 [C1 (Z_to_bv 8 1)].
  Proof. pose proof CR as C. unfold consts_repr_ in C. cbv zeta in C. apply u8_ro. cbn [al_may_return_null AL_pasan] in C. tauto. Qed.

  (* [comment removed for export] *)
  Lemma sec_OOM : exists oomb, rw_cells rsegs v 0x137620 [C1 oomb].
  Proof.
    (first [ pose proof ((img_rw_bytes v 0x137620 1 ltac:(lia) ltac:(lia))) as dR_3; dex1 dR_3 as bs; destruct dR_3 as [L R] | pose proof ((img_rw_bytes v 0x137620 1 ltac:(lia) ltac:(lia))) as dR_3; dand3 dR_3 as bs L R | destruct (img_rw_bytes v 0x137620 1 ltac:(lia) ltac:(lia)) as (bs & L & R) ]).
    destruct bs as [|b [|]]; cbn in L; try lia. exists b.
    refine (rwc_rebytes _ _ _ _ _ _ R); cbn; [OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; exact I| reflexivity].
  Qed.
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma sec_LREG : rw_cells rsegs v (ASecComb.LMA + 48)
      [C8 (wz (sr_reserved (a_sec A))); C8 (wz (Z.of_nat (length (sr_chunks (a_sec A)))))].
  Proof.
    pose proof SR as S. unfold sec_repr_ in S. cbv zeta in S. cbn [al_instance AL_pasan] in S. (first [ dand3 S as S1 S2 _ | destruct S as (S1 & S2 & _) ]).
    unfold off_sec_n_reserved, off_sec_n_chunks in S1, S2. unfold u64_at in S1, S2.
    split; [split; [exact (conj I (conj I I))| cbn [cells_bytes cbytes]; rewrite app_nil_r; apply bytes_at_app; split;
      [exact S1| rewrite length_le8; exact S2]]|].
    apply img_wr_at0; ulma; cbn; lia.
  Qed.
  Lemma sec_LCS : exists cs, rw_cells rsegs v (ASecComb.LMA + 64) [C1 cs].
  Proof.
    (first [ pose proof ((img_rw_bytes v (ASecComb.LMA + 64) 1 ltac:(ulma; lia) ltac:(ulma; lia))) as dR_6; dex1 dR_6 as bs; destruct dR_6 as [L R] | pose proof ((img_rw_bytes v (ASecComb.LMA + 64) 1 ltac:(ulma; lia) ltac:(ulma; lia))) as dR_6; dand3 dR_6 as bs L R | destruct (img_rw_bytes v (ASecComb.LMA + 64) 1 ltac:(ulma; lia) ltac:(ulma; lia)) as (bs & L & R) ]).
    destruct bs as [|b [|]]; cbn in L; try lia. exists b.
    refine (rwc_rebytes _ _ _ _ _ _ R); cbn; [OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; exact I| reflexivity].
  Qed.
  Lemma sec_LSTA : exists (na nf ca mx : word) (bsl : list word),
    rw_cells rsegs v (ASecComb.LMA + 72) [C8 na; C8 nf; C8 ca; C8 mx; CB 512 (u64s bsl)] /\ length bsl = 64%nat.
  Proof.
    (first [ pose proof ((img_rw_words v (ASecComb.LMA + 72) 68 ltac:(ulma; lia) ltac:(ulma; lia))) as dR_7; dex1 dR_7 as ws; destruct dR_7 as [L R] | pose proof ((img_rw_words v (ASecComb.LMA + 72) 68 ltac:(ulma; lia) ltac:(ulma; lia))) as dR_7; dand3 dR_7 as ws L R | destruct (img_rw_words v (ASecComb.LMA + 72) 68 ltac:(ulma; lia) ltac:(ulma; lia)) as (ws & L & R) ]).
    destruct ws as [|na [|nf [|ca [|mx bsl]]]]; cbn in L; try lia.
    exists na, nf, ca, mx, bsl. split; [| lia].
    refine (rwc_rebytes _ _ _ _ _ _ R).
    - cbn -[u64s]. rewrite u64s_length. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; first [exact I | lia].
    - cbn [map cells_bytes cbytes]. rewrite app_nil_r, CB8_bytes. reflexivity.
  Qed.
  Lemma sec_GST : exists (sta stm : word), rw_cells rsegs v (ASecComb.LSTAT + 16) [C8 sta; C8 stm].
  Proof.
    (first [ pose proof ((img_rw_words v (ASecComb.LSTAT + 16) 2 ltac:(ulma; lia) ltac:(ulma; lia))) as dR_8; dex1 dR_8 as ws; destruct dR_8 as [L R] | pose proof ((img_rw_words v (ASecComb.LSTAT + 16) 2 ltac:(ulma; lia) ltac:(ulma; lia))) as dR_8; dand3 dR_8 as ws L R | destruct (img_rw_words v (ASecComb.LSTAT + 16) 2 ltac:(ulma; lia) ltac:(ulma; lia)) as (ws & L & R) ]).
    destruct ws as [|sta [|stm [|]]]; cbn in L; try lia. exists sta, stm. exact R.
  Qed.

  (* [comment removed for export] *)
  Lemma sec_LMTX : rw_cells rsegs v (ASecComb.LMA + 616) [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C2 (wz 0)].
  Proof.
    pose proof LK as L. unfold locks_repr_ in L. cbv zeta in L. cbn [al_instance AL_pasan] in L. (first [ dand3 L as _ L1 _ | destruct L as (_ & L1 & _) ]).
    unfold off_sec_mutex, lockb in L1. cbn [in_dec] in L1. unfold u8_at in L1.
    cell PB 0xb2001 [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0].
    split; [split; [exact (conj I (conj I (conj I I)))|]|].
    - cbn [cells_bytes cbytes]. change (ASecComb.LMA + 616) with (728408 + 680).
      apply bytes_at_app. split; [exact L1|]. cbn [length Z.of_nat Pos.of_succ_nat]. change (728408 + 680 + 1) with 0xb2001.
      apply (bytes_at_as v _ _ _ PB). byteseq.
    - apply img_wr_at0; ulma; cbn; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma sec_PAN : forall i, 0 <= i < sr_reserved (a_sec A) -> exists pan, rw_cells rsegs v (p_pa P + 8 * i) [C8 pan].
  Proof.
    intros i Hi. pose proof SR as S. unfold sec_repr_ in S. cbv zeta in S. (first [ dand7 S as _ _ _ _ _ _ PM | destruct S as (_ & _ & _ & _ & _ & _ & PM) ]).
    pose proof alloc_ceiling_val as CE.
    (first [ pose proof ((wfS A W)) as dR_11; dand4 dR_11 as _ _ SRES _ | destruct (wfS A W) as (_ & _ & SRES & _) ]). unfold kChunksBlockCount in SRES.
    assert (PA : 4096 <= p_pa P /\ p_pa P + kPtrArrayReserve <= alloc_ceiling).
    { pose proof (place_facts A W) as PF. cbv zeta in PF. (first [ dand13 PF as _ _ _ _ _ _ _ _ _ _ _ (PPA & PPB & _) _ | destruct PF as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (PPA & PPB & _) & _) ]).
      apply app_rangeA_arith in PPA. subst P. lia. }
    unfold kPtrArrayReserve in PA.
    assert (M8 : mapped v (p_pa P + 8 * i) 8).
    { intros k Hk. replace (p_pa P + 8 * i + k) with (p_pa (a_pl A) + (8 * i + k)) by (subst P; lia). apply PM. lia. }
    pose proof (rdbytes_bytes_at v (p_pa P + 8 * i) 8 M8 ltac:(lia) ltac:(lia)) as B.
    exists (le_bytes_to_word (rdbytes v (p_pa P + 8 * i) 8)).
    apply ro_rw; [| exact M8]. apply bytes_ro_C8. rewrite le8_of_bytes by apply rdbytes_length. exact B.
  Qed.

  (* [comment removed for export] *)
  Lemma thr_words : forall a (k : nat), p_thr P + off_th_stats <= a -> a + 8 * Z.of_nat k <= p_thr P + off_th_stats + (112 + 8 * 32) ->
    exists ws, length ws = k /\ rw_cells rsegs v a (map C8 ws).
  Proof.
    intros a k H1 H2. unfold off_th_stats in *.
    pose proof (ar_cache _ _ _ _ _ (ai_repr _ _ _ _ _ _ _ AI)) as C. unfold cache_repr_ in C. cbv zeta in C. (first [ dand5 C as _ _ JS TM _ | destruct C as (_ & _ & JS & TM & _) ]).
    unfold off_th_stats in JS. (first [ dex1 JS as bs; destruct JS as [LBS BS] | dand3 JS as bs LBS BS | destruct JS as (bs & LBS & BS) ]).
    pose proof alloc_ceiling_val as CE.
    assert (TP : 4096 <= p_thr P /\ p_thr P + 4096 <= alloc_ceiling).
    { pose proof (place_facts A W) as PF. cbv zeta in PF. destruct PF as ((PT & PT2 & _) & _). apply app_rangeA_arith in PT. subst P. lia. }
    pose proof (bytes_at_mid v (p_thr (a_pl A) + 2800) bs (Z.to_nat (a - (p_thr P + 2800))) (8 * k) BS ltac:(subst P; lia)) as B.
    rewrite Z2Nat.id in B by (subst P; lia). replace (p_thr (a_pl A) + 2800 + (a - (p_thr P + 2800))) with a in B by (subst P; lia).
    exists (words8 (firstn (8 * k) (skipn (Z.to_nat (a - (p_thr P + 2800))) bs)) k). split; [apply words8_length|].
    assert (LEN : length (firstn (8 * k) (skipn (Z.to_nat (a - (p_thr P + 2800))) bs)) = (8 * k)%nat).
    { rewrite firstn_length_le; [reflexivity|]. rewrite length_skipn. subst P. lia. }
    apply ro_rw.
    - split; [apply CB8_wf|]. rewrite CB8_bytes, u64s_words8 by exact LEN. exact B.
    - rewrite CB8_size, words8_length, Nat2Z.inj_mul. intros j Hj.
      replace (a + j) with (p_thr (a_pl A) + (a - p_thr P + j)) by (subst P; lia). apply TM. subst P. lia.
  Qed.
  Lemma sec_thr_stats : exists (v0 v1 v2 mm72 mm80 vl : word),
    rw_cells rsegs v (p_thr P + 2800) [C8 v0; C8 v1; C8 v2] /\
    rw_cells rsegs v (p_thr P + off_th_stats + 72) [C8 mm72; C8 mm80] /\
    rw_cells rsegs v (p_thr P + 2904) [C8 vl].
  Proof.
    (first [ pose proof ((thr_words (p_thr P + 2800) 3 ltac:(unfold off_th_stats; lia) ltac:(unfold off_th_stats; cbn; lia))) as dR_15; dex1 dR_15 as ws1; destruct dR_15 as [L1 R1] | pose proof ((thr_words (p_thr P + 2800) 3 ltac:(unfold off_th_stats; lia) ltac:(unfold off_th_stats; cbn; lia))) as dR_15; dand3 dR_15 as ws1 L1 R1 | destruct (thr_words (p_thr P + 2800) 3 ltac:(unfold off_th_stats; lia) ltac:(unfold off_th_stats; cbn; lia)) as (ws1 & L1 & R1) ]).
    (first [ pose proof ((thr_words (p_thr P + off_th_stats + 72) 2 ltac:(unfold off_th_stats; lia) ltac:(unfold off_th_stats; cbn; lia))) as dR_16; dex1 dR_16 as ws2; destruct dR_16 as [L2 R2] | pose proof ((thr_words (p_thr P + off_th_stats + 72) 2 ltac:(unfold off_th_stats; lia) ltac:(unfold off_th_stats; cbn; lia))) as dR_16; dand3 dR_16 as ws2 L2 R2 | destruct (thr_words (p_thr P + off_th_stats + 72) 2 ltac:(unfold off_th_stats; lia) ltac:(unfold off_th_stats; cbn; lia)) as (ws2 & L2 & R2) ]).
    (first [ pose proof ((thr_words (p_thr P + 2904) 1 ltac:(unfold off_th_stats; lia) ltac:(unfold off_th_stats; cbn; lia))) as dR_17; dex1 dR_17 as ws3; destruct dR_17 as [L3 R3] | pose proof ((thr_words (p_thr P + 2904) 1 ltac:(unfold off_th_stats; lia) ltac:(unfold off_th_stats; cbn; lia))) as dR_17; dand3 dR_17 as ws3 L3 R3 | destruct (thr_words (p_thr P + 2904) 1 ltac:(unfold off_th_stats; lia) ltac:(unfold off_th_stats; cbn; lia)) as (ws3 & L3 & R3) ]).
    destruct ws1 as [|v0 [|v1 [|v2 [|]]]]; cbn in L1; try lia.
    destruct ws2 as [|mm72 [|mm80 [|]]]; cbn in L2; try lia.
    destruct ws3 as [|vl [|]]; cbn in L3; try lia.
    exists v0, v1, v2, mm72, mm80, vl. cbn [map] in R1, R2, R3. exact (conj R1 (conj R2 R3)).
  Qed.

  (* [comment removed for export] *)
  Lemma sec_nch : 0 <= Z.of_nat (length (sr_chunks (a_sec A))) <= sr_reserved (a_sec A) /\ sr_reserved (a_sec A) <= kChunksBlockCount /\
                  (sr_reserved (a_sec A) = 0 \/ sr_reserved (a_sec A) = kChunksBlockCount) /\
                  Z.of_nat (length (sr_chunks (a_sec A))) <= 8274.
  Proof.
    (first [ pose proof ((wfS A W)) as dR_18; dand4 dR_18 as _ LEN RES _ | destruct (wfS A W) as (_ & LEN & RES & _) ]). pose proof (wf_sec_eager A W) as [_ L8]. unfold kChunksBlockCount in *. lia.
  Qed.
  Lemma sec_pa : aobj (p_pa P) kPtrArrayReserve /\ p_pa P + kPtrArrayReserve <= alloc_ceiling /\ p_pa P mod 4096 = 0.
  Proof.
    pose proof (place_facts A W) as PF. cbv zeta in PF. (first [ dand13 PF as _ _ _ _ _ _ _ _ _ _ _ (PPA & PPB & AL) _ | destruct PF as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (PPA & PPB & AL) & _) ]).
    split; [apply aobj_app_rangeA; exact PPA|]. split; [subst P; exact PPB| subst P; exact AL].
  Qed.
End Cells.
