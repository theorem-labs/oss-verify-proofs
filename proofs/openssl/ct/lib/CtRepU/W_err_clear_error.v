(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCt.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP Frame Cells Step Mem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Malloc Require Import MallocRep MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtMallocU Require Import RMallocRep RMallocTree RMalloc_iface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import Prelim STree Malloc Monad Prog LibProg ProgG.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import ApBase ApState ApInv ApErr ApBridge.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtU Require Import Layout Lib_iface Lib_kit.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtHXU Require Import HxpFacts HxpInit HxpGetState.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtBnU Require Import BnKit BnHeap BnRep W_crypto.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepU Require Import ApCells ApRepDefs ApRep ApIface ApWalkTac ApErrKit ApErrKit2 ApErrKit3 W_err_new.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepU Require Import ApUbTab ApUTac.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.ct.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Local Ltac ub1c :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) =>
      let k := eval vm_compute in (ub_kind pc) in
      lazymatch k with
      | 1%Z => zstep
      | 2%Z => first [ (zstep; udecide) | uchk ]
      end
  end.
Local Ltac step := try udecide; repeat ub1c; OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.step.
Local Ltac zstep := try udecide; repeat ub1c; OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.zstep.

Ltac cell_of_bytes bs ::=
  lazymatch bs with
  | le8 ?v => constr:(C8 v)
  | le4 ?v => constr:(C4 v)
  | le2 ?v => constr:(C2 v)
  | [?b] => constr:(C1 b)
  | le1 (zxb ?b) => constr:(C1 b)
  | le1 (Z_to_bv 64 ?z) => constr:(C1 (Z_to_bv 8 z))
  | Z_to_le_bytes 8 ?z => constr:(C8 (Z_to_bv 64 z))
  | Z_to_le_bytes 4 ?z => constr:(C4 (Z_to_bv 64 z))
  | Z_to_le_bytes 1 ?z => constr:(C1 (Z_to_bv 8 z))
  end.

(* [comment removed for export] *)
Ltac zc H := rewrite ?bv_lts_zero_r, ?bv_lts_zero_l in H; unfold bv_eqb, bv_ltu, bv_lts, bv_leu in H; fold_lit_ux_in H; try zsimp_in H; zify_bool H.

Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof alloc_ceiling_range as CEIL_RANGE__); std_lia__].

(* [comment removed for export] *)
Ltac es_store WR :=
  let HS := fresh "HS" in let ESn := fresh "ESn" in
  destruct WR as [HS ESn]; unfold MallocRep.wz, ESO_FLAGS, ESO_MARKS, ESO_BUFFER, ESO_DATA, ESO_DSIZE, ESO_DFLAGS, ESO_FILE, ESO_LINE, ESO_FUNC, ESO_TOP in HS, ESn; step;
  lazymatch type of ESn with es_raw (write_to_mem ?m ?a ?bs) _ _ =>
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem m ?a2 ?bs2) _) =>
      first [ constr_eq a a2; constr_eq bs bs2
            | replace (write_to_mem m a2 bs2) with (write_to_mem m a bs) by (unfold wa; f_equal; first [reflexivity | word_eq_tac | vm_compute; reflexivity]) ]
    end;
    try match goal with H : es_raw m _ _ |- _ => clear H end
  end;
  store_done; rename ESn into ES;
  (* [comment removed for export] *)
  try lazymatch goal with
  | ES : es_raw _ _ ?g, GL : g_len _ |- _ =>
      let GLn := fresh "GLn" in
      assert (GLn : g_len g)
        by (let H := fresh in pose proof GL as H; unfold g_len in H |- *;
            cbn [g_fl g_ma g_bu g_da g_ds g_df g_fi g_li g_fu g_top g_bot set_g_fl set_g_ma set_g_bu set_g_da set_g_ds set_g_df set_g_fi set_g_li set_g_fu set_g_top set_g_bot] in H |- *;
            rewrite ?upd_length in H; rewrite ?upd_length; exact H);
      clear GL; rename GLn into GL
  end.

(* [comment removed for export] *)
Ltac post_call_es segs m ES GL :=
  let ms' := fresh "ms'" in let PO := fresh "POST" in
  intros ms' PO; destruct_exs PO;
  let E := fresh "E" in let MUc := fresh "MUc" in let WMc := fresh "WMc" in let MIc := fresh "MI" in
  destruct PO as [E [MUc [WMc PO]]];
  first [ destruct PO as [MIc PO] | rename PO into MIc ];
  subst ms';
  lazymatch type of MUc with
  | munch _ m ?m' =>
      eapply es_raw_transport in ES; [|exact GL|exact MUc|exact WMc|cbn; lia];
      transport_after_call segs m m' MUc WMc; clear MUc WMc;
      try match goal with H : mem_inv segs m |- _ => clear H end; try clear m
  end;
  try destruct_ands PO;
  try (lazymatch goal with |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
      replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end).

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Definition ERR_CLEAR_ERROR : Z := 0xe8a10.
Definition ERR_CLEAR_ERROR_STACK : Z := 48 + 64 + 16 + 8192.

Definition ERR_clear_error_spec : Prop := forall bo0 : Z * Z,
  ap_stmt ERR_CLEAR_ERROR ERR_CLEAR_ERROR_STACK (fun st OW m a0 a1 a2 a3 a4 a5 bo => bo = bo0) (fun st => err_clear_error st)
          (fun r OW' m' a0' bo' => bo' = bo0 /\ snd r = st_of_ls (ls_of_st (snd r))).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Fixpoint clr (k : nat) (st : ap_st bptr) : ap_st bptr := match k with O => st | S k' => ecl_fin k' (clr k' st) end.

Lemma clr_proj : forall k st, as_top (clr k st) = as_top st /\ as_bottom (clr k st) = as_bottom st /\ as_cnf (clr k st) = as_cnf st.
Proof.
  induction k as [|k IH]; intros st; [repeat split; reflexivity|]. cbn [clr]. destruct (IH st) as (T & B & C).
  pose proof (ecd_proj k (clr k st)) as (PT & PB & _ & _ & _ & _ & _ & PC).
  unfold ecl_fin, ecl_mid. cbn [as_top as_bottom as_cnf set_func set_file set_line set_buf set_marks]. rewrite PT, PB, PC. repeat split; assumption.
Qed.

Lemma clr_shape : forall k st, es_shape st -> es_shape (clr k st).
Proof.
  induction k as [|k IH]; intros st SH; [exact SH|]. cbn [clr]. unfold ecl_fin, ecl_mid. do 5 apply es_shape_setters.
  unfold ecd. destruct (negb _); [destruct (get_data _ _)|]; repeat apply es_shape_setters; apply IH; exact SH.
Qed.

(* [comment removed for export] *)
Lemma clr_hi : forall k st j, (k <= j)%nat ->
  get_file j (clr k st) = get_file j st /\ get_func j (clr k st) = get_func j st /\ get_data j (clr k st) = get_data j st
  /\ get_dflags j (clr k st) = get_dflags j st /\ get_marks j (clr k st) = get_marks j st /\ get_buf j (clr k st) = get_buf j st
  /\ nth j (as_line (clr k st)) 0 = nth j (as_line st) 0.
Proof.
  induction k as [|k IH]; intros st j Hj; [repeat split; reflexivity|]. cbn [clr]. destruct (IH st j ltac:(lia)) as (F1 & F2 & F3 & F4 & F5 & F6 & F7).
  set (X := clr k st) in *. unfold ecl_fin, ecl_mid, ecd, get_file, get_func, get_data, get_dflags, get_marks, get_buf in *.
  destruct (negb _); [destruct (nth k (as_data X) None)|];
    cbn [as_file as_func as_data as_dflags as_marks as_buf as_line set_func set_file set_line set_buf set_marks set_dflags set_data];
    rewrite !nth_lset_other by lia; repeat split; assumption.
Qed.

(* [comment removed for export] *)
Lemma clr_lo : forall k st j, es_shape st -> dflags_ok st -> (k <= ERR_NUM)%nat -> (j < k)%nat ->
  get_file j (clr k st) = None /\ get_func j (clr k st) = None /\ get_marks j (clr k st) = 0 /\ get_buf j (clr k st) = 0
  /\ nth j (as_line (clr k st)) 0 = -1
  /\ ((get_data j (clr k st) = None /\ get_dflags j (clr k st) = 0)
      \/ (exists b, get_data j (clr k st) = Some b /\ get_data j st = Some b /\ get_dflags j (clr k st) = ERR_TXT_MALLOCED)).
Proof.
  induction k as [|k IH]; intros st j SH DF Hk Hj; [lia|]. cbn [clr].
  pose proof (clr_shape k st SH) as SHk. pose proof SHk as (L1 & L2 & L3 & L4 & L5 & L6 & L7). unfold ERR_NUM in *.
  set (X := clr k st) in *.
  destruct (Nat.eq_dec j k) as [->|NE].
  - (* [comment removed for export] *)
    destruct (clr_hi k st k ltac:(lia)) as (_ & _ & F3 & F4 & _). fold X in F3, F4.
    unfold ecl_fin, ecl_mid, ecd, get_file, get_func, get_data, get_dflags, get_marks, get_buf in *.
    destruct (Z.eqb_spec (Z.land (nth k (as_dflags X) 0) ERR_TXT_MALLOCED) 0) as [E0|E0]; cbn [negb].
    + cbn [as_file as_func as_data as_dflags as_marks as_buf as_line set_func set_file set_line set_buf set_marks set_dflags set_data].
      rewrite !nth_lset_same by lia. repeat split; try reflexivity. left. split; reflexivity.
    + destruct (nth k (as_data X) None) as [b|] eqn:GD.
      * cbn [as_file as_func as_data as_dflags as_marks as_buf as_line set_func set_file set_line set_buf set_marks set_dflags set_data].
        rewrite !nth_lset_same by lia. repeat split; try reflexivity. right. exists b. rewrite GD. split; [reflexivity|]. split; [symmetry; exact F3|reflexivity].
      * exfalso. apply E0. rewrite F4. apply DF. unfold get_data. symmetry. exact F3.
  - destruct (IH st j SH DF ltac:(lia) ltac:(lia)) as (G1 & G2 & G3 & G4 & G5 & G6). fold X in G1, G2, G3, G4, G5, G6.
    unfold ecl_fin, ecl_mid, ecd, get_file, get_func, get_data, get_dflags, get_marks, get_buf in *.
    destruct (negb _); [destruct (nth k (as_data X) None)|];
      cbn [as_file as_func as_data as_dflags as_marks as_buf as_line set_func set_file set_line set_buf set_marks set_dflags set_data];
      rewrite !nth_lset_other by lia; repeat split; assumption.
Qed.

Lemma list_eq_nth : forall {X} (l1 l2 : list X) d, length l1 = length l2 -> (forall j, (j < length l1)%nat -> nth j l1 d = nth j l2 d) -> l1 = l2.
Proof.
  induction l1 as [|x l1 IH]; intros [|y l2] d HL HN; cbn in HL; try discriminate; [reflexivity|].
  f_equal; [exact (HN 0%nat ltac:(cbn; lia))|]. apply (IH l2 d); [lia|]. intros j Hj. exact (HN (S j) ltac:(cbn; lia)).
Qed.

(* [comment removed for export] *)
Lemma clr_nf : forall st, es_shape st -> dflags_ok st ->
  set_bottom 0 (set_top 0 (clr ERR_NUM st)) = st_of_ls (ls_of_st (set_bottom 0 (set_top 0 (clr ERR_NUM st)))).
Proof.
  intros st SH DF. pose proof (clr_shape ERR_NUM st SH) as SHX.
  assert (SL : forall j, (j < ERR_NUM)%nat -> let X := clr ERR_NUM st in get_file j X = None /\ get_func j X = None /\ get_marks j X = 0 /\ get_buf j X = 0 /\ nth j (as_line X) 0 = -1
            /\ ((get_data j X = None /\ get_dflags j X = 0) \/ (exists b, get_data j X = Some b /\ get_data j st = Some b /\ get_dflags j X = ERR_TXT_MALLOCED))).
  { intros j Hj. exact (clr_lo ERR_NUM st j SH DF ltac:(lia) Hj). }
  set (X := clr ERR_NUM st) in *. clearbody X. destruct X as [t b fi fu ma bu li da df cn].
  destruct SHX as (L1 & L2 & L3 & L4 & L5 & L6 & L7). cbn [as_marks as_buf as_data as_dflags as_file as_line as_func] in L1, L2, L3, L4, L5, L6, L7.
  unfold get_file, get_func, get_marks, get_buf, get_data, get_dflags in SL. cbn -[nth Z.land ERR_TXT_MALLOCED ERR_NUM] in SL.
  unfold st_of_ls, ls_of_st, set_bottom, set_top. cbn [as_top as_bottom as_file as_func as_marks as_buf as_line as_data as_dflags as_cnf]. unfold ERR_NUM in *.
  assert (MN : forall (l : list (option (bptr * Z))) j0,
            nth j0 (map (fun d => match d with Some _ => ERR_TXT_MALLOCED | None => 0 end) l) 0 = match nth j0 l None with Some _ => ERR_TXT_MALLOCED | None => 0 end).
  { intros l j0. exact (map_nth (fun d : option (bptr * Z) => match d with Some _ => ERR_TXT_MALLOCED | None => 0 end) l None j0). }
  assert (EFI : fi = repeat None 16).
  { apply (list_eq_nth _ _ None); [rewrite repeat_length; exact L5|]. intros j Hj. rewrite nth_repeat. exact (proj1 (SL j ltac:(lia))). }
  assert (EFU : fu = repeat None 16).
  { apply (list_eq_nth _ _ None); [rewrite repeat_length; exact L7|]. intros j Hj. rewrite nth_repeat. exact (proj1 (proj2 (SL j ltac:(lia)))). }
  assert (EMA : ma = repeat 0 16).
  { apply (list_eq_nth _ _ 0); [rewrite repeat_length; exact L1|]. intros j Hj. rewrite nth_repeat. exact (proj1 (proj2 (proj2 (SL j ltac:(lia))))). }
  assert (EBU : bu = repeat 0 16).
  { apply (list_eq_nth _ _ 0); [rewrite repeat_length; exact L2|]. intros j Hj. rewrite nth_repeat. exact (proj1 (proj2 (proj2 (proj2 (SL j ltac:(lia)))))). }
  assert (ELI : li = repeat (-1) 16).
  { apply (list_eq_nth _ _ 0); [rewrite repeat_length; exact L6|]. intros j Hj. rewrite nth_repeat_lt by lia. exact (proj1 (proj2 (proj2 (proj2 (proj2 (SL j ltac:(lia))))))). }
  assert (EDF : df = map (fun d : option (bptr * Z) => match d with Some _ => ERR_TXT_MALLOCED | None => 0 end) da).
  { apply (list_eq_nth _ _ 0); [rewrite length_map; lia|]. intros j Hj. rewrite MN.
    destruct (proj2 (proj2 (proj2 (proj2 (proj2 (SL j ltac:(lia))))))) as [[GD GF]|(bb & GD & _ & GF)]; rewrite GD, GF; reflexivity. }
  rewrite EFI, EFU, EMA, EBU, ELI, EDF. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma tb_data : forall (X : ap_st bptr), as_data (set_bottom 0 (set_top 0 X)) = as_data X. Proof. reflexivity. Qed.
Lemma tb_dflags : forall (X : ap_st bptr), as_dflags (set_bottom 0 (set_top 0 X)) = as_dflags X. Proof. reflexivity. Qed.
Lemma tb_cnf : forall (X : ap_st bptr), as_cnf (set_bottom 0 (set_top 0 X)) = as_cnf X. Proof. reflexivity. Qed.
Lemma tb_top : forall (X : ap_st bptr), as_top (set_bottom 0 (set_top 0 X)) = 0%nat. Proof. reflexivity. Qed.
Lemma tb_bot : forall (X : ap_st bptr), as_bottom (set_bottom 0 (set_top 0 X)) = 0%nat. Proof. reflexivity. Qed.
Lemma tb_marks : forall (X : ap_st bptr), as_marks (set_bottom 0 (set_top 0 X)) = as_marks X. Proof. reflexivity. Qed.
Lemma tb_shape : forall (X : ap_st bptr), es_shape X -> es_shape (set_bottom 0 (set_top 0 X)). Proof. intros X H. exact H. Qed.

Lemma get_data_tb : forall (X : ap_st bptr) i, get_data i (set_bottom 0 (set_top 0 X)) = get_data i X. Proof. reflexivity. Qed.
Lemma get_dflags_tb : forall (X : ap_st bptr) i, get_dflags i (set_bottom 0 (set_top 0 X)) = get_dflags i X. Proof. reflexivity. Qed.
Lemma get_data_over : forall (X : ap_st bptr) i, (length (as_data X) <= i)%nat -> get_data i X = None.
Proof. intros X i H. unfold get_data. apply nth_overflow. exact H. Qed.
Lemma get_dflags_over : forall (X : ap_st bptr) i, (length (as_dflags X) <= i)%nat -> get_dflags i X = 0.
Proof. intros X i H. unfold get_dflags. apply nth_overflow. exact H. Qed.
(* [comment removed for export] *)
Lemma as_data_in : forall (X : ap_st bptr) p n, In (Some (p, n)) (as_data X) -> exists i, (i < length (as_data X))%nat /\ get_data i X = Some (p, n).
Proof. intros X p n Hin. destruct (In_nth _ _ None Hin) as (i & Hi & Hn). exists i. split; [exact Hi|exact Hn]. Qed.
Lemma as_data_tb_in : forall (X : ap_st bptr) p n, In (Some (p, n)) (as_data (set_bottom 0 (set_top 0 X))) -> In (Some (p, n)) (as_data X).
Proof. intros X p n H. exact H. Qed.
Lemma es_ids_tb : forall (X : ap_st bptr) q, In q (es_ids (set_bottom 0 (set_top 0 X))) -> In q (es_ids X).
Proof. intros X q H. unfold es_ids in *. rewrite st_blocks_set_bottom, st_blocks_set_top in H. exact H. Qed.
Lemma optb_ok_of_slots : forall OW' (X : ap_st bptr),
  (forall i q k, get_data i X = Some (q, k) -> In (q, badr OW' q, k) OW' /\ 0 < badr OW' q) -> Forall (optb_ok OW') (as_data X).
Proof.
  intros OW' X H. apply Forall_forall. intros [[q k]|] Hin; [|exact I]. destruct (as_data_in X q k Hin) as (i & _ & Gi). exact (H i q k Gi).
Qed.

(* [comment removed for export] *)
Lemma clear_step_tree : forall {B} i n (K : unit -> @AM bptr B) (st : ap_st bptr),
  abind (err_clear_slots i (S n)) K st
  = ofree (option_map fst (get_file i (ecl_mid i st))) (ofree (option_map fst (get_func i (ecl_mid i st))) (abind (err_clear_slots (S i) n) K (ecl_fin i st))).
Proof.
  intros B i n K st. cbn [err_clear_slots]. unfold abind at 1. unfold abind at 1. rewrite err_clear_false_tree.
  rewrite !apbind_ofree. cbn [apbind fst snd]. reflexivity.
Qed.

Section Proofs.
  Hypothesis HF : rfree_stmt.

  Section Act.
  Variables (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (m : mem) (s : PState) (st : ap_st bptr) (OW LB : list block) (E : ap_env) (bo0 : Z * Z) (lo B : Z) (canary : word).
  Hypothesis IDS : ids_ok E st.
  Hypothesis SPB : bv_unsigned sp <= B.
  Hypothesis B63 : B < 2 ^ 63.
  Hypothesis CEIL : alloc_ceiling <= lo.
  Hypothesis GLO : 3493888 <= lo.
  Hypothesis LO : lo <= bv_unsigned sp - (48 + 64 + 16 + 8192).
  Hypothesis SP16 : bv_unsigned sp mod 16 = 0.
  Hypothesis FRM : frm0 fc.
  Hypothesis SH : es_shape st.
  Hypothesis IES : In (p_es E, e_es E, 904) OW.
  Hypothesis EESP : 0 < e_es E.
  Hypothesis EESC : e_es E + 904 <= alloc_ceiling.
  Hypothesis EESI : e_es E + 904 <= 65536 \/ 3493888 <= e_es E.
  Hypothesis OF : Forall (optb_ok OW) (as_file st).
  Hypothesis OFN : Forall (optb_ok OW) (as_func st).
  Hypothesis OD : Forall (optb_ok OW) (as_data st).
  Hypothesis AS0 : exists m0, ap_state st m0 OW E bo0.
  Hypothesis DF0 : dflags_ok st.
  Hypothesis CAN : canary = rr_guard.
  Hypothesis EA : errno_addr (Z_to_bv 64 RATP) = 3355012.
  Variable K : list block.
  Hypothesis KOW : forall b, In b K -> In b OW.
  Hypothesis KIDS : forall b, In b K -> ~ In (blk_id b) (es_ids st ++ env_ids E).

  Local Notation W2 := ([(bv_unsigned sp - 8320, bv_unsigned sp); (e_es E, e_es E + 904)]%Z) (only parsing).
  Local Notation SB := (seg_base s m OW st E bo0 LB K (bv_unsigned sp) B) (only parsing).
  Let POST := ap_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s OW LB E lo B canary m K
                (fun (r : unit * ap_st bptr) (OW' : list block) (m' : mem) (a0' : word) (bo' : Z * Z) => bo' = bo0 /\ snd r = st_of_ls (ls_of_st (snd r))).
  Definition ce_frame (j0 : list byte) : list cell := [CB 8 j0; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
  Definition eci_frame (i : nat) : list cell :=
    [C8 s6; C8 s5; C8 s4; C8 (Z_to_bv 64 16); C8 (Z_to_bv 64 (Z.of_nat i)); C8 (Z_to_bv 64 (e_es E)); C8 sp; C8 (Z_to_bv 64 0xe8a54)].
  Definition FIN : unit -> @AM bptr unit := fun _ => amodify (fun s' : ap_st bptr => set_bottom 0%nat (set_top 0%nat s')).

  (* [comment removed for export] *)
  Fixpoint rms (k : nat) (L : list block) : list block :=
    match k with O => L | S k' => lremove (get_func k' st) (lremove (get_file k' st) (rms k' L)) end.

  Lemma rms_keep : forall k L (b : block), In b L ->
    (forall j q n, (j < k)%nat -> get_file j st = Some (q, n) -> blk_id b <> q) ->
    (forall j q n, (j < k)%nat -> get_func j st = Some (q, n) -> blk_id b <> q) -> In b (rms k L).
  Proof using sp.
    induction k as [|k IH]; intros L b Hb HFI HFU; [exact Hb|]. cbn [rms].
    apply lremove_keep; [apply lremove_keep; [apply IH; [exact Hb| |]|]|].
    - intros j q n Hj G. eapply HFI; [|exact G]. lia.
    - intros j q n Hj G. eapply HFU; [|exact G]. lia.
    - intros q n G. eapply HFI; [|exact G]. lia.
    - intros q n G. eapply HFU; [|exact G]. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma I16 : forall i, (i < 16)%nat -> (i < length (as_file st))%nat /\ (i < length (as_func st))%nat /\ (i < length (as_data st))%nat /\ length (as_dflags st) = length (as_data st).
  Proof using CEIL EESC GLO LO SH. intros i Hi. pose proof SH as (L1 & L2 & L3 & L4 & L5 & L6 & L7). unfold ERR_NUM in *. repeat split; lia. Qed.

  Lemma clr_perm : forall k, (k <= 16)%nat -> exists pre, Permutation (pre ++ st_blocks (clr k st)) (st_blocks st).
  Proof using SH sp.
    induction k as [|k IH]; intros Hk; [exists []; apply Permutation_refl|].
    destruct (IH ltac:(lia)) as [pre P]. cbn [clr].
    destruct (st_blocks_ecl_fin k (clr k st) (clr_shape k st SH) ltac:(unfold ERR_NUM; lia)) as (pre' & P' & _).
    exists (pre ++ (optb (get_file k (clr k st)) ++ optb (get_func k (clr k st)) ++ pre')). rewrite <- app_assoc.
    eapply Permutation_trans; [|exact P]. apply Permutation_app_head. exact P'.
  Qed.

  Lemma clr_marks : forall k, marks_sub (clr k st) st.
  Proof.
    induction k as [|k IH]; [apply marks_sub_refl|]. cbn [clr]. eapply marks_sub_trans; [apply marks_sub_ecl_fin|exact IH].
  Qed.

  Lemma clr_ids : forall k, (k <= 16)%nat -> ids_ok E (clr k st).
  Proof using IDS SH sp.
    intros k Hk. destruct (clr_perm k Hk) as [pre P]. pose proof (ids_ok_top _ _ IDS) as [T B']. pose proof (clr_proj k st) as (PT & PB & _).
    eapply ids_ok_sub; [exact P|rewrite PT; exact T|rewrite PB; exact B'|apply clr_marks|exact IDS].
  Qed.

  Lemma clr_es_ids : forall k q, (k <= 16)%nat -> In q (es_ids (clr k st)) -> In q (es_ids st).
  Proof using SH sp. intros k q Hk Hq. destruct (clr_perm k Hk) as [pre P]. eapply es_ids_sub_perm; [exact P|exact Hq]. Qed.

  (* [comment removed for export] *)
  Lemma slot_file_in : forall i q n, (i < 16)%nat -> get_file i st = Some (q, n) -> In (q, badr OW q, n) (rms i OW) /\ 0 < badr OW q.
  Proof using IDS OF sp.
    intros i q n Hi GF. destruct (optb_ok_nth OW _ i q n OF GF) as [HIn HP]. split; [|exact HP].
    pose proof (ids_ok_nodup_arrays E st IDS) as (NF & NN & ND). apply rms_keep; [exact HIn| |]; cbn [blk_id fst snd].
    - intros j q' n' Hj G. eapply (fm_nodup_slots (as_file st) i j); [exact NF|exact GF|exact G|lia].
    - intros j q' n' Hj G. eapply ids_file_func_ne; [exact IDS|exact GF|exact G].
  Qed.
  Lemma slot_func_in : forall i q n, (i < 16)%nat -> get_func i st = Some (q, n) ->
    In (q, badr OW q, n) (lremove (get_file i st) (rms i OW)) /\ 0 < badr OW q.
  Proof using IDS OFN sp.
    intros i q n Hi GN. destruct (optb_ok_nth OW _ i q n OFN GN) as [HIn HP]. split; [|exact HP].
    pose proof (ids_ok_nodup_arrays E st IDS) as (NF & NN & ND). apply lremove_keep; [apply rms_keep; [exact HIn| |]|]; cbn [blk_id fst snd].
    - intros j q' n' Hj G. apply not_eq_sym. eapply ids_file_func_ne; [exact IDS|exact G|exact GN].
    - intros j q' n' Hj G. eapply (fm_nodup_slots (as_func st) i j); [exact NN|exact GN|exact G|lia].
    - intros q' n' G. apply not_eq_sym. eapply ids_file_func_ne; [exact IDS|exact G|exact GN].
  Qed.
  Lemma slot_data_in : forall k i q n, get_data i st = Some (q, n) -> In (q, badr OW q, n) (rms k OW) /\ 0 < badr OW q.
  Proof using IDS OD sp.
    intros k i q n GD. destruct (optb_ok_nth OW _ i q n OD GD) as [HIn HP]. split; [|exact HP].
    apply rms_keep; [exact HIn| |]; cbn [blk_id fst snd].
    - intros j q' n' Hj G. apply not_eq_sym. eapply ids_file_data_ne; [exact IDS|exact G|exact GD].
    - intros j q' n' Hj G. apply not_eq_sym. eapply ids_func_data_ne; [exact IDS|exact G|exact GD].
  Qed.
  Lemma es_in_rms : forall k, In (p_es E, e_es E, 904) (rms k OW).
  Proof using IDS IES sp.
    intros k. apply rms_keep; [exact IES| |]; cbn [blk_id fst snd]; intros j q n Hj G; apply not_eq_sym; (eapply ids_es_ne; [exact IDS|]);
      [eapply es_ids_file; exact G|eapply es_ids_func; exact G].
  Qed.
  Lemma badr_rms_data : forall k i q n, get_data i st = Some (q, n) -> badr (rms k OW) q = badr OW q.
  Proof using IDS.
    induction k as [|k IH]; intros i q n GD; [reflexivity|]. cbn [rms].
    rewrite badr_lremove by (intros q' n' G; apply not_eq_sym; eapply ids_func_data_ne; [exact IDS|exact G|exact GD]).
    rewrite badr_lremove by (intros q' n' G; apply not_eq_sym; eapply ids_file_data_ne; [exact IDS|exact G|exact GD]). eapply IH. exact GD.
  Qed.
  Lemma rest_rms : forall k mX, ap_rest mX OW E bo0 (as_cnf st) -> ap_rest mX (rms k OW) E bo0 (as_cnf st).
  Proof using IDS.
    induction k as [|k IH]; intros mX AR; [exact AR|]. cbn [rms]. apply rest_lremove; [apply rest_lremove; [apply IH; exact AR|]|].
    - intros q n G. split; [eapply file_not_rest; [exact IDS|exact G]|eapply ids_es_ne; [exact IDS|eapply es_ids_file; exact G]].
    - intros q n G. split; [eapply func_not_rest; [exact IDS|exact G]|eapply ids_es_ne; [exact IDS|eapply es_ids_func; exact G]].
  Qed.
  Lemma K_rms : forall k b, In b K -> In b (rms k OW).
  Proof using KIDS KOW sp.
    intros k b Hb. apply rms_keep; [apply KOW; exact Hb| |]; intros j q n Hj G EQ; apply (KIDS b Hb); apply in_app_iff; left; rewrite EQ;
      [eapply es_ids_file; exact G|eapply es_ids_func; exact G].
  Qed.
  Lemma ees16 : e_es E mod 16 = 0.
  Proof. destruct AS0 as [m0 A]. pose proof (ap_state_es _ _ _ _ _ A) as (_ & _ & _ & _ & _ & _ & H & _). exact H. Qed.

  (* [comment removed for export] *)
  Definition at_pc (pc : Z) (i : nat) (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) (mc : mem) : machine_state :=
    MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -48)) gp (Z_to_bv 64 RATP) x5 x6 x7 sp (Z_to_bv 64 (e_es E)) x10 x11 x12 x13 x14 x15 x16 x17
            (Z_to_bv 64 (Z.of_nat i)) (Z_to_bv 64 16) s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
       F (Z_to_bv 64 pc) fc None mc (seg_rom ctusegs).

  (* [comment removed for export] *)
  Definition round_ok (i n : nat) : Prop :=
    forall (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) sZ mb mc (errv2 : word) (j0 : list byte),
      SB sZ (rms i OW) mb -> munch W2 mb mc -> wmono ctusegs mb mc ->
      rw_cells ctusegs mc (bv_unsigned sp + -48) (ce_frame j0) -> rw_cells ctusegs mc 3355012 [C4 errv2] ->
      stk ctusegs mc lo (bv_unsigned sp + -48) -> mem_inv ctusegs mc ->
      es_raw mc (e_es E) (g_of (clr i st) (badr OW)) ->
      implM ctusegs (interp (ap_embed (abind (err_clear_slots i n) FIN (clr i st)))) sZ POST
        (at_pc 0xe8a44 i x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 mc).

  (* [comment removed for export] *)
  Definition FINAL : ap_st bptr := set_bottom 0 (set_top 0 (clr 16 st)).

  Lemma fin_nf : FINAL = st_of_ls (ls_of_st FINAL).
  Proof using DF0 SH. pose proof (clr_nf st SH DF0) as NF. change ERR_NUM with 16%nat in NF. exact NF. Qed.

  Lemma fin_shape : es_shape FINAL.
  Proof using SH. unfold FINAL. apply tb_shape. apply clr_shape. exact SH. Qed.

  Lemma fin_dsub : forall i q k, get_data i FINAL = Some (q, k) -> get_data i st = Some (q, k).
  Proof using CEIL DF0 EESC GLO LO SH.
    intros i q k Hd. unfold FINAL in Hd. rewrite get_data_tb in Hd.
    pose proof (clr_shape 16 st SH) as (_ & _ & L3' & _). unfold ERR_NUM in L3'.
    assert (Hi : (i < 16)%nat).
    { destruct (Nat.lt_ge_cases i 16) as [X|X]; [exact X|]. rewrite get_data_over in Hd by lia. discriminate. }
    destruct (clr_lo 16 st i SH DF0 ltac:(unfold ERR_NUM; lia) Hi) as (_ & _ & _ & _ & _ & [[GD _]|(b & GD & GD0 & _)]); rewrite GD in Hd; [discriminate|].
    injection Hd as ->. exact GD0.
  Qed.

  Lemma fin_dflags : dflags_ok FINAL.
  Proof using CEIL DF0 EESC GLO LO SH.
    intros i Hd. unfold FINAL in *. rewrite get_data_tb in Hd. rewrite get_dflags_tb.
    pose proof (clr_shape 16 st SH) as (_ & _ & L3 & L4 & _). unfold ERR_NUM in L3, L4.
    destruct (Nat.lt_ge_cases i 16) as [Hi|Hi]; [|rewrite get_dflags_over by lia; reflexivity].
    destruct (clr_lo 16 st i SH DF0 ltac:(unfold ERR_NUM; lia) Hi) as (_ & _ & _ & _ & _ & [[GD GF]|(b & GD & _ & GF)]); [rewrite GF; reflexivity|rewrite GD in Hd; discriminate].
  Qed.

  Lemma fin_ids : ids_ok E FINAL.
  Proof using IDS SH sp. unfold FINAL. eapply ids_ok_same; [rewrite st_blocks_set_bottom, st_blocks_set_top; reflexivity|rewrite tb_top; unfold ERR_NUM; lia|rewrite tb_bot; unfold ERR_NUM; lia|apply marks_sub_eq; apply tb_marks|apply clr_ids; lia]. Qed.

  Lemma fin_kids : forall b, In b K -> ~ In (blk_id b) (es_ids FINAL).
  Proof using KIDS SH sp.
    intros b Hb Hin. apply (KIDS b Hb). apply in_app_iff. left. exact (clr_es_ids 16 _ (Nat.le_refl 16%nat) (es_ids_tb _ _ Hin)).
  Qed.

  Lemma fin_data_slots : forall i q k, get_data i FINAL = Some (q, k) -> In (q, badr (rms 16 OW) q, k) (rms 16 OW) /\ 0 < badr (rms 16 OW) q.
  Proof using CEIL DF0 EESC GLO IDS LO OD SH. intros i q k Hd. pose proof (fin_dsub i q k Hd) as GD0. rewrite (badr_rms_data 16 i q k GD0). apply (slot_data_in 16 i q k GD0). Qed.

  Lemma fin_state : forall m9, ap_rest m9 OW E bo0 (as_cnf st) -> es_raw m9 (e_es E) (g_of FINAL (badr OW)) -> ap_state FINAL m9 (rms 16 OW) E bo0.
  Proof using CEIL DF0 EESC GLO IDS LO OD SH.
    intros m9 AR9 ES. pose proof fin_nf as NF. apply ap_state_join.
    - unfold FINAL. rewrite tb_cnf. rewrite (proj2 (proj2 (clr_proj 16 st))). apply rest_rms. exact AR9.
    - exact fin_shape.
    - rewrite (g_of_adr_ext FINAL (badr (rms 16 OW)) (badr OW)); [exact ES| | |].
      + rewrite NF. cbn [as_file st_of_ls ls_of_st]. intros p n Hin. apply repeat_spec in Hin. discriminate.
      + rewrite NF. cbn [as_func st_of_ls ls_of_st]. intros p n Hin. apply repeat_spec in Hin. discriminate.
      + intros p n Hin. destruct (as_data_in FINAL p n Hin) as (i & _ & Gi). eapply badr_rms_data. exact (fin_dsub i p n Gi).
    - rewrite NF. cbn [as_file st_of_ls ls_of_st]. apply Forall_forall. intros o Ho. apply repeat_spec in Ho. subst o. exact I.
    - rewrite NF. cbn [as_func st_of_ls ls_of_st]. apply Forall_forall. intros o Ho. apply repeat_spec in Ho. subst o. exact I.
    - apply optb_ok_of_slots. exact fin_data_slots.
  Qed.

  Lemma fin_data : forall m9, data_cells m9 OW st -> data_cells m9 (rms 16 OW) FINAL.
  Proof using CEIL DF0 EESC GLO IDS LO SH.
    intros m9 DC9. apply (data_cells_sub m9 (rms 16 OW) st).
    - eapply data_cells_OW; [exact DC9|]. intros i q k Hd. eapply badr_rms_data. exact Hd.
    - intros i q k Hd. exists i. apply fin_dsub. exact Hd.
    - exact fin_dflags.
  Qed.

  (* [comment removed for export] *)
  Lemma ece_finish : forall (x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) sZ mb m9 (errv' : word),
    SB sZ (rms 16 OW) mb -> munch W2 mb m9 -> wmono ctusegs mb m9 ->
    es_raw m9 (e_es E) (g_of FINAL (badr OW)) -> stk ctusegs m9 lo (bv_unsigned sp) -> mem_inv ctusegs m9 ->
    rw_cells ctusegs m9 3355012 [C4 errv'] ->
    POST (tt, FINAL) sZ
         (MS (mkR ra sp gp (wz RATP) x5 x6 x7 s0 s1 x10 x11 x12 x13 x14 x15 x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
             F (ret_pc ra) fc None m9 (seg_rom ctusegs)).
  Proof using AS0 B63 CAN CEIL DF0 EA EESC FRM GLO IDS IES KIDS LO OD SH SP16 SPB.
    intros until errv'. intros SBc MU WM ES ST MI ERR.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    assert (SB9 : SB sZ (rms 16 OW) m9).
    { eapply (seg_base_munch s m OW st E bo0 LB K (bv_unsigned sp) lo B CEIL); [unfold GLOBALS_TOP; lia|lia|exact SBc|exact MU|exact WM|].
      constructor; [left; cbn; lia|]. constructor; [|constructor].
      right. right. exists (p_es E), (e_es E), 904. split; [apply es_in_rms|]. split; [apply (es_writable OW st E bo0 K IDS AS0 KIDS)|cbn; lia]. }
    destruct SB9 as (HEAP9 & AUX9 & LX9 & AR9 & RB9 & DC9 & DIN9 & KP9 & KOW9 & IES9 & SO9 & FA9).
    pose proof (fin_state m9 AR9 ES) as AS9. pose proof (fin_data m9 DC9) as DC9'. pose proof fin_ids as IDS9. pose proof fin_kids as KID9. pose proof fin_nf as NF.
    revert AS9 DC9' IDS9 KID9 NF. generalize FINAL. intros FIN AS9 DC9' IDS9 KID9 NF.
    set (OW16 := rms 16 OW) in *. clearbody OW16.
    unfold POST, ap_post.
    exists x5, x6, x7, x10, x11, x12, x13, x14, x15, x16, x17, x28, x29, x30, x31, F, fc, m9, OW16, errv', bo0.
    split; [reflexivity|]. split; [exact FRM|]. split; [intros; reflexivity|].
    split; [|split; [exact LX9|split; [exact SO9|split; [exact FA9|split; [|split; [reflexivity|]]]]]].
    3:{ cbn [snd]. exact NF. }
    all: cbn [snd].
    2:{ split; [exact KOW9|]. split; [exact KID9|exact KP9]. }
    unfold ap_pre. split; [exact HEAP9|]. split; [exact AS9|]. split; [exact IDS9|]. split; [exact DC9'|]. split; [exact AUX9|]. split; [exact SPB|]. split; [exact B63|].
    split; [exact ST|]. split; [exact CEIL|]. split; [unfold GLOBALS_TOP; exact GLO|]. split; [clear - LO SPR; lia|].
    split. { unfold MallocRep.wz. rewrite EA. exact ERR. }
    split. { rewrite CAN. eapply RHEAP_ssp. exact HEAP9. } split. { exact MI. } exact SP16.
  Qed.

  (* [comment removed for export] *)
  Lemma slot_i : forall i, (i < 16)%nat ->
    get_file i (clr i st) = get_file i st /\ get_func i (clr i st) = get_func i st /\ get_data i (clr i st) = get_data i st /\ get_dflags i (clr i st) = get_dflags i st.
  Proof. intros i Hi. destruct (clr_hi i st i (Nat.le_refl i)) as (F1 & F2 & F3 & F4 & _). repeat split; assumption. Qed.
  Lemma slot_i_mid : forall i, get_file i (ecd i (clr i st)) = get_file i (clr i st) /\ get_func i (ecd i (clr i st)) = get_func i (clr i st)
    /\ nth i (as_file (ecd i (clr i st))) None = get_file i (clr i st) /\ nth i (as_func (ecd i (clr i st))) None = get_func i (clr i st)
    /\ get_file i (ecl_mid i (clr i st)) = get_file i (clr i st) /\ get_func i (ecl_mid i (clr i st)) = get_func i (clr i st).
  Proof.
    intros i. pose proof (ecd_proj i (clr i st)) as (_ & _ & PF & PN & _). unfold get_file, get_func, ecl_mid. cbn [as_file as_func set_line set_buf set_marks].
    rewrite PF, PN. repeat split; reflexivity.
  Qed.
  Lemma shape_mid : forall i, es_shape (ecd i (clr i st)).
  Proof using SH. intros i. unfold ecd. destruct (negb _); [destruct (get_data _ _)|]; repeat apply es_shape_setters; apply clr_shape; exact SH. Qed.
  Lemma clr_S : forall i, clr (S i) st = ecl_fin i (clr i st). Proof. reflexivity. Qed.

  (* [comment removed for export] *)
  Lemma ece_body2 : forall (i n : nat) (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x22 x28 x29 x30 x31 : word) sZ mb mc (errv2 : word) (j0 : list byte),
    (i < 16)%nat ->
    SB sZ (rms i OW) mb -> munch W2 mb mc -> wmono ctusegs mb mc ->
    rw_cells ctusegs mc (bv_unsigned sp + -48) (ce_frame j0) -> rw_cells ctusegs mc (bv_unsigned sp + -112) (eci_frame i) ->
    rw_cells ctusegs mc 3355012 [C4 errv2] ->
    stk ctusegs mc lo (bv_unsigned sp + -112) -> mem_inv ctusegs mc ->
    es_raw mc (e_es E) (g_of (ecd i (clr i st)) (badr OW)) ->
    (forall (y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 : word) sW mb' mc' (errv3 : word),
        SB sW (rms (S i) OW) mb' -> munch W2 mb' mc' -> wmono ctusegs mb' mc' ->
        rw_cells ctusegs mc' (bv_unsigned sp + -48) (ce_frame j0) -> rw_cells ctusegs mc' 3355012 [C4 errv3] ->
        stk ctusegs mc' lo (bv_unsigned sp + -48) -> mem_inv ctusegs mc' ->
        es_raw mc' (e_es E) (g_of (clr (S i) st) (badr OW)) ->
        implM ctusegs (interp (ap_embed (abind (err_clear_slots (S i) n) FIN (clr (S i) st)))) sW POST
          (at_pc 0xe8a58 (S i) y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 mc')) ->
    implM ctusegs (interp (lofree (option_map fst (get_file i st)) (lofree (option_map fst (get_func i st))
                             (ap_embed (abind (err_clear_slots (S i) n) FIN (clr (S i) st)))))) sZ POST
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -112)) gp (Z_to_bv 64 RATP) x5 x6 x7 (Z_to_bv 64 (bv_unsigned sp + -48)) (Z_to_bv 64 (e_es E))
               x10 x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 (8 * Z.of_nat i)) (Z_to_bv 64 (4 * Z.of_nat i)) (Z_to_bv 64 (e_es E + 4 * Z.of_nat i)) (Z_to_bv 64 (e_es E + 512 + 4 * Z.of_nat i))
               x22 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0xe8598) fc None mc (seg_rom ctusegs)).
  Proof using AS0 B63 CEIL EESC EESI EESP GLO HF IDS IES KIDS LO OF OFN SH SPB canary.
    intros until j0. intros Hi SBc MU WM FR FRi ERR2 ST MI ES KONT.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    assert (Hi' : (i < ERR_NUM)%nat) by (unfold ERR_NUM; exact Hi).
    pose proof ees16 as EES16.
    set (X := clr i st) in *.
    pose proof (shape_mid i) as SHY. fold X in SHY.
    assert (GL : g_len (g_of (ecd i X) (badr OW))) by (apply g_len_of; exact SHY).
    destruct (slot_i i Hi) as (XF & XN & XD & XG). fold X in XF, XN, XD, XG.
    destruct (slot_i_mid i) as (YF & YN & YF' & YN' & _). fold X in YF, YN, YF', YN'. rewrite XF in YF, YF'. rewrite XN in YN, YN'.
    assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -112)) = bv_unsigned sp + -112) by (apply unsigned_lit; lia).
    unfold at_pc, ce_frame, eci_frame in *. unfold implM. iprefix.
    (* [comment removed for export] *)
    step. step. es_store (es_wr_ma mc (e_es E) _ i (Z_to_bv 64 0) ES GL Hi'). name_mem m1.
    (* [comment removed for export] *)
    step. step. es_store (es_wr_fl m1 (e_es E) _ i (Z_to_bv 64 0) ES GL Hi'). name_mem m2.
    (* [comment removed for export] *)
    step. step. step. es_store (es_wr_bu m2 (e_es E) _ i (Z_to_bv 64 0) ES GL Hi'). name_mem m3.
    do 4 step. es_store (es_wr_li m3 (e_es E) _ i (Z_to_bv 64 (-1)) ES GL Hi'). name_mem m4.
    (* [comment removed for export] *)
    pose proof (es_rd_fi m4 (e_es E) _ i (wa (e_es E + 576 + 8 * Z.of_nat i)) ES GL Hi' eq_refl) as RD. step. clear RD.
    setreg 10 (wz (optr (badr OW) (get_file i st))) ltac:(cbn [g_fi g_of set_g_ma set_g_fl set_g_bu set_g_li]; rewrite nth_wl_optr, YF'; reflexivity).
    do 4 step.
    (* [comment removed for export] *)
    assert (SB4 : SB sZ (rms i OW) m4).
    { eapply (seg_base_munch s m OW st E bo0 LB K (bv_unsigned sp) lo B CEIL); [unfold GLOBALS_TOP; lia|lia|exact SBc|exact MU|exact WM|].
      constructor; [left; cbn; lia|]. constructor; [|constructor].
      right. right. exists (p_es E), (e_es E), 904. split; [apply es_in_rms|]. split; [apply (es_writable OW st E bo0 K IDS AS0 KIDS)|cbn; lia]. }
    clear MU WM.
    ihere.
    lazymatch goal with |- impl ?segs _ (?c ?stt) (epost ?EE) ?ms =>
      lazymatch EE with (fun p => ?Q (fst p) (snd p)) => change (implM segs c stt Q ms) end end.
    eapply (CRYPTO_free_opt_walk HF) with (B := B) (lo := lo) (errv := errv2) (od := get_file i st) (adr := badr OW) (L := rms i OW ++ LB);
      [eapply seg_base_heap; exact SB4 | | eapply seg_base_aux; exact SB4 | rewrite ESP; lia | rewrite ESP; exact ST | exact CEIL | unfold GLOBALS_TOP; lia
      | rewrite ESP; unfold CRYPTO_FREE_STACK, RFREE_STACK; lia | unfold LX_ERRNO, RATP; exact ERR2 | exact MI | reflexivity
      | eapply seg_base_crypto_statics; exact SB4 | reflexivity | ].
    { destruct (get_file i st) as [[qf nf]|] eqn:GF; [|exact I]. apply in_app_iff. left. exact (proj1 (slot_file_in i qf nf Hi GF)). }
    intros sD msD PO. unfold ofree_post in PO. rewrite ?ESP in PO.
    destruct PO as (r5 & r6 & r7 & r10 & r11 & r12 & r13 & r14 & r15 & r16 & r17 & r28 & r29 & r30 & r31 & m5
                    & -> & MI5 & ST5 & ERR5 & AUX5 & HP5 & FA5 & SO5 & HEAP5).
    replace (ret_pc (Z_to_bv 64 0xe8604)) with (Z_to_bv 64 0xe8604) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    unfold LX_ERRNO, RATP in ERR5. change (3355176 - 164) with 3355012 in ERR5.
    (* [comment removed for export] *)
    assert (SB5 : SB sD (lremove (get_file i st) (rms i OW)) m5).
    { eapply (seg_base_free s m OW st E bo0 LB K (bv_unsigned sp) B); [exact SB4| |exact HP5|lia|exact HEAP5|exact AUX5|exact SO5|exact FA5].
      intros q k GF. split; [|split].
      - change q with (blk_id (q, badr OW q, k)). apply in_map. exact (proj1 (slot_file_in i q k Hi GF)).
      - split; [eapply file_not_rest; [exact IDS|exact GF]|]. split; [intros j q' k' Hd EQ; subst q'; exact (ids_file_data_ne E st i j q k q k' IDS GF Hd eq_refl)|].
        eapply K_not_es; [exact KIDS|eapply es_ids_file; exact GF].
      - eapply ids_es_ne; [exact IDS|eapply es_ids_file; exact GF]. }
    pose proof (agree_of_heap_pres _ _ _ _ HP5) as AG5.
    apply (rw_cells_agree _ _ _ _ _ AG5) in FR; [| intros a Ha; left; cbn in Ha; lia].
    apply (rw_cells_agree _ _ _ _ _ AG5) in FRi; [| intros a Ha; left; cbn in Ha; lia].
    eapply es_raw_agree in ES; [|exact GL|exact AG5|].
    2:{ intros a Ha. right. right. exists (p_es E, e_es E, 904). split; [|cbn; lia].
        apply lremove_keep; [apply in_app_iff; left; apply es_in_rms|]. intros q k GF. cbn. apply not_eq_sym. eapply ids_es_ne; [exact IDS|eapply es_ids_file; exact GF]. }
    clear AG5 HP5 HEAP5 AUX5 SB4 MI ST ERR2. rename MI5 into MI. rename ST5 into ST.
    (* [comment removed for export] *)
    pose proof (munch_refl [(bv_unsigned sp - 8320, bv_unsigned sp); (e_es E, e_es E + 904)]%Z m5) as MU. pose proof (wmono_refl ctusegs m5) as WM.
    unfold implM. iprefix.
    step. step. es_store (es_wr_fi m5 (e_es E) _ i (Z_to_bv 64 0) ES GL Hi'). name_mem m6.
    pose proof (es_rd_fu m6 (e_es E) _ i (wa (e_es E + 768 + 8 * Z.of_nat i)) ES GL Hi' eq_refl) as RD. step. clear RD.
    setreg 10 (wz (optr (badr OW) (get_func i st))) ltac:(cbn [g_fu g_of set_g_ma set_g_fl set_g_bu set_g_li set_g_fi]; rewrite nth_wl_optr, YN'; reflexivity).
    do 4 step.
    assert (SB6 : SB sD (lremove (get_file i st) (rms i OW)) m6).
    { eapply (seg_base_munch s m OW st E bo0 LB K (bv_unsigned sp) lo B CEIL); [unfold GLOBALS_TOP; lia|lia|exact SB5|exact MU|exact WM|].
      constructor; [left; cbn; lia|]. constructor; [|constructor].
      right. right. exists (p_es E), (e_es E), 904. split; [eapply seg_base_es; exact SB5|]. split; [apply (es_writable OW st E bo0 K IDS AS0 KIDS)|cbn; lia]. }
    clear MU WM.
    ihere.
    lazymatch goal with |- impl ?segs _ (?c ?stt) (epost ?EE) ?ms =>
      lazymatch EE with (fun p => ?Q (fst p) (snd p)) => change (implM segs c stt Q ms) end end.
    eapply (CRYPTO_free_opt_walk HF) with (B := B) (lo := lo) (errv := errv2) (od := get_func i st) (adr := badr OW) (L := lremove (get_file i st) (rms i OW) ++ LB);
      [eapply seg_base_heap; exact SB6 | | eapply seg_base_aux; exact SB6 | rewrite ESP; lia | rewrite ESP; exact ST | exact CEIL | unfold GLOBALS_TOP; lia
      | rewrite ESP; unfold CRYPTO_FREE_STACK, RFREE_STACK; lia | unfold LX_ERRNO, RATP; exact ERR5 | exact MI | reflexivity
      | eapply seg_base_crypto_statics; exact SB6 | reflexivity | ].
    { destruct (get_func i st) as [[qn nn]|] eqn:GN; [|exact I]. apply in_app_iff. left. exact (proj1 (slot_func_in i qn nn Hi GN)). }
    intros sE msE PO. unfold ofree_post in PO. rewrite ?ESP in PO.
    destruct PO as (q5 & q6 & q7 & q10 & q11 & q12 & q13 & q14 & q15 & q16 & q17 & q28 & q29 & q30 & q31 & m7
                    & -> & MI7 & ST7 & ERR7 & AUX7 & HP7 & FA7 & SO7 & HEAP7).
    replace (ret_pc (Z_to_bv 64 0xe862c)) with (Z_to_bv 64 0xe862c) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    unfold LX_ERRNO, RATP in ERR7. change (3355176 - 164) with 3355012 in ERR7.
    assert (SB7 : SB sE (rms (S i) OW) m7).
    { change (rms (S i) OW) with (lremove (get_func i st) (lremove (get_file i st) (rms i OW))).
      eapply (seg_base_free s m OW st E bo0 LB K (bv_unsigned sp) B); [exact SB6| |exact HP7|lia|exact HEAP7|exact AUX7|exact SO7|exact FA7].
      intros q k GN. split; [|split].
      - change q with (blk_id (q, badr OW q, k)). apply in_map. exact (proj1 (slot_func_in i q k Hi GN)).
      - split; [eapply func_not_rest; [exact IDS|exact GN]|]. split; [intros j q' k' Hd EQ; subst q'; exact (ids_func_data_ne E st i j q k q k' IDS GN Hd eq_refl)|].
        eapply K_not_es; [exact KIDS|eapply es_ids_func; exact GN].
      - eapply ids_es_ne; [exact IDS|eapply es_ids_func; exact GN]. }
    pose proof (agree_of_heap_pres _ _ _ _ HP7) as AG7.
    apply (rw_cells_agree _ _ _ _ _ AG7) in FR; [| intros a Ha; left; cbn in Ha; lia].
    apply (rw_cells_agree _ _ _ _ _ AG7) in FRi; [| intros a Ha; left; cbn in Ha; lia].
    eapply es_raw_agree in ES; [|exact GL|exact AG7|].
    2:{ intros a Ha. right. right. exists (p_es E, e_es E, 904). split; [|cbn; lia].
        apply lremove_keep; [apply in_app_iff; left; apply lremove_keep; [apply es_in_rms|]|]; intros q k G; cbn; apply not_eq_sym; (eapply ids_es_ne; [exact IDS|]);
          [eapply es_ids_file; exact G|eapply es_ids_func; exact G]. }
    clear AG7 HP7 HEAP7 AUX7 SB6 SB5 MI ST ERR5. rename MI7 into MI. rename ST7 into ST.
    (* [comment removed for export] *)
    pose proof (munch_refl [(bv_unsigned sp - 8320, bv_unsigned sp); (e_es E, e_es E + 904)]%Z m7) as MU. pose proof (wmono_refl ctusegs m7) as WM.
    unfold implM. iprefix.
    es_store (es_wr_fu m7 (e_es E) _ i (Z_to_bv 64 0) ES GL Hi'). name_mem m8.
    do 9 step. release_frame FRi ST (bv_unsigned sp + -48). step. step.
    setreg 18 (Z_to_bv 64 (Z.of_nat (S i))) ltac:(f_equal; rewrite ?unsigned_lit by lia; lia).
    (* [comment removed for export] *)
    lazymatch type of ES with es_raw _ _ ?g =>
      replace g with (g_of (clr (S i) st) (badr OW)) in ES
        by (rewrite clr_S; fold X; unfold ecl_fin, ecl_mid; rewrite g_of_set_func, g_of_set_file, g_of_set_line, g_of_set_buf, g_of_set_marks;
            cbn [g_fl g_ma g_bu g_da g_ds g_df g_fi g_li g_fu g_top g_bot set_g_fl set_g_ma set_g_bu set_g_da set_g_ds set_g_df set_g_fi set_g_li set_g_fu set_g_top set_g_bot g_of];
            unfold MallocRep.wz; cbn [optr]; rewrite (upd_zeros 16 i Hi); reflexivity)
    end.
    ihere.
    lazymatch goal with |- impl ?segs _ (?c ?stt) (epost ?EE) ?ms =>
      lazymatch EE with (fun p => ?Q (fst p) (snd p)) => change (implM segs c stt Q ms) end end.
    eapply (KONT _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ sE m7 m8 errv2); [exact SB7|exact MU|exact WM|exact FR|exact ERR7|exact ST|exact MI|exact ES].
  Qed.

  (* [comment removed for export] *)
  Lemma ece_round_k : forall (i n : nat) (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) sZ mb mc (errv2 : word) (j0 : list byte),
    (i < 16)%nat ->
    SB sZ (rms i OW) mb -> munch W2 mb mc -> wmono ctusegs mb mc ->
    rw_cells ctusegs mc (bv_unsigned sp + -48) (ce_frame j0) -> rw_cells ctusegs mc 3355012 [C4 errv2] ->
    stk ctusegs mc lo (bv_unsigned sp + -48) -> mem_inv ctusegs mc ->
    es_raw mc (e_es E) (g_of (clr i st) (badr OW)) ->
    (forall (y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 : word) sW mb' mc' (errv3 : word),
        SB sW (rms (S i) OW) mb' -> munch W2 mb' mc' -> wmono ctusegs mb' mc' ->
        rw_cells ctusegs mc' (bv_unsigned sp + -48) (ce_frame j0) -> rw_cells ctusegs mc' 3355012 [C4 errv3] ->
        stk ctusegs mc' lo (bv_unsigned sp + -48) -> mem_inv ctusegs mc' ->
        es_raw mc' (e_es E) (g_of (clr (S i) st) (badr OW)) ->
        implM ctusegs (interp (ap_embed (abind (err_clear_slots (S i) n) FIN (clr (S i) st)))) sW POST
          (at_pc 0xe8a58 (S i) y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 mc')) ->
    implM ctusegs (interp (ap_embed (abind (err_clear_slots i (S n)) FIN (clr i st)))) sZ POST
      (at_pc 0xe8a44 i x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 mc).
  Proof using AS0 B63 CEIL DF0 EESC EESI EESP GLO HF IDS IES KIDS LO OD OF OFN SH SP16 SPB canary.
    intros until j0. intros Hi SBc MU WM FR ERR2 ST MI ES KONT.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    assert (Hi' : (i < ERR_NUM)%nat) by (unfold ERR_NUM; exact Hi).
    pose proof ees16 as EES16.
    set (X := clr i st) in *.
    pose proof (clr_shape i st SH) as SHX. fold X in SHX.
    assert (GL : g_len (g_of X (badr OW))) by (apply g_len_of; exact SHX).
    destruct (slot_i i Hi) as (XF & XN & XD & XG). fold X in XF, XN, XD, XG.
    destruct (slot_i_mid i) as (_ & _ & _ & _ & MF & MN). fold X in MF, MN. rewrite XF in MF. rewrite XN in MN.
    assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -48)) = bv_unsigned sp + -48) by (apply unsigned_lit; lia).
    assert (ESP2 : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -112)) = bv_unsigned sp + -112) by (apply unsigned_lit; lia).
    (* [comment removed for export] *)
    rewrite (clear_step_tree i n FIN X), MF, MN, !ap_embed_ofree. change (ecl_fin i X) with (clr (S i) st).
    unfold at_pc, ce_frame in *. unfold implM. iprefix.
    pose proof (munch_refl [(bv_unsigned sp - 112, bv_unsigned sp - 48)]%Z mc) as MUs. pose proof (wmono_refl ctusegs mc) as WMs.
    do 4 step. carve_frame 64%nat ST. do 10 step.
    eapply es_raw_transport in ES; [|exact GL|exact MUs|exact WMs|cbn; lia]. clear MUs WMs. name_mem m0.
    step. repeat ub1c.
    setreg 19 (Z_to_bv 64 (4 * Z.of_nat i)) ltac:(f_equal; rewrite Z.shiftl_mul_pow2 by lia; lia).
    setreg 20 (Z_to_bv 64 (e_es E + 4 * Z.of_nat i)) ltac:(f_equal; rewrite Z.shiftl_mul_pow2 by lia; lia).
    setreg 21 (Z_to_bv 64 (e_es E + 512 + 4 * Z.of_nat i)) ltac:(f_equal; rewrite Z.shiftl_mul_pow2 by lia; lia).
    (* [comment removed for export] *)
    pose proof (es_rd_df1 m0 (e_es E) _ i (wa (e_es E + 512 + 4 * Z.of_nat i)) ES GL Hi' eq_refl) as RD. step. clear RD.
    step.
    set (f := get_dflags i st).
    setreg 10 (Z_to_bv 64 (Z.land f ERR_TXT_MALLOCED))
      ltac:(cbn [g_df g_of]; rewrite nth_wl; change (nth i (as_dflags X) 0) with (get_dflags i X); rewrite XG; unfold zx8, MallocRep.wz;
            rewrite (unsigned_lit (_ mod 2 ^ 8)) by (pose proof (Z.mod_pos_bound (bv_unsigned (Z_to_bv 64 (get_dflags i st))) (2 ^ 8) ltac:(lia)); lia);
            rewrite dflag_bit; reflexivity).
    assert (FR01 : 0 <= Z.land f ERR_TXT_MALLOCED <= 1) by apply land_malloced_range.
    step. setreg 18 (Z_to_bv 64 (8 * Z.of_nat i)) ltac:(f_equal; rewrite ?unsigned_lit by lia; rewrite Z.shiftl_mul_pow2 by lia; lia).
    step. if_cases KF; zc KF; rewrite ?land_malloced_mask in KF.
    - (* [comment removed for export] *)
      step. step. step.
      pose proof (es_rd_da m0 (e_es E) _ i (wa (e_es E + 256 + 8 * Z.of_nat i)) ES GL Hi' eq_refl) as RD. step. clear RD.
      setreg 10 (Z_to_bv 64 (optr (badr OW) (get_data i st))) ltac:(cbn [g_da g_of]; rewrite nth_wl_optr; change (nth i (as_data X) None) with (get_data i X); rewrite XD; reflexivity).
      destruct (get_data i st) as [[pd nd]|] eqn:GD; cbn [optr].
      2:{ exfalso. pose proof (DF0 i GD) as Z0. fold f in Z0. lia. }
      destruct (slot_data_in i i pd nd GD) as [HINd HPd].
      pose proof (blk_bounds _ _ _ _ _ _ (seg_base_heap _ _ _ _ _ _ _ _ _ _ _ _ _ SBc) ltac:(apply in_app_iff; left; exact HINd)) as (BD1 & BD2 & BD3 & BD4 & BD5).
      pose proof (blk_disjoint _ _ _ pd (badr OW pd) nd (p_es E) (e_es E) 904 (seg_base_heap _ _ _ _ _ _ _ _ _ _ _ _ _ SBc)
                    ltac:(apply in_app_iff; left; exact HINd) ltac:(apply in_app_iff; left; apply es_in_rms)
                    ltac:(eapply ids_data_es_ne; [exact IDS|exact GD])) as DJd.
      step. if_cases K2; zc K2; [exfalso; rewrite ?unsigned_lit in K2 by lia; lia|]. clear K2.
      (* [comment removed for export] *)
      assert (SB1 : SB sZ (rms i OW) m0).
      { eapply (seg_base_munch s m OW st E bo0 LB K (bv_unsigned sp) lo B CEIL); [unfold GLOBALS_TOP; lia|lia|exact SBc|exact MU|exact WM|].
        constructor; [left; cbn; lia|]. constructor; [|constructor].
        right. right. exists (p_es E), (e_es E), 904. split; [apply es_in_rms|]. split; [apply (es_writable OW st E bo0 K IDS AS0 KIDS)|cbn; lia]. }
      clear MU WM.
      pose proof SB1 as (HEAP1 & AUX1 & LX1 & AR1 & RB1 & DC1 & DIN1 & KP1 & KOW1 & IES1 & SO1 & FA1).
      destruct (proj1 DC1 i pd nd GD) as [ND1 [junkd HD]].
      assert (EK : exists k, Z.to_nat nd = S k) by (exists (Z.to_nat nd - 1)%nat; lia). destruct EK as [kd EK]. rewrite EK in HD.
      apply (rw_cells_split_CB ctusegs m0 (badr OW pd) [] (S kd) junkd [] [1%nat; kd]) in HD; [|cbn; lia].
      cbn [mk_CB_cells app] in HD.
      pose proof (munch_refl [(bv_unsigned sp - 8320, bv_unsigned sp); (badr OW pd, badr OW pd + 1)]%Z m0) as MU3. pose proof (wmono_refl ctusegs m0) as WM3.
      step. name_mem m1.
      lazymatch type of HD with rw_cells _ _ _ ?cs =>
        pose proof (rw_cells_merge ctusegs m1 (badr OW pd) (@nil cell) cs (@nil cell) ltac:(rewrite app_nil_r; exact HD)) as HD' end.
      cbn [app cells_size csize cells_bytes cbytes length] in HD'.
      match type of HD' with rw_cells _ _ _ [CB ?k ?bs] => replace k with (Z.to_nat nd) in HD' by lia end.
      assert (SB2 : SB sZ (rms i OW) m1).
      { eapply (seg_base_store_data s m OW st E bo0 LB K (bv_unsigned sp) lo B CEIL ltac:(unfold GLOBALS_TOP; lia) ltac:(lia) IDS KIDS sZ (rms i OW) m0 m1 i pd nd);
          [exact SB1|exact GD|exact HINd| | |exact MU3|exact WM3|exact HD']; lia. }
      eapply es_raw_transport in ES; [|exact GL|exact MU3|exact WM3|cbn; lia].
      clear MU3 WM3 HD HD' SB1 HEAP1 AUX1 LX1 AR1 RB1 DC1 DIN1 KP1 KOW1 IES1 SO1 FA1.
      (* [comment removed for export] *)
      pose proof (munch_refl [(bv_unsigned sp - 8320, bv_unsigned sp); (e_es E, e_es E + 904)]%Z m1) as MU. pose proof (wmono_refl ctusegs m1) as WM.
      step. step. es_store (es_wr_df m1 (e_es E) _ i (Z_to_bv 64 1) ES GL Hi'). name_mem m2.
      ihere.
      lazymatch goal with |- impl ?segs _ (?c ?stt) (epost ?EE) ?ms =>
        lazymatch EE with (fun p => ?Q (fst p) (snd p)) => change (implM segs c stt Q ms) end end.
      lazymatch type of ES with es_raw _ _ ?g =>
        replace g with (g_of (ecd i X) (badr OW)) in ES
          by (unfold ecd; rewrite XG, XD; fold f; replace (Z.land f ERR_TXT_MALLOCED =? 0) with false by (symmetry; apply Z.eqb_neq; lia); cbn [negb];
              rewrite g_of_set_dflags; unfold ERR_TXT_MALLOCED, MallocRep.wz; reflexivity)
      end.
      eapply (ece_body2 i n _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ sZ m1 m2 errv2 _ Hi); [exact SB2|exact MU|exact WM|exact FR|exact FR0|exact ERR2|exact ST|exact MI|exact ES|exact KONT].
    - (* [comment removed for export] *)
      setreg 10 (Z_to_bv 64 0) ltac:(first [rewrite KF | rewrite <- KF]; reflexivity).
      step. step. step.
      es_store (es_wr_da m0 (e_es E) _ i (Z_to_bv 64 0) ES GL Hi'). name_mem m1.
      step. step.
      es_store (es_wr_ds m1 (e_es E) _ i (Z_to_bv 64 0) ES GL Hi'). name_mem m2.
      step.
      es_store (es_wr_df m2 (e_es E) _ i (Z_to_bv 64 0) ES GL Hi'). name_mem m3.
      ihere.
      lazymatch goal with |- impl ?segs _ (?c ?stt) (epost ?EE) ?ms =>
        lazymatch EE with (fun p => ?Q (fst p) (snd p)) => change (implM segs c stt Q ms) end end.
      lazymatch type of ES with es_raw _ _ ?g =>
        replace g with (g_of (ecd i X) (badr OW)) in ES
          by (unfold ecd; rewrite XG; fold f; replace (Z.land f ERR_TXT_MALLOCED =? 0) with true by (symmetry; apply Z.eqb_eq; lia); cbn [negb];
              rewrite g_of_set_dflags, g_of_set_data; cbn [optr osize]; unfold MallocRep.wz; reflexivity)
      end.
      eapply (ece_body2 i n _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ sZ mb m3 errv2 _ Hi); [exact SBc|exact MU|exact WM|exact FR|exact FR0|exact ERR2|exact ST|exact MI|exact ES|exact KONT].
  Qed.

  (* [comment removed for export] *)
  Lemma ece_round : forall i n, (S i < 16)%nat -> round_ok (S i) n -> round_ok i (S n).
  Proof using AS0 B63 CEIL DF0 EESC EESI EESP GLO HF IDS IES KIDS LO OD OF OFN SH SP16 SPB.
    intros i n HSi IH. unfold round_ok. intros until j0. intros SBc MU WM FR ERR2 ST MI ES.
    eapply (ece_round_k i n _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ sZ mb mc errv2 j0 ltac:(lia)); [exact SBc|exact MU|exact WM|exact FR|exact ERR2|exact ST|exact MI|exact ES|].
    intros until errv3. intros SB' MU' WM' FR' ERR' ST' MI' ES'.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    unfold round_ok, at_pc in IH. unfold at_pc. unfold implM. iprefix.
    step. if_cases KK; zc KK; [|exfalso; rewrite ?unsigned_lit in KK by lia; lia]. clear KK.
    ihere.
    lazymatch goal with |- impl ?segs _ (?c ?stt) (epost ?EE) ?ms =>
      lazymatch EE with (fun p => ?Q (fst p) (snd p)) => change (implM segs c stt Q ms) end end.
    eapply (IH _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ sW mb' mc' errv3 j0); [exact SB'|exact MU'|exact WM'|exact FR'|exact ERR'|exact ST'|exact MI'|exact ES'].
  Qed.

  Lemma fin_tree : forall X : ap_st bptr, abind (err_clear_slots 16 0) FIN X = ARet (tt, set_bottom 0 (set_top 0 X)).
  Proof. intros X. reflexivity. Qed.

  (* [comment removed for export] *)
  Lemma ece_last_gen : forall X16 : ap_st bptr, clr 16 st = X16 -> round_ok 15 1.
  Proof using AS0 B63 CAN CEIL DF0 EA EESC EESI EESP FRM GLO HF IDS IES KIDS LO OD OF OFN SH SP16 SPB.
    intros X16 EX16. unfold round_ok. intros until j0. intros SBc MU WM FR ERR2 ST MI ES.
    eapply (ece_round_k 15 0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ sZ mb mc errv2 j0 ltac:(lia)); [exact SBc|exact MU|exact WM|exact FR|exact ERR2|exact ST|exact MI|exact ES|].
    intros until errv3. intros SB' MU' WM' FR' ERR' ST' MI' ES'.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    pose proof ees16 as EES16.
    (* [comment removed for export] *)
    pose proof (clr_shape 16 st SH) as SH16. clear ES. rename ES' into ES. rewrite EX16 in SH16, ES. rewrite EX16.
    assert (GL : g_len (g_of X16 (badr OW))) by (apply g_len_of; exact SH16).
    unfold at_pc, ce_frame in *. unfold implM. iprefix.
    step. if_cases KK; zc KK; [exfalso; rewrite ?unsigned_lit in KK by lia; lia|]. clear KK.
    (* [comment removed for export] *)
    es_store (es_wr_tb0 mc' (e_es E) _ ES GL). name_mem m1.
    (* [comment removed for export] *)
    do 6 step. release_frame FR' ST' (bv_unsigned sp). step.
    subst X16.
    replace (set_g_bot 0 (set_g_top 0 (g_of (clr 16 st) (badr OW)))) with (g_of FINAL (badr OW)) in ES
      by (unfold FINAL; rewrite g_of_set_bottom, g_of_set_top; reflexivity).
    rewrite (fin_tree (clr 16 st)). fold FINAL.
    apply evt_done. cbn [ap_embed interp impl]. apply evt_done. unfold epost. cbn [fst snd].
    eapply (ece_finish _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ sW mb' m1 errv3); [exact SB'|exact MU'|exact WM'|exact ES|exact ST'|exact MI'|exact ERR'].
  Qed.
  Lemma ece_last : round_ok 15 1.
  Proof using AS0 B63 CAN CEIL DF0 EA EESC EESI EESP FRM GLO HF IDS IES KIDS LO OD OF OFN SH SP16 SPB. exact (ece_last_gen (clr 16 st) eq_refl). Qed.

  (* [comment removed for export] *)
  Lemma ece_loop : forall n i, (i + n = 16)%nat -> (1 <= n)%nat -> round_ok i n.
  Proof using AS0 B63 CAN CEIL DF0 EA EESC EESI EESP FRM GLO HF IDS IES KIDS LO OD OF OFN SH SP16 SPB.
    induction n as [|n IH]; intros i Hin Hn; [lia|]. destruct n as [|n'].
    - replace i with 15%nat by lia. exact ece_last.
    - apply ece_round; [lia|]. apply IH; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma ece_act : forall (tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (errv : word),
    RHEAP s (OW ++ LB) m -> ap_state st m OW E bo0 -> data_cells m OW st -> rauxv_ok m B ->
    stk ctusegs m lo (bv_unsigned sp) -> rw_cells ctusegs m 3355012 [C4 errv] -> mem_inv ctusegs m -> tp = wz RATP ->
    implM ctusegs (interp (ap_embed (err_clear_error st))) s POST
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz ERR_CLEAR_ERROR) fc None m (seg_rom ctusegs)).
  Proof using AS0 B63 CAN CEIL DF0 EA EESC EESI EESP FRM GLO HF IDS IES KIDS KOW LO OD OF OFN SH SP16 SPB.
    intros until errv. intros HEAP AS DC AUX ST ERR MI ->.
    unfold ERR_CLEAR_ERROR, MallocRep.wz in *.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    pose proof (munch_refl [(bv_unsigned sp - 48 - 1024, bv_unsigned sp); (3355012, 3355012 + 4)]%Z m) as MU. pose proof (wmono_refl ctusegs m) as WM.
    assert (INCL : forall b, In b OW -> In b (OW ++ LB)) by (intros b Hb; apply in_app_iff; left; exact Hb).
    unfold implM. iprefix.
    carve_frame 48%nat ST. do 9 step.
    name_mem m1.
    assert (AS1 : ap_state st m1 OW E bo0).
    { eapply (ap_state_of_munch st m m1); [exact AS|exact HEAP|exact INCL|exact MU|exact WM|exact CEIL|unfold GLOBALS_TOP; exact GLO|].
      constructor; [cbn; lia|]. constructor; [right; reflexivity|constructor]. }
    assert (HEAP1 : RHEAP s (OW ++ LB) m1).
    { eapply LH_frame; [exact HEAP| exact MU| exact WM|]. constructor; [apply W_ok_stack; cbn; lia|]. constructor; [apply W_ok_errno|constructor]. }
    assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -48)) = bv_unsigned sp + -48) by (apply unsigned_lit; lia).
    eapply evt_cut.
    { eapply (get_state_call _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m1 lo s (OW ++ LB) OW E st bo0 errv 0);
        [exact AS1|exact HEAP1|exact INCL|rewrite ESP; exact ST|exact CEIL|unfold GLOBALS_TOP; lia|rewrite ESP; lia|rewrite ESP; clear - SP16 SPR GLO LO;
         replace (bv_unsigned sp + -48) with (bv_unsigned sp - 48) by lia; rewrite Zminus_mod, SP16; reflexivity
        |exact ERR|exact MI|reflexivity|left; reflexivity|reflexivity]. }
    post_call_esp ESP m1.
    match goal with H : stk ctusegs _ lo _ |- _ => rename H into ST end.
    match goal with H : rw_cells ctusegs _ 3355012 _ |- _ => rename H into ERR2 end.
    match goal with H : mem_inv ctusegs _ |- _ => rename H into MI2 end.
    name_mem m2. clear AS1 HEAP1.
    assert (AS2 : ap_state st m2 OW E bo0).
    { eapply (ap_state_of_munch st m m2); [exact AS|exact HEAP|exact INCL|exact MU|exact WM|exact CEIL|unfold GLOBALS_TOP; exact GLO|].
      constructor; [cbn; lia|]. constructor; [right; reflexivity|constructor]. }
    destruct (seg_close s OW LB _ m m2 lo (bv_unsigned sp) B HEAP AUX CEIL ltac:(unfold GLOBALS_TOP; lia) ltac:(lia) MU WM) as (HEAP2 & AUX2 & LX2).
    { constructor; [left; cbn; lia|]. constructor; [right; left; reflexivity|constructor]. }
    assert (DIN : forall i q k, get_data i st = Some (q, k) -> In (q, badr OW q, k) (OW ++ LB)).
    { intros i q k Hd. apply INCL. exact (proj1 (optb_ok_nth OW _ i q k OD Hd)). }
    assert (DC2 : data_cells m2 OW st).
    { eapply (data_cells_of_munch s (OW ++ LB) _ m m2); [exact DC|exact DIN|exact HEAP|exact CEIL|exact MU|exact WM|].
      constructor; [left; cbn; lia|]. constructor; [|constructor]. right. left. reflexivity. }
    assert (KP2 : kept K m m2).
    { eapply (kept_of_munch s (OW ++ LB) _ m m2 K lo); [exact HEAP|intros b Hb; apply INCL; apply KOW; exact Hb|exact CEIL|exact MU|].
      constructor; [left; cbn; lia|]. constructor; [|constructor]. right. left. reflexivity. }
    assert (SB2 : SB s OW m2).
    { eapply seg_base_intro; [exact HEAP2|exact AUX2|exact LX2|exact AS2|exact DC2|exact KP2|exact KOW]. }
    clear MU WM AS HEAP AUX DC m1 HEAP2 AUX2 LX2 DC2 KP2.
    pose proof (ap_state_es _ _ _ _ _ AS2) as (ES & GL & _).
    step. if_cases KK; zc KK; [exfalso; rewrite ?unsigned_lit in KK by lia; lia|]. clear KK.
    unfold MallocRep.wz. step. step. step.
    setreg 18 (Z_to_bv 64 (Z.of_nat 0)) ltac:(reflexivity).
    ihere.
    lazymatch goal with |- impl ?segs _ (?c ?stt) (epost ?EE) ?ms =>
      lazymatch EE with (fun p => ?Q (fst p) (snd p)) => change (implM segs c stt Q ms) end end.
    change (err_clear_error st) with (abind (err_clear_slots 0 16) FIN (clr 0 st)).
    eapply (ece_loop 16 0 eq_refl ltac:(lia) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ s m2 m2 _ _);
      [exact SB2|apply munch_refl|apply wmono_refl|exact FR|exact ERR2|exact ST|exact MI2|exact ES].
  Qed.
  End Act.

  (* [comment removed for export] *)
  Theorem ERR_clear_error_walk : ERR_clear_error_spec.
  Proof using HF.
    intros bo0. unfold ap_stmt. intros until K. intros PRE TP FRM EBO KOW KIDS. subst bo.
    destruct PRE as (HEAP & AS & IDS & DC & AUX & SPB & B63 & ST & CEIL & GLO & LO & ERR & SSP & MI & SP16).
    unfold ERR_CLEAR_ERROR_STACK, GLOBALS_TOP in *.
    assert (EA : errno_addr (Z_to_bv 64 RATP) = 3355012) by (unfold errno_addr, RATP; rewrite unsigned_lit by lia; reflexivity).
    pose proof ERR as ERR'. unfold MallocRep.wz in ERR'. rewrite EA in ERR'.
    pose proof (ap_state_es _ _ _ _ _ AS) as (_ & _ & SH & IES & EESP & EESB & EES16 & OF & OFN & OD). unfold ES_SIZE in IES, EESB.
    assert (INCL : forall b, In b OW -> In b (OW ++ LB)) by (intros b Hb; apply in_app_iff; left; exact Hb).
    pose proof (blk_bounds _ _ _ _ _ _ HEAP (INCL _ IES)) as (_ & _ & EESC & EESI & _).
    pose proof (ssp_canary_0 _ _ _ _ HEAP SSP) as CAN.
    pose proof (data_cells_dflags _ _ _ DC) as DF0.
    eapply (ece_act ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m s st OW LB E bo0 lo B canary
              IDS SPB B63 CEIL GLO LO SP16);
      first [exact FRM|exact SH|exact IES|exact EESP|exact EESC|exact EESI|exact OF|exact OFN|exact OD|exact (ex_intro _ m AS)|exact DF0|exact CAN
            |unfold errno_addr in EA; exact EA|exact KOW|exact KIDS|exact HEAP|exact AS|exact DC|exact AUX|exact ST|exact ERR'|exact MI|exact TP].
  Qed.
End Proofs.
End WithCeiling0.
