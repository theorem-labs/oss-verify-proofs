(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCt.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import Prelim Malloc Prog LibProg CtSizes CtWire CtModel ApBase ApState ApErr ApBridge.
From Stdlib Require Import ZArith List Lia Bool.
From Stdlib Require Import Sorting.Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtMallocU Require Import RMallocRep RMallocTree RMalloc_iface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import STree Monad ProgG Stdio.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtU Require Import Layout Lib_iface Lib_kit Printf_lib.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtBnU Require Import BnKit BnHeap BnRep W_crypto.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtHXU Require Import HxpInit HxpFacts.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepU Require Import ApUTac ApCells ApRepDefs ApRep ApWalkTac ApErrKit ApErrKit2 ApErrKit3 ApIface W_err_new W_err_set_debug W_err_set_error W_get_object_walk W_c2i_ibuf W_c2i_int W_prefix_create.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtParseU Require Import PzDefs.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtSctU Require Import SctDefs W_sct_free W_sct_list_free SctRep W_sct_new W_sct_leaves W_memdup W_sct_set1_signature SctStmt W_o2i_sig.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.ct.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope am_scope.

Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof alloc_ceiling_range as CEIL_RANGE__); std_lia__].
Ltac cell_of_bytes bs ::=
  lazymatch bs with
  | le8 ?v => constr:(C8 v)
  | le4 ?v => constr:(C4 v)
  | le2 ?v => constr:(C2 v)
  | [?b] => constr:(C1 b)
  | le1 (zxb ?b) => constr:(C1 b)
  | Z_to_le_bytes 8 ?z => constr:(C8 (Z_to_bv 64 z))
  | Z_to_le_bytes 4 ?z => constr:(C4 (Z_to_bv 64 z))
  end.
Ltac zc H := rewrite ?bv_lts_zero_r, ?bv_lts_zero_l in H; unfold bv_eqb, bv_ltu, bv_lts, bv_leu in H; fold_lit_ux_in H; try zsimp_in H; zify_bool H.

(* [comment removed for export] *)
Lemma land_ones64_neg : forall x, - 2 ^ 64 <= x < 0 -> Z.land x 18446744073709551615 = x + 2 ^ 64.
Proof.
  intros x Hx. change 18446744073709551615 with (Z.ones 64). rewrite Z.land_ones by lia.
  symmetry. apply Z.mod_unique with (q := -1); lia.
Qed.

Lemma land_ones64_small : forall x, 0 <= x < 2 ^ 64 -> Z.land x 18446744073709551615 = x.
Proof. intros x Hx. change 18446744073709551615 with (Z.ones 64). rewrite Z.land_ones by lia. apply Z.mod_small. lia. Qed.

(* [comment removed for export] *)
Lemma lor_hi_lo : forall b q k, 0 <= b < 256 -> 0 <= q -> 0 <= k -> Z.lor (b * 2 ^ k) (q * 2 ^ (k + 8)) = (q * 256 + b) * 2 ^ k.
Proof.
  intros b q k Hb Hq Hk.
  assert (L : Z.land (b * 2 ^ k) (q * 2 ^ (k + 8)) = 0).
  { apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
    destruct (Z.lt_ge_cases i k).
    - rewrite Z.mul_pow2_bits_low by lia. reflexivity.
    - destruct (Z.lt_ge_cases i (k + 8)).
      + rewrite (Z.mul_pow2_bits_low q (k + 8) i) by lia. apply Bool.andb_false_r.
      + rewrite Z.mul_pow2_bits by lia. rewrite (Z.bits_above_log2 b (i - k)); [reflexivity| lia|].
        destruct (Z.eq_dec b 0) as [->|]; [cbn; lia|]. apply Z.lt_le_trans with 8; [apply Z.log2_lt_pow2; lia| lia]. }
  rewrite <- Z.lxor_lor by exact L. rewrite <- Z.add_nocarry_lxor by exact L.
  rewrite (Z.pow_add_r 2 k 8) by lia. change (2 ^ 8) with 256. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma sct_free_abind : forall {A} (x : sctr bptr) (k : unit -> AM A) (st0 : ap_st bptr),
  abind (sct_free x) k st0
  = ofree (sc_logid x) (ofree (option_map fst (sc_ext x)) (ofree (option_map fst (sc_sig x)) (ofree (option_map fst (sc_blob x)) (AFree (sc_blk x) (k tt st0))))).
Proof.
  intros A x k st0. unfold sct_free, abind, afree_opt, afree, aret.
  destruct (sc_logid x) as [l|]; destruct (sc_ext x) as [[e en]|]; destruct (sc_sig x) as [[g gn]|]; destruct (sc_blob x) as [[b bn]|]; reflexivity.
Qed.

Lemma ap_embed_sct_free : forall {A} (x : sctr bptr) (k : unit -> AM A) (st0 : ap_st bptr),
  ap_embed (abind (sct_free x) k st0) = lfree_sct x (ap_embed (k tt st0)).
Proof. intros A x k st0. rewrite sct_free_abind. unfold lfree_sct. rewrite !ap_embed_ofree. reflexivity. Qed.

Lemma lremove_app : forall od L1 L2, lremove od (L1 ++ L2) = lremove od L1 ++ lremove od L2.
Proof. intros [[q n]|] L1 L2; cbn [lremove]; [apply lb_remove_app| reflexivity]. Qed.

Lemma remove_sct_app : forall x L1 L2, remove_sct x (L1 ++ L2) = remove_sct x L1 ++ remove_sct x L2.
Proof. intros x L1 L2. unfold remove_sct. rewrite !lremove_app, lb_remove_app. reflexivity. Qed.

Lemma lremove_notin : forall od L, (match od with Some (q, _) => ~ In q (map blk_id L) | None => True end) -> lremove od L = L.
Proof. intros [[q n]|] L H; cbn [lremove]; [apply lb_remove_notin; exact H| reflexivity]. Qed.

(* [comment removed for export] *)
Lemma remove_sct_notin : forall adr x L,
  (forall q, In q (map blk_id (sct_blocks adr x)) -> ~ In q (map blk_id L)) -> remove_sct x L = L.
Proof.
  intros adr x L H. unfold remove_sct. unfold sct_blocks in H. rewrite !map_app in H. cbn [map oblk blk_id fst snd app] in H.
  assert (HL : lremove (osz32 (sc_logid x)) L = L).
  { apply lremove_notin. destruct (sc_logid x) as [l|]; cbn; [| exact I]. apply H. left. reflexivity. }
  rewrite HL.
  assert (HE : lremove (sc_ext x) L = L).
  { apply lremove_notin. destruct (sc_ext x) as [[e en]|]; [| exact I]. apply H. rewrite !in_app_iff. right. left. left. reflexivity. }
  rewrite HE.
  assert (HG : lremove (sc_sig x) L = L).
  { apply lremove_notin. destruct (sc_sig x) as [[g gn]|]; [| exact I]. apply H. rewrite !in_app_iff. right. right. left. left. reflexivity. }
  rewrite HG.
  assert (HB : lremove (sc_blob x) L = L).
  { apply lremove_notin. destruct (sc_blob x) as [[b bn]|]; [| exact I]. apply H. rewrite !in_app_iff. right. right. right. left. left. reflexivity. }
  rewrite HB. apply lb_remove_notin. apply H. rewrite !in_app_iff. right. right. right. right. left. reflexivity.
Qed.

Lemma remove_sct_self : forall adr x, List.NoDup (map blk_id (sct_blocks adr x)) -> remove_sct x (sct_blocks adr x) = [].
Proof.
  intros adr x ND. unfold remove_sct, sct_blocks in *.
  destruct (sc_logid x) as [l|]; destruct (sc_ext x) as [[e en]|]; destruct (sc_sig x) as [[g gn]|]; destruct (sc_blob x) as [[b bn]|];
    cbn [osz32 option_map oblk app lremove map blk_id fst snd] in *;
    repeat (rewrite lb_remove_hd; [| assumption]; match goal with H : List.NoDup (_ :: _) |- _ => apply NoDup_cons_iff in H; destruct H as [_ H] end);
    reflexivity.
Qed.

(* [comment removed for export] *)
Lemma remove_sct_fresh : forall adr x (OWX LB : list block),
  List.NoDup (map blk_id (OWX ++ sct_blocks adr x ++ LB)) -> remove_sct x (OWX ++ sct_blocks adr x ++ LB) = OWX ++ LB.
Proof.
  intros adr x OWX LB ND. rewrite (remove_sct_app x OWX), (remove_sct_app x (sct_blocks adr x) LB).
  rewrite (map_app blk_id OWX), (map_app blk_id (sct_blocks adr x) LB) in ND.
  pose proof (NoDup_app_split _ _ ND) as (N23 & D1 & N1). pose proof (NoDup_app_split _ _ N23) as (N3 & D2 & N2).
  rewrite (remove_sct_notin adr x OWX), (remove_sct_self adr x N2), (remove_sct_notin adr x LB); [reflexivity| |].
  - intros q Hq Hin. exact (D2 q Hq Hin).
  - intros q Hq Hin. apply (D1 q Hin). apply in_app_iff. left. exact Hq.
Qed.

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.
Section Proofs.
  Hypothesis HM : rmalloc_stmt.
  Hypothesis HF : rfree_stmt.

  Section Act.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (m : mem) (s : PState) (st : ap_st bptr) (OW LB : list block) (E : ap_env) (bo : Z * Z) (lo B : Z) (errv canary : word) (K : list block).
  Variables (adr : bptr -> Z) (c : list Z) (D p len PIN : Z).
  Hypothesis PRE : ap_pre s st m OW LB E bo sp lo B errv canary O2I_SCT_STACK.
  Hypothesis TP : tp = wz RATP.
  Hypothesis FRM : frm0 fc.
  Hypothesis KOW : forall b, In b K -> In b OW.
  Hypothesis KIDS : forall b, In b K -> ~ In (blk_id b) (es_ids st ++ env_ids E).
  Hypothesis PAY : payload_ok m LB D c.
  Hypothesis P0 : 0 <= p.
  Hypothesis LEN : 1 <= len <= MAX_SCT_SIZE.
  Hypothesis PL : p + len <= zlength c.
  Hypothesis ADR : forall b, In b LB -> adr (blk_id b) = blk_addr b.
  Hypothesis PINlo : bv_unsigned sp <= PIN.
  Hypothesis PINhi : PIN + 8 <= B.
  Hypothesis HPIN : rw_cells ctusegs m PIN [C8 (wz (D + p))].

  Local Notation X0 := ([(PIN, PIN + 8)] ++ LIBW_AP) (only parsing).
  Local Notation SPOST := (o2i_sct_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F s OW LB E lo B canary m K adr c D p len PIN) (only parsing).

  Lemma ctx_facts :
    Forall (fun b => 0 <= b < 256) c /\ 0 < D /\ D + zlength c < 2 ^ 63 /\ zlength c < 2 ^ 30 /\ D + zlength c <= alloc_ceiling
    /\ alloc_ceiling <= lo /\ 3493888 <= lo /\ lo <= bv_unsigned sp - O2I_SCT_STACK /\ bv_unsigned sp <= B /\ B < 2 ^ 63 /\ 0 <= bv_unsigned sp < 2 ^ 64
    /\ Z.of_nat (length (to_bytes c)) = zlength c /\ List.NoDup (map blk_id (OW ++ LB))
    /\ (exists pb PA psz, In (pb, PA, psz) LB /\ PA <= D /\ D + zlength c <= PA + psz)
    /\ bv_unsigned sp mod 16 = 0.
  Proof using LEN P0 PAY PL PRE.
    destruct PRE as (HEAP & AS & IDS & DC & AUX & SPB & B63 & ST & CEIL & GLO & LO & ERR & SSP & MI & SP16).
    destruct PAY as (_ & HF' & D0 & D63 & D30 & HB).
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    assert (HPB : exists pb PA psz, In (pb, PA, psz) LB /\ PA <= D /\ D + zlength c <= PA + psz).
    { destruct HB as [->|([[pb PA] psz] & HBLK & BL1 & BL2)]; [exfalso; revert PL LEN; cbn; unfold zlength; cbn; lia|].
      exists pb, PA, psz. cbn [blk_addr blk_size fst snd] in BL1, BL2. repeat split; [exact HBLK| lia| lia]. }
    assert (DC' : D + zlength c <= alloc_ceiling).
    { destruct HPB as (pb & PA & psz & HBLK & BL1 & BL2).
      pose proof (LH_block_range _ _ _ _ HEAP ltac:(apply in_app_iff; right; exact HBLK)) as (BB0 & BB1 & BB2 & BB3 & BB4). cbn [blk_addr blk_size fst snd] in *. lia. }
    pose proof (LH_nodup _ _ _ HEAP) as ND. unfold GLOBALS_TOP in *.
    repeat (split; [first [assumption|lia|apply zlength_to_bytes]|]). exact SP16.
  Qed.

  Local Ltac ctx := pose proof ctx_facts as (DF & D0 & D63 & D30 & DCEIL & CEIL & GLO & LO & SPB & B63 & SPR & DLEN & NDL & PBX & SP16);
                   unfold O2I_SCT_STACK, O2I_SCT_SIGNATURE_STACK, ERR_SET_ERROR_STACK in LO.

  Lemma ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -80)) = bv_unsigned sp + -80.
  Proof using LEN P0 PAY PL PRE. ctx. apply unsigned_lit; lia. Qed.
  Lemma EA : errno_addr (Z_to_bv 64 RATP) = 3355012.
  Proof. unfold errno_addr, RATP; rewrite unsigned_lit by lia; reflexivity. Qed.

  (* [comment removed for export] *)
  Definition oinv (sX : PState) (stX : ap_st bptr) (mX : mem) (OWX : list block) (errvX : word) (boX : Z * Z) (NEW : list block) : Prop :=
    ap_pre sX stX mX OWX (NEW ++ LB) E boX (Z_to_bv 64 (bv_unsigned sp + -80)) lo B errvX canary O2I_SCT_SIGNATURE_STACK
    /\ lx_pres LB (bv_unsigned sp) X0 m mX
    /\ (forall b, In b K -> In b OWX) /\ (forall b, In b K -> ~ In (blk_id b) (es_ids stX ++ env_ids E)) /\ kept K m mX
    /\ ps_so sX = ps_so s /\ ps_fa sX = ps_fa s
    /\ bytes_at ctusegs mX D (to_bytes c).

  (* [comment removed for export] *)
  Lemma oinv0 : oinv s st m OW errv bo [].
  Proof using KIDS KOW LEN P0 PAY PL PRE.
    ctx. destruct PRE as (HEAP & AS & IDS & DC & AUX & SPB' & B63' & ST & CEIL' & GLO' & LO' & ERR & SSP & MI & SP16').
    pose proof PAY as (HB & _). pose proof ESP as ESP.
    destruct (stk_carve ctusegs m lo (bv_unsigned sp) 80%nat ST ltac:(cbn; lia)) as [ST' _]. change (Z.of_nat 80%nat) with 80 in ST'.
    split; [| split; [apply lx_pres_refl| split; [exact KOW| split; [exact KIDS| split; [apply kept_refl| split; [reflexivity| split; [reflexivity| exact HB]]]]]]].
    unfold ap_pre. cbn [app]. rewrite ESP.
    split; [exact HEAP|]. split; [exact AS|]. split; [exact IDS|]. split; [exact DC|]. split; [exact AUX|]. split; [lia|]. split; [lia|].
    split; [replace (bv_unsigned sp + -80) with (bv_unsigned sp - 80) by lia; exact ST'|].
    split; [exact CEIL|]. split; [exact GLO'|]. split; [unfold O2I_SCT_SIGNATURE_STACK, ERR_SET_ERROR_STACK; lia|]. split; [exact ERR|]. split; [exact SSP|]. split; [exact MI|].
    replace (bv_unsigned sp + -80) with (bv_unsigned sp - 80) by lia. rewrite Zminus_mod, SP16. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma oinv_facts : forall sX stX mX OWX errvX boX NEW,
    oinv sX stX mX OWX errvX boX NEW ->
    RHEAP sX (OWX ++ NEW ++ LB) mX /\ List.NoDup (map blk_id (OWX ++ NEW ++ LB))
    /\ (forall q Aq n, In (q, Aq, n) (OWX ++ NEW ++ LB) -> 0 < Aq /\ 0 <= n /\ Aq + n <= alloc_ceiling /\ (Aq + n <= 0x10000 \/ 0x355000 <= Aq) /\ Aq mod 16 = 0)
    /\ (forall q Aq n, In (q, Aq, n) NEW -> ~ In q (map blk_id (OWX ++ LB)))
    /\ (forall q Aq n pb PA psz, In (q, Aq, n) NEW -> In (pb, PA, psz) LB -> Aq + n <= PA \/ PA + psz <= Aq)
    /\ (forall q Aq n pb PA psz, In (q, Aq, n) NEW -> In (pb, PA, psz) OWX -> Aq + n <= PA \/ PA + psz <= Aq).
  Proof.
    intros until NEW. intros (PREX & _). destruct PREX as (HEAP & _).
    pose proof (LH_nodup _ _ _ HEAP) as ND.
    assert (FR : forall q Aq n, In (q, Aq, n) NEW -> ~ In q (map blk_id (OWX ++ LB))).
    { intros q Aq n Hq Hin. rewrite !map_app in ND. rewrite map_app in Hin. apply in_app_iff in Hin.
      pose proof (in_ids _ _ _ _ Hq) as IQ.
      destruct Hin as [Hin|Hin].
      - exact (NoDup_app_disjoint _ _ _ ND Hin ltac:(apply in_app_iff; left; exact IQ)).
      - destruct (NoDup_app_split _ _ ND) as (N23 & _ & _). exact (NoDup_app_disjoint _ _ _ N23 IQ Hin). }
    split; [exact HEAP|]. split; [exact ND|]. split; [intros q Aq n Hq; exact (blk_bounds _ _ _ q Aq n HEAP Hq)|]. split; [exact FR|]. split.
    - intros q Aq n pb PA psz Hq Hb. eapply (blk_disjoint _ _ _ q Aq n pb PA psz HEAP); [apply in_app_iff; right; apply in_app_iff; left; exact Hq| apply in_app_iff; right; apply in_app_iff; right; exact Hb|].
      intros ->. apply (FR pb Aq n Hq). rewrite map_app. apply in_app_iff. right. exact (in_ids _ _ _ _ Hb).
    - intros q Aq n pb PA psz Hq Hb. eapply (blk_disjoint _ _ _ q Aq n pb PA psz HEAP); [apply in_app_iff; right; apply in_app_iff; left; exact Hq| apply in_app_iff; left; exact Hb|].
      intros ->. apply (FR pb Aq n Hq). rewrite map_app. apply in_app_iff. left. exact (in_ids _ _ _ _ Hb).
  Qed.

  (* [comment removed for export] *)
  Definition own_iv (NEW : list block) (iv : Z * Z) : Prop :=
    (lo <= fst iv /\ snd iv <= bv_unsigned sp) \/ iv = (PIN, PIN + 8) \/ (exists q Aq n, In (q, Aq, n) NEW /\ Aq <= fst iv /\ snd iv <= Aq + n).

  Lemma oinv_munch : forall sX stX mX OWX errvX boX NEW mY W,
    oinv sX stX mX OWX errvX boX NEW ->
    munch W mX mY -> wmono ctusegs mX mY -> mem_inv ctusegs mY -> stk ctusegs mY lo (bv_unsigned sp + -80) ->
    rw_cells ctusegs mY 3355012 [C4 errvX] ->
    Forall (own_iv NEW) W ->
    oinv sX stX mY OWX errvX boX NEW.
  Proof using LEN P0 PAY PINhi PINlo PL PRE.
    intros until W. intros OI MU WM MI ST ERR HW. ctx.
    pose proof (oinv_facts _ _ _ _ _ _ _ OI) as (HEAP3 & ND3 & BND & FRESH & DJL & DJO).
    destruct OI as (PREX & LX & KO & KI & KP & SO & FA & HB).
    destruct PREX as (HEAP & AS & IDS & DC & AUX & SPB' & B63' & ST0 & CEIL' & GLO' & LO' & ERR0 & SSP & MI0 & SP16').
    pose proof ESP as ESP. rewrite ESP in *.
    assert (INCL : forall b, In b OWX -> In b (OWX ++ NEW ++ LB)) by (intros b Hb; apply in_app_iff; left; exact Hb).
    pose proof (ap_state_es _ _ _ _ _ AS) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & OD).
    assert (HW3 : Forall (fun iv : Z * Z => lo <= fst iv \/ iv = (3355012, 3355016)
               \/ (exists q Aq n, In (q, Aq, n) (OWX ++ NEW ++ LB) /\ ~ In q (map blk_id OWX) /\ Aq <= fst iv /\ snd iv <= Aq + n)) W).
    { eapply Forall_impl; [| exact HW]. intros iv [[H1 H2]|[->|(q & Aq & n & Hq & H1 & H2)]]; [left; exact H1| left; cbn; lia| right; right].
      exists q, Aq, n. split; [apply in_app_iff; right; apply in_app_iff; left; exact Hq|]. split; [| split; [exact H1| exact H2]].
      intros Hin. apply (FRESH q Aq n Hq). rewrite map_app. apply in_app_iff. left. exact Hin. }
    assert (HEAPY : RHEAP sX (OWX ++ NEW ++ LB) mY).
    { eapply LH_frame; [exact HEAP| exact MU| exact WM|]. eapply Forall_impl; [| exact HW].
      intros [x y] [[H1 H2]|[E0|(q & Aq & n & Hq & H1 & H2)]]; cbn [fst snd] in *.
      - left. cbn. lia.
      - injection E0; intros -> ->. left. cbn. lia.
      - right. right. exists (q, Aq, n). split; [apply in_app_iff; right; apply in_app_iff; left; exact Hq| cbn; lia]. }
    split; [| split; [| split; [exact KO| split; [exact KI| split; [| split; [exact SO| split; [exact FA|]]]]]]].
    - unfold ap_pre. rewrite ESP. split; [exact HEAPY|].
      split. { eapply (ap_state_of_munch_blk stX mX mY OWX E boX sX (OWX ++ NEW ++ LB)); [exact AS| exact HEAP| exact INCL| exact MU| exact WM| exact CEIL| unfold GLOBALS_TOP; exact GLO| exact HW3]. }
      split; [exact IDS|].
      split. { eapply (data_cells_of_munch sX (OWX ++ NEW ++ LB) _ mX mY); [exact DC| intros i q k Hd; apply INCL; exact (proj1 (optb_ok_nth OWX _ i q k OD Hd))| exact HEAP| exact CEIL| exact MU| exact WM|].
               eapply Forall_impl; [| exact HW3]. intros iv [Hx|[Hx|(q & Aq & n & H1 & H2 & H3)]]; [left; exact Hx| right; left; exact Hx| right; right].
               exists q, Aq, n. split; [exact H1|]. split; [| exact H3]. intros i q' k Hd E0. apply H2. rewrite <- E0. eapply in_ids. exact (proj1 (optb_ok_nth OWX _ i q' k OD Hd)). }
      split. { eapply rauxv_ok_frame; [exact AUX| exact MU| exact WM|]. eapply Forall_impl; [| exact HW].
               intros iv [[H1 H2]|[->|(q & Aq & n & Hq & H1 & H2)]]; cbn [fst snd] in *; [unfold RAUXV_CELL, GLOBALS_TOP in *; lia| unfold RAUXV_CELL; cbn; lia|].
               pose proof (BND q Aq n ltac:(apply in_app_iff; right; apply in_app_iff; left; exact Hq)). unfold RAUXV_CELL. lia. }
      split; [lia|]. split; [lia|]. split; [exact ST|]. split; [exact CEIL|]. split; [unfold GLOBALS_TOP; lia|]. split; [exact LO'|].
      split; [unfold MallocRep.wz; rewrite EA; exact ERR|]. split; [rewrite (ssp_canary_0 _ _ _ _ HEAP SSP); eapply RHEAP_ssp; exact HEAPY|].
      split; [exact MI| exact SP16'].
    - eapply lx_pres_trans; [exact LX|].
      eapply (lx_pres_munch_gen sX (OWX ++ NEW) LB W mX mY (bv_unsigned sp) X0 lo); [rewrite <- app_assoc; exact HEAP| exact CEIL| unfold GLOBALS_TOP; lia| lia| exact MU| exact WM|].
      eapply Forall_impl; [| exact HW]. intros iv [[H1 H2]|[->|(q & Aq & n & Hq & H1 & H2)]]; [left; split; assumption| right; left| right; right].
      + split; [cbn; lia|]. intros a Ha. cbn [fst snd] in Ha. cbn. left. lia.
      + exists q, Aq, n. split; [apply in_app_iff; right; exact Hq| split; assumption].
    - eapply kept_trans; [exact KP|].
      eapply (kept_of_munch sX (OWX ++ NEW ++ LB) _ mX mY K lo); [exact HEAP| intros b Hb; apply INCL; apply KO; exact Hb| exact CEIL| exact MU|].
      eapply Forall_impl; [| exact HW3]. intros iv [Hx|[Hx|(q & Aq & n & H1 & H2 & H3)]]; [left; exact Hx| right; left; exact Hx| right; right].
      exists q, Aq, n. split; [exact H1|]. split; [| exact H3]. intros Hin. apply H2. apply in_map_iff in Hin. destruct Hin as (b & Eb & Hb). rewrite <- Eb. apply in_map. apply KO. exact Hb.
    - destruct PBX as (pb & PA & psz & HPB & PB1 & PB2).
      eapply bytes_at_transport; [exact HB| exact MU|]. rewrite DLEN. apply disjoint_from_outside || idtac.
      clear - HW DJL HPB PB1 PB2 CEIL DCEIL LO D0 PINlo. induction W as [|[x y] W IH]; [exact I|]. apply Forall_cons_iff in HW. destruct HW as [H1 H2].
      cbn [disjoint_from]. split; [| apply IH; exact H2]. unfold own_iv in H1. cbn [fst snd] in H1.
      destruct H1 as [[H1 H3]|[E0|(q & Aq & n & Hq & H1 & H3)]]; [cbn; lia| injection E0; intros -> ->; cbn; lia|].
      pose proof (DJL q Aq n pb PA psz Hq HPB). cbn. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma oinv_alloc : forall sX stX mX OWX errvX boX NEW sY mY (errvY : word) pn A n,
    oinv sX stX mX OWX errvX boX NEW ->
    rheap_pres (OWX ++ NEW ++ LB) (bv_unsigned sp + -80) mX mY ->
    RHEAP sY ((pn, A, n) :: OWX ++ NEW ++ LB) mY ->
    mem_inv ctusegs mY -> stk ctusegs mY lo (bv_unsigned sp + -80) -> rw_cells ctusegs mY LX_ERRNO [C4 errvY] -> rauxv_ok mY B ->
    ps_fa sY = ps_fa sX -> ps_so sY = ps_so sX ->
    oinv sY stX mY OWX errvY boX ((pn, A, n) :: NEW).
  Proof using LEN P0 PAY PL PRE.
    intros until n. intros OI HP HEAPY MI ST ERR AUX FA' SO'. ctx.
    destruct OI as (PREX & LX & KO & KI & KP & SO & FA & HB).
    destruct PREX as (HEAP & AS & IDS & DC & AUX0 & SPB' & B63' & ST0 & CEIL' & GLO' & LO' & ERR0 & SSP & MI0 & SP16').
    pose proof ESP as ESP. rewrite ESP in *.
    pose proof (ap_state_es _ _ _ _ _ AS) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & OD).
    unfold LX_ERRNO, RATP in ERR. change (3355176 - 164) with 3355012 in ERR.
    assert (HEAPY' : RHEAP sY (OWX ++ ((pn, A, n) :: NEW) ++ LB) mY) by (eapply RHEAP_perm; [exact HEAPY| apply Permutation_middle]).
    pose proof (agree_of_heap_pres _ _ _ _ HP) as AG.
    split; [| split; [| split; [exact KO| split; [exact KI| split; [| split; [rewrite SO'; exact SO| split; [rewrite FA'; exact FA|]]]]]]].
    - unfold ap_pre. rewrite ESP. split; [exact HEAPY'|].
      split; [eapply ap_state_heap_pres_app; [exact AS| exact HP]|].
      split; [exact IDS|].
      split. { eapply data_cells_heap_pres; [exact DC| exact HP|]. intros i q k Hd. apply in_app_iff. left. exact (proj1 (optb_ok_nth OWX _ i q k OD Hd)). }
      split; [exact AUX|]. split; [lia|]. split; [lia|]. split; [exact ST|]. split; [exact CEIL|]. split; [exact GLO'|]. split; [exact LO'|].
      split; [unfold MallocRep.wz; rewrite EA; exact ERR|]. split; [rewrite (ssp_canary_0 _ _ _ _ HEAP SSP); eapply RHEAP_ssp; exact HEAPY'|].
      split; [exact MI| exact SP16'].
    - eapply lx_pres_trans; [exact LX|]. eapply lx_pres_weaken; [eapply lx_pres_of_heap_pres; exact HP| lia| | intros a Ha; exact Ha].
      intros b Hb. apply in_app_iff. right. apply in_app_iff. right. exact Hb.
    - eapply kept_trans; [exact KP|]. eapply kept_of_heap_pres; [exact HP|]. intros b Hb. apply in_app_iff. left. apply KO. exact Hb.
    - destruct PBX as (pb & PA & psz & HPB & PB1 & PB2).
      eapply bytes_at_agree; [exact AG| exact HB|]. intros a Ha. rewrite DLEN in Ha. right. right. exists (pb, PA, psz).
      split; [apply in_app_iff; right; apply in_app_iff; right; exact HPB| cbn; lia].
  Qed.

  (* [comment removed for export] *)
  Lemma oinv_call : forall sX stX mX OWX errvX boX NEW,
    oinv sX stX mX OWX errvX boX NEW ->
    RHEAP sX (OWX ++ NEW ++ LB) mX /\ rauxv_ok mX B /\ bv_unsigned sp + -80 <= B
    /\ stk ctusegs mX lo (bv_unsigned sp + -80) /\ alloc_ceiling <= lo /\ GLOBALS_TOP <= lo
    /\ rw_cells ctusegs mX LX_ERRNO [C4 errvX] /\ mem_inv ctusegs mX /\ crypto_statics mX /\ ap_state stX mX OWX E boX.
  Proof using LEN P0 PAY PL PRE.
    intros until NEW. intros (PREX & _). ctx.
    destruct PREX as (HEAP & AS & IDS & DC & AUX0 & SPB' & B63' & ST0 & CEIL' & GLO' & LO' & ERR0 & SSP & MI0 & SP16').
    pose proof ESP as ESP. rewrite ESP in *. pose proof AS as (_ & _ & (CS & _) & _).
    unfold MallocRep.wz in ERR0. rewrite EA in ERR0.
    repeat (split; [first [assumption| lia]|]). exact AS.
  Qed.

  (* [comment removed for export] *)
  Lemma oinv_after : forall sX stX mX OWX errvX boX NEW sY stY mY OWY (errvY : word) boY XX NEW2,
    oinv sX stX mX OWX errvX boX NEW ->
    ap_pre sY stY mY OWY (NEW2 ++ NEW ++ LB) E boY (Z_to_bv 64 (bv_unsigned sp + -80)) lo B errvY canary 0 ->
    lx_pres (NEW ++ LB) (bv_unsigned sp + -80) (XX ++ LIBW_AP) mX mY ->
    (forall a, rin_ivs XX a -> (bv_unsigned sp - 80 <= a < bv_unsigned sp) \/ (exists q Aq n, In (q, Aq, n) NEW /\ Aq <= a < Aq + n)) ->
    ps_so sY = ps_so sX -> ps_fa sY = ps_fa sX ->
    blocks_kept K stY OWY mX mY ->
    oinv sY stY mY OWY errvY boY (NEW2 ++ NEW).
  Proof using LEN P0 PAY PINlo PL PRE.
    intros until NEW2. intros OI PREY LXY HXX SO' FA' (BK1 & BK2 & BK3). ctx.
    pose proof (oinv_facts _ _ _ _ _ _ _ OI) as (HEAP3 & ND3 & BND & FRESH & DJL & DJO).
    destruct OI as (PREX & LX & KO & KI & KP & SO & FA & HB).
    pose proof (agree_of_lx_pres _ _ _ _ _ LXY) as AG.
    assert (CL : forall a, in_block LB a -> ~ rin_ivs LIBW_AP a -> lx_client (NEW ++ LB) (bv_unsigned sp + -80) (XX ++ LIBW_AP) a).
    { intros a (b & Hb & Hr) HX. destruct b as [[pb PA] psz]. cbn [blk_addr blk_size fst snd] in Hr.
      pose proof (BND pb PA psz ltac:(apply in_app_iff; right; apply in_app_iff; right; exact Hb)) as (B1 & B2 & B3 & B4 & B5).
      split.
      - intros HIN. apply rin_ivs_app in HIN. destruct HIN as [HIN|HIN]; [| exact (HX HIN)].
        destruct (HXX a HIN) as [Hs|(q & Aq & n & Hq & Ha)]; [lia|]. pose proof (DJL q Aq n pb PA psz Hq Hb). lia.
      - right. left. exists (pb, PA, psz). split; [apply in_app_iff; right; exact Hb| cbn; lia]. }
    split; [rewrite <- app_assoc; eapply ap_pre_restack; [exact PREY| rewrite ESP; unfold O2I_SCT_SIGNATURE_STACK, ERR_SET_ERROR_STACK; lia]|].
    split. { eapply lx_pres_trans; [exact LX|]. intros a Ha [HXa Hc]. apply (LXY a Ha). cbn [rin_ivs fst snd app] in HXa.
             destruct Hc as [Hc|[Hblk|Hc]].
             - split; [| left; lia]. intros HIN. apply rin_ivs_app in HIN. destruct HIN as [HIN|HIN]; [| apply HXa; right; exact HIN].
               destruct (HXX a HIN) as [Hs|(q & Aq & n & Hq & Hq2)]; [lia|].
               pose proof (BND q Aq n ltac:(apply in_app_iff; right; apply in_app_iff; left; exact Hq)). lia.
             - apply CL; [exact Hblk| intros HIN; apply HXa; right; exact HIN].
             - split; [| right; right; exact Hc]. intros HIN. apply rin_ivs_app in HIN. destruct HIN as [HIN|HIN]; [| apply HXa; right; exact HIN].
               destruct (HXX a HIN) as [Hs|(q & Aq & n & Hq & Hq2)]; [unfold GLOBALS_TOP in *; lia|].
               pose proof (BND q Aq n ltac:(apply in_app_iff; right; apply in_app_iff; left; exact Hq)). unfold ralloc_static in Hc. lia. }
    split; [exact BK1|]. split.
    { intros b Hb Hin. apply in_app_iff in Hin. destruct Hin as [Hin|Hin]; [exact (BK2 b Hb Hin)|]. apply (KI b Hb). apply in_app_iff. right. exact Hin. }
    split; [eapply kept_trans; [exact KP| exact BK3]|].
    split; [rewrite SO'; exact SO|]. split; [rewrite FA'; exact FA|].
    destruct PBX as (pb & PA & psz & HPB & PB1 & PB2).
    pose proof (BND pb PA psz ltac:(apply in_app_iff; right; apply in_app_iff; right; exact HPB)) as (B1 & B2 & B3 & B4 & B5).
    eapply bytes_at_agree; [exact AG| exact HB|]. intros a Ha. rewrite DLEN in Ha. apply CL.
    - exists (pb, PA, psz). split; [exact HPB| cbn; lia].
    - unfold LIBW_AP. cbn [rin_ivs fst snd]. lia.
  Qed.

  (* [comment removed for export] *)
  Definition site_ok (rs : rsite) (pc : Z) : Prop :=
    (rs = RS_sct_43 /\ pc = 0x19c7b8) \/ (rs = RS_sct_ext /\ pc = 0x19c938) \/ (rs = RS_sct_sig /\ pc = 0x19c9c8).

  (* [comment removed for export] *)
  Definition raise_post (x8 x9 x18 x19 x20 x21 x22 x23 : word) (mX : mem) (NEW : list block) (r : unit * ap_st bptr) (s' : PState) : machine_state -> Prop :=
    fun ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F' : bvmap 5 word) (fc' : bv 32) m' OW' (errv' : word) bo',
      ms' = MS (mkR (Z_to_bv 64 0x19c9f4) (Z_to_bv 64 (bv_unsigned sp + -80)) gp (wz RATP) t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7
                    x18 x19 x20 x21 x22 x23 s8 s9 s10 s11 t3 t4 t5 t6)
               F' (Z_to_bv 64 0x19c9f4) fc' None m' (seg_rom ctusegs)
      /\ frm0 fc' /\ (forall k : reg, bv_unsigned k <> 10 -> reg_get F' k = reg_get F k)
      /\ oinv s' (snd r) m' OW' errv' bo' NEW
      /\ lx_pres (NEW ++ LB) (bv_unsigned sp + -80) LIBW_AP mX m'.

  Lemma raise_blk : forall rs pc (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x28 x29 x30 x31 : word)
      (FX : bvmap 5 word) (fcX : bv 32) sX stX mX OWX errvX boX NEW,
    site_ok rs pc -> oinv sX stX mX OWX errvX boX NEW -> frm0 fcX -> (forall k : reg, bv_unsigned k <> 10 -> reg_get FX k = reg_get F k) ->
    implM ctusegs (interp (ap_embed (err_raise rs stX))) sX (raise_post x8 x9 x18 x19 x20 x21 x22 x23 mX NEW)
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -80)) gp (wz RATP) x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 s8 s9 s10 s11 x28 x29 x30 x31)
          FX (Z_to_bv 64 pc) fcX None mX (seg_rom ctusegs)).
  Proof using s7 HF HM LEN P0 PAY PINlo PL PRE.
    intros until NEW. intros SITE OI FRMX FEX. ctx. pose proof ESP as ESP.
    pose proof OI as (PREX & LX & KO & KI & KP & SO & FA & HB).
    destruct (lit_ok_auto A_CT_OCT_C 19 ltac:(vm_compute; reflexivity)) as (fs & fk & LF).
    destruct (lit_ok_auto A_O2I_SCT 8 ltac:(vm_compute; reflexivity)) as (ns & nk & LN).
    assert (RSF : rs_flen rs = 19) by (destruct SITE as [(-> & _)|[(-> & _)|(-> & _)]]; reflexivity).
    assert (RSN : rs_fnlen rs = 8) by (destruct SITE as [(-> & _)|[(-> & _)|(-> & _)]]; reflexivity).
    rewrite <- RSF in LF. rewrite <- RSN in LN.
    unfold err_raise.
    destruct SITE as [(RS & ->)|[(RS & ->)|(RS & ->)]].
    (* [comment removed for export] *)
    all: unfold implM; iprefix; step; ihere; to_implM.
    all: eapply implM_abind; [pose proof (ERR_new_walk HF boX) as W; unfold ap_stmt in W;
      eapply W; [eapply ap_pre_stack_le; [exact PREX| unfold ERR_NEW_STACK, O2I_SCT_SIGNATURE_STACK, ERR_SET_ERROR_STACK; lia]| reflexivity| exact FRMX| reflexivity| exact KO| exact KI]|].
    all: intros r1 sA ms1 PO1; cbv beta in PO1.
    all: destruct PO1 as (q0 & q1 & q2 & q10 & q11 & q12 & q13 & q14 & q15 & q16 & q17 & q3 & q4 & q5 & q6 & F1 & fc1 & mA & OW1 & errv1 & bo1
                     & -> & FRM1 & FE1 & PREa & LXa & SOa & FAa & BKa & EBO1); subst bo1; rewrite ESP in LXa.
    all: rewrite ret_pc_even by first [lia| reflexivity].
    all: assert (OIa : oinv sA (snd r1) mA OW1 errv1 boX NEW) by
      (eapply (oinv_after sX stX mX OWX errvX boX NEW sA (snd r1) mA OW1 errv1 boX [] []); [exact OI| exact PREa| exact LXa| intros a []| exact SOa| exact FAa| exact BKa]).
    all: pose proof OIa as (PREa' & _ & KOa & KIa & _).
    (* [comment removed for export] *)
    all: unfold implM; iprefix; do 5 step;
      try (lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 0x19c9e0) _ _ _ _) => fail | _ => step end);
      step; ihere; to_implM.
    all: eapply implM_abind; [pose proof (ERR_set_debug_walk HM HF rs A_CT_OCT_C A_O2I_SCT boX _ _ _ _ LF LN) as W; unfold ap_stmt in W;
      eapply W; [eapply ap_pre_stack_le; [exact PREa'| unfold ERR_SET_DEBUG_STACK, O2I_SCT_SIGNATURE_STACK, ERR_SET_ERROR_STACK; lia]| reflexivity| exact FRM1| subst rs; repeat split; reflexivity| exact KOa| exact KIa]|].
    all: intros r2 sB ms2 PO2; cbv beta in PO2.
    all: destruct PO2 as (p0 & p1' & p2' & p10 & p11 & p12 & p13 & p14 & p15 & p16 & p17 & p3 & p4 & p5 & p6 & F2 & fc2 & mB & OW2 & errv2 & bo2
                     & -> & FRM2 & FE2 & PREb & LXb & SOb & FAb & BKb & EBO2); subst bo2; rewrite ESP in LXb.
    all: rewrite ret_pc_even by first [lia| reflexivity].
    all: assert (OIb : oinv sB (snd r2) mB OW2 errv2 boX NEW) by
      (eapply (oinv_after sA (snd r1) mA OW1 errv1 boX NEW sB (snd r2) mB OW2 errv2 boX [] []); [exact OIa| exact PREb| exact LXb| intros a []| exact SOb| exact FAb| exact BKb]).
    all: pose proof OIb as (PREb' & _ & KOb & KIb & _).
    (* [comment removed for export] *)
    all: unfold implM; iprefix; do 3 step; step; ihere; to_implM.
    all: eapply implM_mono; [pose proof (ERR_set_error_walk rs 50 104 boX) as W; unfold ap_stmt in W;
      eapply W; [eapply ap_pre_stack_le; [exact PREb'| unfold O2I_SCT_SIGNATURE_STACK, ERR_SET_ERROR_STACK; lia]| reflexivity| exact FRM2| | exact KOb| exact KIb];
      cbn; unfold ERR_LIB_SYS, MallocRep.wz; repeat split; try reflexivity; try lia; subst rs; reflexivity|].
    all: intros r3 sC ms3 PO3; cbv beta in PO3.
    all: destruct PO3 as (o0 & o1 & o2 & o10 & o11 & o12 & o13 & o14 & o15 & o16 & o17 & o3 & o4 & o5 & o6 & F3 & fc3 & mC & OW3 & errv3 & bo3
                     & -> & FRM3 & FE3 & PREc & LXc & SOc & FAc & BKc & EBO3); subst bo3; rewrite ESP in LXc.
    all: rewrite ret_pc_even by first [lia| reflexivity].
    all: assert (OIc : oinv sC (snd r3) mC OW3 errv3 boX NEW) by
      (eapply (oinv_after sB (snd r2) mB OW2 errv2 boX NEW sC (snd r3) mC OW3 errv3 boX [] []); [exact OIb| exact PREc| exact LXc| intros a []| exact SOc| exact FAc| exact BKc]).
    all: unfold raise_post; exists o0, o1, o2, o10, o11, o12, o13, o14, o15, o16, o17, o3, o4, o5, o6, F3, fc3, mC, OW3, errv3, boX.
    all: split; [reflexivity|]; split; [exact FRM3|]; split; [intros k Hk; rewrite (FE3 k Hk), (FE2 k Hk), (FE1 k Hk); apply (FEX k Hk)|].
    all: split; [exact OIc|].
    all: eapply lx_pres_trans; [exact LXa|]; eapply lx_pres_trans; [exact LXb| exact LXc].
  Qed.

  Lemma oinv_perm : forall sX stX mX OWX errvX boX NEW NEW',
    Permutation NEW NEW' -> oinv sX stX mX OWX errvX boX NEW -> oinv sX stX mX OWX errvX boX NEW'.
  Proof.
    intros until NEW'. intros HPm (PREX & REST). split; [| exact REST].
    destruct PREX as (HEAP & REST2). split; [| exact REST2].
    eapply RHEAP_perm; [exact HEAP|]. apply Permutation_app_head. apply Permutation_app_tail. exact HPm.
  Qed.

  (* [comment removed for export] *)
  Definition hi_frame : list cell := [C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

  (* [comment removed for export] *)
  Lemma free_exit : forall (x8 x18 x19 x20 x21 x22 x23 : word) mS (r : unit * ap_st bptr) sF msF (x1 : sctr bptr) (adr1 : bptr -> Z) A1 (jl : word),
    raise_post x8 (wz A1) x18 x19 x20 x21 x22 x23 mS (sct_blocks adr1 x1) r sF msF ->
    adr1 (sc_blk x1) = A1 ->
    rw_cells ctusegs mS (bv_unsigned sp + -80) (C8 jl :: hi_frame) ->
    rw_cells ctusegs mS PIN [C8 (wz (D + p))] ->
    sct_ptr_cells mS adr1 x1 ->
    implM ctusegs (interp (ap_embed (abind (sct_free x1) (fun _ => aret None) (snd r)))) sF SPOST msF.
  Proof using HF LEN P0 PAY PINlo PL PRE.
    intros until jl. intros RP EA1 FR HP PC. ctx. pose proof ESP as ESP. subst tp.
    unfold raise_post in RP.
    destruct RP as (w0 & w1 & w2 & w10 & w11 & w12 & w13 & w14 & w15 & w16 & w17 & w3 & w4 & w5 & w6 & FF & fcF & mF & OWF & errvF & boF
                    & -> & FRMF & FEF & OIF & LXF).
    pose proof (oinv_facts _ _ _ _ _ _ _ OIF) as (HEAPF & NDF & BND & FRESH & DJL & DJO).
    pose proof (oinv_call _ _ _ _ _ _ _ OIF) as (_ & AUXF & SPBF & STF & _ & _ & ERRF & MIF & CSF & ASF).
    pose proof OIF as (PREF & LXe & KO & KI & KP & SO & FA & HB).
    assert (HXIN : In (sc_blk x1, A1, SCT_SIZE) (sct_blocks adr1 x1)) by (unfold sct_blocks; rewrite !in_app_iff; right; right; right; right; left; rewrite EA1; reflexivity).
    pose proof (BND (sc_blk x1) A1 SCT_SIZE ltac:(apply in_app_iff; right; apply in_app_iff; left; exact HXIN)) as (BX0 & _ & BXC & BXI & _). unfold SCT_SIZE in BXC, BXI.
    (* [comment removed for export] *)
    pose proof (agree_of_lx_pres _ _ _ _ _ LXF) as AG.
    assert (CLs : forall a, bv_unsigned sp + -80 <= a -> lx_client (sct_blocks adr1 x1 ++ LB) (bv_unsigned sp + -80) LIBW_AP a).
    { intros a Ha. split; [unfold LIBW_AP; cbn [rin_ivs fst snd]; lia| left; exact Ha]. }
    assert (CLb : forall a, A1 <= a < A1 + 104 -> lx_client (sct_blocks adr1 x1 ++ LB) (bv_unsigned sp + -80) LIBW_AP a).
    { intros a Ha. split; [unfold LIBW_AP; cbn [rin_ivs fst snd]; lia|]. right. left. exists (sc_blk x1, A1, SCT_SIZE). split; [apply in_app_iff; left; exact HXIN| cbn; unfold SCT_SIZE; lia]. }
    unfold hi_frame in FR.
    apply (rw_cells_agree _ _ _ _ _ AG) in FR; [| intros a Ha; apply CLs; cbn in Ha; lia].
    apply (rw_cells_agree _ _ _ _ _ AG) in HP; [| intros a Ha; apply CLs; cbn in Ha; lia].
    assert (PC' : sct_ptr_cells mF adr1 x1).
    { unfold sct_ptr_cells in *. cbn zeta in *. unfold SCTO_SCT, SCTO_LOG_ID, SCTO_EXT, SCTO_SIG in *. rewrite EA1 in PC |- *.
      destruct PC as (C1 & C2 & C3 & C4).
      split; [| split; [| split]]. all: eapply ro_cells_agree; [exact AG| eassumption| intros a Ha; apply CLb; cbn in Ha; lia]. }
    clear AG CLs CLb FRESH DJL DJO PC.
    pose proof (munch_refl (@nil (Z * Z)) mF) as MU. pose proof (wmono_refl ctusegs mF) as WM.
    unfold implM. iprefix. step. step. step. ihere. to_implM.
    rewrite ap_embed_sct_free.
    eapply (SCT_free_walk' HF) with (L := OWF ++ sct_blocks adr1 x1 ++ LB) (lo := lo) (B := B) (adr := adr1);
      [exact HEAPF| exact AUXF| rewrite ESP; lia| rewrite ESP; exact STF| exact CEIL| unfold GLOBALS_TOP; lia
      | rewrite ESP; unfold SCT_FREE_STACK, CRYPTO_FREE_STACK, RFREE_STACK; lia
      | exact ERRF| exact MIF| reflexivity| exact CSF
      | apply Forall_forall; intros b Hb; apply in_app_iff; right; apply in_app_iff; left; exact Hb
      | rewrite (map_app blk_id OWF), (map_app blk_id (sct_blocks adr1 x1) LB) in NDF; destruct (NoDup_app_split _ _ NDF) as (N23 & _ & _); destruct (NoDup_app_split _ _ N23) as (_ & _ & N2); exact N2
      | exact NDF| exact PC'| rewrite EA1; reflexivity|].
    intros sG msG PO. unfold ofree_post in PO. rewrite ?ESP in PO.
    destruct PO as (g0 & g1 & g2 & g10 & g11 & g12 & g13 & g14 & g15 & g16 & g17 & g3 & g4 & g5 & g6 & mG
                    & -> & MIG & STG & ERRG & AUXG & HPG & FAG & SOG & HEAPG).
    rewrite (remove_sct_fresh adr1 x1 OWF LB NDF) in HPG, HEAPG.
    replace (ret_pc (Z_to_bv 64 0x19c77c)) with (Z_to_bv 64 0x19c77c) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    cbn [ap_embed aret interp]. apply implM_ret.
    pose proof (agree_of_heap_pres _ _ _ _ HPG) as AGG.
    apply (rw_cells_agree _ _ _ _ _ AGG) in FR; [| intros a Ha; left; cbn in Ha; lia].
    apply (rw_cells_agree _ _ _ _ _ AGG) in HP; [| intros a Ha; left; cbn in Ha; lia].
    clear MU WM. pose proof (munch_refl (@nil (Z * Z)) mG) as MU. pose proof (wmono_refl ctusegs mG) as WM.
    step. step. do 9 step. release_frame FR STG (bv_unsigned sp). step. step.
    apply evt_done. unfold o2i_sct_post. cbn [fst snd].
    eexists _, _, _, _, _, _, _, _, _, _, _, _, _, _, FF, fcF, mG, OWF, errvF, boF, adr, [].
    split; [unfold MallocRep.wz; reflexivity|]. split; [exact FRMF|]. split; [exact FEF|].
    split. { cbn [app]. destruct PREF as (_ & _ & IDS & DC & _ & _ & _ & _ & _ & _ & _ & _ & SSP & _ & _).
             pose proof (ap_state_es _ _ _ _ _ ASF) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & OD).
             unfold ap_pre. split; [exact HEAPG|].
             split; [eapply ap_state_heap_pres_app; [exact ASF| exact HPG]|].
             split; [exact IDS|].
             split; [eapply data_cells_heap_pres; [exact DC| exact HPG| intros i q k Hd; apply in_app_iff; left; exact (proj1 (optb_ok_nth OWF _ i q k OD Hd))]|].
             split; [exact AUXG|]. split; [lia|]. split; [lia|]. split; [exact STG|]. split; [exact CEIL|]. split; [unfold GLOBALS_TOP; lia|]. split; [lia|].
             split; [unfold LX_ERRNO, RATP in ERRG; unfold MallocRep.wz; rewrite EA; exact ERRG|].
             split; [rewrite (ssp_canary_0 _ _ _ _ HEAPF SSP); eapply RHEAP_ssp; exact HEAPG|].
             split; [exact MIG| exact SP16]. }
    split. { eapply lx_pres_trans; [exact LXe|]. eapply lx_pres_weaken; [eapply lx_pres_of_heap_pres; exact HPG| lia| intros b Hb; apply in_app_iff; right; exact Hb| intros a Ha; exact Ha]. }
    split; [rewrite SOG; exact SO|]. split; [rewrite FAG; exact FA|].
    split. { split; [exact KO|]. split; [intros b Hb Hin; apply (KI b Hb); apply in_app_iff; left; exact Hin|].
             eapply kept_trans; [exact KP|]. eapply kept_of_heap_pres; [exact HPG| intros b Hb; apply in_app_iff; left; apply KO; exact Hb]. }
    split; [intros b Hb; reflexivity|]. split; [intros b []|]. split; [reflexivity|]. unfold MallocRep.wz in *. exact HP.
  Qed.

  (* [comment removed for export] *)
  Lemma pre_resp : forall sF (st' : ap_st bptr) mX OW' LB' (errv' : word) boX stk0,
    ap_pre sF st' mX OW' LB' E boX (Z_to_bv 64 (bv_unsigned sp + -80)) lo B errv' canary stk0 ->
    stk ctusegs mX lo (bv_unsigned sp) ->
    ap_pre sF st' mX OW' LB' E boX sp lo B errv' canary 0.
  Proof using LEN P0 PAY PL PRE.
    intros until stk0. intros PREX ST4. ctx.
    destruct PREX as (HEAP & AS & IDS & DC & AUX & SPB' & B63' & ST0 & CEIL' & GLO' & LO' & ERR0 & SSP & MI0 & SP16').
    unfold ap_pre. repeat (split; [first [assumption|lia]|]). exact SP16.
  Qed.

  (* [comment removed for export] *)
  Lemma sct_rep_munch : forall sX L mX mY W adr1 x1,
    sct_rep mX L adr1 x1 -> RHEAP sX L mX -> munch W mX mY -> wmono ctusegs mX mY ->
    Forall (fun iv : Z * Z => alloc_ceiling <= fst iv) W -> sct_rep mY L adr1 x1.
  Proof.
    intros sX L mX mY W adr1 x1 (H1 & H2 & H3 & H4 & H5 & H6 & REST) HEAP MU WM HW.
    assert (DJ : forall q Aq n k, In (q, Aq, n) L -> 0 <= k <= n -> disjoint_from W Aq k).
    { intros q Aq n k Hq Hk. pose proof (blk_bounds _ _ _ q Aq n HEAP Hq) as (B1 & B2 & B3 & B4 & B5). clear - HW Hk B3.
      induction W as [|[x y] W IH]; [exact I|]. apply Forall_cons_iff in HW. destruct HW as [Hx HW]. cbn [fst] in Hx. cbn. split; [lia| apply IH; exact HW]. }
    assert (AR : forall o, arr_rep mX L adr1 o -> arr_rep mY L adr1 o).
    { intros [[q n]|] Ho; cbn in *; [| exact I]. destruct Ho as (Hn & HL & bs & HC). split; [exact Hn|]. split; [exact HL|]. exists bs.
      eapply rw_cells_transport; [exact HC| exact MU| exact WM|]. cbn [cells_size csize Nat.add]. rewrite Nat.add_0_r, Z2Nat.id by lia. eapply DJ; [exact HL| lia]. }
    split; [exact H1|]. split.
    { eapply rw_cells_transport; [exact H2| exact MU| exact WM|]. rewrite sct_cells_size. eapply DJ; [exact H1| unfold SCT_SIZE; lia]. }
    split; [apply AR; exact H3|]. split; [apply AR; exact H4|]. split; [apply AR; exact H5|]. split; [apply AR; exact H6|]. exact REST.
  Qed.

  (* [comment removed for export] *)
  Lemma fin_ok : forall (x1 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x21 x22 x23 x28 x29 x30 x31 pv : word) (FX : bvmap 5 word) (fcX : bv 32)
      sX stX mX OWX errvX boX (xr : sctr bptr) (adr1 : bptr -> Z) A1 (jl : word),
    oinv sX stX mX OWX errvX boX (sct_blocks adr1 xr) -> frm0 fcX -> (forall k : reg, bv_unsigned k <> 10 -> reg_get FX k = reg_get F k) ->
    adr1 (sc_blk xr) = A1 ->
    rw_cells ctusegs mX (bv_unsigned sp + -80) (C8 jl :: hi_frame) ->
    rw_cells ctusegs mX PIN [C8 pv] ->
    sct_rep mX (OWX ++ sct_blocks adr1 xr ++ LB) adr1 xr ->
    (forall b, In b LB -> adr1 (blk_id b) = adr (blk_id b)) -> sc_version xr = CtWire.byte c p ->
    evt ctusegs (fun ms'' => o2i_sct_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F s OW LB E lo B canary m K adr c D p len PIN (Some xr, stX) sX ms'')
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -80)) gp (wz RATP) x5 x6 x7 x8 (wz A1) x10 x11 x12 x13 x14 x15 x16 x17 (wz 0) (wz PIN) (Z_to_bv 64 (D + p + len)) x21 x22 x23 s8 s9 s10 s11 x28 x29 x30 x31)
          FX (Z_to_bv 64 0x19c750) fcX None mX (seg_rom ctusegs)).
  Proof using LEN P0 PAY PINhi PINlo PL PRE.
    intros until jl. intros OI FRMX FEX EA1 FR HP SR ADR1 VER. ctx. pose proof ESP as ESP.
    pose proof (oinv_facts _ _ _ _ _ _ _ OI) as (HEAPX & NDX & BND & FRESH & DJL & DJO).
    pose proof (oinv_call _ _ _ _ _ _ _ OI) as (_ & _ & _ & STX & _ & _ & ERRX & MIX & _).
    unfold LX_ERRNO, RATP in ERRX. change (3355176 - 164) with 3355012 in ERRX.
    pose proof (munch_refl [(PIN, PIN + 8)]%Z mX) as MU. pose proof (wmono_refl ctusegs mX) as WM.
    unfold hi_frame in FR. unfold MallocRep.wz. rename MIX into MI.
    step. name_mem m1.
    assert (OI1 : oinv sX stX m1 OWX errvX boX (sct_blocks adr1 xr)).
    { eapply oinv_munch; [exact OI| exact MU| exact WM| exact MI| exact STX| exact ERRX|]. constructor; [right; left; reflexivity| constructor]. }
    assert (SR1 : sct_rep m1 (OWX ++ sct_blocks adr1 xr ++ LB) adr1 xr).
    { eapply sct_rep_munch; [exact SR| exact HEAPX| exact MU| exact WM|]. constructor; [cbn; lia| constructor]. }
    pose proof OI1 as (PRE1 & LX1 & KO & KI & KP & SO & FA & HB).
    step. if_cases K0; zc K0; [| exfalso; apply K0; reflexivity]. clear K0.
    step. do 9 step. release_frame FR STX (bv_unsigned sp). step. step.
    apply evt_done. unfold o2i_sct_post. cbn [fst snd].
    eexists _, _, _, _, _, _, _, _, _, _, _, _, _, _, FX, fcX, m1, OWX, errvX, boX, adr1, (sct_blocks adr1 xr).
    split; [rewrite EA1; reflexivity|]. split; [exact FRMX|]. split; [exact FEX|].
    split; [eapply pre_resp; [exact PRE1| exact STX]|].
    split; [exact LX1|]. split; [exact SO|]. split; [exact FA|].
    split; [split; [exact KO| split; [intros b Hb Hin; apply (KI b Hb); apply in_app_iff; left; exact Hin| exact KP]]|].
    split; [exact ADR1|].
    split; [intros [[q Aq] n] Hb; cbn; exact (FRESH q Aq n Hb)|].
    split; [reflexivity|]. split; [exact SR1|]. split; [exact HP| exact VER].
  Qed.

  (* [comment removed for export] *)
  Lemma sct_new_cells_rep : forall mX A adr0 pn,
    rw_cells ctusegs mX A (sct_new_cells (Z_to_bv 64 (-1))) -> rw_cells ctusegs mX A (sct_cells adr0 (sct_new pn) (-1) 0).
  Proof.
    intros mX A adr0 pn H. eapply rw_cells_recast; [exact H| cbn; repeat split; auto| unfold sct_cells, sct_new_cells, MallocRep.wz; cbn -[Z_to_bv le4 le8]; bytes_lit_eq| reflexivity].
  Qed.

  (* [comment removed for export] *)
  Lemma frame_join : forall mX v,
    rw_cells ctusegs mX (bv_unsigned sp + -80) [C8 v] -> rw_cells ctusegs mX (bv_unsigned sp + -72) hi_frame ->
    rw_cells ctusegs mX (bv_unsigned sp + -80) (C8 v :: hi_frame).
  Proof.
    intros mX v H0 H1.
    apply (proj2 (rw_cells_app mX _ [C8 v] hi_frame)). split; [exact H0|]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ].
    replace (bv_unsigned sp + -80 + 8) with (bv_unsigned sp + -72) by lia. exact H1.
  Qed.

  Lemma u64be_lt c0 q : u64be c0 q < 2 ^ 64.
  Proof.
    unfold u64be. pose proof (byte_range c0 q). pose proof (byte_range c0 (q+1)). pose proof (byte_range c0 (q+2)). pose proof (byte_range c0 (q+3)).
    pose proof (byte_range c0 (q+4)). pose proof (byte_range c0 (q+5)). pose proof (byte_range c0 (q+6)). pose proof (byte_range c0 (q+7)). lia.
  Qed.

  (* [comment removed for export] *)
  Definition v1_rec (pn lg : bptr) (ts : Z) (o : option (bptr * Z)) : sctr bptr := mkSCT pn (CtWire.byte c p) None (Some lg) ts o (olen o) 0 0 None.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition v1_cells (Cl ts X : Z) (elw : word) : list cell :=
    [C4 (Z_to_bv 64 (u32 0)); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 Cl); C8 (Z_to_bv 64 32); C8 (Z_to_bv 64 ts); C8 (Z_to_bv 64 X); C8 elw;
     C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); CB 6 (repeat (Z_to_bv 8 0) 6); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 (u32 (-1))); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 (u32 0)); C4 (Z_to_bv 64 0)].

  Lemma v1_tail : forall (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x23 x28 x29 x30 x31 pv elw : word)
      sX mX (errvX : word) (pn lg : bptr) (A Cl ts : Z) (o : option (bptr * Z)) (adr3 : bptr -> Z) (bl : list byte),
    let x3 := v1_rec pn lg ts o in
    let el := olen o in
    oinv sX st mX OW errvX bo (sct_blocks adr3 x3) ->
    adr3 pn = A -> adr3 lg = Cl -> (forall b, In b LB -> adr3 (blk_id b) = adr (blk_id b)) ->
    rw_cells ctusegs mX (bv_unsigned sp + -80) (C8 pv :: hi_frame) ->
    rw_cells ctusegs mX PIN [C8 (wz (D + p))] ->
    rw_cells ctusegs mX A (v1_cells Cl ts (optr adr3 o) elw) ->
    rw_cells ctusegs mX Cl [CB 32%nat bl] ->
    match o with Some (e, n) => 0 < n /\ exists be, rw_cells ctusegs mX (adr3 e) [CB (Z.to_nat n) be] | None => True end ->
    0 <= el <= len - 43 -> 43 <= len -> CtWire.byte c p = 0 -> 0 <= ts < 2 ^ 64 ->
    implM ctusegs (interp (ap_embed ((' (s13, r) <- o2i_sct_signature x3 c (p + 43 + el) (len - 43 - el) ;;
                                       (if r <=? 0 then err_raise RS_sct_sig ;;; sct_free s13 ;;; aret None else aret (Some s13))) st))) sX SPOST
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -80)) gp (wz RATP) x5 x6 x7 sp (wz A) x10 x11 x12 x13 x14 x15 x16 x17 (wz 0) (wz PIN) (wz el) (wz (D + p + 43)) (wz (len - 43)) x23 s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x19c978) fc None mX (seg_rom ctusegs)).
  Proof using FRM HF HM LEN P0 PAY PINhi PINlo PL PRE tp.
    intros until bl. cbv zeta. intros OI E3pn E3lg ADR3 FR HP HC HL HE EL L43 BY0 TSR. ctx. pose proof ESP as ESP.
    set (x3 := v1_rec pn lg ts o) in *. set (el := olen o) in *.
    pose proof (oinv_facts _ _ _ _ _ _ _ OI) as (HEAPX & NDX & BND & FRESH & DJL & _).
    pose proof (oinv_call _ _ _ _ _ _ _ OI) as (_ & _ & _ & STX & _ & _ & ERRX & MI & _).
    unfold LX_ERRNO, RATP in ERRX. change (3355176 - 164) with 3355012 in ERRX.
    destruct PBX as (pb & PA & psz & HPB & PB1 & PB2).
    assert (HXIN : In (pn, A, SCT_SIZE) (sct_blocks adr3 x3)).
    { unfold sct_blocks. rewrite !in_app_iff. right. right. right. right. left. change (sc_blk x3) with pn. rewrite E3pn. reflexivity. }
    assert (HLIN : In (lg, Cl, 32) (sct_blocks adr3 x3)).
    { unfold sct_blocks. rewrite !in_app_iff. left. change (sc_logid x3) with (Some lg). cbn. left. rewrite E3lg. reflexivity. }
    pose proof (BND pn A SCT_SIZE ltac:(apply in_app_iff; right; apply in_app_iff; left; exact HXIN)) as (BA0 & _ & BAC & BAI & _). unfold SCT_SIZE in BAC, BAI.
    pose proof (BND lg Cl 32 ltac:(apply in_app_iff; right; apply in_app_iff; left; exact HLIN)) as (BL0 & _ & BLC & BLI & _).
    pose proof (DJL pn A SCT_SIZE pb PA psz HXIN HPB) as SEPA. unfold SCT_SIZE in SEPA.
    assert (NDB : List.NoDup (map blk_id (sct_blocks adr3 x3))).
    { rewrite (map_app blk_id OW), (map_app blk_id (sct_blocks adr3 x3) LB) in NDX.
      destruct (NoDup_app_split _ _ NDX) as (N23 & _ & _). destruct (NoDup_app_split _ _ N23) as (_ & _ & N2). exact N2. }
    assert (DJLA : Cl + 32 <= A \/ A + 104 <= Cl).
    { eapply (blk_disjoint _ _ _ lg Cl 32 pn A 104 HEAPX); [apply in_app_iff; right; apply in_app_iff; left; exact HLIN| apply in_app_iff; right; apply in_app_iff; left; exact HXIN|].
      intros ->. unfold sct_blocks in NDB. change (sc_logid x3) with (Some pn) in NDB. cbn [osz32 option_map oblk map blk_id fst snd app] in NDB.
      apply NoDup_cons_iff in NDB. destruct NDB as [NN _]. apply NN. rewrite !map_app, !in_app_iff. right. right. right. left. reflexivity. }
    pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp); (PIN, PIN + 8); (A, A + 104)]%Z mX) as MU. pose proof (wmono_refl ctusegs mX) as WM.
    unfold hi_frame in FR. unfold MallocRep.wz in HP. unfold MallocRep.wz. unfold v1_cells in HC.
    (* [comment removed for export] *)
    unfold implM. iprefix.
    step. step. uchk.
    step. setreg 21%Z (Z_to_bv 64 (D + p + 43 + el)) ltac:(symmetry; apply bv_eq; rewrite ?unsigned_lit by lia; bv_solve).
    step. step. setreg 20%Z (Z_to_bv 64 (len - 43 - el)) ltac:(symmetry; apply bv_eq; rewrite ?unsigned_lit by lia; bv_solve).
    step. step. step. step. name_mem m4.
    ihere. to_implM.
    assert (OI4 : oinv sX st m4 OW errvX bo (sct_blocks adr3 x3)).
    { eapply oinv_munch; [exact OI| exact MU| exact WM| exact MI| exact STX| exact ERRX|].
      constructor; [left; cbn; lia|]. constructor; [right; left; reflexivity|]. constructor; [| constructor]. right. right. exists pn, A, SCT_SIZE. split; [exact HXIN| cbn; unfold SCT_SIZE; lia]. }
    pose proof OI4 as (PRE4 & LX4 & KO4 & KI4 & KP4 & SO4 & FA4 & HB4).
    (* [comment removed for export] *)
    apply (proj1 (rw_cells_app m4 (bv_unsigned sp + -80) [C8 (Z_to_bv 64 (D + p + 43 + el))] _)) in FR. destruct FR as [FRP FRH]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in FRH.
    replace (bv_unsigned sp + -80 + 8) with (bv_unsigned sp + -72) in FRH by lia.
    assert (HC4 : rw_cells ctusegs m4 (adr3 (sc_blk x3)) (sct_cells adr3 x3 (-1) 0)).
    { change (sc_blk x3) with pn. rewrite E3pn. unfold sct_cells. subst x3. unfold v1_rec.
      cbn [sc_version sc_blob sc_bloblen sc_logid sc_ts sc_ext sc_extlen sc_hash sc_sigalg sc_sig sc_siglen optr osz32 option_map logid_len].
      rewrite E3lg, BY0. unfold MallocRep.wz, CT_V1_HASHLEN. fold el. exact HC. }
    pose proof (o2i_sct_signature_walk HM HF) as W. unfold o2i_sct_signature_spec in W.
    eapply implM_abind.
    { eapply W with (LB := sct_blocks adr3 x3 ++ LB) (K := K) (adr := adr3) (x := x3) (vs := 0) (PIN := bv_unsigned sp + -80) (lo := lo) (B := B) (E := E) (bo := bo) (OW := OW) (errv := errvX) (canary := canary); clear W.
    - exact PRE4.
    - reflexivity.
    - exact FRM.
    - exact KO4.
    - exact KI4.
    - split; [exact HB4|]. destruct PAY as (_ & P1 & P2 & P3 & P4 & _). split; [exact P1|]. split; [exact P2|]. split; [exact P3|]. split; [exact P4|].
      right. exists (pb, PA, psz). split; [apply in_app_iff; right; exact HPB| cbn; lia].
    - lia.
    - lia.
    - lia.
    - lia.
    - change (sc_blk x3) with pn. rewrite E3pn. apply in_app_iff. left. exact HXIN.
    - change (sc_blk x3) with pn. rewrite E3pn. unfold SCT_SIZE. lia.
    - intros pb' PA' psz' Hb' H1 H2. change (sc_blk x3) with pn. intros ->.
      destruct (nodup_blk_eq _ _ _ _ _ _ NDX ltac:(apply in_app_iff; right; exact Hb') ltac:(apply in_app_iff; right; apply in_app_iff; left; exact HXIN)) as [-> ->].
      unfold SCT_SIZE in H2. lia.
    - exact HC4.
    - exact BY0.
    - reflexivity.
    - intros b Hb. apply in_app_iff. left. exact Hb.
    - exact NDB.
    - rewrite ESP. lia.
    - lia.
    - clear - SP16. Z.div_mod_to_equations. lia.
    - replace (D + (p + 43 + el)) with (D + p + 43 + el) by lia. exact FRP.
    - change (sc_blk x3) with pn. rewrite E3pn. reflexivity.
    - reflexivity.
    - reflexivity. }
    clear W.
    (* [comment removed for export] *)
    intros r sS msS POS. unfold o2i_sig_post in POS. rewrite ?ESP in POS.
    destruct POS as (v0 & v1 & v2 & v11 & v12 & v13 & v14 & v15 & v16 & v17 & v3 & v4 & v5 & v6 & FS & fcS & mS & OWS & errvS & boS & adrS & NEWS
                     & -> & FRMS & FES & PRES & LXS & SOS & FAS & BKS & ADRS & HCS & Eblk & Elg & Eext & Eblob & Ever & RST).
    destruct r as [[xr res] st']. cbn [fst snd] in *.
    replace (ret_pc (Z_to_bv 64 0x19c9a0)) with (Z_to_bv 64 0x19c9a0) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    change (sc_blk x3) with pn in LXS, HCS, Eblk. rewrite E3pn in LXS, HCS.
    assert (OI5 : oinv sS st' mS OWS errvS boS (NEWS ++ sct_blocks adr3 x3)).
    { eapply (oinv_after sX st m4 OW errvX bo (sct_blocks adr3 x3) sS st' mS OWS errvS boS [(bv_unsigned sp + -80, bv_unsigned sp + -80 + 8); (A, A + SCT_SIZE)]%Z NEWS);
        [exact OI4| exact PRES| exact LXS| | exact SOS| exact FAS| exact BKS].
      intros a Ha. cbn [rin_ivs fst snd] in Ha. destruct Ha as [Ha|[Ha|[]]]; [left; lia| right]. exists pn, A, SCT_SIZE. split; [exact HXIN| lia]. }
    (* [comment removed for export] *)
    pose proof (agree_of_lx_pres _ _ _ _ _ LXS) as AGS.
    assert (CLs : forall a, bv_unsigned sp + -80 <= a -> ~ (bv_unsigned sp + -80 <= a < bv_unsigned sp + -72) ->
                  lx_client (sct_blocks adr3 x3 ++ LB) (bv_unsigned sp + -80) ([(bv_unsigned sp + -80, bv_unsigned sp + -80 + 8); (A, A + SCT_SIZE)]%Z ++ LIBW_AP) a).
    { intros a Ha Hn. split; [unfold LIBW_AP, SCT_SIZE; cbn [rin_ivs fst snd app]; lia| left; exact Ha]. }
    assert (CLb : forall q Aq n a, In (q, Aq, n) (sct_blocks adr3 x3) -> (Aq + n <= A \/ A + 104 <= Aq) -> Aq <= a < Aq + n ->
                  lx_client (sct_blocks adr3 x3 ++ LB) (bv_unsigned sp + -80) ([(bv_unsigned sp + -80, bv_unsigned sp + -80 + 8); (A, A + SCT_SIZE)]%Z ++ LIBW_AP) a).
    { intros q Aq n a Hq Hd Ha. pose proof (BND q Aq n ltac:(apply in_app_iff; right; apply in_app_iff; left; exact Hq)) as (B1 & B2 & B3 & B4 & B5).
      split; [unfold LIBW_AP, SCT_SIZE; cbn [rin_ivs fst snd app]; lia|]. right. left. exists (q, Aq, n). split; [apply in_app_iff; left; exact Hq| cbn; lia]. }
    apply (rw_cells_agree _ _ _ _ _ AGS) in FRH; [| intros a Ha; apply CLs; cbn in Ha; lia].
    apply (rw_cells_agree _ _ _ _ _ AGS) in HP; [| intros a Ha; apply CLs; cbn in Ha; lia].
    apply (rw_cells_agree _ _ _ _ _ AGS) in HL; [| intros a Ha; eapply (CLb lg Cl 32); [exact HLIN| lia| cbn in Ha; lia]].
    assert (HE' : match o with Some (e, n) => 0 < n /\ exists be, rw_cells ctusegs mS (adrS e) [CB (Z.to_nat n) be] | None => True end).
    { destruct o as [[e n]|]; [| exact I]. destruct HE as (Hn & be & HBE).
      assert (HEIN : In (e, adr3 e, n) (sct_blocks adr3 x3)) by (unfold sct_blocks; rewrite !in_app_iff; right; left; left; reflexivity).
      assert (DJE : adr3 e + n <= A \/ A + 104 <= adr3 e).
      { eapply (blk_disjoint _ _ _ e (adr3 e) n pn A 104 HEAPX); [apply in_app_iff; right; apply in_app_iff; left; exact HEIN| apply in_app_iff; right; apply in_app_iff; left; exact HXIN|].
        intros ->. unfold sct_blocks in NDB. change (sc_logid x3) with (Some lg) in NDB. change (sc_ext x3) with (Some (pn, n)) in NDB.
        cbn [osz32 option_map oblk map blk_id fst snd app] in NDB.
        apply NoDup_cons_iff in NDB. destruct NDB as [_ NDB]. apply NoDup_cons_iff in NDB. destruct NDB as [NN _]. apply NN. rewrite !map_app, !in_app_iff. right. right. left. reflexivity. }
      split; [exact Hn|]. exists be. rewrite (ADRS (e, adr3 e, n)) by (apply in_app_iff; left; exact HEIN). cbn [blk_id fst snd].
      pose proof (BND e (adr3 e) n ltac:(apply in_app_iff; right; apply in_app_iff; left; exact HEIN)) as (BE1 & BE2 & BE3 & BE4 & BE5).
      apply (rw_cells_transport _ _ _ _ _ _ HBE MU) in WM as HBE4; [| cbn; rewrite Nat.add_0_r, Z2Nat.id by lia; lia].
      eapply (rw_cells_agree _ _ _ _ _ AGS); [exact HBE4|].
      intros a Ha. eapply (CLb e (adr3 e) n); [exact HEIN| exact DJE| cbn in Ha; rewrite Nat.add_0_r, Z2Nat.id in Ha by lia; lia]. }
    clear HE AGS CLs CLb MU WM MI.
    pose proof (oinv_call _ _ _ _ _ _ _ OI5) as (_ & _ & _ & STS & _ & _ & ERRS & MI & _).
    unfold LX_ERRNO, RATP in ERRS. change (3355176 - 164) with 3355012 in ERRS.
    pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp); (PIN, PIN + 8); (A, A + 104)]%Z mS) as MU. pose proof (wmono_refl ctusegs mS) as WM.
    assert (ElgS : adrS lg = Cl) by (rewrite (ADRS (lg, Cl, 32)) by (apply in_app_iff; left; exact HLIN); exact E3lg).
    assert (EpnS : adrS pn = A) by (rewrite (ADRS (pn, A, SCT_SIZE)) by (apply in_app_iff; left; exact HXIN); exact E3pn).
    assert (SGN : 0 <= sc_siglen xr).
    { destruct (res <=? 0); [destruct RST as (_ & _ & SG & _); unfold sc_siglen; rewrite SG; lia|].
      destruct RST as (_ & _ & _ & _ & _ & _ & _ & _ & SG). unfold sc_siglen. destruct (sc_sig xr) as [[q n]|]; lia. }
    (* [comment removed for export] *)
    unfold implM. iprefix. step. if_cases KR; zc KR.
    - (* [comment removed for export] *)
      destruct (res <=? 0) eqn:ER.
      2:{ exfalso. apply Z.leb_gt in ER. destruct RST as (Eres & Hle & _). rewrite land_ones64_small in KR by lia.
          apply Bool.andb_false_iff in KR. destruct KR as [KR|KR]; apply Z.ltb_ge in KR; lia. }
      destruct RST as (Eres & ENS & SIGN & HPl). subst res NEWS. cbn [Z.leb app] in OI5, HCS |- *.
      assert (EBS : sct_blocks adrS xr = sct_blocks adr3 x3).
      { unfold sct_blocks. rewrite Elg, Eext, Eblob, SIGN, Eblk. change (sc_logid x3) with (Some lg). change (sc_ext x3) with o. change (sc_sig x3) with (@None (bptr * Z)). change (sc_blob x3) with (@None (bptr * Z)).
        cbn [osz32 option_map oblk app]. rewrite ElgS, EpnS, E3lg, E3pn. destruct o as [[e n]|]; cbn [oblk app]; [| reflexivity].
        rewrite (ADRS (e, adr3 e, n)) by (apply in_app_iff; left; unfold sct_blocks; rewrite !in_app_iff; right; left; left; reflexivity). reflexivity. }
      rewrite <- EBS in OI5.
      ihere. to_implM.
      eapply implM_abind; [eapply (raise_blk RS_sct_sig); [right; right; split; reflexivity| exact OI5| exact FRMS| exact FES]|].
      intros r5 sF msF RP. cbv beta.
      unfold MallocRep.wz in HPl. unfold hi_frame in FRH |- *.
      eapply (free_exit _ _ _ _ _ _ _ mS r5 sF msF xr adrS A (Z_to_bv 64 (D + (p + 43 + el))));
        [exact RP| rewrite Eblk; exact EpnS| apply frame_join; [exact HPl| exact FRH]| exact HP| eapply sct_ptr_cells_of_cells; rewrite Eblk, EpnS; exact HCS].
    - (* [comment removed for export] *)
      destruct (res <=? 0) eqn:ER.
      { exfalso. destruct RST as (Eres & _). subst res. change (Z.land (-1) 18446744073709551615) with 18446744073709551615 in KR1. lia. }
      apply Z.leb_gt in ER. destruct RST as (Eres & Hle & HPl & Ets & Eel & Hh & Ha & Hnid & SG).
      replace (if res <=? 0 then 0 else 0) with 0 in HCS by (destruct (res <=? 0); reflexivity).
      unfold MallocRep.wz in HPl. unfold hi_frame in FRH.
      ihere. to_implM. apply implM_aret.
      step. step. step. setreg 20%Z (Z_to_bv 64 (D + p + len)) ltac:(symmetry; apply bv_eq; rewrite ?unsigned_lit by lia; bv_solve).
      uchk. step. step. step.
      assert (T1 : (bv_unsigned (Z_to_bv 64 0) <? bv_unsigned (Z_to_bv 64 (D + (p + 43 + el) + res))) = true) by (rewrite !unsigned_lit by lia; apply Z.ltb_lt; lia).
      assert (T2 : (bv_unsigned (Z_to_bv 64 (D + p + len)) <? bv_wrap 64 1) = false) by (rewrite unsigned_lit by lia; apply Z.ltb_ge; change (bv_wrap 64 1) with 1; lia).
      step. if_cases KN; [first [exfalso; rewrite v_sltu_b2z, v_sltiu_b2z, T1, T2 in KN; vm_compute in KN; discriminate KN| clear KN]
                         | first [exfalso; rewrite v_sltu_b2z, v_sltiu_b2z, T1, T2 in KN; vm_compute in KN; discriminate KN| clear KN]].
      clear T1 T2.
      (* [comment removed for export] *)
      assert (EBS : sct_blocks adrS xr = [(lg, Cl, 32)] ++ oblk adrS o ++ NEWS ++ [(pn, A, SCT_SIZE)]).
      { unfold sct_blocks. rewrite Elg, Eext, Eblob, Eblk. change (sc_logid x3) with (Some lg). change (sc_ext x3) with o. change (sc_blob x3) with (@None (bptr * Z)).
        cbn [osz32 option_map oblk app]. rewrite ElgS, EpnS. destruct (sc_sig xr) as [[g gn]|]; [destruct SG as (-> & _)| rewrite SG]; reflexivity. }
      assert (EO : oblk adrS o = oblk adr3 o).
      { destruct o as [[e n]|]; [| reflexivity]. cbn. rewrite (ADRS (e, adr3 e, n)) by (apply in_app_iff; left; unfold sct_blocks; rewrite !in_app_iff; right; left; left; reflexivity). reflexivity. }
      assert (EB3 : sct_blocks adr3 x3 = [(lg, Cl, 32)] ++ oblk adr3 o ++ [(pn, A, SCT_SIZE)]).
      { unfold sct_blocks. change (sc_logid x3) with (Some lg). change (sc_ext x3) with o. change (sc_blob x3) with (@None (bptr * Z)). change (sc_sig x3) with (@None (bptr * Z)). change (sc_blk x3) with pn.
        cbn [osz32 option_map oblk app]. rewrite E3lg, E3pn. reflexivity. }
      assert (OIF : oinv sS st' mS OWS errvS boS (sct_blocks adrS xr)).
      { eapply oinv_perm; [| exact OI5]. rewrite EBS, EB3, EO.
        pose proof (Permutation_app_swap_app NEWS ([(lg, Cl, 32)] ++ oblk adr3 o) [(pn, A, SCT_SIZE)]) as PM. rewrite <- !app_assoc in PM. exact PM. }
      pose proof (oinv_facts _ _ _ _ _ _ _ OIF) as (_ & NDF & _ & FRESHF & _).
      assert (ADRS' : forall b, In b LB -> adrS (blk_id b) = adr (blk_id b)).
      { intros b Hb. rewrite (ADRS b) by (apply in_app_iff; right; exact Hb). apply ADR3. exact Hb. }
      assert (SR : sct_rep mS (OWS ++ sct_blocks adrS xr ++ LB) adrS xr).
      { split. { rewrite Eblk, EpnS. apply in_app_iff. right. apply in_app_iff. left. rewrite EBS. rewrite !in_app_iff. right. right. right. left. reflexivity. }
        split; [rewrite Eblk, EpnS; exact HCS|].
        split. { rewrite Elg. change (sc_logid x3) with (Some lg). cbn. rewrite ElgS. split; [lia|]. split; [apply in_app_iff; right; apply in_app_iff; left; rewrite EBS; left; reflexivity|]. eexists. exact HL. }
        split. { rewrite Eext. change (sc_ext x3) with o. destruct o as [[e n]|]; [| exact I]. cbn. destruct HE' as (Hn & be & HBE). split; [exact Hn|].
                 split; [apply in_app_iff; right; apply in_app_iff; left; rewrite EBS; rewrite !in_app_iff; right; left; left; reflexivity|]. exists be. exact HBE. }
        split. { destruct (sc_sig xr) as [[g gn]|]; [| exact I]. destruct SG as (ENS & Hgn & _ & HG). cbn. split; [exact Hgn|].
                 split; [apply in_app_iff; right; apply in_app_iff; left; rewrite EBS, ENS; rewrite !in_app_iff; right; right; left; left; reflexivity|]. eexists. exact HG. }
        split; [rewrite Eblob; exact I|].
        split. { rewrite (map_app blk_id OWS), (map_app blk_id (sct_blocks adrS xr) LB) in NDF.
                 destruct (NoDup_app_split _ _ NDF) as (N23 & _ & _). destruct (NoDup_app_split _ _ N23) as (_ & _ & N2). exact N2. }
        rewrite Ever, Ets, Eel, Eext, sc_siglen_olen || rewrite Ever, Ets, Eel, Eext. change (sc_version x3) with (CtWire.byte c p). change (sc_ts x3) with ts. change (sc_extlen x3) with (olen o). change (sc_ext x3) with o.
        rewrite BY0. split; [right; lia|]. split; [intros _; exact Hnid|]. split; [exact Hh|]. split; [exact Ha|]. split; [exact TSR|]. split; [reflexivity|].
        rewrite <- sc_siglen_olen, Eblob. change (sc_blob x3) with (@None (bptr * Z)). cbn [olen]. fold el. unfold MAX_SCT_SIZE in *. repeat split; lia. }
      eapply (fin_ok _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ FS fcS sS st' mS OWS errvS boS xr adrS A (Z_to_bv 64 (D + (p + 43 + el) + res)));
        [exact OIF| exact FRMS| exact FES| rewrite Eblk; exact EpnS| apply frame_join; [exact HPl| exact FRH]| exact HP| exact SR| exact ADRS'| rewrite Ever; reflexivity].
  Qed.

  (* [comment removed for export] *)
  Definition v1_term (pn : bptr) (st0 : ap_st bptr) : aprog bptr (option (sctr bptr) * ap_st bptr) :=
    (let s := set_version (CtWire.byte c p) (sct_new pn) in
      if len <? 43 then err_raise RS_sct_43 ;;; sct_free s ;;; aret None
      else
        let len := len - 43 in
        let p := p + 1 in
        lg <- amalloc CT_V1_HASHLEN ;;
        let s := set_logid (Some lg) s in
        let p := p + CT_V1_HASHLEN in
        let s := set_ts (u64be c p) s in
        let p := p + 8 in
        let len2 := u16be c p in
        let p := p + 2 in
        if len <? len2 then err_raise RS_sct_ext ;;; sct_free s ;;; aret None
        else
          s <- (if 0 <? len2 then e <- amalloc len2 ;; aret (set_ext (Some (e, len2)) len2 s) else aret (set_ext None 0 s)) ;;
          let p := p + len2 in
          let len := len - len2 in
          ' (s, r) <- o2i_sct_signature s c p len ;;
          if r <=? 0 then err_raise RS_sct_sig ;;; sct_free s ;;; aret None
          else aret (Some s)) st0.

  (* [comment removed for export] *)
  Lemma v1_main : forall (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x22 x23 x28 x29 x30 x31 : word)
      sX mX (errvX : word) pn A (jl : word),
    oinv sX st mX OW errvX bo [(pn, A, SCT_SIZE)] ->
    rw_cells ctusegs mX (bv_unsigned sp + -80) (C8 jl :: hi_frame) ->
    rw_cells ctusegs mX PIN [C8 (wz (D + p))] ->
    rw_cells ctusegs mX A (sct_cells adr (set_version 0 (sct_new pn)) (-1) 0) ->
    CtWire.byte c p = 0 ->
    implM ctusegs (interp (ap_embed (v1_term pn st))) sX SPOST
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -80)) gp (wz RATP) x5 x6 x7 sp (wz A) x10 x11 x12 x13 x14 x15 x16 x17 (wz 0) (wz PIN) (wz len) (wz (D + p)) x22 x23 s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x19c7b0) fc None mX (seg_rom ctusegs)).
  Proof using FRM HF HM LEN P0 PAY PINhi PINlo PL PRE tp.
    intros until jl. intros OI FR HP HC BY0. ctx. pose proof ESP as ESP.
    pose proof (oinv_facts _ _ _ _ _ _ _ OI) as (HEAPX & NDX & BND & FRESH & DJL & _).
    pose proof (oinv_call _ _ _ _ _ _ _ OI) as (_ & _ & _ & STX & _ & _ & ERRX & MI & _).
    unfold LX_ERRNO, RATP in ERRX. change (3355176 - 164) with 3355012 in ERRX.
    destruct PBX as (pb & PA & psz & HPB & PB1 & PB2).
    pose proof (BND pn A SCT_SIZE ltac:(apply in_app_iff; right; left; reflexivity)) as (BA0 & _ & BAC & BAI & _). unfold SCT_SIZE in BAC, BAI.
    pose proof (DJL pn A SCT_SIZE pb PA psz ltac:(left; reflexivity) HPB) as SEPA. unfold SCT_SIZE in SEPA.
    assert (BY : forall i, 0 <= i < zlength c -> CtWire.byte c i = znth c i).
    { intros i Hi. unfold CtWire.byte, u8. apply Z.mod_small. pose proof (znth_range c i DF). lia. }
    pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp); (PIN, PIN + 8); (A, A + 104)]%Z mX) as MU. pose proof (wmono_refl ctusegs mX) as WM.
    unfold hi_frame in FR. unfold MallocRep.wz in HP.
    set (x0 := set_version (CtWire.byte c p) (sct_new pn)).
    set (adr0 := fun b : bptr => if bptr_eqb b pn then A else adr b).
    assert (E0pn : adr0 pn = A) by (subst adr0; cbn beta; rewrite bptr_eqb_refl; reflexivity).
    assert (EB0 : sct_blocks adr0 x0 = [(pn, A, SCT_SIZE)]).
    { subst x0 adr0. unfold sct_blocks. cbn [sc_logid sc_ext sc_sig sc_blob sc_blk set_version sct_new osz32 option_map oblk app]. rewrite bptr_eqb_refl. reflexivity. }
    unfold v1_term. cbv zeta. fold x0. unfold MallocRep.wz.
    unfold implM. iprefix.
    step. step. if_cases K43; zc K43.
    2:{ (* [comment removed for export] *)
        replace (len <? 43) with true by (symmetry; apply Z.ltb_lt; revert K43; rewrite ?unsigned_lit by lia; lia).
        ihere. to_implM.
        rewrite <- EB0 in OI.
        eapply implM_abind; [eapply (raise_blk RS_sct_43); [left; split; reflexivity| exact OI| exact FRM| intros; reflexivity]|].
        intros r sF msF RP. cbv beta.
        eapply (free_exit _ _ _ _ _ _ _ mX r sF msF x0 adr0 A jl); [exact RP| exact E0pn| exact FR| exact HP|].
        eapply sct_ptr_cells_of_cells. change (sc_blk x0) with pn. rewrite E0pn.
        subst x0. unfold sct_cells in HC |- *. cbn [sc_version sc_blob sc_bloblen sc_logid sc_ts sc_ext sc_extlen sc_hash sc_sigalg sc_sig sc_siglen sct_new set_version optr osz32 option_map logid_len] in HC |- *.
        rewrite BY0. exact HC. }
    (* [comment removed for export] *)
    replace (len <? 43) with false by (symmetry; apply Z.ltb_ge; revert K43; rewrite ?unsigned_lit by lia; lia).
    assert (L43 : 43 <= len) by (revert K43; rewrite ?unsigned_lit by lia; lia). clear K43.
    subst x0. unfold sct_cells in HC. cbn [sc_version sc_blob sc_bloblen sc_logid sc_ts sc_ext sc_extlen sc_hash sc_sigalg sc_sig sc_siglen sct_new set_version optr osz32 option_map logid_len] in HC.
    unfold MallocRep.wz in HC. cbn [u32 Z.modulo Z.pow_pos Pos.iter Z.mul] in HC.
    set (x0 := set_version (CtWire.byte c p) (sct_new pn)) in *.
    unfold CT_V1_HASHLEN. replace (p + 1 + 32 + 10) with (p + 43) by lia. replace (p + 1 + 32 + 8) with (p + 41) by lia. replace (p + 1 + 32) with (p + 33) by lia.
    set (len2 := u16be c (p + 41)). set (ts := u64be c (p + 33)).
    step. setreg 22%Z (Z_to_bv 64 (D + p + 1)) ltac:(symmetry; apply bv_eq; rewrite ?unsigned_lit by lia; bv_solve).
    step. uchk. step. name_mem m1.
    assert (OI1 : oinv sX st m1 OW errvX bo [(pn, A, SCT_SIZE)]).
    { eapply oinv_munch; [exact OI| exact MU| exact WM| exact MI| exact STX| exact ERRX|].
      constructor; [left; cbn; lia|]. constructor; [right; left; reflexivity|]. constructor; [| constructor]. right. right. exists pn, A, SCT_SIZE. split; [left; reflexivity| cbn; unfold SCT_SIZE; lia]. }
    clear OI. rename OI1 into OI.
    do 7 step. ihere. cbn [abind apbind amalloc aret ap_embed fst snd]. to_implM.
    pose proof (oinv_call _ _ _ _ _ _ _ OI) as (HEAP1 & AUX1 & _ & ST1 & _ & _ & ERR1 & MI1 & CS1 & _).
    pose proof OI as (_ & _ & _ & _ & _ & _ & _ & HB1).
    assert (SRC : bytes_at ctusegs m1 (D + p + 1) (to_bytes (slice c (p + 1) 32))).
    { unfold slice, to_bytes. rewrite <- firstn_map, <- skipn_map. fold (to_bytes c). apply bytes_at_firstn.
      replace (D + p + 1) with (D + Z.of_nat (Z.to_nat (p + 1))) by lia. apply bytes_at_skipn; [exact HB1|]. apply Nat2Z.inj_le. rewrite DLEN. lia. }
    assert (SLEN : length (to_bytes (slice c (p + 1) 32)) = Z.to_nat 32) by (unfold to_bytes; rewrite length_map; apply slice_length; lia).
    eapply (CRYPTO_memdup_walk HM) with (B := B) (lo := lo) (errv := errvX) (L := OW ++ [(pn, A, SCT_SIZE)] ++ LB)
                                        (pp := pb) (PA := PA) (psz := psz) (P := D + p + 1) (n := 32) (src := to_bytes (slice c (p + 1) 32));
      [exact HEAP1| exact AUX1| rewrite ESP; lia| rewrite ESP; exact ST1| exact CEIL| unfold GLOBALS_TOP; lia
      | rewrite ESP; unfold CRYPTO_MEMDUP_STACK, CRYPTO_MALLOC_STACK, RMALLOC_STACK; lia
      | exact ERR1| exact MI1| reflexivity| exact CS1
      | apply in_app_iff; right; apply in_app_iff; right; exact HPB| lia| lia| exact SRC| exact SLEN
      | apply bv_eq; rewrite ?unsigned_lit by lia; bv_solve| reflexivity| lia| reflexivity|].
    intros lg sL msL POL. unfold calloc_post in POL. rewrite ?ESP in POL.
    destruct POL as (u0 & u1 & u2 & u11 & u12 & u13 & u14 & u15 & u16 & u17 & u3 & u4 & u5 & u6 & mL & Cl & errvL
                     & -> & MIL & STL & ERRL & AUXL & HPL & FAL & SOL & BRL & HEAPL & (BLKL & _)).
    replace (ret_pc (Z_to_bv 64 0x19c800)) with (Z_to_bv 64 0x19c800) by (symmetry; apply ret_pc_even; [lia| reflexivity]). unfold MallocRep.wz.
    assert (OI2 : oinv sL st mL OW errvL bo [(lg, Cl, 32); (pn, A, SCT_SIZE)]).
    { eapply oinv_alloc; [exact OI| exact HPL| exact HEAPL| exact MIL| exact STL| exact ERRL| exact AUXL| exact FAL| exact SOL]. }
    pose proof (oinv_facts _ _ _ _ _ _ _ OI2) as (_ & ND2 & _ & FRESH2 & DJL2 & _).
    pose proof BRL as (BL0 & BL16 & _ & BLC & BLI).
    pose proof (LH_nodup _ _ _ HEAPL) as NDl. cbn [map blk_id fst snd app] in NDl. apply NoDup_cons_iff in NDl. destruct NDl as [NL _].
    assert (NLP : lg <> pn) by (intros ->; apply NL; rewrite map_app; apply in_app_iff; right; left; reflexivity).
    pose proof (blk_disjoint _ _ _ lg Cl 32 pn A SCT_SIZE HEAPL ltac:(left; reflexivity) ltac:(right; apply in_app_iff; right; left; reflexivity) NLP) as DJLA. unfold SCT_SIZE in DJLA.
    pose proof (agree_of_heap_pres _ _ _ _ HPL) as AGL.
    apply (rw_cells_agree _ _ _ _ _ AGL) in FR; [| intros a Ha; left; cbn in Ha; lia].
    apply (rw_cells_agree _ _ _ _ _ AGL) in HP; [| intros a Ha; left; cbn in Ha; lia].
    apply (rw_cells_agree _ _ _ _ _ AGL) in HC; [| intros a Ha; right; right; exists (pn, A, SCT_SIZE); split; [apply in_app_iff; right; left; reflexivity| cbn in Ha |- *; unfold SCT_SIZE in *; lia]].
    unfold LX_ERRNO, RATP in ERRL. change (3355176 - 164) with 3355012 in ERRL.
    pose proof OI2 as (_ & _ & _ & _ & _ & _ & _ & HB2).
    clear MU WM AGL MI SRC SLEN HEAP1 AUX1 ST1 ERR1 MI1 CS1 HB1 STX ERRX. rename MIL into MI.
    pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp); (PIN, PIN + 8); (A, A + 104)]%Z mL) as MU. pose proof (wmono_refl ctusegs mL) as WM.
    cbn [apbind fst snd].
    (* [comment removed for export] *)
    unfold implM. iprefix.
    step. step. if_cases K1; zc K1; [exfalso; revert K1; rewrite ?land_ones64_small by lia; lia|]. clear K1.
    step. step. uchk.
    step. setreg 10%Z (Z_to_bv 64 (D + p + 33)) ltac:(symmetry; apply bv_eq; rewrite ?unsigned_lit by lia; bv_solve).
    step. step. uchk.
    (* [comment removed for export] *)
    set (b0 := znth c (p + 33)). set (b1 := znth c (p + 34)). set (b2 := znth c (p + 35)). set (b3 := znth c (p + 36)).
    set (b4 := znth c (p + 37)). set (b5 := znth c (p + 38)). set (b6 := znth c (p + 39)). set (b7 := znth c (p + 40)).
    pose proof (znth_range c (p + 33) DF) as R0'. pose proof (znth_range c (p + 34) DF) as R1'. pose proof (znth_range c (p + 35) DF) as R2'. pose proof (znth_range c (p + 36) DF) as R3'.
    pose proof (znth_range c (p + 37) DF) as R4'. pose proof (znth_range c (p + 38) DF) as R5'. pose proof (znth_range c (p + 39) DF) as R6'. pose proof (znth_range c (p + 40) DF) as R7'.
    fold b0 in R0'. fold b1 in R1'. fold b2 in R2'. fold b3 in R3'. fold b4 in R4'. fold b5 in R5'. fold b6 in R6'. fold b7 in R7'.
    set (q1 := b0 * 256 + b1). set (q2 := q1 * 256 + b2). set (q3 := q2 * 256 + b3). set (q4 := q3 * 256 + b4). set (q5 := q4 * 256 + b5). set (q6 := q5 * 256 + b6).
    assert (Q1 : 0 <= q1 < 2 ^ 16) by lia. assert (Q2 : 0 <= q2 < 2 ^ 24) by lia. assert (Q3 : 0 <= q3 < 2 ^ 32) by lia.
    assert (Q4 : 0 <= q4 < 2 ^ 40) by lia. assert (Q5 : 0 <= q5 < 2 ^ 48) by lia. assert (Q6 : 0 <= q6 < 2 ^ 56) by lia.
    assert (TSQ : ts = q6 * 256 + b7).
    { subst ts q6 q5 q4 q3 q2 q1 b0 b1 b2 b3 b4 b5 b6 b7. unfold u64be. rewrite !BY by lia.
      replace (p + 33 + 1) with (p + 34) by lia. replace (p + 33 + 2) with (p + 35) by lia. replace (p + 33 + 3) with (p + 36) by lia. replace (p + 33 + 4) with (p + 37) by lia.
      replace (p + 33 + 5) with (p + 38) by lia. replace (p + 33 + 6) with (p + 39) by lia. replace (p + 33 + 7) with (p + 40) by lia. reflexivity. }
    (* [comment removed for export] *)
    pose proof (payload_read _ D c (p + 33) (wa (D + p + 33)) HB2 DF ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD. step. clear RD. rewrite (zxb_lit (znth c (p + 33))) by lia. fold b0.
    step. setreg 11%Z (Z_to_bv 64 (D + p + 34)) ltac:(symmetry; apply bv_eq; rewrite ?unsigned_lit by lia; bv_solve).
    step. setreg 12%Z (Z_to_bv 64 (D + p + 35)) ltac:(symmetry; apply bv_eq; rewrite ?unsigned_lit by lia; bv_solve).
    step.
    step. setreg 10%Z (Z_to_bv 64 (b0 * 2 ^ 56)) ltac:(rewrite (unsigned_lit b0), Z.shiftl_mul_pow2 by lia; reflexivity).
    step. step. uchk.
    (* [comment removed for export] *)
    Local Ltac ts_rd i bi HB DF :=
      pose proof (payload_read _ D c (p + i) (wa (D + p + i)) HB DF ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD; step; clear RD; rewrite (zxb_lit (znth c (p + i))) by lia; fold bi.
    Local Ltac ts_sh r bi k := step; setreg r (Z_to_bv 64 (bi * 2 ^ k)) ltac:(rewrite (unsigned_lit bi), Z.shiftl_mul_pow2 by lia; reflexivity).
    Local Ltac ts_or r bi qo qn kprev k :=
      step; setreg r (Z_to_bv 64 (qn * 2 ^ k))
              ltac:(rewrite (unsigned_lit (bi * 2 ^ k)), (unsigned_lit (qo * 2 ^ kprev)) by lia; change (qo * 2 ^ kprev) with (qo * 2 ^ (k + 8));
                    rewrite lor_hi_lo by lia; replace (qo * 256 + bi) with qn by reflexivity; reflexivity).
    Local Ltac ts_ad r i := step; setreg r (Z_to_bv 64 (D + p + i)) ltac:(symmetry; apply bv_eq; rewrite ?unsigned_lit by lia; bv_solve).
    ts_rd 34 b1 HB2 DF. step. ts_sh 13%Z b1 48. ts_or 10%Z b1 b0 q1 56 48. ts_ad 12%Z 36. step. uchk.
    ts_rd 35 b2 HB2 DF. step. ts_ad 12%Z 37. ts_sh 11%Z b2 40. ts_or 10%Z b2 q1 q2 48 40. step. step. uchk.
    ts_rd 36 b3 HB2 DF. step. ts_sh 13%Z b3 32. ts_or 10%Z b3 q2 q3 40 32. ts_ad 12%Z 38. step. uchk.
    ts_rd 37 b4 HB2 DF. step. ts_ad 12%Z 39. ts_sh 11%Z b4 24. ts_or 11%Z b4 q3 q4 32 24. step. step. uchk.
    ts_rd 38 b5 HB2 DF. step. ts_sh 13%Z b5 16. ts_or 11%Z b5 q4 q5 24 16. ts_ad 12%Z 40. step. uchk.
    ts_rd 39 b6 HB2 DF. step. ts_ad 10%Z 41. ts_sh 13%Z b6 8. ts_or 11%Z b6 q5 q6 16 8. step. step. uchk.
    (* [comment removed for export] *)
    ts_rd 40 b7 HB2 DF. step.
    step. setreg 11%Z (Z_to_bv 64 ts) ltac:(rewrite (unsigned_lit b7), (unsigned_lit (q6 * 2 ^ 8)) by lia; change (2 ^ 8) with 256; rewrite lor_shl8 by lia; rewrite TSQ; reflexivity).
    step. step. uchk. step. uchk.
    clear Q1 Q2 Q3 Q4 Q5 Q6 TSQ R0' R1' R2' R3' R4' R5' R6' R7'. clearbody q1 q2 q3 q4 q5 q6. clear q1 q2 q3 q4 q5 q6.
    pose proof (u64be_nonneg c (p + 33)) as TS0. fold ts in TS0.
    (* [comment removed for export] *)
    pose proof (znth_range c (p + 41) DF) as R41. pose proof (znth_range c (p + 42) DF) as R42.
    pose proof (payload_read _ D c (p + 41) (wa (D + p + 41)) HB2 DF ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD. step. clear RD. rewrite (zxb_lit (znth c (p + 41))) by lia.
    pose proof (payload_read _ D c (p + 42) (wa (D + p + 42)) HB2 DF ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD. step. clear RD. rewrite (zxb_lit (znth c (p + 42))) by lia.
    step. setreg 22%Z (Z_to_bv 64 (len - 43)) ltac:(symmetry; apply bv_eq; rewrite ?unsigned_lit by lia; bv_solve).
    step. step.
    setreg 20%Z (Z_to_bv 64 len2)
      ltac:(subst len2; unfold u16be; rewrite !BY by lia; replace (p + 41 + 1) with (p + 42) by lia; f_equal;
            rewrite (unsigned_lit (znth c (p + 41))), (unsigned_lit (znth c (p + 42))) by lia; rewrite Z.shiftl_mul_pow2 by lia; change (2 ^ 8) with 256;
            rewrite (unsigned_lit (znth c (p + 41) * 256)) by lia; symmetry; apply lor_shl8; lia).
    pose proof (u16be_range c (p + 41)) as L2R. fold len2 in L2R.
    step. setreg 21%Z (Z_to_bv 64 (D + p + 43)) ltac:(symmetry; apply bv_eq; rewrite ?unsigned_lit by lia; bv_solve).
    step. name_mem m2.
    set (x2 := set_ts ts (set_logid (Some lg) x0)) in *.
    set (adr2 := fun b : bptr => if bptr_eqb b lg then Cl else if bptr_eqb b pn then A else adr b).
    assert (E2lg : adr2 lg = Cl) by (subst adr2; cbn beta; rewrite bptr_eqb_refl; reflexivity).
    assert (E2pn : adr2 pn = A) by (subst adr2; cbn beta; rewrite (bptr_eqb_neq pn lg) by (intros E0; apply NLP; symmetry; exact E0); rewrite bptr_eqb_refl; reflexivity).
    assert (EB2 : sct_blocks adr2 x2 = [(lg, Cl, 32); (pn, A, SCT_SIZE)]).
    { subst x2 x0 adr2. unfold sct_blocks. cbn [sc_logid sc_ext sc_sig sc_blob sc_blk set_ts set_logid set_version sct_new osz32 option_map oblk app]. rewrite bptr_eqb_refl.
      rewrite (bptr_eqb_neq pn lg) by (intros E0; apply NLP; symmetry; exact E0). rewrite bptr_eqb_refl. reflexivity. }
    assert (HC2 : rw_cells ctusegs m2 (adr2 (sc_blk x2)) (sct_cells adr2 x2 (-1) 0)).
    { change (sc_blk x2) with pn. rewrite E2pn. subst x2 x0. unfold sct_cells.
      cbn [sc_version sc_blob sc_bloblen sc_logid sc_ts sc_ext sc_extlen sc_hash sc_sigalg sc_sig sc_siglen sct_new set_version set_logid set_ts optr osz32 option_map logid_len].
      rewrite E2lg, BY0. unfold MallocRep.wz, CT_V1_HASHLEN. exact HC. }
    assert (OI3 : oinv sL st m2 OW errvL bo (sct_blocks adr2 x2)).
    { rewrite EB2. eapply oinv_munch; [exact OI2| exact MU| exact WM| exact MI| exact STL| exact ERRL|].
      constructor; [left; cbn; lia|]. constructor; [right; left; reflexivity|]. constructor; [| constructor]. right. right. exists pn, A, SCT_SIZE. split; [right; left; reflexivity| cbn; unfold SCT_SIZE; lia]. }
    step. if_cases KE; zc KE.
    2:{ (* [comment removed for export] *)
        replace (len - 43 <? len2) with true by (symmetry; apply Z.ltb_lt; revert KE; rewrite ?unsigned_lit by lia; lia).
        ihere. to_implM.
        eapply implM_abind; [eapply (raise_blk RS_sct_ext); [right; left; split; reflexivity| exact OI3| exact FRM| intros; reflexivity]|].
        intros r sF msF RP. cbv beta.
        eapply (free_exit _ _ _ _ _ _ _ m2 r sF msF x2 adr2 A); [exact RP| exact E2pn| exact FR| exact HP| eapply sct_ptr_cells_of_cells; exact HC2]. }
    replace (len - 43 <? len2) with false by (symmetry; apply Z.ltb_ge; revert KE; rewrite ?unsigned_lit by lia; lia).
    assert (LE2 : len2 <= len - 43) by (revert KE; rewrite ?unsigned_lit by lia; lia). clear KE.
    pose proof (u64be_lt c (p + 33)) as TS1. fold ts in TS1.
    assert (ADR2 : forall b, In b LB -> adr2 (blk_id b) = adr (blk_id b)).
    { intros [[b Ab] nb] Hb. subst adr2. cbn beta. cbn [blk_id fst snd].
      rewrite (bptr_eqb_neq b lg) by (intros ->; apply (FRESH2 lg Cl 32 ltac:(left; reflexivity)); rewrite map_app; apply in_app_iff; right; exact (in_ids _ _ _ _ Hb)).
      rewrite (bptr_eqb_neq b pn) by (intros ->; apply (FRESH2 pn A SCT_SIZE ltac:(right; left; reflexivity)); rewrite map_app; apply in_app_iff; right; exact (in_ids _ _ _ _ Hb)).
      reflexivity. }
    assert (EB2' : sct_blocks adr2 (v1_rec pn lg ts None) = sct_blocks adr2 x2) by reflexivity.
    step. if_cases KZ; zc KZ.
    - (* [comment removed for export] *)
      assert (L20 : len2 = 0) by (revert KZ; rewrite ?unsigned_lit by lia; lia). clear KZ.
      replace (0 <? len2) with false by (symmetry; apply Z.ltb_ge; lia).
      ihere. cbn [abind apbind aret]. to_implM.
      clearbody len2. subst len2.
      eapply (v1_tail _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 (D + p + 43)) (Z_to_bv 64 0) sL m2 errvL pn lg A Cl ts None adr2);
        [rewrite EB2'; exact OI3| exact E2pn| exact E2lg| exact ADR2| exact FR| exact HP| exact HC| exact BLKL| exact I| cbn; lia| exact L43| exact BY0| lia].
    - (* [comment removed for export] *)
      assert (L2P : 0 < len2) by (revert KZ; rewrite ?unsigned_lit by lia; lia). clear KZ.
      replace (0 <? len2) with true by (symmetry; apply Z.ltb_lt; lia).
      do 6 step. ihere. cbn [abind apbind amalloc aret ap_embed fst snd]. to_implM.
      rewrite EB2 in OI3.
      pose proof (oinv_call _ _ _ _ _ _ _ OI3) as (HEAP3 & AUX3 & _ & ST3 & _ & _ & ERR3 & MI3 & CS3 & _).
      pose proof OI3 as (_ & _ & _ & _ & _ & _ & _ & HB3).
      assert (SRC : bytes_at ctusegs m2 (D + p + 43) (to_bytes (slice c (p + 43) len2))).
      { unfold slice, to_bytes. rewrite <- firstn_map, <- skipn_map. fold (to_bytes c). apply bytes_at_firstn.
        replace (D + p + 43) with (D + Z.of_nat (Z.to_nat (p + 43))) by lia. apply bytes_at_skipn; [exact HB3|]. apply Nat2Z.inj_le. rewrite DLEN. lia. }
      assert (SLEN : length (to_bytes (slice c (p + 43) len2)) = Z.to_nat len2) by (unfold to_bytes; rewrite length_map; apply slice_length; lia).
      eapply (CRYPTO_memdup_walk HM) with (B := B) (lo := lo) (errv := errvL) (L := OW ++ [(lg, Cl, 32); (pn, A, SCT_SIZE)] ++ LB)
                                          (pp := pb) (PA := PA) (psz := psz) (P := D + p + 43) (n := len2) (src := to_bytes (slice c (p + 43) len2));
        [exact HEAP3| exact AUX3| rewrite ESP; lia| rewrite ESP; exact ST3| exact CEIL| unfold GLOBALS_TOP; lia
        | rewrite ESP; unfold CRYPTO_MEMDUP_STACK, CRYPTO_MALLOC_STACK, RMALLOC_STACK; lia
        | exact ERR3| exact MI3| reflexivity| exact CS3
        | apply in_app_iff; right; apply in_app_iff; right; exact HPB| lia| lia| exact SRC| exact SLEN
        | reflexivity| reflexivity| unfold MAX_SCT_SIZE in LEN; lia| reflexivity|].
      intros e sE msE POE. unfold calloc_post in POE. rewrite ?ESP in POE.
      destruct POE as (w0 & w1 & w2 & w11 & w12 & w13 & w14 & w15 & w16 & w17 & w3 & w4 & w5 & w6 & mE & Ce & errvE
                       & -> & MIE & STE & ERRE & AUXE & HPE & FAE & SOE & BRE & HEAPE & (BLKE & _)).
      replace (ret_pc (Z_to_bv 64 0x19c970)) with (Z_to_bv 64 0x19c970) by (symmetry; apply ret_pc_even; [lia| reflexivity]). unfold MallocRep.wz.
      assert (OI4 : oinv sE st mE OW errvE bo [(e, Ce, len2); (lg, Cl, 32); (pn, A, SCT_SIZE)]).
      { eapply oinv_alloc; [exact OI3| exact HPE| exact HEAPE| exact MIE| exact STE| exact ERRE| exact AUXE| exact FAE| exact SOE]. }
      pose proof (oinv_facts _ _ _ _ _ _ _ OI4) as (_ & ND4 & _ & FRESH4 & DJL4 & _).
      pose proof BRE as (BE0 & BE16 & _ & BEC & BEI).
      pose proof (LH_nodup _ _ _ HEAPE) as NDe. cbn [map blk_id fst snd app] in NDe. apply NoDup_cons_iff in NDe. destruct NDe as [NE _].
      assert (NEP : e <> pn) by (intros ->; apply NE; rewrite map_app; apply in_app_iff; right; right; left; reflexivity).
      assert (NEL : e <> lg) by (intros ->; apply NE; rewrite map_app; apply in_app_iff; right; left; reflexivity).
      pose proof (blk_disjoint _ _ _ e Ce len2 pn A SCT_SIZE HEAPE ltac:(left; reflexivity) ltac:(right; apply in_app_iff; right; right; left; reflexivity) NEP) as DJEA. unfold SCT_SIZE in DJEA.
      pose proof (agree_of_heap_pres _ _ _ _ HPE) as AGE.
      apply (rw_cells_agree _ _ _ _ _ AGE) in FR; [| intros a Ha; left; cbn in Ha; lia].
      apply (rw_cells_agree _ _ _ _ _ AGE) in HP; [| intros a Ha; left; cbn in Ha; lia].
      apply (rw_cells_agree _ _ _ _ _ AGE) in HC; [| intros a Ha; right; right; exists (pn, A, SCT_SIZE); split; [apply in_app_iff; right; right; left; reflexivity| cbn in Ha |- *; unfold SCT_SIZE; lia]].
      apply (rw_cells_agree _ _ _ _ _ AGE) in BLKL; [| intros a Ha; right; right; exists (lg, Cl, 32); split; [apply in_app_iff; right; left; reflexivity| cbn in Ha |- *; lia]].
      unfold LX_ERRNO, RATP in ERRE. change (3355176 - 164) with 3355012 in ERRE.
      clear MU WM AGE MI SRC SLEN HEAP3 AUX3 ST3 ERR3 MI3 CS3 HB3. rename MIE into MI.
      pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp); (PIN, PIN + 8); (A, A + 104)]%Z mE) as MU. pose proof (wmono_refl ctusegs mE) as WM.
      cbn [apbind fst snd].
      (* [comment removed for export] *)
      unfold implM. iprefix.
      step. step. if_cases K1; zc K1; [exfalso; revert K1; rewrite ?land_ones64_small by lia; lia|]. clear K1.
      name_mem m3. ihere. to_implM.
      set (adr3 := fun b : bptr => if bptr_eqb b e then Ce else adr2 b).
      assert (E3e : adr3 e = Ce) by (subst adr3; cbn beta; rewrite bptr_eqb_refl; reflexivity).
      assert (E3pn : adr3 pn = A) by (subst adr3; cbn beta; rewrite (bptr_eqb_neq pn e) by (intros E0; apply NEP; symmetry; exact E0); exact E2pn).
      assert (E3lg : adr3 lg = Cl) by (subst adr3; cbn beta; rewrite (bptr_eqb_neq lg e) by (intros E0; apply NEL; symmetry; exact E0); exact E2lg).
      assert (ADR3 : forall b, In b LB -> adr3 (blk_id b) = adr (blk_id b)).
      { intros b Hb. subst adr3. cbn beta. rewrite (bptr_eqb_neq (blk_id b) e); [apply ADR2; exact Hb|].
        destruct b as [[b' Ab] nb]. cbn. intros ->. apply (FRESH4 e Ce len2 ltac:(left; reflexivity)). rewrite map_app. apply in_app_iff. right. exact (in_ids _ _ _ _ Hb). }
      assert (EB3 : sct_blocks adr3 (v1_rec pn lg ts (Some (e, len2))) = [(lg, Cl, 32); (e, Ce, len2); (pn, A, SCT_SIZE)]).
      { unfold sct_blocks, v1_rec. cbn [sc_logid sc_ext sc_sig sc_blob sc_blk osz32 option_map oblk app]. rewrite E3lg, E3e, E3pn. reflexivity. }
      assert (OI5 : oinv sE st m3 OW errvE bo (sct_blocks adr3 (v1_rec pn lg ts (Some (e, len2))))).
      { rewrite EB3. eapply oinv_perm; [apply perm_swap|].
        eapply oinv_munch; [exact OI4| exact MU| exact WM| exact MI| exact STE| exact ERRE|].
        constructor; [left; cbn; lia|]. constructor; [right; left; reflexivity|]. constructor; [| constructor]. right. right. exists pn, A, SCT_SIZE. split; [right; right; left; reflexivity| cbn; unfold SCT_SIZE; lia]. }
      replace (Z_to_bv 64 Ce) with (Z_to_bv 64 (optr adr3 (Some (e, len2)))) in HC by (cbn [optr]; rewrite E3e; reflexivity).
      eapply (v1_tail _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 (D + p + 43)) (Z_to_bv 64 0) sE m3 errvE pn lg A Cl ts (Some (e, len2)) adr3);
        [exact OI5| exact E3pn| exact E3lg| exact ADR3| exact FR| exact HP| exact HC| exact BLKL| | cbn; lia| exact L43| exact BY0| lia].
      split; [exact L2P|]. exists (to_bytes (slice c (p + 43) len2)). rewrite E3e. exact BLKE.
  Qed.

  Theorem sct_main : forall (t0 t1 t2 t3 a3 a4 a5 a6 a7 t4 t5 t6 : word), PIN mod 8 = 0 ->
    implM ctusegs (interp (ap_embed (o2i_sct c p len st))) s SPOST
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz 0) (wz PIN) (wz len) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz O2I_SCT) fc None m (seg_rom ctusegs)).
  Proof using FRM HF HM HPIN KIDS KOW LEN P0 PAY PINhi PINlo PL PRE TP.
    intros until t6. intros PINal. ctx. pose proof ESP as ESP. rewrite TP.
    pose proof PRE as (HEAP & AS & IDS & DC & AUX & SPB' & B63' & ST & CEIL' & GLO' & LO' & ERR & SSP & MI & _).
    unfold MallocRep.wz in ERR. rewrite EA in ERR.
    pose proof PAY as (HB & _). unfold MallocRep.wz in HPIN. pose proof HPIN as HP. clear HPIN.
    unfold O2I_SCT, MallocRep.wz.
    pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl ctusegs m) as WM.
    unfold implM. iprefix.
    (* [comment removed for export] *)
    carve_frame 80%nat ST. do 11 step. step. step.
    step. step. step. if_cases KL; zc KL; rewrite land_ones64_neg in KL by (unfold MAX_SCT_SIZE in LEN; lia); [| exfalso; unfold MAX_SCT_SIZE in LEN; lia]. clear KL.
    step. name_mem m1.
    assert (OI1 : oinv s st m1 OW errv bo []).
    { eapply oinv_munch; [apply oinv0| exact MU| exact WM| exact MI| exact ST| exact ERR|]. constructor; [left; cbn; lia| constructor]. }
    (* [comment removed for export] *)
    step. ihere.
    unfold o2i_sct. replace ((len =? 0) || (MAX_SCT_SIZE <? len)) with false by (symmetry; unfold MAX_SCT_SIZE in *; apply orb_false_intro; [apply Z.eqb_neq| apply Z.ltb_ge]; lia).
    cbn [abind apbind amalloc aret ap_embed fst snd]. to_implM.
    pose proof (oinv_call _ _ _ _ _ _ _ OI1) as (HEAP1 & AUX1 & SPB1 & ST1 & _ & _ & ERR1 & MI1 & CS1 & AS1).
    change SZ_SCT with SCT_SIZE.
    eapply (SCT_new_walk HM) with (B := B) (lo := lo) (errv := errv) (L := OW ++ [] ++ LB);
      [exact HEAP1| exact AUX1| rewrite ESP; lia| rewrite ESP; exact ST1| exact CEIL| unfold GLOBALS_TOP; lia
      | rewrite ESP; unfold SCT_NEW_STACK, CRYPTO_ZALLOC_STACK, CRYPTO_MALLOC_STACK, RMALLOC_STACK; lia
      | exact ERR1| exact MI1| reflexivity| exact CS1| reflexivity|].
    intros pn sN msN PON. unfold calloc_post in PON. rewrite ?ESP in PON.
    destruct PON as (n0 & n1 & n2 & n11 & n12 & n13 & n14 & n15 & n16 & n17 & n3 & n4 & n5 & n6 & mN & A & errvN
                     & -> & MIN & STN & ERRN & AUXN & HPN & FAN & SON & BRN & HEAPN & BLKN).
    replace (ret_pc (Z_to_bv 64 0x19c6ec)) with (Z_to_bv 64 0x19c6ec) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    assert (OI2 : oinv sN st mN OW errvN bo [(pn, A, SCT_SIZE)]).
    { eapply oinv_alloc; [exact OI1| exact HPN| exact HEAPN| exact MIN| exact STN| exact ERRN| exact AUXN| exact FAN| exact SON]. }
    cbn [apbind fst snd].
    lazymatch goal with |- implM ?sg (interp (ap_embed ((if ?b then ?T1 else ?T2) ?stt))) ?sx ?Q ?ms =>
      change (implM sg (interp (ap_embed ((if b then v1_term pn else T2) stt))) sx Q ms) end.
    pose proof (oinv_facts _ _ _ _ _ _ _ OI2) as (_ & ND2 & _ & FRESH2 & DJL2 & _).
    destruct PBX as (pb & PA & psz & HPB & PB1 & PB2).
    pose proof (DJL2 pn A SCT_SIZE pb PA psz ltac:(left; reflexivity) HPB) as SEPA. unfold SCT_SIZE in SEPA.
    pose proof BRN as (BA0 & BA16 & _ & BAC & BAI). unfold SCT_SIZE in BAC, BAI.
    (* [comment removed for export] *)
    pose proof (agree_of_heap_pres _ _ _ _ HPN) as AGN.
    apply (rw_cells_agree _ _ _ _ _ AGN) in FR; [| intros a Ha; left; cbn in Ha; lia].
    apply (rw_cells_agree _ _ _ _ _ AGN) in HP; [| intros a Ha; left; cbn in Ha; lia].
    apply (sct_new_cells_rep mN A adr pn) in BLKN. rename BLKN into HC. unfold sct_cells in HC.
    cbn [sc_version sc_blob sc_bloblen sc_logid sc_ts sc_ext sc_extlen sc_hash sc_sigalg sc_sig sc_siglen sct_new optr osz32 option_map logid_len u32 Z.modulo Z.pow_pos Pos.iter Z.mul] in HC.
    unfold MallocRep.wz in HC.
    pose proof OI2 as (_ & _ & _ & _ & _ & _ & _ & HB2).
    unfold LX_ERRNO, RATP in ERRN. change (3355176 - 164) with 3355012 in ERRN.
    clear MU WM AGN HB HEAP AS DC AUX ST ERR SSP HEAP1 AUX1 ST1 ERR1 MI1 CS1 AS1 MI.
    pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp); (PIN, PIN + 8); (A, A + 104)]%Z mN) as MU. pose proof (wmono_refl ctusegs mN) as WM.
    rename MIN into MI.
    assert (BY : forall i, 0 <= i < zlength c -> CtWire.byte c i = znth c i).
    { intros i Hi. unfold CtWire.byte, u8. apply Z.mod_small. pose proof (znth_range c i DF). lia. }
    pose proof (znth_range c p DF) as R0.
    (* [comment removed for export] *)
    unfold MallocRep.wz. unfold implM. iprefix.
    step. if_cases K0; zc K0; [exfalso; revert K0; rewrite ?land_ones64_small by lia; lia|]. clear K0.
    uchk. step. step. uchk. step. step. uchk. step. uchk.
    pose proof (payload_read _ D c p (wa (D + p)) HB2 DF ltac:(lia) eq_refl) as RD. step. clear RD. rewrite (zxb_lit (znth c p)) by lia.
    step. name_mem m2.
    step. if_cases KV; zc KV.
    - (* [comment removed for export] *)
      assert (V0 : znth c p = 0) by (revert KV; rewrite ?unsigned_lit by lia; lia). clear KV.
      replace (CtWire.byte c p =? 0) with true by (symmetry; apply Z.eqb_eq; rewrite BY by lia; exact V0).
      ihere. to_implM.
      assert (OI3 : oinv sN st m2 OW errvN bo [(pn, A, SCT_SIZE)]).
      { eapply oinv_munch; [exact OI2| exact MU| exact WM| exact MI| exact STN| exact ERRN|].
        constructor; [left; cbn; lia|]. constructor; [right; left; reflexivity|]. constructor; [| constructor]. right. right. exists pn, A, SCT_SIZE. split; [left; reflexivity| cbn; unfold SCT_SIZE; lia]. }
      rewrite V0 in HC.
      eapply (v1_main _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ sN m2 errvN pn A); [exact OI3| exact FR| exact HP| exact HC| rewrite BY by lia; exact V0].
    - (* [comment removed for export] *)
      replace (CtWire.byte c p =? 0) with false by (symmetry; apply Z.eqb_neq; rewrite BY by lia; revert KV; rewrite ?unsigned_lit by lia; lia).
      do 6 step. ihere. cbn [abind apbind amalloc aret ap_embed fst snd]. to_implM.
      assert (OI3 : oinv sN st m2 OW errvN bo [(pn, A, SCT_SIZE)]).
      { eapply oinv_munch; [exact OI2| exact MU| exact WM| exact MI| exact STN| exact ERRN|].
        constructor; [left; cbn; lia|]. constructor; [right; left; reflexivity|]. constructor; [| constructor]. right. right. exists pn, A, SCT_SIZE. split; [left; reflexivity| cbn; unfold SCT_SIZE; lia]. }
      pose proof (oinv_call _ _ _ _ _ _ _ OI3) as (HEAP3 & AUX3 & _ & ST3 & _ & _ & ERR3 & MI3 & CS3 & AS3).
      assert (SRC : bytes_at ctusegs m2 (D + p) (to_bytes (slice c p len))).
      { unfold slice, to_bytes. rewrite <- firstn_map, <- skipn_map. fold (to_bytes c). apply bytes_at_firstn.
        replace (D + p) with (D + Z.of_nat (Z.to_nat p)) by lia. apply bytes_at_skipn; [exact HB2|]. apply Nat2Z.inj_le. rewrite DLEN. lia. }
      assert (SLEN : length (to_bytes (slice c p len)) = Z.to_nat len) by (unfold to_bytes; rewrite length_map; apply slice_length; lia).
      eapply (CRYPTO_memdup_walk HM) with (B := B) (lo := lo) (errv := errvN) (L := OW ++ [(pn, A, SCT_SIZE)] ++ LB)
                                          (pp := pb) (PA := PA) (psz := psz) (P := D + p) (n := len) (src := to_bytes (slice c p len));
        [exact HEAP3| exact AUX3| rewrite ESP; lia| rewrite ESP; exact ST3| exact CEIL| unfold GLOBALS_TOP; lia
        | rewrite ESP; unfold CRYPTO_MEMDUP_STACK, CRYPTO_MALLOC_STACK, RMALLOC_STACK; lia
        | exact ERR3| exact MI3| reflexivity| exact CS3
        | apply in_app_iff; right; apply in_app_iff; right; exact HPB| lia| lia| exact SRC| exact SLEN| reflexivity| reflexivity| unfold MAX_SCT_SIZE in LEN; lia| reflexivity|].
      intros q sQ msQ POQ. unfold calloc_post in POQ. rewrite ?ESP in POQ.
      destruct POQ as (u0 & u1 & u2 & u11 & u12 & u13 & u14 & u15 & u16 & u17 & u3 & u4 & u5 & u6 & mQ & C & errvQ
                       & -> & MIQ & STQ & ERRQ & AUXQ & HPQ & FAQ & SOQ & BRQ & HEAPQ & (BLKQ & _)).
      replace (ret_pc (Z_to_bv 64 0x19c738)) with (Z_to_bv 64 0x19c738) by (symmetry; apply ret_pc_even; [lia| reflexivity]). unfold MallocRep.wz.
      assert (OI4 : oinv sQ st mQ OW errvQ bo [(q, C, len); (pn, A, SCT_SIZE)]).
      { eapply oinv_alloc; [exact OI3| exact HPQ| exact HEAPQ| exact MIQ| exact STQ| exact ERRQ| exact AUXQ| exact FAQ| exact SOQ]. }
      pose proof (oinv_facts _ _ _ _ _ _ _ OI4) as (_ & ND4 & _ & FRESH4 & DJL4 & _).
      pose proof BRQ as (BC0 & BC16 & _ & BCC & BCI).
      pose proof (LH_nodup _ _ _ HEAPQ) as NDQ. cbn [map blk_id fst snd app] in NDQ. apply NoDup_cons_iff in NDQ. destruct NDQ as [NQ _].
      assert (NQP : q <> pn) by (intros ->; apply NQ; rewrite map_app; apply in_app_iff; right; left; reflexivity).
      pose proof (blk_disjoint _ _ _ q C len pn A SCT_SIZE HEAPQ ltac:(left; reflexivity) ltac:(right; apply in_app_iff; right; left; reflexivity) NQP) as DJQ. unfold SCT_SIZE in DJQ.
      (* [comment removed for export] *)
      pose proof (agree_of_heap_pres _ _ _ _ HPQ) as AGQ.
      apply (rw_cells_agree _ _ _ _ _ AGQ) in FR; [| intros a Ha; left; cbn in Ha; lia].
      apply (rw_cells_agree _ _ _ _ _ AGQ) in HP; [| intros a Ha; left; cbn in Ha; lia].
      apply (rw_cells_agree _ _ _ _ _ AGQ) in HC; [| intros a Ha; right; right; exists (pn, A, SCT_SIZE); split; [apply in_app_iff; right; left; reflexivity| cbn in Ha |- *; unfold SCT_SIZE; lia]].
      unfold LX_ERRNO, RATP in ERRQ. change (3355176 - 164) with 3355012 in ERRQ.
      clear MU WM AGQ MI. rename MIQ into MI.
      pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp); (PIN, PIN + 8); (A, A + 104)]%Z mQ) as MU. pose proof (wmono_refl ctusegs mQ) as WM.
      (* [comment removed for export] *)
      apply implM_ret.
      step. step. if_cases K1; zc K1; [exfalso; revert K1; rewrite ?land_ones64_small by lia; lia|]. clear K1.
      step. step. uchk. step. setreg 20%Z (Z_to_bv 64 (D + p + len)) ltac:(symmetry; apply bv_eq; rewrite ?unsigned_lit by lia; bv_solve).
      name_mem m3. cbn [fst snd].
      set (adr1 := fun b : bptr => if bptr_eqb b q then C else if bptr_eqb b pn then A else adr b).
      set (xr := set_blob (Some (q, len)) (set_version (CtWire.byte c p) (sct_new pn))).
      assert (Eq1 : adr1 q = C) by (subst adr1; cbn beta; rewrite bptr_eqb_refl; reflexivity).
      assert (Epn : adr1 pn = A) by (subst adr1; cbn beta; rewrite (bptr_eqb_neq pn q) by (intros E0; apply NQP; symmetry; exact E0); rewrite bptr_eqb_refl; reflexivity).
      assert (EB : sct_blocks adr1 xr = [(q, C, len); (pn, A, SCT_SIZE)]).
      { subst xr. unfold sct_blocks. cbn [sc_logid sc_ext sc_sig sc_blob sc_blk set_blob set_version sct_new osz32 option_map oblk app]. rewrite Eq1, Epn. reflexivity. }
      assert (OI5 : oinv sQ st m3 OW errvQ bo (sct_blocks adr1 xr)).
      { rewrite EB. eapply oinv_munch; [exact OI4| exact MU| exact WM| exact MI| exact STQ| exact ERRQ|].
        constructor; [left; cbn; lia|]. constructor; [right; left; reflexivity|]. constructor; [| constructor]. right. right. exists pn, A, SCT_SIZE. split; [right; left; reflexivity| cbn; unfold SCT_SIZE; lia]. }
      assert (ADR1 : forall b, In b LB -> adr1 (blk_id b) = adr (blk_id b)).
      { intros [[b Ab] nb] Hb. subst adr1. cbn.
        rewrite (bptr_eqb_neq b q) by (intros ->; apply (FRESH4 q C len ltac:(left; reflexivity)); rewrite map_app; apply in_app_iff; right; exact (in_ids _ _ _ _ Hb)).
        rewrite (bptr_eqb_neq b pn) by (intros ->; apply (FRESH4 pn A SCT_SIZE ltac:(right; left; reflexivity)); rewrite map_app; apply in_app_iff; right; exact (in_ids _ _ _ _ Hb)).
        reflexivity. }
      assert (SR : sct_rep m3 (OW ++ sct_blocks adr1 xr ++ LB) adr1 xr).
      { rewrite EB. split; [change (sc_blk xr) with pn; rewrite Epn; apply in_app_iff; right; right; left; reflexivity|].
        split. { change (sc_blk xr) with pn. rewrite Epn. unfold sct_cells. subst xr.
                 cbn [sc_version sc_blob sc_bloblen sc_logid sc_ts sc_ext sc_extlen sc_hash sc_sigalg sc_sig sc_siglen sct_new set_blob set_version optr osz32 option_map logid_len].
                 rewrite Eq1, BY, (u32_small (znth c p)), (u32_small 0) by lia. unfold MallocRep.wz. exact HC. }
        split; [exact I|]. split; [exact I|]. split; [exact I|].
        split. { cbn [arr_rep sc_blob xr set_blob]. rewrite Eq1. split; [lia|]. split; [apply in_app_iff; right; left; reflexivity|]. eexists. exact BLKQ. }
        split. { rewrite EB. cbn. constructor; [| constructor; [intros []| constructor]]. cbn. intros [E0|[]]. exact (NQP (eq_sym E0)). }
        subst xr. cbn [sc_version sc_hash sc_sigalg sc_ts sc_extlen sc_ext sc_sig sc_blob set_blob set_version sct_new olen sct_nid].
        pose proof (byte_range c p) as BR. rewrite BY in BR |- * by lia.
        split; [right; lia|]. split; [intros E0; exfalso; revert KV; rewrite E0, ?unsigned_lit by lia; lia|].
        unfold MAX_SCT_SIZE in *. repeat split; lia. }
      eapply (fin_ok _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc sQ st m3 OW errvQ bo xr adr1 A);
        [exact OI5| exact FRM| intros; reflexivity| exact Epn| exact FR| exact HP| exact SR| exact ADR1| subst xr; reflexivity].
  Qed.
  End Act.

  (* [comment removed for export] *)
  Theorem o2i_sct_walk : o2i_sct_spec.
  Proof using HF HM.
    unfold o2i_sct_spec. intros until PIN. intros PRE TP FRM KOW KIDS PAY P0 LEN PL ADR PINlo PINhi PINal HPIN -> -> ->.
    eapply sct_main; eassumption.
  Qed.
End Proofs.
End WithCeiling0.
