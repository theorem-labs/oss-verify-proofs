(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require Import ShapeAlg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Tac Bytes.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require Import LBase LSCPS.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import BImg RT_defs CJ_iface AShadow.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Export CJ_traces.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition is_pc0 (x : Z) : Prop := x = PC0_MALLOC \/ x = PC0_FREE \/ x = PC0_REALLOC.

Lemma is_pc0_lits : PC0_MALLOC = 0x54760 /\ PC0_FREE = 0x54600 /\ PC0_REALLOC = 0x549fc /\ TRACE_MAX_LEN = 30.
Proof. repeat split; reflexivity. Qed.

(* [comment removed for export] *)
Lemma not_pc0_high : forall r, 0x81ed8 <= r -> ~ is_pc0 r.
Proof. intros r Hr [H|[H|H]]; rewrite H in Hr; cbv in Hr; apply Hr; reflexivity. Qed.

(* [comment removed for export] *)
Notation frec := (Z * Z * Z)%type (only parsing).
Notation fchain := (list (Z * Z * Z)) (only parsing).
Definition fr_f (x : frec) : Z := fst (fst x).
Definition fr_ra (x : frec) : Z := snd (fst x).
Definition fr_s0 (x : frec) : Z := snd x.

(* [comment removed for export] *)
Fixpoint chain_cells (m : word -> option byte) (ch : fchain) : Prop :=
  match ch with
  | [] => True
  | (f, r, s) :: ch' => bytes_at bsegs m (f - 16) (le8 (wz s) ++ le8 (wz r)) /\ chain_cells m ch'
  end.

(* [comment removed for export] *)
Fixpoint chain_ok (fl : Z) (ch : fchain) (top : Z) : Prop :=
  match ch with
  | [] => True
  | (f, r, s) :: ch' =>
      fl <= f /\ f mod 8 = 0 /\ f + 16 < top /\ 4096 <= r < 2^64 /\ ~ is_pc0 r /\ 0 <= s < 2^64
      /\ match ch' with [] => s <= f | (f', _, _) :: _ => f' = s /\ f < f' end
      /\ chain_ok fl ch' top
  end.

(* [comment removed for export] *)
Definition chain_trace (k : Z) (ch : fchain) : list Z :=
  firstn (Z.to_nat (TRACE_MAX_LEN - k)) (map fr_ra ch).

Lemma chain_ok_mono : forall fl fl' ch top, chain_ok fl ch top -> fl' <= fl -> chain_ok fl' ch top.
Proof.
  intros fl fl' ch. induction ch as [|[[f r] s] ch IH]; intros top H Hle; [exact I|]. cbn in H |- *.
  destruct H as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8). repeat (split; [first [lia | assumption]|]).
  eapply IH; eauto.
Qed.

Lemma chain_ok_floor : forall fl ch top x, chain_ok fl ch top -> In x ch -> fl <= fr_f x /\ fr_f x + 16 < top.
Proof.
  intros fl ch. induction ch as [|[[f r] s] ch IH]; intros top x H Hin; [destruct Hin|]. cbn in H.
  destruct H as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8).
  destruct Hin as [<-|Hin]; [cbn; lia|]. eapply IH; eauto.
Qed.

Lemma chain_trace_nil : forall k, chain_trace k [] = [].
Proof. intros k. unfold chain_trace. cbn. apply firstn_nil. Qed.

Lemma chain_trace_cons : forall k f r s ch, k < TRACE_MAX_LEN ->
  chain_trace k ((f, r, s) :: ch) = r :: chain_trace (k + 1) ch.
Proof.
  intros k f r s ch Hk. unfold chain_trace. cbn [map fr_ra fst snd].
  replace (Z.to_nat (TRACE_MAX_LEN - k)) with (S (Z.to_nat (TRACE_MAX_LEN - (k + 1)))) by lia. reflexivity.
Qed.

Lemma chain_trace_full : forall k ch, TRACE_MAX_LEN <= k -> chain_trace k ch = [].
Proof. intros k ch Hk. unfold chain_trace. replace (Z.to_nat (TRACE_MAX_LEN - k)) with O by lia. reflexivity. Qed.

Lemma chain_trace_length : forall k ch, Z.of_nat (length (chain_trace k ch)) <= Z.max 0 (TRACE_MAX_LEN - k).
Proof. intros k ch. unfold chain_trace. rewrite firstn_length. lia. Qed.

(* [comment removed for export] *)
Lemma uwt_of_chain : forall m lo top pc0 fl ch prev f k,
  is_pc0 pc0 -> chain_cells m ch -> chain_ok fl ch top -> lo + 16 <= fl -> 0 <= k ->
  match ch with [] => False | (f0, _, _) :: _ => f = f0 /\ prev < f0 end ->
  uwt m lo top pc0 prev f k (chain_trace k ch).
Proof.
  intros m lo top pc0 fl ch. revert fl.
  induction ch as [|[[f0 r] s] ch IH]; intros fl prev f k P0 CC CO Hlo Hk HD; [destruct HD|].
  destruct HD as [-> Hprev]. cbn in CC, CO. destruct CC as [BY CC]. destruct CO as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8).
  destruct (Z.lt_ge_cases k TRACE_MAX_LEN) as [Hk30|Hk30].
  2:{ rewrite chain_trace_full by exact Hk30. apply uwt_stop. right; right; right. exact Hk30. }
  rewrite chain_trace_cons by exact Hk30.
  assert (Er : bv_unsigned (wz r) = r) by (unfold wz; apply unsigned_lit; lia).
  assert (Es : bv_unsigned (wz s) = s) by (unfold wz; apply unsigned_lit; lia).
  assert (E1 : (if bv_unsigned (wz r) =? pc0 then [] else [bv_unsigned (wz r)]) = [r]).
  { rewrite Er. destruct (Z.eqb_spec r pc0) as [->|]; [exfalso; exact (H5 P0)| reflexivity]. }
  assert (E2 : k + (if bv_unsigned (wz r) =? pc0 then 0 else 1) = k + 1).
  { rewrite Er. destruct (Z.eqb_spec r pc0) as [->|]; [exfalso; exact (H5 P0)| reflexivity]. }
  change (r :: chain_trace (k + 1) ch) with ([r] ++ chain_trace (k + 1) ch). rewrite <- E1.
  eapply uwt_hop; [lia| exact H2| lia| exact Hk30| lia| exact BY| rewrite Er; lia|].
  rewrite E2, Es. destruct ch as [|[[f1 r1] s1] ch'].
  - rewrite chain_trace_nil. apply uwt_stop. left. exact H7.
  - destruct H7 as [-> Hlt]. eapply (IH fl); [exact P0| exact CC| exact H8| exact Hlo| lia|]. split; [reflexivity| exact Hlt].
Qed.

(* [comment removed for export] *)
Lemma uwt_nonfp : forall m lo top pc0 prev f k, f <= prev -> uwt m lo top pc0 prev f k [].
Proof. intros. apply uwt_stop. left. assumption. Qed.

(* [comment removed for export] *)
Lemma uwt_hook_nonfp : forall m sp top pc0 s0v, s0v <= sp -> uwt m sp top pc0 sp s0v 2 [].
Proof. intros. apply uwt_nonfp. assumption. Qed.

Lemma uwt_hook_fp : forall m sp top pc0 spE ra s0v CH,
  is_pc0 pc0 ->
  chain_cells m ((spE, ra, s0v) :: CH) -> chain_ok spE ((spE, ra, s0v) :: CH) top ->
  sp + 16 <= spE ->
  uwt m sp top pc0 sp spE 2 (chain_trace 2 ((spE, ra, s0v) :: CH)).
Proof.
  intros m sp top pc0 spE ra s0v CH P0 CC CO Hsp.
  eapply (uwt_of_chain m sp top pc0 spE); [exact P0| exact CC| exact CO| lia| lia|]. split; [reflexivity| lia].
Qed.

(* [comment removed for export] *)
Lemma hop1_ok_intro : forall sp0 sp, ASTACK_BOTTOM sp0 < sp -> sp + 16 < ASTACK_TOP sp0 -> sp mod 8 = 0 -> hop1_ok sp0 sp = true.
Proof.
  intros sp0 sp H1 H2 H3. unfold hop1_ok.
  rewrite (proj2 (Z.ltb_lt _ _) H1), (proj2 (Z.ltb_lt _ _) H2), (proj2 (Z.eqb_eq _ _) H3). reflexivity.
Qed.

Lemma art_malloc_ok (AI : art_iface) :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (mo : Model) (g : lghost)
         (sp0 SPB : Z) (LB : list cblock) (LF : list fframe) (TRS : list (list Z)) (B : Z)
         (n lo : Z) (errv : word) (tl : list Z),
  ART AI sp0 SPB LB LF TRS B m mo g ->
  bv_unsigned sp <= SPB ->
  stk bsegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - AMALLOC_STACK ->
  rw_cells bsegs m AERRNO [C4 errv] ->
  mem_inv bsegs m ->
  tp = wz ATP ->
  a0 = wz n -> 0 <= n < 2^32 ->
  cost_malloc n <= B ->
  4096 <= bv_unsigned ra /\ bv_unsigned ra <> PC0_MALLOC ->   (* [comment removed for export] *)
  uwt m (bv_unsigned sp) (ASTACK_TOP sp0) PC0_MALLOC (bv_unsigned sp) (bv_unsigned s0) 2 tl ->
  trs_room (PC0_MALLOC :: bv_unsigned ra :: tl) TRS ->
  ASTACK_BOTTOM sp0 < bv_unsigned sp -> bv_unsigned sp + 16 < ASTACK_TOP sp0 -> bv_unsigned sp mod 8 = 0 ->
  LSCPS bsegs (amalloc_post (ART AI) ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc sp0 SPB LB LF TRS B
                            (PC0_MALLOC :: bv_unsigned ra :: tl) n lo m g)
       (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
           F (wz AMALLOC) fc None m (seg_rom bsegs)) mo g.
Proof.
  intros. rewrite <- (hook_tr_ok PC0_MALLOC sp0 (bv_unsigned sp) (bv_unsigned ra) tl) in * by (apply hop1_ok_intro; assumption).
  eapply (art_malloc AI); eassumption.
Qed.

Lemma art_free_ok (AI : art_iface) :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (mo : Model) (g : lghost)
         (sp0 SPB : Z) (LB : list cblock) (LF : list fframe) (TRS : list (list Z)) (B : Z)
         (A n lo : Z) (errv : word) (tl : list Z),
  ART AI sp0 SPB LB LF TRS B m mo g -> In (A, n) LB ->
  bv_unsigned sp <= SPB ->
  stk bsegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - AMALLOC_STACK ->
  rw_cells bsegs m AERRNO [C4 errv] ->
  mem_inv bsegs m ->
  tp = wz ATP ->
  a0 = wz A ->
  cost_free <= B ->
  4096 <= bv_unsigned ra /\ bv_unsigned ra <> PC0_FREE ->   (* [comment removed for export] *)
  uwt m (bv_unsigned sp) (ASTACK_TOP sp0) PC0_FREE (bv_unsigned sp) (bv_unsigned s0) 2 tl ->
  trs_room (PC0_FREE :: bv_unsigned ra :: tl) TRS ->
  ASTACK_BOTTOM sp0 < bv_unsigned sp -> bv_unsigned sp + 16 < ASTACK_TOP sp0 -> bv_unsigned sp mod 8 = 0 ->
  LSCPS bsegs (afree_post (ART AI) ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc sp0 SPB LB LF TRS B
                          (PC0_FREE :: bv_unsigned ra :: tl) A lo errv m g)
       (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
           F (wz AFREE) fc None m (seg_rom bsegs)) mo g.
Proof.
  intros. rewrite <- (hook_tr_ok PC0_FREE sp0 (bv_unsigned sp) (bv_unsigned ra) tl) in * by (apply hop1_ok_intro; assumption).
  eapply (art_free AI); eassumption.
Qed.

Lemma art_realloc_ok (AI : art_iface) :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (mo : Model) (g : lghost)
         (sp0 SPB : Z) (LB : list cblock) (LF : list fframe) (TRS : list (list Z)) (B : Z)
         (A k n lo : Z) (old : list byte) (errv : word) (tl : list Z),
  ART AI sp0 SPB LB LF TRS B m mo g -> In (A, k) LB -> bytes_at bsegs m A old -> Z.of_nat (length old) = k ->
  bv_unsigned sp <= SPB ->
  stk bsegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - AMALLOC_STACK ->
  rw_cells bsegs m AERRNO [C4 errv] ->
  mem_inv bsegs m ->
  tp = wz ATP ->
  a0 = wz A -> a1 = wz n -> 0 < n < 2^32 ->
  cost_realloc n <= B ->
  4096 <= bv_unsigned ra /\ bv_unsigned ra <> PC0_REALLOC ->   (* [comment removed for export] *)
  uwt m (bv_unsigned sp) (ASTACK_TOP sp0) PC0_REALLOC (bv_unsigned sp) (bv_unsigned s0) 2 tl ->
  trs_room (PC0_REALLOC :: bv_unsigned ra :: tl) TRS ->
  ASTACK_BOTTOM sp0 < bv_unsigned sp -> bv_unsigned sp + 16 < ASTACK_TOP sp0 -> bv_unsigned sp mod 8 = 0 ->
  LSCPS bsegs (arealloc_post (ART AI) ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc sp0 SPB LB LF TRS B
                             (PC0_REALLOC :: bv_unsigned ra :: tl) A k n lo old m g)
       (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
           F (wz AREALLOC) fc None m (seg_rom bsegs)) mo g.
Proof.
  intros. rewrite <- (hook_tr_ok PC0_REALLOC sp0 (bv_unsigned sp) (bv_unsigned ra) tl) in * by (apply hop1_ok_intro; assumption).
  eapply (art_realloc AI); eassumption.
Qed.

Lemma art_realloc_null_ok (AI : art_iface) :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (mo : Model) (g : lghost)
         (sp0 SPB : Z) (LB : list cblock) (LF : list fframe) (TRS : list (list Z)) (B : Z)
         (n lo : Z) (errv : word) (tl : list Z),
  ART AI sp0 SPB LB LF TRS B m mo g ->
  bv_unsigned sp <= SPB ->
  stk bsegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - AMALLOC_STACK ->
  rw_cells bsegs m AERRNO [C4 errv] ->
  mem_inv bsegs m ->
  tp = wz ATP ->
  a0 = wz 0 -> a1 = wz n -> 0 <= n < 2^32 ->
  cost_malloc n <= B ->
  4096 <= bv_unsigned ra /\ bv_unsigned ra <> PC0_REALLOC ->   (* [comment removed for export] *)
  uwt m (bv_unsigned sp) (ASTACK_TOP sp0) PC0_REALLOC (bv_unsigned sp) (bv_unsigned s0) 2 tl ->
  trs_room (PC0_REALLOC :: bv_unsigned ra :: tl) TRS ->
  ASTACK_BOTTOM sp0 < bv_unsigned sp -> bv_unsigned sp + 16 < ASTACK_TOP sp0 -> bv_unsigned sp mod 8 = 0 ->
  LSCPS bsegs (amalloc_post (ART AI) ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc sp0 SPB LB LF TRS B
                            (PC0_REALLOC :: bv_unsigned ra :: tl) n lo m g)
       (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
           F (wz AREALLOC) fc None m (seg_rom bsegs)) mo g.
Proof.
  intros. rewrite <- (hook_tr_ok PC0_REALLOC sp0 (bv_unsigned sp) (bv_unsigned ra) tl) in * by (apply hop1_ok_intro; assumption).
  eapply (art_realloc_null AI); eassumption.
Qed.

(* [comment removed for export] *)
Lemma chain_ok_cons : forall fl spE ra s0v CH top,
  fl <= spE -> spE mod 8 = 0 -> spE + 16 < top -> 4096 <= ra < 2^64 -> ~ is_pc0 ra -> 0 <= s0v < 2^64 ->
  chain_ok spE CH top ->
  match CH with [] => s0v <= spE | (f', _, _) :: _ => f' = s0v /\ spE < f' end ->
  chain_ok fl ((spE, ra, s0v) :: CH) top.
Proof.
  intros fl spE ra s0v CH top H1 H2 H3 H4 H5 H6 CO LK. cbn. repeat (split; [assumption|]).
  eapply chain_ok_mono; [exact CO| exact H1].
Qed.

(* [comment removed for export] *)
Definition chain_link (s0v spE : Z) (CH : list (Z * Z * Z)) : Prop :=
  match CH with [] => s0v <= spE | (f, _, _) :: _ => f = s0v /\ spE < f end.

(* [comment removed for export] *)
Lemma hook_trace_fp : forall pc0 site spE ra s0v CH,
  pc0 :: site :: chain_trace 2 ((spE, ra, s0v) :: CH) = trunc30 (pc0 :: site :: ra :: map fr_ra CH).
Proof. intros. unfold chain_trace, trunc30. reflexivity. Qed.

(* [comment removed for export] *)
Fixpoint self_chain (rs : Z) (frames : list (Z * Z)) (tail : list (Z * Z * Z)) : list (Z * Z * Z) :=
  match frames with [] => tail | (f, s) :: fr' => (f, rs, s) :: self_chain rs fr' tail end.

Lemma map_fr_ra_self_chain : forall rs frames tail,
  map fr_ra (self_chain rs frames tail) = repeat rs (length frames) ++ map fr_ra tail.
Proof. intros rs frames tail. induction frames as [|[f s] fr IH]; [reflexivity|]. cbn. f_equal. exact IH. Qed.

(* [comment removed for export] *)
Lemma chain_cells_ext : forall m m' fl ch top,
  chain_cells m ch -> chain_ok fl ch top ->
  (forall a, fl - 16 <= a < top -> m' (wa a) = m (wa a)) -> chain_cells m' ch.
Proof.
  intros m m' fl ch. induction ch as [|[[f r] s] ch IH]; intros top CC CO E; [exact I|]. cbn in CC, CO |- *.
  destruct CC as [BY CC]. destruct CO as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8). split.
  - destruct BY as (B0 & B1 & B2). split; [exact B0|]. split; [exact B1|]. intros i Hi.
    rewrite <- (B2 i Hi). unfold mrd. rewrite E; [reflexivity|].
    assert (Hi16 : (i < 16)%nat) by (clear -Hi; first [rewrite length_app, !length_le8 in Hi | idtac]; cbn in Hi; lia). lia.
  - eapply IH; eauto.
Qed.

Lemma chain_cells_munch : forall W m m' fl ch top,
  chain_cells m ch -> chain_ok fl ch top -> munch W m m' -> 16 <= fl -> top <= 2^64 ->
  (forall lo hi, In (lo, hi) W -> hi <= fl - 16 \/ top <= lo) -> chain_cells m' ch.
Proof.
  intros W m m' fl ch top CC CO MU Hfl Htop HW. eapply chain_cells_ext; [exact CC| exact CO|].
  intros a Ha. apply MU. rewrite wa_unsigned by lia.
  clear -HW Ha. induction W as [|[lo hi] W IH]; [exact I|]. cbn. split.
  - destruct (HW lo hi ltac:(left; reflexivity)); lia.
  - apply IH. intros lo' hi' Hin. apply HW. right. exact Hin.
Qed.

Lemma ASTACK_TOP_le : forall sp0, sp0 - 0xa0 <= ASTACK_TOP sp0 <= sp0 - 0xa0 + 4095.
Proof. intros sp0. unfold ASTACK_TOP, roundup. Z.div_mod_to_equations. lia. Qed.

(* [comment removed for export] *)
Lemma chain_cells_cj_pres : forall sp0 LB LF SP m m' fl ch,
  chain_cells m ch -> chain_ok fl ch (ASTACK_TOP sp0) -> cj_pres sp0 LB LF SP m m' ->
  0 <= SP -> SP + 16 <= fl -> sp0 + 4096 <= 2^64 -> chain_cells m' ch.
Proof.
  intros sp0 LB LF SP m m' fl ch CC CO PR HSP Hfl Hsp0. pose proof (ASTACK_TOP_le sp0).
  eapply chain_cells_ext; [exact CC| exact CO|]. intros a Ha.
  destruct (PR a ltac:(lia) ltac:(left; lia)) as [E _]. exact E.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Record trs_iface : Type := mkTI {
  TINV : Z -> list (list Z) -> Prop;        (* [comment removed for export] *)
  STAT : list Z -> Prop;                    (* [comment removed for export] *)
  NPMAX : Z;                                (* [comment removed for export] *)
  tinv_room : forall np TRS tr, TINV np TRS -> STAT tr -> trs_room tr TRS;
  tinv_put : forall np TRS TRS' tr, TINV np TRS -> STAT tr -> trs_put tr TRS TRS' -> TINV np TRS';
  tinv_room_paid : forall np TRS tr, TINV np TRS -> np < NPMAX -> trs_room tr TRS;
  tinv_put_paid : forall np TRS TRS' tr, TINV np TRS -> np < NPMAX -> trs_put tr TRS TRS' -> TINV (np + 1) TRS';
  tinv_mono : forall np np' TRS, TINV np TRS -> np <= np' -> TINV np' TRS;
  tinv_same : forall np TRS TRS' tr, TINV np TRS -> In tr TRS -> trs_put tr TRS TRS' -> TRS' = TRS
}.

(* [comment removed for export] *)
Lemma tinv_after_put : forall (TI : trs_iface) np TRS TRS' tr,
  TINV TI np TRS -> STAT TI tr -> trs_put tr TRS TRS' -> TINV TI np TRS'.
Proof. intros. eapply tinv_put; eauto. Qed.

(* [comment removed for export] *)
Lemma tinv_put_or : forall (TI : trs_iface) np TRS TRS' tr,
  TINV TI np TRS -> STAT TI tr -> (trs_put tr TRS TRS' \/ TRS' = TRS) -> TINV TI np TRS'.
Proof. intros TI np TRS TRS' tr TV ST [P| ->]; [eapply tinv_put; eauto| exact TV]. Qed.

Lemma tinv_put_paid_or : forall (TI : trs_iface) np TRS TRS' tr,
  TINV TI np TRS -> np < NPMAX TI -> (trs_put tr TRS TRS' \/ TRS' = TRS) -> TINV TI (np + 1) TRS'.
Proof.
  intros TI np TRS TRS' tr TV NP [P| ->]; [eapply tinv_put_paid; eauto|].
  eapply tinv_mono; [exact TV| lia].
Qed.

(* [comment removed for export] *)
Section MkTinv.
  Variable S : list (list Z).        (* [comment removed for export] *)
  Variable NP : Z.
  Hypothesis HK : Z.of_nat (length S) + NP + 1 <= DEPOT_KMAX.
  Hypothesis HNP : 0 <= NP.

  Definition tr_eq_dec : forall x y : list Z, {x = y} + {x <> y} := list_eq_dec Z.eq_dec.
  Definition nonstatic (tr : list Z) : bool := if in_dec tr_eq_dec tr S then false else true.
  Definition npaid (TRS : list (list Z)) : Z := Z.of_nat (length (List.filter nonstatic TRS)).

  Definition tinv_inst (np : Z) (TRS : list (list Z)) : Prop := NoDup TRS /\ 0 <= np /\ npaid TRS <= np.

  Lemma filter_static_incl : forall TRS, incl (List.filter (fun tr => negb (nonstatic tr)) TRS) S.
  Proof.
    intros TRS tr H. apply List.filter_In in H as [_ H]. unfold nonstatic in H.
    destruct (in_dec tr_eq_dec tr S); [assumption| discriminate].
  Qed.

  Lemma length_split_filter : forall (f : list Z -> bool) (l : list (list Z)),
    length l = (length (List.filter f l) + length (List.filter (fun x => negb (f x)) l))%nat.
  Proof. intros f l. induction l as [|x l IH]; [reflexivity|]. cbn. destruct (f x); cbn; lia. Qed.

  Lemma NoDup_filter' : forall (f : list Z -> bool) l, NoDup l -> NoDup (List.filter f l).
  Proof. intros f l H. rewrite NoDup_ListNoDup in *. apply List.NoDup_filter. exact H. Qed.

  Lemma tinv_inst_length : forall np TRS, tinv_inst np TRS -> Z.of_nat (length TRS) <= Z.of_nat (length S) + np.
  Proof.
    intros np TRS (ND & Hnp & HP). unfold npaid in HP.
    rewrite (length_split_filter nonstatic TRS).
    pose proof (List.NoDup_incl_length (proj1 (NoDup_ListNoDup _) (NoDup_filter' (fun tr => negb (nonstatic tr)) TRS ND))
                  (filter_static_incl TRS)) as L.
    lia.
  Qed.

  Lemma tinv_inst_room : forall np TRS tr, tinv_inst np TRS -> np <= NP -> trs_room tr TRS.
  Proof.
    intros np TRS tr H Hle. right. pose proof (tinv_inst_length np TRS H). lia.
  Qed.

  Lemma tinv_inst_put_stat : forall np TRS TRS' tr, tinv_inst np TRS -> In tr S -> trs_put tr TRS TRS' -> tinv_inst np TRS'.
  Proof.
    intros np TRS TRS' tr (ND & Hnp & HP) HS [[_ ->]|[NI ->]]; [split; [exact ND| split; [exact Hnp| exact HP]]|].
    split; [| split; [exact Hnp|]].
    - rewrite NoDup_ListNoDup in *. constructor; assumption.
    - unfold npaid in *. cbn. unfold nonstatic at 1. destruct (in_dec tr_eq_dec tr S); [exact HP| contradiction].
  Qed.

  Lemma tinv_inst_put_paid : forall np TRS TRS' tr, tinv_inst np TRS -> trs_put tr TRS TRS' -> tinv_inst (np + 1) TRS'.
  Proof.
    intros np TRS TRS' tr (ND & Hnp & HP) [[_ ->]|[NI ->]]; [split; [exact ND| split; [lia| lia]]|].
    split; [| split; [lia|]].
    - rewrite NoDup_ListNoDup in *. constructor; assumption.
    - unfold npaid in *. cbn. destruct (nonstatic tr); cbn [length]; lia.
  Qed.

  Definition tinv_full (np : Z) (TRS : list (list Z)) : Prop := tinv_inst np TRS /\ np <= NP.

  Lemma mk_tinv_room : forall np TRS tr, tinv_full np TRS -> In tr S -> trs_room tr TRS.
  Proof. intros np TRS tr [H Hle] _. eapply tinv_inst_room; eauto. Qed.
  Lemma mk_tinv_put : forall np TRS TRS' tr, tinv_full np TRS -> In tr S -> trs_put tr TRS TRS' -> tinv_full np TRS'.
  Proof. intros np TRS TRS' tr [H Hle] HS HP. split; [eapply tinv_inst_put_stat; eauto| exact Hle]. Qed.
  Lemma mk_tinv_room_paid : forall np TRS tr, tinv_full np TRS -> np < NP -> trs_room tr TRS.
  Proof. intros np TRS tr [H Hle] Hlt. eapply tinv_inst_room; eauto. Qed.
  Lemma mk_tinv_put_paid : forall np TRS TRS' tr, tinv_full np TRS -> np < NP -> trs_put tr TRS TRS' -> tinv_full (np + 1) TRS'.
  Proof. intros np TRS TRS' tr [H Hle] Hlt HP. split; [eapply tinv_inst_put_paid; eauto| lia]. Qed.
  Lemma mk_tinv_mono : forall np np' TRS, tinv_full np TRS -> np <= np' -> np' <= NP -> tinv_full np' TRS.
  Proof. intros np np' TRS [(ND & Hnp & HP) Hle] H1 H2. split; [split; [exact ND| split; lia]| exact H2]. Qed.
  Lemma mk_tinv_same : forall np TRS TRS' tr, tinv_full np TRS -> In tr TRS -> trs_put tr TRS TRS' -> TRS' = TRS.
  Proof. intros np TRS TRS' tr _ HIn [[_ E]|[NI _]]; [exact E| contradiction]. Qed.

  (* [comment removed for export] *)
  Lemma mk_tinv_init : tinv_full 0 [].
  Proof. split; [| exact HNP]. split; [constructor| split; [lia| unfold npaid; cbn; lia]]. Qed.
End MkTinv.

(* [comment removed for export] *)
Definition mk_tinv (S : list (list Z)) (NP : Z) (HK : Z.of_nat (length S) + NP + 1 <= DEPOT_KMAX) (HNP : 0 <= NP) : trs_iface :=
  mkTI (fun np TRS => tinv_full S NP np TRS \/ (tinv_inst S (Z.min np NP) TRS /\ NP < np))
       (fun tr => In tr S) NP
       ltac:(intros np TRS tr [H|[H Hlt]] HS; [eapply mk_tinv_room; eauto| eapply tinv_inst_room; eauto; lia])
       ltac:(intros np TRS TRS' tr [H|[H Hlt]] HS HP; [left; eapply mk_tinv_put; eauto| right; split; [eapply tinv_inst_put_stat; eauto| exact Hlt]])
       ltac:(intros np TRS tr [H|[H Hlt]] Hnp; [eapply mk_tinv_room_paid; eauto| exfalso; lia])
       ltac:(intros np TRS TRS' tr [H|[H Hlt]] Hnp HP; [| exfalso; lia];
             destruct (Z.lt_ge_cases (np + 1) (NP + 1)) as [L|L];
             [left; eapply mk_tinv_put_paid; eauto| left; eapply mk_tinv_put_paid; eauto])
       ltac:(intros np np' TRS [[H Hle]|[H Hlt]] Hle';
             [ destruct (Z.le_gt_cases np' NP) as [L|L];
               [left; eapply mk_tinv_mono; eauto; split; assumption
               | right; split; [replace (Z.min np' NP) with NP by lia; destruct H as (ND & Hnp & HP); split; [exact ND| split; lia]| lia]]
             | right; split; [replace (Z.min np' NP) with (Z.min np NP) by lia; exact H| lia]])
       ltac:(intros np TRS TRS' tr _ HIn [[_ E]|[NI _]]; [exact E| contradiction]).

Lemma mk_tinv_STAT : forall S NP HK HNP tr, STAT (mk_tinv S NP HK HNP) tr <-> In tr S.
Proof. intros. reflexivity. Qed.

Lemma mk_tinv_TINV_init : forall S NP HK HNP, TINV (mk_tinv S NP HK HNP) 0 [].
Proof. intros. left. apply mk_tinv_init. exact HNP. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma rz_size_cases : forall n,
  rz_size n = 16 \/ rz_size n = 32 \/ rz_size n = 64 \/ rz_size n = 128 \/ rz_size n = 256 \/ rz_size n = 512
  \/ rz_size n = 1024 \/ rz_size n = 2048.
Proof. intros n. unfold rz_size, rz_log. repeat (destruct (_ <=? _)); cbv; tauto. Qed.

Lemma rz_size_le : forall n, 0 <= n -> rz_size n <= n / 2 + 16 /\ 16 <= rz_size n <= 2048.
Proof.
  intros n Hn. unfold rz_size, rz_log.
  repeat (lazymatch goal with |- context [if ?c then _ else _] => destruct c eqn:?; [|] end);
  repeat match goal with H : (_ <=? _) = true |- _ => apply Z.leb_le in H | H : (_ <=? _) = false |- _ => apply Z.leb_gt in H end;
  cbv [Z.shiftl Pos.iter Z.mul Pos.mul]; Z.div_mod_to_equations; lia.
Qed.

Lemma rounded8_le : forall n, 0 <= n -> Z.max n 8 <= rounded8 n <= Z.max n 8 + 7.
Proof. intros n Hn. unfold rounded8, roundup. Z.div_mod_to_equations. lia. Qed.

Lemma needed0_le : forall n, 0 <= n -> n + 16 <= needed0 n <= Z.max n 8 + 7 + rz_size n.
Proof. intros n Hn. unfold needed0. pose proof (rounded8_le n Hn). pose proof (rz_size_le n Hn). lia. Qed.

Lemma rz_size_small : forall n, n <= 64512 -> rz_size n <= 1024.
Proof.
  intros n Hn. unfold rz_size, rz_log.
  repeat (lazymatch goal with |- context [if ?c then _ else _] => destruct c eqn:?; [|] end);
  repeat match goal with H : (_ <=? _) = true |- _ => apply Z.leb_le in H | H : (_ <=? _) = false |- _ => apply Z.leb_gt in H end;
  cbv [Z.shiftl Pos.iter Z.mul Pos.mul]; lia.
Qed.

Lemma rounded8_small : forall n, 0 <= n <= 64512 -> rounded8 n <= 64512.
Proof. intros n Hn. unfold rounded8, roundup. Z.div_mod_to_equations. lia. Qed.

(* [comment removed for export] *)
Lemma is_primary_bound : forall n, 0 <= n -> is_primary n = true -> n <= 64512.
Proof.
  intros n Hn H. unfold is_primary, KMAXSIZE in H. apply Z.leb_le in H.
  destruct (Z.le_gt_cases n 64512) as [L|L]; [exact L|]. exfalso.
  unfold needed0, rz_size, rz_log in H.
  repeat (lazymatch type of H with context [if ?c then _ else _] => destruct c eqn:?; [|] end);
  repeat match goal with K : (_ <=? _) = true |- _ => apply Z.leb_le in K | K : (_ <=? _) = false |- _ => apply Z.leb_gt in K end;
  try lia.
  cbv [Z.shiftl Pos.iter Z.mul Pos.mul] in H. pose proof (rounded8_le n Hn). lia.
Qed.

(* [comment removed for export] *)
Fixpoint zcheck_upto (f : Z -> bool) (fuel : nat) (z : Z) : bool :=
  match fuel with O => true | S k => f z && zcheck_upto f k (z + 1) end.
Lemma zcheck_upto_sound : forall f fuel z, zcheck_upto f fuel z = true ->
  forall x, z <= x < z + Z.of_nat fuel -> f x = true.
Proof.
  induction fuel as [|k IH]; intros z H x Hx; [lia|]. cbn in H. apply andb_true_iff in H as [H1 H2].
  destruct (Z.eq_dec x z) as [->|NE]; [exact H1|]. apply (IH (z + 1) H2). lia.
Qed.
Definition pslot_ok_b (n : Z) : bool := (pslot n <=? 2 * n + 32) && (pslot n <=? n + 17408) && (32 <=? pslot n).
Lemma pslot_ok_all : zcheck_upto pslot_ok_b 64513 0 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma pslot_ok : forall n, 0 <= n <= 64512 -> pslot n <= 2 * n + 32 /\ pslot n <= n + 17408 /\ 32 <= pslot n.
Proof.
  intros n Hn. pose proof (zcheck_upto_sound _ _ _ pslot_ok_all n) as H.
  change (Z.of_nat 64513) with 64513%Z in H. specialize (H ltac:(lia)).
  unfold pslot_ok_b in H. apply andb_true_iff in H as [H H3]. apply andb_true_iff in H as [H1 H2].
  apply Z.leb_le in H1. apply Z.leb_le in H2. apply Z.leb_le in H3. lia.
Qed.

Lemma smapsize_le : forall n, 0 <= n -> smapsize n <= n + 12296.
Proof.
  intros n Hn. unfold smapsize, needed. pose proof (needed0_le n Hn). pose proof (rz_size_le n Hn).
  destruct (is_primary n); unfold roundup; Z.div_mod_to_equations; lia.
Qed.

Lemma asz_le : forall n, 0 <= n -> asz n <= 2 * n + 32 /\ asz n <= n + 17408 /\ 32 <= asz n.
Proof.
  intros n Hn. unfold asz. destruct (is_primary n) eqn:E.
  - apply pslot_ok. split; [exact Hn| apply is_primary_bound; assumption].
  - pose proof (smapsize_le n Hn).
    assert (64512 < n).
    { destruct (Z.le_gt_cases n 64512) as [L|L]; [|exact L]. exfalso.
      unfold is_primary, KMAXSIZE in E. apply Z.leb_gt in E. unfold needed0 in E.
      pose proof (rz_size_small n ltac:(lia)). pose proof (rounded8_small n ltac:(lia)). lia. }
    unfold smapsize, roundup in *. pose proof (needed0_le n Hn). unfold needed in *. rewrite E in *.
    pose proof (rz_size_le n Hn). Z.div_mod_to_equations. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma is_primary_small : forall n, 0 <= n <= 64512 -> is_primary n = true.
Proof.
  intros n Hn. unfold is_primary, KMAXSIZE. apply Z.leb_le. unfold needed0.
  pose proof (rz_size_small n ltac:(lia)). pose proof (rounded8_small n ltac:(lia)). lia.
Qed.

Lemma cost_malloc_le8 : forall n, 0 <= n -> cost_malloc n <= 8 * n + 192 + 2^19 + CL24_TAX.
Proof. intros n Hn. unfold cost_malloc, SEC_SLOT_TAX, CL24_TAX. pose proof (asz_le n Hn). destruct (is_primary n); destruct (is_cl24 n); lia. Qed.

Lemma cost_malloc_le4 : forall n, 0 <= n -> cost_malloc n <= 4 * n + 69696 + 2^19 + CL24_TAX.
Proof. intros n Hn. unfold cost_malloc, SEC_SLOT_TAX, CL24_TAX. pose proof (asz_le n Hn). destruct (is_primary n); destruct (is_cl24 n); lia. Qed.

Lemma cost_malloc_le8_prim : forall n, 0 <= n <= 64512 -> cost_malloc n <= 8 * n + 192 + CL24_TAX.
Proof. intros n Hn. unfold cost_malloc, CL24_TAX. rewrite (is_primary_small n Hn). pose proof (asz_le n ltac:(lia)). destruct (is_cl24 n); lia. Qed.

Lemma cost_malloc_le4_prim : forall n, 0 <= n <= 64512 -> cost_malloc n <= 4 * n + 69696 + CL24_TAX.
Proof. intros n Hn. unfold cost_malloc, CL24_TAX. rewrite (is_primary_small n Hn). pose proof (asz_le n ltac:(lia)). destruct (is_cl24 n); lia. Qed.

(* [comment removed for export] *)
Lemma cost_malloc_le13 : forall n, 0 <= n -> cost_malloc n <= 13 * n + 192 + CL24_TAX.
Proof.
  intros n Hn. unfold cost_malloc, SEC_SLOT_TAX, CL24_TAX, asz. destruct (is_cl24 n); destruct (is_primary n) eqn:E.
  1,3: pose proof (pslot_ok n ltac:(split; [exact Hn| apply is_primary_bound; assumption])); lia.
  all: pose proof (smapsize_le n Hn);
    assert (64512 < n) by
     (destruct (Z.le_gt_cases n 64512) as [L|L]; [|exact L]; exfalso;
      unfold is_primary, KMAXSIZE in E; apply Z.leb_gt in E; unfold needed0 in E;
      pose proof (rz_size_small n ltac:(lia)); pose proof (rounded8_small n ltac:(lia)); lia);
    lia.
Qed.

Lemma cost_malloc_bound13 : forall n L, 0 <= n <= L -> cost_malloc n <= 13 * L + 192 + CL24_TAX.
Proof. intros n L H. pose proof (cost_malloc_le13 n ltac:(lia)). unfold CL24_TAX in *. lia. Qed.

Lemma cost_malloc_64 : cost_malloc 64 = 448.
Proof. vm_compute. reflexivity. Qed.

Lemma cost_malloc_pos : forall n, 0 <= n -> 192 <= cost_malloc n.
Proof. intros n Hn. unfold cost_malloc, SEC_SLOT_TAX, CL24_TAX. pose proof (asz_le n Hn). destruct (is_primary n); destruct (is_cl24 n); lia. Qed.

Lemma cost_free_eq : cost_free = 64.
Proof. reflexivity. Qed.

Lemma cost_realloc_eq : forall n, cost_realloc n = cost_malloc n + 64.
Proof. intros n. reflexivity. Qed.

(* [comment removed for export] *)
Lemma cost_malloc_bound8 : forall n L, 0 <= n <= L -> cost_malloc n <= 8 * L + 192 + 2^19 + CL24_TAX.
Proof. intros n L H. pose proof (cost_malloc_le8 n ltac:(lia)). unfold CL24_TAX in *. lia. Qed.

Lemma cost_malloc_bound4 : forall n L, 0 <= n <= L -> cost_malloc n <= 4 * L + 69696 + 2^19 + CL24_TAX.
Proof. intros n L H. pose proof (cost_malloc_le4 n ltac:(lia)). unfold CL24_TAX in *. lia. Qed.

Lemma cost_malloc_bound8_prim : forall n L, 0 <= n <= L -> L <= 64512 -> cost_malloc n <= 8 * L + 192 + CL24_TAX.
Proof. intros n L H HL. pose proof (cost_malloc_le8_prim n ltac:(lia)). unfold CL24_TAX in *. lia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition lf_room (k : Z) (LF : list fframe) (d : Z) : Prop := lf_count k LF + d <= fcap k.

Lemma fcap_vals : fcap 1 = 8192 /\ fcap 2 = 4096 /\ fsz 1 = 128 /\ fsz 2 = 256.
Proof. repeat split; reflexivity. Qed.

Lemma lf_count_nonneg : forall k LF, 0 <= lf_count k LF.
Proof. intros k LF. induction LF as [|[F k'] LF IH]; cbn; [lia|]. destruct (k' =? k); lia. Qed.

Lemma lf_room_alloc : forall k LF d, lf_room k LF d -> 1 <= d -> lf_count k LF < fcap k.
Proof. intros k LF d H Hd. unfold lf_room in H. lia. Qed.

Lemma lf_room_push : forall k LF d F, lf_room k LF d -> 1 <= d -> lf_room k ((F, k) :: LF) (d - 1).
Proof. intros k LF d F H Hd. unfold lf_room in *. cbn. rewrite Z.eqb_refl. lia. Qed.

Lemma lf_room_other : forall k k' LF d F, lf_room k LF d -> k' <> k -> lf_room k ((F, k') :: LF) d.
Proof. intros k k' LF d F H NE. unfold lf_room in *. cbn. destruct (Z.eqb_spec k' k); [lia| lia]. Qed.

Lemma lf_count_remove_le : forall k F LF, lf_count k (lf_remove F LF) <= lf_count k LF.
Proof.
  intros k F LF. induction LF as [|[G k'] LF IH]; cbn; [lia|].
  destruct (G =? F); cbn; [pose proof (lf_count_nonneg k LF); destruct (k' =? k); lia|]. destruct (k' =? k); lia.
Qed.

Lemma lf_room_remove : forall k LF d F, lf_room k LF d -> lf_room k (lf_remove F LF) d.
Proof. intros k LF d F H. unfold lf_room in *. pose proof (lf_count_remove_le k F LF). lia. Qed.

Lemma lf_room_mono : forall k LF d d', lf_room k LF d -> d' <= d -> lf_room k LF d'.
Proof. intros. unfold lf_room in *. lia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition stack_sh_zero (m : word -> option byte) (sp0 SP : Z) : Prop := sh_zero m (ASTACK_BOTTOM sp0) SP.

Lemma stack_sh_zero_lower : forall m sp0 SP SP', stack_sh_zero m sp0 SP -> SP' <= SP -> stack_sh_zero m sp0 SP'.
Proof. intros m sp0 SP SP' H Hle a Ha. apply H. lia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma in_map_fst_pair : forall (A n : Z) (L : list (Z * Z)), In (A, n) L -> In A (map fst L).
Proof. intros A n L H. apply (in_map fst) in H. exact H. Qed.


End CeilWrap.
(* [comment removed for export] *)
Notation frec := (Z * Z * Z)%type (only parsing).
Notation fchain := (list (Z * Z * Z)) (only parsing).
