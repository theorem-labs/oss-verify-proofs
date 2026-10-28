(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Arr ZBridge CellsX TacX.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import N8Store.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_n8 segs m a bs.   (* [comment removed for export] *)
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition UNWINDFAST : Z := 0x1e1b08.
Definition UF_LOOP    : Z := 0x1e1bc8.
Definition UF_EXIT    : Z := 0x1e1c04.
Definition UNWIND     : Z := 0x1e2164.
Definition UNWINDIMPL : Z := 0x1c7740.
Definition GOT_PAGESIZECACHED : Z := 0x5e77f8.   (* [comment removed for export] *)
Definition KPAGE : Z := 4096.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition goodframe (lo v top : Z) : bool :=
  (lo <? v) && (v <? top - 16) && (v mod 8 =? 0).

(* [comment removed for export] *)
Fixpoint uloop (pc0 md : Z) (CH : list (Z * Z)) (acc : list Z) {struct CH} : list Z :=
  match CH with
  | [] => acc
  | (ra, v) :: rest =>
      if md <=? Z.of_nat (length acc) then acc
      else if ra <? KPAGE then acc
      else let acc' := if ra =? pc0 then acc else acc ++ [ra] in
           match rest with
           | [] => acc'                      (* [comment removed for export] *)
           | _ => uloop pc0 md rest acc'
           end
  end.

Definition utrace (pc0 bp top bot md : Z) (CH : list (Z * Z)) : list Z :=
  if top <? KPAGE then [pc0]
  else if goodframe bot bp top then uloop pc0 md CH [pc0] else [pc0].

(* [comment removed for export] *)
Section WithSegs.
Variable segs : list Segment.

Inductive frame_chain (m : word -> option byte) (top : Z) : Z -> list (Z * Z) -> Prop :=
| fc_last : forall f ra v,
    rw_cells segs m (f + -16) [C8 (wz v); C8 (wz ra)] ->
    0 <= ra < 2^64 -> 0 <= v < 2^64 ->
    goodframe f v top = false ->
    frame_chain m top f [(ra, v)]
| fc_link : forall f ra v rest,
    rw_cells segs m (f + -16) [C8 (wz v); C8 (wz ra)] ->
    0 <= ra < 2^64 -> 0 <= v < 2^64 ->
    goodframe f v top = true ->
    frame_chain m top v rest ->
    frame_chain m top f ((ra, v) :: rest).

Lemma frame_chain_nonnil : forall m top f CH, frame_chain m top f CH -> CH <> [].
Proof. intros m top f CH H; inversion H; congruence. Qed.

(* [comment removed for export] *)
Definition below (W : list ivl) (b : Z) : Prop := forall lo hi, In (lo, hi) W -> hi <= b.

Lemma below_disjoint : forall W b A n, below W b -> b <= A -> disjoint_from W A n.
Proof.
  induction W as [|[lo hi] W IH]; intros b A n HB HA; cbn; [exact I|].
  split. { right. specialize (HB lo hi (or_introl eq_refl)). lia. }
  apply (IH b); [|exact HA]. intros lo' hi' Hin. apply (HB lo' hi'). right. exact Hin.
Qed.

Lemma below_le : forall W b b', below W b -> b <= b' -> below W b'.
Proof. intros W b b' HB L lo hi Hin. specialize (HB lo hi Hin). lia. Qed.

(* [comment removed for export] *)
Lemma frame_chain_transport : forall W m m' top f CH,
  frame_chain m top f CH -> below W (f - 16) ->
  munch W m m' -> wmono segs m m' ->
  frame_chain m' top f CH.
Proof.
  intros W m m' top f CH H. induction H as [f ra v C R V G|f ra v rest C R V G H IH]; intros HB MU WM.
  - apply fc_last; try assumption. eapply rw_cells_transport; [exact C|exact MU|exact WM|].
    apply (below_disjoint W (f - 16)); [exact HB|lia].
  - apply fc_link; try assumption.
    + eapply rw_cells_transport; [exact C|exact MU|exact WM|]. apply (below_disjoint W (f - 16)); [exact HB|lia].
    + apply IH; try assumption. apply (below_le W (f - 16)); [exact HB|].
      unfold goodframe in G. apply andb_prop in G. destruct G as [G _]. apply andb_prop in G. destruct G as [G1 _].
      apply Z.ltb_lt in G1. lia.
Qed.

Lemma uloop_length_le : forall pc0 md CH acc,
  (Z.of_nat (length acc) <= md) -> Z.of_nat (length (uloop pc0 md CH acc)) <= Z.max md (Z.of_nat (length acc)) + 0
  /\ (length acc <= length (uloop pc0 md CH acc))%nat.
Proof.
  intros pc0 md CH. induction CH as [|[ra v] rest IH]; intros acc Hle; cbn [uloop].
  - lia.
  - destruct (Z.leb_spec md (Z.of_nat (length acc))); [lia|].
    destruct (Z.ltb_spec ra KPAGE); [lia|].
    set (acc' := if ra =? pc0 then acc else acc ++ [ra]).
    assert (L' : (length acc <= length acc')%nat /\ Z.of_nat (length acc') <= md).
    { subst acc'. destruct (ra =? pc0); [split; [lia|lia]|]. rewrite length_app. cbn. lia. }
    destruct rest as [|x rest'].
    + lia.
    + specialize (IH acc' (proj2 L')). lia.
Qed.

Lemma uloop_prefix : forall pc0 md CH acc, exists tl, uloop pc0 md CH acc = acc ++ tl.
Proof.
  intros pc0 md CH. induction CH as [|[ra v] rest IH]; intros acc; cbn [uloop].
  - exists []. rewrite app_nil_r. reflexivity.
  - destruct (md <=? Z.of_nat (length acc)). { exists []; rewrite app_nil_r; reflexivity. }
    destruct (ra <? KPAGE). { exists []; rewrite app_nil_r; reflexivity. }
    destruct rest as [|x rest'].
    + destruct (ra =? pc0). { exists []; rewrite app_nil_r; reflexivity. } { exists [ra]. reflexivity. }
    + destruct (ra =? pc0).
      * apply IH.
      * destruct (IH (acc ++ [ra])) as [tl E]. exists (ra :: tl). rewrite E, <- app_assoc. reflexivity.
Qed.

End WithSegs.


(* [comment removed for export] *)
Lemma uloop_cut : forall pc0 md ra v rest acc,
  md <= Z.of_nat (length acc) -> uloop pc0 md ((ra, v) :: rest) acc = acc.
Proof. intros. cbn [uloop]. destruct (Z.leb_spec md (Z.of_nat (length acc))); [|lia]. destruct rest; reflexivity. Qed.

Lemma uloop_page : forall pc0 md ra v rest acc,
  Z.of_nat (length acc) < md -> ra < KPAGE -> uloop pc0 md ((ra, v) :: rest) acc = acc.
Proof.
  intros. cbn [uloop]. destruct (Z.leb_spec md (Z.of_nat (length acc))); [lia|].
  destruct (Z.ltb_spec ra KPAGE); [|lia]. destruct rest; reflexivity.
Qed.

Definition upush (pc0 ra : Z) (acc : list Z) : list Z := if ra =? pc0 then acc else acc ++ [ra].

Lemma uloop_last : forall pc0 md ra v acc,
  Z.of_nat (length acc) < md -> KPAGE <= ra -> uloop pc0 md [(ra, v)] acc = upush pc0 ra acc.
Proof.
  intros. cbn [uloop]. destruct (Z.leb_spec md (Z.of_nat (length acc))); [lia|].
  destruct (Z.ltb_spec ra KPAGE); [lia|]. reflexivity.
Qed.

Lemma uloop_link : forall pc0 md ra v x rest acc,
  Z.of_nat (length acc) < md -> KPAGE <= ra ->
  uloop pc0 md ((ra, v) :: x :: rest) acc = uloop pc0 md (x :: rest) (upush pc0 ra acc).
Proof.
  intros. cbn [uloop]. destruct (Z.leb_spec md (Z.of_nat (length acc))); [lia|].
  destruct (Z.ltb_spec ra KPAGE); [lia|]. reflexivity.
Qed.

Lemma upush_length : forall pc0 ra acc, (length acc <= length (upush pc0 ra acc) <= S (length acc))%nat.
Proof. intros. unfold upush. destruct (ra =? pc0); [lia|]. rewrite length_app; cbn; lia. Qed.

Lemma upush_range : forall pc0 ra acc, (forall x, In x acc -> 0 <= x < 2^64) -> 0 <= ra < 2^64 ->
  forall x, In x (upush pc0 ra acc) -> 0 <= x < 2^64.
Proof.
  intros pc0 ra acc H Hra x Hin. unfold upush in Hin. destruct (ra =? pc0); [auto|].
  apply in_app_or in Hin. destruct Hin as [Hin|[<-|[]]]; auto.
Qed.

Lemma upd_app_r : forall {X} (l1 l2 : list X) i x, (length l1 <= i)%nat -> upd (l1 ++ l2) i x = l1 ++ upd l2 (i - length l1) x.
Proof.
  induction l1 as [|y l1 IH]; intros l2 i x Hi; cbn. { rewrite Nat.sub_0_r. reflexivity. }
  destruct i as [|i]; [cbn in Hi; lia|]. cbn. f_equal. apply IH. cbn in Hi. lia.
Qed.

Lemma skipn_cons_nth : forall {X} (l : list X) n, (n < length l)%nat -> exists y, skipn n l = y :: skipn (S n) l.
Proof.
  induction l as [|z l IH]; intros n Hn; cbn in Hn; [lia|].
  destruct n as [|n]; cbn. { exists z. reflexivity. } apply IH. lia.
Qed.

Lemma buf_push : forall (acc : list Z) (buf : list word) (ra : Z),
  (length acc < length buf)%nat ->
  upd (map wz acc ++ skipn (length acc) buf) (length acc) (wz ra) = map wz (acc ++ [ra]) ++ skipn (length (acc ++ [ra])) buf.
Proof.
  intros acc buf ra Hl. rewrite upd_app_r by (rewrite length_map; lia). rewrite length_map, Nat.sub_diag.
  destruct (skipn_cons_nth buf (length acc) Hl) as [y E]. rewrite E. cbn [upd].
  rewrite map_app, <- app_assoc. cbn [map app]. rewrite length_app. cbn [length]. rewrite Nat.add_1_r. reflexivity.
Qed.


Lemma land7_mod8 : forall v, Z.land v 7 = v mod 8.
Proof. intros v. change 7 with (2^3 - 1). rewrite zb_land_mask by lia. reflexivity. Qed.

Lemma goodframe_true : forall lo v top, goodframe lo v top = true <-> (lo < v /\ v < top - 16 /\ v mod 8 = 0).
Proof.
  intros. unfold goodframe. rewrite !Bool.andb_true_iff, !Z.ltb_lt, Z.eqb_eq. tauto.
Qed.

Lemma goodframe_false : forall lo v top, goodframe lo v top = false <-> ~ (lo < v /\ v < top - 16 /\ v mod 8 = 0).
Proof.
  intros. rewrite <- goodframe_true. destruct (goodframe lo v top); split; congruence.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition uf_W (lo spv OBJ BUFN : Z) : list ivl :=
  [(lo, spv); (OBJ + 8, OBJ + 12); (OBJ + 16, OBJ + 16 + 8 * BUFN)].

Definition uf_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (OBJ BUFN lo : Z) (buf : list word) (T : list Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch (uf_W lo (bv_unsigned sp) OBJ BUFN) m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' (OBJ + 8) [C4 (wz (Z.of_nat (length T)))]
    /\ u64arr asegs m' (OBJ + 16) (map wz T ++ skipn (length T) buf)
    /\ stk asegs m' lo (bv_unsigned sp).

Section UF.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (OBJ BUFN lo PSC pc0 bp TOP BOT MD : Z) (buf : list word) (m : word -> option byte).

  Hypothesis LBUF : length buf = Z.to_nat BUFN.
  Hypothesis MDR  : 2 <= MD <= BUFN.
  Hypothesis BUFR : BUFN < 2^20.
  Hypothesis OBJR : 0 <= OBJ.
  Hypothesis PC0R : KPAGE <= pc0 < 2^64.
  Hypothesis BPR  : 0 <= bp < 2^64.
  Hypothesis TOPR : KPAGE <= TOP < 2^64.
  Hypothesis BOTR : 0 <= BOT < TOP.
  Hypothesis PSCR : 0 <= PSC /\ PSC + 8 <= lo.                (* [comment removed for export] *)
  Hypothesis IMGLO: AIMG_TOP <= lo.                             (* [comment removed for export] *)
  Hypothesis LO   : lo + 64 <= bv_unsigned sp.
  Hypothesis SPO  : bv_unsigned sp <= OBJ + 8.            (* [comment removed for export] *)
  Hypothesis OBP  : OBJ + 16 + 8 * BUFN <= bp - 16.        (* [comment removed for export] *)

  Let W := uf_W lo (bv_unsigned sp) OBJ BUFN.

  Lemma W_below : below W (bp - 16).
  Proof.
    unfold W, uf_W, below. intros l h Hin. cbn in Hin.
    destruct Hin as [E|[E|[E|[]]]]; inversion E; subst; lia.
  Qed.

  Notation POST T := (uf_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc OBJ BUFN lo buf T m).

  (* [comment removed for export] *)
  Lemma uf_exit : forall (t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 t3 t4 t5 t6 : word)
      (m1 : word -> option byte) (T : list Z),
    rw_cells asegs m1 (bv_unsigned sp + -64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    stk asegs m1 lo (bv_unsigned sp + -64) ->
    munch W m m1 -> wmono asegs m m1 -> mem_inv asegs m1 ->
    rw_cells asegs m1 (OBJ + 8) [C4 (wz (Z.of_nat (length T)))] ->
    u64arr asegs m1 (OBJ + 16) (map wz T ++ skipn (length T) buf) ->
    evt asegs (POST T)
      (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7
               x18 x19 x20 x21 x22 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 UF_EXIT) fc None m1 (seg_rom asegs)).
  Proof.
    intros until T. intros FR ST MU WM MI SZ BUF.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. change (2 ^ Z.of_N 64) with (2^64) in SPR.
    unfold UF_EXIT.
    do 8 step. release_frame FR ST (bv_unsigned sp). step. step.
    finish.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Ltac uf_exit_last CASES EQ2 :=
    let G := fresh "G" in
    destruct CASES as [[G ->]|[G ?]];
    [ rewrite uloop_last by (unfold KPAGE; lia); rewrite <- EQ2; eapply uf_exit; eassumption
    | exfalso; apply goodframe_true in G; try rewrite land7_mod8 in *; lia ].

  (* [comment removed for export] *)
  Lemma uf_loop : forall CH f (acc : list Z) (m1 : word -> option byte)
      (t0 t1 t2 a6 a7 x18 x19 x20 x21 x22 t3 t4 t5 t6 : word),
    frame_chain asegs m1 TOP f CH ->
    bp <= f -> 0 <= f < 2^64 ->
    (forall x, In x acc -> 0 <= x < 2^64) ->
    (1 <= length acc)%nat -> Z.of_nat (length acc) <= MD ->
    rw_cells asegs m1 (bv_unsigned sp + -64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    stk asegs m1 lo (bv_unsigned sp + -64) ->
    munch W m m1 -> wmono asegs m m1 -> mem_inv asegs m1 ->
    rw_cells asegs m1 (OBJ + 8) [C4 (wz (Z.of_nat (length acc)))] ->
    u64arr asegs m1 (OBJ + 16) (map wz acc ++ skipn (length acc) buf) ->
    evt asegs (POST (uloop pc0 MD CH acc))
      (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 (wz MD) (wz (TOP - 16)) (wz OBJ) (wz pc0) (wz f) (wz KPAGE)
               (wz (OBJ + 16)) (wz (Z.of_nat (length acc))) a6 a7 x18 x19 x20 x21 x22 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 UF_LOOP) fc None m1 (seg_rom asegs)).
  Proof.
    induction CH as [|[rav v] rest IH];
      intros f acc m1 t0 t1 t2 a6 a7 x18 x19 x20 x21 x22 t3 t4 t5 t6 FC BPF FR64 ACC L1 LMD FR ST MU WM MI SZ BUF.
    { exfalso. exact (frame_chain_nonnil _ _ _ _ _ FC eq_refl). }
    pose proof (bv_unsigned_in_range 64 sp) as SPR; unfold bv_modulus in SPR; change (2 ^ Z.of_N 64) with (2^64) in SPR.
    pose proof (u64arr_bound _ _ _ _ BUF) as BB; rewrite length_app, length_map, length_skipn, LBUF in BB.
    unfold UF_LOOP, KPAGE in *. unfold wz. unfold W, uf_W in MU.
    pose proof (munch_refl (uf_W lo (bv_unsigned sp) OBJ BUFN) m1) as MU1. unfold uf_W in MU1.
    pose proof (wmono_refl asegs m1) as WM1.
    (* [comment removed for export] *)
    assert (CELLS : rw_cells asegs m1 (f + -16) [C8 (Z_to_bv 64 v); C8 (Z_to_bv 64 rav)] /\ 0 <= rav < 2^64 /\ 0 <= v < 2^64
                    /\ ((goodframe f v TOP = false /\ rest = []) \/ (goodframe f v TOP = true /\ frame_chain asegs m1 TOP v rest))).
    { inversion FC; subst; unfold wz in *.
      - split; [assumption|]. split; [assumption|]. split; [assumption|]. left. split; [assumption|reflexivity].
      - split; [assumption|]. split; [assumption|]. split; [assumption|]. right. split; assumption. }
    clear FC. destruct CELLS as (C & RR & VR & CASES).
    (* [comment removed for export] *)
    step. if_cases K; zify_cond K.
    { rewrite uloop_cut by lia. eapply uf_exit; eassumption. }
    (* [comment removed for export] *)
    step. step. if_cases K2; zify_cond K2.
    { rewrite uloop_page by (unfold KPAGE; lia). eapply uf_exit; eassumption. }
    (* [comment removed for export] *)
    assert (TAIL : forall (m2 : word -> option byte) (a7' : word) (acc2 : list Z),
      acc2 = upush pc0 rav acc ->
      rw_cells asegs m2 (f + -16) [C8 (Z_to_bv 64 v); C8 (Z_to_bv 64 rav)] ->
      rw_cells asegs m2 (bv_unsigned sp + -64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
      stk asegs m2 lo (bv_unsigned sp + -64) ->
      munch (uf_W lo (bv_unsigned sp) OBJ BUFN) m m2 -> wmono asegs m m2 -> mem_inv asegs m2 ->
      munch (uf_W lo (bv_unsigned sp) OBJ BUFN) m1 m2 -> wmono asegs m1 m2 ->
      rw_cells asegs m2 (OBJ + 8) [C4 (Z_to_bv 64 (Z.of_nat (length acc2)))] ->
      u64arr asegs m2 (OBJ + 16) (map wz acc2 ++ skipn (length acc2) buf) ->
      evt asegs (POST (uloop pc0 MD ((rav, v) :: rest) acc))
        (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 (Z_to_bv 64 MD) (Z_to_bv 64 (TOP - 16)) (Z_to_bv 64 OBJ)
                 (Z_to_bv 64 pc0) (Z_to_bv 64 f) (Z_to_bv 64 4096) (Z_to_bv 64 (OBJ + 16)) (Z_to_bv 64 (Z.of_nat (length acc2)))
                 (Z_to_bv 64 rav) a7' x18 x19 x20 x21 x22 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x1e1bec) fc None m2 (seg_rom asegs))).
    { intros m2 a7' acc2 EQ2 C2 FR2 ST2 MU2 WM2 MI2 MU12 WM12 SZ2 BUF2. unfold uf_W in MU2, MU12.
      assert (L2 : (length acc <= length acc2 <= S (length acc))%nat) by (subst acc2; apply upush_length).
      clear FR ST MU WM MI SZ BUF MU1 WM1 C.
      (* [comment removed for export] *)
      step.
      (* [comment removed for export] *)
      step. if_cases K4; zify_cond K4. { uf_exit_last CASES EQ2. }
      (* [comment removed for export] *)
      step. if_cases K5; zify_cond K5. { uf_exit_last CASES EQ2. }
      (* [comment removed for export] *)
      zstep. step. step. if_cases K6; zify_cond K6. 2:{ uf_exit_last CASES EQ2. }
      (* [comment removed for export] *)
      rewrite land7_mod8 in K6.
      destruct CASES as [[G _]|[G FCR]]. { exfalso. apply goodframe_false in G. lia. }
      destruct rest as [|x rest']. { exfalso. exact (frame_chain_nonnil _ _ _ _ _ FCR eq_refl). }
      rewrite uloop_link by (unfold KPAGE; lia). rewrite <- EQ2.
      apply (IH v acc2 m2); try assumption.
      - eapply frame_chain_transport; [exact FCR| |exact MU12|exact WM12].
        eapply below_le; [apply W_below|]. lia.
      - lia.
      - subst acc2. apply upush_range; assumption.
      - lia.
      - lia. }
    step. if_cases K3; zify_cond K3.
    + (* [comment removed for export] *)
      apply (TAIL _ a7 acc); try assumption.
      unfold upush. rewrite (proj2 (Z.eqb_eq _ _)) by lia. reflexivity.
    + (* [comment removed for export] *)
      zstep. replace (Z.of_nat (length acc) ≪ 3) with (8 * Z.of_nat (length acc)) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
      zstep. zstep. step.
      pose proof (u64arr_store_ok asegs _ _ _ (Z.of_nat (length acc)) _ BUF ltac:(rewrite length_app, length_map, length_skipn, LBUF; lia) eq_refl) as SOK.
      step.
      pose proof (u64arr_write asegs _ _ _ (Z.of_nat (length acc)) (Z_to_bv 64 rav) BUF ltac:(rewrite length_app, length_map, length_skipn, LBUF; lia)) as BUF'.
      rewrite Nat2Z.id in BUF'. clear BUF. store_done.
      change (Z_to_bv 64 rav) with (wz rav) in BUF'. rewrite buf_push in BUF' by (rewrite LBUF; lia).
      replace (Z.of_nat (length acc) + 1) with (Z.of_nat (length (acc ++ [rav]))) in * by (rewrite length_app; cbn; lia).
      eapply (TAIL _ _ (acc ++ [rav])); try eassumption.
      unfold upush. rewrite (proj2 (Z.eqb_neq _ _)) by lia. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Theorem unwindfast_spec : forall (t0 t1 t2 a6 a7 t3 t4 t5 t6 : word) (CH : list (Z * Z)),
    (goodframe BOT bp TOP = true -> frame_chain asegs m TOP bp CH) ->
    rw_cells asegs m (OBJ + 8) [C4 (wz (Z.of_nat 0))] \/ (exists szj, rw_cells asegs m (OBJ + 8) [C4 szj]) ->
    u64arr asegs m (OBJ + 16) buf ->
    rw_cells asegs m GOT_PAGESIZECACHED [C8 (wz PSC)] ->
    rw_cells asegs m PSC [C8 (wz KPAGE)] ->
    stk asegs m lo (bv_unsigned sp) ->
    mem_inv asegs m ->
    evt asegs (POST (utrace pc0 bp TOP BOT MD CH))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz OBJ) (wz pc0) (wz bp) (wz TOP) (wz BOT) (wz MD) a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 UNWINDFAST) fc None m (seg_rom asegs)).
  Proof.
    intros until CH. intros FCH SZ0 BUF GOTC PGC ST MI.
    assert (SZ : exists szj, rw_cells asegs m (OBJ + 8) [C4 szj]) by (destruct SZ0 as [H|H]; [eexists; exact H|exact H]). clear SZ0.
    destruct SZ as [szj SZ].
    pose proof (bv_unsigned_in_range 64 sp) as SPR; unfold bv_modulus in SPR; change (2 ^ Z.of_N 64) with (2^64) in SPR.
    pose proof (u64arr_bound _ _ _ _ BUF) as BB; rewrite LBUF in BB.
    pose proof (rw_cells_bound _ _ _ _ GOTC) as GB; cbn [cells_size csize Nat.add] in GB.
    pose proof (munch_refl (uf_W lo (bv_unsigned sp) OBJ BUFN) m) as MU. unfold uf_W in MU.
    pose proof (wmono_refl asegs m) as WM.
    unfold UNWINDFAST, GOT_PAGESIZECACHED, KPAGE, AIMG_TOP in *. unfold wz in *.
    carve_frame 64%nat ST.
    (* [comment removed for export] *)
    do 9 step.
    (* [comment removed for export] *)
    step. zstep. step. zstep.
    replace (MD mod 4294967296) with MD by (symmetry; apply Z.mod_small; lia).
    (* [comment removed for export] *)
    step. if_cases K0; zify_cond K0. { exfalso. lia. }
    (* [comment removed for export] *)
    step. step. step. step. if_cases K1; zify_cond K1. { exfalso. lia. }
    (* [comment removed for export] *)
    step. zstep. step.
    pose proof (u64arr_store_ok asegs _ _ _ 0 _ BUF ltac:(rewrite LBUF; lia) eq_refl) as SOK.
    replace (OBJ + 16 + 8 * 0) with (OBJ + 16) in SOK by lia.
    step.
    pose proof (u64arr_write asegs _ _ _ 0 (Z_to_bv 64 pc0) BUF ltac:(rewrite LBUF; lia)) as BUF'.
    replace (OBJ + 16 + 8 * 0) with (OBJ + 16) in BUF' by lia. clear BUF. store_done.
    assert (EB : upd buf (Z.to_nat 0) (Z_to_bv 64 pc0) = map wz [pc0] ++ skipn (length [pc0]) buf).
    { destruct buf as [|b0 buf']; [cbn in LBUF; lia|]. reflexivity. }
    rewrite EB in BUF'. clear EB.
    (* [comment removed for export] *)
    step. if_cases K2; zify_cond K2.
    2:{ (* [comment removed for export] *) exfalso. rewrite Z.shiftr_div_pow2 in K2 by lia. Z.div_mod_to_equations. lia. }
    unfold utrace. unfold KPAGE. replace (TOP <? 4096) with false by (symmetry; apply Z.ltb_ge; lia).
    (* [comment removed for export] *)
    step. if_cases K3; zify_cond K3. { exfalso. lia. }
    (* [comment removed for export] *)
    step. if_cases K4; zify_cond K4.
    { replace (goodframe BOT bp TOP) with false by (symmetry; apply goodframe_false; lia).
      eapply uf_exit; try eassumption. }
    (* [comment removed for export] *)
    zstep. step. if_cases K5; zify_cond K5.
    { replace (goodframe BOT bp TOP) with false by (symmetry; apply goodframe_false; lia).
      eapply uf_exit; try eassumption. }
    (* [comment removed for export] *)
    zstep. step. if_cases K6; zify_cond K6.
    { rewrite land7_mod8 in K6. replace (goodframe BOT bp TOP) with false by (symmetry; apply goodframe_false; lia).
      eapply uf_exit; try eassumption. }
    rewrite land7_mod8 in K6.
    replace (goodframe BOT bp TOP) with true in * by (symmetry; apply goodframe_true; lia).
    (* [comment removed for export] *)
    zstep. step.
    replace (TOP + -16) with (TOP - 16) by lia.
    apply (uf_loop CH bp [pc0] _ t0 t1 t2 _ _ _ _ _ _ _ t3 t4 t5 t6); try assumption; try (cbn; lia).
    eapply frame_chain_transport; [exact (FCH eq_refl)| |exact MU|exact WM]. apply W_below.
  Qed.
End UF.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition uw_W (lo spv OBJ BUFN : Z) : list ivl :=
  [(lo, spv); (OBJ + 8, OBJ + 12); (OBJ + 16, OBJ + 16 + 8 * BUFN); (OBJ + 2056, OBJ + 2064)].

Definition uw_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (OBJ BUFN lo bp : Z) (buf : list word) (T : list Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch (uw_W lo (bv_unsigned sp) OBJ BUFN) m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' (OBJ + 8) [C4 (wz (Z.of_nat (length T)))]
    /\ u64arr asegs m' (OBJ + 16) (map wz T ++ skipn (length T) buf)
    /\ rw_cells asegs m' (OBJ + 2056) [C8 (wz bp)]
    /\ stk asegs m' lo (bv_unsigned sp).

Section UW.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (OBJ BUFN lo PSC pc0 bp TOP BOT MD : Z) (buf : list word) (m : word -> option byte).

  Hypothesis LBUF : length buf = Z.to_nat BUFN.
  Hypothesis MDR  : 2 <= MD <= BUFN.
  Hypothesis BUFR : BUFN <= 255.
  Hypothesis OBJR : 0 <= OBJ.
  Hypothesis PC0R : KPAGE <= pc0 < 2^64.
  Hypothesis BPR  : 0 <= bp < 2^64.
  Hypothesis TOPR : KPAGE <= TOP < 2^64.
  Hypothesis BOTR : 0 <= BOT < TOP.
  Hypothesis PSCR : 0 <= PSC /\ PSC + 8 <= lo.
  Hypothesis IMGLO: AIMG_TOP <= lo.
  Hypothesis LO   : lo + 64 <= bv_unsigned sp.
  Hypothesis SPO  : bv_unsigned sp <= OBJ + 8.
  Hypothesis OBP  : OBJ + 2064 <= bp - 16.

  Theorem unwind_spec : forall (t0 t1 t2 a4 t3 t4 t5 t6 tfj : word) (CH : list (Z * Z)),
    (goodframe BOT bp TOP = true -> frame_chain asegs m TOP bp CH) ->
    (exists szj, rw_cells asegs m (OBJ + 8) [C4 szj]) ->
    u64arr asegs m (OBJ + 16) buf ->
    rw_cells asegs m (OBJ + 2056) [C8 tfj] ->
    rw_cells asegs m GOT_PAGESIZECACHED [C8 (wz PSC)] ->
    rw_cells asegs m PSC [C8 (wz KPAGE)] ->
    stk asegs m lo (bv_unsigned sp) ->
    mem_inv asegs m ->
    evt asegs (uw_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc OBJ BUFN lo bp buf (utrace pc0 bp TOP BOT MD CH) m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz OBJ) (wz MD) (wz pc0) (wz bp) a4 (wz TOP) (wz BOT) (wz 1)
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 UNWIND) fc None m (seg_rom asegs)).
  Proof.
    intros until CH. intros FCH [szj SZ] BUF TF GOTC PGC ST MI.
    pose proof (bv_unsigned_in_range 64 sp) as SPR; unfold bv_modulus in SPR; change (2 ^ Z.of_N 64) with (2^64) in SPR.
    pose proof (u64arr_bound _ _ _ _ BUF) as BB; rewrite LBUF in BB.
    pose proof (munch_refl (uw_W lo (bv_unsigned sp) OBJ BUFN) m) as MU. unfold uw_W in MU.
    pose proof (wmono_refl asegs m) as WM.
    unfold UNWIND, GOT_PAGESIZECACHED, KPAGE, AIMG_TOP in *. unfold wz in *.
    carve_frame 64%nat ST.
    do 8 step.
    (* [comment removed for export] *)
    step. zstep. zstep. zstep. zstep. step.
    replace (Z.b2z (MD <? 1)) with 0 by (replace (MD <? 1) with false by (symmetry; apply Z.ltb_ge; lia); reflexivity).
    replace (Z.land ((0 + -1) mod 18446744073709551616) bp) with bp.
    2:{ change ((0 + -1) mod 18446744073709551616) with (2^64 - 1). rewrite zb_land_mask_l by lia. rewrite Z.mod_small by lia. reflexivity. }
    (* [comment removed for export] *)
    step.
    (* [comment removed for export] *)
    step. if_cases K0; zify_cond K0. { exfalso. lia. }
    step. if_cases K1; zify_cond K1. 2:{ exfalso. lia. }
    step. if_cases K2; zify_cond K2. 2:{ exfalso. revert K2. rewrite ?unsigned_lit by lia. lia. }
    (* [comment removed for export] *)
    do 5 step. do 7 step. release_frame FR ST (bv_unsigned sp). step. step.
    eapply evt_mono.
    { eapply (unwindfast_spec ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc OBJ BUFN lo PSC pc0 bp TOP BOT MD buf m1);
        unfold KPAGE, AIMG_TOP, GOT_PAGESIZECACHED, wz; try eassumption; try lia.
      - intros G. eapply frame_chain_transport; [exact (FCH G)| |exact MU|exact WM].
        unfold below. intros l h Hin. cbn in Hin. destruct Hin as [E|[E|[E|[E|[]]]]]; inversion E; subst; lia.
      - right. eexists. exact SZ. }
    cbv beta. intros ms' PO. unfold uf_post in PO. unfold uw_post.
    destruct PO as (x5 & x6 & x7 & x10 & x11 & x12 & x13 & x14 & x15 & x16 & x17 & x28 & x29 & x30 & x31 & m' & E & MU' & WM' & MI' & SZ' & BUF' & ST').
    exists x5, x6, x7, x10, x11, x12, x13, x14, x15, x16, x17, x28, x29, x30, x31, m'.
    split; [exact E|]. split.
    { eapply munch_trans; [exact MU|]. eapply munch_weaken; [|exact MU']. unfold sub_fp, uf_W; cbn [outside]. intros x (A1 & A2 & A3 & A4 & _). repeat split; assumption. }
    split; [eapply wmono_trans; [exact WM|exact WM']|]. split; [exact MI'|]. split; [exact SZ'|]. split; [exact BUF'|]. split; [|exact ST'].
    eapply rw_cells_transport; [exact TF|exact MU'|exact WM'|]. unfold uf_W; cbn [disjoint_from cells_size csize Nat.add]. lia.
  Qed.
End UW.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition ASAN_INITED   : Z := 0x6ab5d8.   (* [comment removed for export] *)
Definition TSD_KEY_INITED : Z := 0x6aa160.  (* [comment removed for export] *)
Definition TSD_KEY : Z := 0x6aa164.         (* [comment removed for export] *)
Definition OFF_UNWINDING : Z := 3168.       (* [comment removed for export] *)


Lemma shl32_shr29 : forall K, 0 <= K < 2^31 -> Z.shiftr ((Z.shiftl K 32) mod 18446744073709551616) 29 = 8 * K.
Proof.
  intros K HK. rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia.
  rewrite Z.mod_small by (split; [lia|]; change 18446744073709551616 with (2^32 * 2^32); nia).
  change (2^32) with (2^29 * 8). rewrite Z.mul_assoc, (Z.mul_comm K), <- Z.mul_assoc. rewrite Z.mul_comm.
  rewrite Z.div_mul by lia. lia.
Qed.


Lemma sel_mask_true : forall c x, c = true -> 0 <= x < 2^64 ->
  Z.land ((0 - Z.b2z c) mod 18446744073709551616) x = x.
Proof.
  intros c x -> Hx. cbn [Z.b2z]. change ((0 - 1) mod 18446744073709551616) with (2^64 - 1).
  rewrite zb_land_mask_l by lia. apply Z.mod_small. lia.
Qed.


(* [comment removed for export] *)
Ltac head_of t := lazymatch t with ?h _ => head_of h | _ => t end.
Ltac post_callU segs m :=
  let ms' := fresh "ms'" in let PO := fresh "PO" in
  intros ms' PO;
  (let h := head_of ltac:(type of PO) in try unfold h in PO);
  cbv delta [uf_W uw_W] in PO;
  rewrite ?unsigned_lit in PO by lia; rewrite ?Z.add_0_r in PO; revert ms' PO; post_call segs m.
Tactic Notation "callU" uconstr(SPEC) :=
  lazymatch goal with
  | |- evt ?segs _ (MS _ _ _ _ _ ?m _) => eapply evt_cut; [ eapply SPEC | post_callU segs m ]
  end.

Definition ui_W (lo spv OBJ BUFN T : Z) : list ivl :=
  [(lo, spv); (OBJ + 8, OBJ + 12); (OBJ + 16, OBJ + 16 + 8 * BUFN); (OBJ + 2056, OBJ + 2064); (T + OFF_UNWINDING, T + OFF_UNWINDING + 1)].

Definition ui_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (OBJ BUFN lo bp T : Z) (buf : list word) (TR : list Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch (ui_W lo (bv_unsigned sp) OBJ BUFN T) m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' (OBJ + 8) [C4 (wz (Z.of_nat (length TR)))]
    /\ u64arr asegs m' (OBJ + 16) (map wz TR ++ skipn (length TR) buf)
    /\ rw_cells asegs m' (OBJ + 2056) [C8 (wz bp)]
    /\ rw_cells asegs m' (T + OFF_UNWINDING) [C1 (b8 0)]
    /\ stk asegs m' lo (bv_unsigned sp).

Section UI.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (OBJ BUFN lo PSC pc0 bp TOP BOT MD : Z) (buf : list word) (m : word -> option byte).
  (* [comment removed for export] *)
  Variables (TSD CTX T : Z).   (* [comment removed for export] *)

  Hypothesis LBUF : length buf = Z.to_nat BUFN.
  Hypothesis MDR  : 2 <= MD <= BUFN.
  Hypothesis BUFR : BUFN <= 255.
  Hypothesis OBJR : 0 <= OBJ.
  Hypothesis PC0R : KPAGE <= pc0 < 2^64.
  Hypothesis BPR  : 0 <= bp < 2^64.
  Hypothesis TOPR : KPAGE <= TOP <= 2^47.   (* [comment removed for export] *)
  Hypothesis BOTR : 0 <= BOT < TOP.
  Hypothesis PSCR : AIMG_LO <= PSC /\ PSC + 8 <= AIMG_TOP.    (* [comment removed for export] *)
  Hypothesis IMGLO: AIMG_TOP <= lo.
  Hypothesis LO   : lo + 144 <= bv_unsigned sp.
  Hypothesis SPO  : bv_unsigned sp <= OBJ.
  Hypothesis OBP  : OBJ + 2064 <= bp - 16.
  Hypothesis TPR  : 88 <= bv_unsigned tp /\ bv_unsigned tp - 88 + 8 <= lo.
  Hypothesis TSDR : 0 <= TSD /\ TSD + 8 <= lo.
  Hypothesis CTXR : 0 < CTX /\ CTX + 160 <= lo.
  (* [comment removed for export] *)
  Hypothesis TR_  : 4096 <= T /\ (T + OFF_UNWINDING + 1 <= AIMG_LO \/ AIMG_TOP <= T) /\ T + OFF_UNWINDING + 1 <= lo.

  Theorem unwindimpl_spec : forall (t0 t1 t2 a6 a7 t3 t4 t5 t6 tfj : word) (CH : list (Z * Z)),
    (goodframe BOT bp TOP = true -> frame_chain asegs m TOP bp CH) ->
    (exists szj, rw_cells asegs m (OBJ + 8) [C4 szj]) ->
    u64arr asegs m (OBJ + 16) buf ->
    rw_cells asegs m (OBJ + 2056) [C8 tfj] ->
    rw_cells asegs m GOT_PAGESIZECACHED [C8 (wz PSC)] ->
    rw_cells asegs m PSC [C8 (wz KPAGE)] ->
    rw_cells asegs m ASAN_INITED [C1 (b8 1)] ->
    rw_cells asegs m TSD_KEY_INITED [C1 (b8 1)] -> rw_cells asegs m TSD_KEY [C4 (wz 0)] ->
    rw_cells asegs m (bv_unsigned tp + -88) [C8 (wz TSD)] ->
    rw_cells asegs m TSD [C8 (wz CTX)] ->
    rw_cells asegs m (CTX + 152) [C8 (wz T)] ->
    rw_cells asegs m (T + 8) [C8 (wz TOP); C8 (wz BOT)] ->
    rw_cells asegs m (T + 40) [C1 (b8 0)] ->
    rw_cells asegs m (T + OFF_UNWINDING) [C1 (b8 0)] ->
    stk asegs m lo (bv_unsigned sp) ->
    mem_inv asegs m ->
    evt asegs (ui_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc OBJ BUFN lo bp T buf (utrace pc0 bp TOP BOT MD CH) m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz OBJ) (wz pc0) (wz bp) (wz 0) (wz 1) (wz MD) a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 UNWINDIMPL) fc None m (seg_rom asegs)).
  Proof.
    intros until CH. intros FCH [szj SZ] BUF TF GOTC PGC AI TKI TKK TPC TSDC CTXC TC T40 TUW ST MI.
    pose proof (bv_unsigned_in_range 64 sp) as SPR; unfold bv_modulus in SPR; change (2 ^ Z.of_N 64) with (2^64) in SPR.
    pose proof (bv_unsigned_in_range 64 tp) as TPRR; unfold bv_modulus in TPRR; change (2 ^ Z.of_N 64) with (2^64) in TPRR.
    pose proof (u64arr_bound _ _ _ _ BUF) as BB; rewrite LBUF in BB.
    pose proof (munch_refl (ui_W lo (bv_unsigned sp) OBJ BUFN T) m) as MU. unfold ui_W in MU.
    pose proof (wmono_refl asegs m) as WM.
    unfold UNWINDIMPL, GOT_PAGESIZECACHED, KPAGE, AIMG_LO, AIMG_TOP, ASAN_INITED, TSD_KEY_INITED, TSD_KEY, OFF_UNWINDING in *. unfold wz, b8 in *.
    carve_frame 80%nat ST.
    do 11 step.
    (* [comment removed for export] *)
    do 6 step. step.
    (* [comment removed for export] *)
    step. step. step. step. zstep. zstep. step.
    replace (bv_unsigned (sxb (Z_to_bv 8 1))) with 1 by (vm_compute; reflexivity).
    change ((1 + -1) mod 18446744073709551616 <? 1) with true. cbn [Z.b2z].
    (* [comment removed for export] *)
    step. if_cases K0; zify_cond K0. { exfalso. revert K0. rewrite ?unsigned_lit by lia. lia. }
    (* [comment removed for export] *)
    step. carve_frame 16%nat ST. step. st1.
    (* [comment removed for export] *)
    step. step. step. step. step. if_cases K1; zify_cond K1. { exfalso. revert K1. change (bv_unsigned (Z_to_bv 8 1)) with 1. rewrite unsigned_lit by lia. lia. }
    step. rewrite sx32_wz by lia. unfold wz.
    (* [comment removed for export] *)
    step. step. step. step. zstep. zstep.   (* [comment removed for export] *)
    try rewrite shl32_shr29 by lia. change ((0 ≪ 32) mod 18446744073709551616 ≫ 29) with 0.
    zstep. replace (TSD + 0) with TSD by lia. step. step.
    (* [comment removed for export] *)
    step. if_cases K2; zify_cond K2. { exfalso. lia. }
    step. step. step. release_frame FR0 ST (bv_unsigned sp + -80). step.
    (* [comment removed for export] *)
    step. if_cases K3; zify_cond K3. { exfalso. lia. }
    zstep. step. step. st1.
    step. if_cases K4; zify_cond K4. { exfalso. revert K4. change (bv_unsigned (Z_to_bv 8 0)) with 0. rewrite ?unsigned_lit by lia. lia. }
    (* [comment removed for export] *)
    step. step. step. step. step. if_cases K5; zify_cond K5. 2:{ exfalso. revert K5. change (bv_unsigned (sxb (Z_to_bv 8 0))) with 0. lia. }
    step. step. zstep. zstep. zstep. step.
    rewrite (sel_mask_true (BOT <? TOP) TOP) by (first [apply Z.ltb_lt; lia | lia]).
    (* [comment removed for export] *)
    step. step. step. step. step. step. if_cases K6; zify_cond K6. 2:{ exfalso. revert K6. change (bv_unsigned (sxb (Z_to_bv 8 0))) with 0. lia. }
    step. step. zstep. zstep. zstep. step.
    rewrite (sel_mask_true (BOT <? TOP) BOT) by (first [apply Z.ltb_lt; lia | lia]).
    (* [comment removed for export] *)
    step. step. if_cases K7; zify_cond K7. { exfalso. revert K7. rewrite ?unsigned_lit by lia. lia. }
    do 8 step. step.
    callU (unwind_spec _ _ gp tp _ _ _ _ _ _ _ _ _ s9 s10 s11 F fc OBJ BUFN lo PSC pc0 bp TOP BOT MD buf).
    all: unfold KPAGE, AIMG_LO, AIMG_TOP, GOT_PAGESIZECACHED, wz in *; try eassumption; try (first [clear - LBUF TOPR MDR PSCR IMGLO TR_; lia | lia]).
    all: try (rewrite ?unsigned_lit by lia; first [eassumption | lia]).
    { intros G. eapply frame_chain_transport; [exact (FCH G)| |exact MU|exact WM].
      unfold below. intros l h Hin. cbn in Hin. destruct Hin as [E|[E|[E|[E|[E|[]]]]]]; inversion E; subst; lia. }
    { eexists. eassumption. }
    (* [comment removed for export] *)
    st1.
    do 11 step. release_frame FR POST (bv_unsigned sp). step.
    finish.
  Qed.
End UI.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma utrace_length : forall pc0 bp top bot md CH, 1 <= md ->
  1 <= Z.of_nat (length (utrace pc0 bp top bot md CH)) <= md.
Proof.
  intros pc0 bp top bot md CH Hmd. unfold utrace.
  destruct (top <? KPAGE); [cbn; lia|]. destruct (goodframe bot bp top); [|cbn; lia].
  pose proof (uloop_length_le pc0 md CH [pc0] ltac:(cbn; lia)) as [A B]. cbn [length] in A, B. lia.
Qed.

Lemma uloop_range : forall pc0 md CH acc,
  Forall (fun rv : Z * Z => 0 <= fst rv < 2^64) CH -> (forall x, In x acc -> 0 <= x < 2^64) ->
  forall x, In x (uloop pc0 md CH acc) -> 0 <= x < 2^64.
Proof.
  intros pc0 md CH. induction CH as [|[ra v] rest IH]; intros acc HC HA x Hx; cbn [uloop] in Hx.
  - apply HA, Hx.
  - apply Forall_cons_iff in HC. destruct HC as [Hra HC]. cbn [fst] in Hra.
    destruct (md <=? Z.of_nat (length acc)). { apply HA, Hx. }
    destruct (ra <? KPAGE). { apply HA, Hx. }
    assert (HA' : forall y, In y (if ra =? pc0 then acc else acc ++ [ra]) -> 0 <= y < 2^64).
    { intros y Hy. destruct (ra =? pc0). { apply HA, Hy. } apply in_app_or in Hy. destruct Hy as [Hy|[<-|[]]]; [apply HA, Hy|lia]. }
    destruct rest as [|r rest']. { apply HA', Hx. } exact (IH _ HC HA' x Hx).
Qed.

Lemma utrace_range : forall pc0 bp top bot md CH,
  Forall (fun rv : Z * Z => 0 <= fst rv < 2^64) CH -> 0 <= pc0 < 2^64 ->
  Forall (fun x => 0 <= x < 2^64) (utrace pc0 bp top bot md CH).
Proof.
  intros pc0 bp top bot md CH HC Hpc. apply Forall_forall. intros x Hx. unfold utrace in Hx.
  destruct (top <? KPAGE). { destruct Hx as [<-|[]]. lia. }
  destruct (goodframe bot bp top). 2:{ destruct Hx as [<-|[]]. lia. }
  eapply uloop_range; [exact HC| |exact Hx]. intros y [<-|[]]. lia.
Qed.

Lemma frame_chain_ranges : forall segs m top f CH, frame_chain segs m top f CH -> Forall (fun rv : Z * Z => 0 <= fst rv < 2^64) CH.
Proof.
  intros segs m top f CH H. induction H; constructor; cbn [fst]; try assumption. constructor.
Qed.
