(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Arr Bytes SysStep Exec CellsX TacX.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import PropExec MState Mem Cells Step Frame.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Ref Require Import RSegs RMalloc_iface_stmt HeapSR_iface ECH_Xpres ECH_SR.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import Prelim STree Malloc Prog.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac ech_off_lit d := lazymatch (eval vm_compute in (andb (Z.leb 0 d) (Z.ltb d 8192))) with true => d end.

Ltac addr_diff E A ::=
  lazymatch E with
  | Z.add ?X ?c1 =>
      lazymatch A with
      | Z.add X ?c2 => let c1 := zlit c1 in let c2 := zlit c2 in let d := eval vm_compute in (c1 - c2)%Z in ech_off_lit d
      | X => let c1 := zlit c1 in ech_off_lit c1
      | _ => let e := zlit E in let a := zlit A in let d := eval vm_compute in (e - a)%Z in ech_off_lit d
      end
  | _ =>
      lazymatch A with
      | Z.add E ?c2 => let c2 := zlit c2 in let d := eval vm_compute in (- c2)%Z in ech_off_lit d
      | E => constr:(0%Z)
      | _ => let e := zlit E in let a := zlit A in let d := eval vm_compute in (e - a)%Z in ech_off_lit d
      end
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma amo_aligned_Z : forall wd z, 0 <= z < 2^64 -> z mod amo_bytes wd = 0 -> amo_aligned wd (Z_to_bv 64 z) = true.
Proof. intros wd z Hz Hm. unfold amo_aligned. rewrite unsigned_lit by lia. rewrite Hm. reflexivity. Qed.

Ltac amo_fix :=
  repeat match goal with
  | |- context [amo_aligned ?wd (Z_to_bv 64 ?z)] =>
      rewrite (amo_aligned_Z wd z) by (first [cbn [amo_bytes]; lia | cbn [amo_bytes]; nia]); cbn [negb]
  end;
  repeat match goal with
  | |- context [Z.eqb ?x ?x] => rewrite (Z.eqb_refl x)
  end;
  cbv beta iota delta [amo_val inval_resv with_resv c_resv].

Ltac astep_core segs R F pc fc rv m ro :=
  let fw := eval vm_compute in (fetch_word segs (Z_to_bv 64 pc)) in
  lazymatch fw with
  | Some ?w =>
      let d := eval vm_compute in (decode_any w) in
      lazymatch d with
      | Some (?i, ?sz) =>
        eapply evt_step;
        [ split; [reflexivity|];
          rewrite (step_gen segs R F (Z_to_bv 64 pc) fc rv m ro w i sz) by (vm_compute; reflexivity);
          exec_pre i; exec_cbv; simp_is_x0; simp_regs; vnorm_for i;
          amo_fix; simp_regs;
          try solve_load; try solve_store; reflexivity
        | simp_regs; vnorm_for i; mem_after_store_opt; post_step i ]
      | None => fail "undecodable instruction at" pc
      end
  | None => fail "no instruction at" pc
  end.
Ltac astep :=
  lazymatch goal with
  | |- evt ?segs ?Q (MS ?R ?F (Z_to_bv 64 ?pc) ?fc ?rv ?m ?ro) => astep_core segs R F pc fc rv m ro
  | |- evt _ _ (MS _ _ ?pc _ _ _ _) => fail "pc is not a literal:" pc
  end.
(* [comment removed for export] *)
Lemma sx32_lit : forall x, 0 <= x < 2^31 -> sx32 (Z_to_bv 64 x) = Z_to_bv 64 x.
Proof. intros x Hx. apply sx32_wz. exact Hx. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition stale (P : Prop) : Prop := P.
Ltac carry MU WM :=
  lazymatch type of MU with
  | munch ?W ?m0 ?m1 =>
      repeat match goal with
      | H : rw_cells ?segs m0 ?A ?cs |- _ =>
          first [ apply (fun HH => @rw_cells_transport segs W m0 m1 A cs HH MU WM) in H; [| cbn; lia]
                | change (stale (rw_cells segs m0 A cs)) in H ]
      | H : bytes_at ?segs m0 ?A ?bs |- _ =>
          first [ apply (fun HH => @bytes_at_transport segs W m0 m1 A bs HH MU) in H; [| cbn; lia]
                | change (stale (bytes_at segs m0 A bs)) in H ]
      | H : stk ?segs m0 ?lo ?hi |- _ =>
          first [ apply (fun HH => @stk_transport_disjoint segs W m0 m1 lo hi HH MU WM) in H; [| cbn; lia]
                | change (stale (stk segs m0 lo hi)) in H ]
      end
  end.
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac extend_munch MU WM MU' WM' :=
  lazymatch type of MU with munch ?W ?m ?m0 =>
  lazymatch type of MU' with munch ?W' m0 ?m1 =>
    let T := fresh "MUx" in
    assert (T : munch W m m1)
      by (eapply munch_trans; [exact MU|]; eapply munch_weaken; [| exact MU'];
          let xa := fresh "xa" in let Hxa := fresh "Hxa" in
          intros xa Hxa; unfold outside in *; cbn in *; first [tauto | lia]);
    clear MU; rename T into MU;
    let T2 := fresh "WMx" in
    pose proof (wmono_trans _ _ _ _ WM WM') as T2; clear WM; rename T2 into WM;
    clear MU' WM'   (* [comment removed for export] *)
  end end.

(* [comment removed for export] *)
Ltac land_exs PO :=
  let T := type of PO in let T' := eval hnf in T in
  lazymatch T' with
  | ex _ => let v := fresh "v" in destruct PO as [v PO]; land_exs PO
  | _ => idtac
  end.
Ltac land MU WM :=
  let ms' := fresh "ms'" in let PO := fresh "PO" in
  intros ms' PO; land_exs PO; destruct_ands PO; subst ms';
  lazymatch type of MU with munch _ _ ?m0 =>
    match goal with MUc : munch _ m0 ?m1 |- _ =>
      match goal with WMc : wmono _ m0 m1 |- _ =>
        rewrite ?unsigned_lit in MUc by lia;
        repeat match goal with H : context [bv_unsigned (Z_to_bv 64 _)] |- _ =>
          lazymatch type of H with munch _ _ _ => fail | _ => rewrite ?unsigned_lit in H by lia end end;
        carry MUc WMc; extend_munch MU WM MUc WMc
      end
    end
  end;
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
    repeat match goal with H : mem_inv _ ?mx |- _ => lazymatch mx with mc => fail | _ => clear H end end;
    repeat match goal with H : stale _ |- _ => clear H end;
    try (lazymatch goal with _ : stk _ mc _ _ |- _ => idtac end;
         match goal with H : stk _ mc _ _ |- _ => rename H into ST end)
  end;
  try (lazymatch goal with |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
        replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [lia| reflexivity]) end);
  (* [comment removed for export] *)
  repeat match goal with H : ?v = Z_to_bv 64 _ |- _ => is_var v; subst v end.

(* [comment removed for export] *)
Ltac norm_addr H :=
  lazymatch type of H with
  | rw_cells ?segs ?m ?a ?cs => let v := eval vm_compute in a in change (rw_cells segs m v cs) in H
  | bytes_at ?segs ?m ?a ?bs => let v := eval vm_compute in a in change (bytes_at segs m v bs) in H
  end.
(* [comment removed for export] *)
Ltac split_head H H1 :=
  lazymatch type of H with
  | rw_cells ?segs ?m ?a (?c :: ?cs) =>
      change (rw_cells segs m a ([c] ++ cs)) in H;
      apply (proj1 (rw_cells_app segs m a [c] cs)) in H;
      destruct H as [H1 H]; try norm_addr H
  end.

(* [comment removed for export] *)
Ltac join_cells :=
  first [ assumption
        | lazymatch goal with
          | |- rw_cells ?segs ?m ?a (?c :: ?cs) =>
              change (rw_cells segs m a ([c] ++ cs)); apply (proj2 (rw_cells_app segs m a [c] cs)); split;
              [ assumption
              | let a' := eval vm_compute in (a + Z.of_nat (cells_size [c]))%Z in
                change (rw_cells segs m a' cs); join_cells ]
          end ].

(* [comment removed for export] *)
Ltac if_lit :=
  match goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      let v := eval vm_compute in c in replace c with v by (vm_compute; reflexivity); cbv iota
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma byte_range : forall b : byte, 0 <= bv_unsigned b < 256.
Proof. intros b. pose proof (bv_unsigned_in_range 8 b) as R. unfold bv_modulus in R. cbn in R. lia. Qed.
Lemma word_range : forall w : word, 0 <= bv_unsigned w < 2^64.
Proof. intros w. pose proof (bv_unsigned_in_range 64 w) as R. unfold bv_modulus in R. cbn in R. lia. Qed.
Lemma signed_lit : forall z, - 2^63 <= z < 2^63 -> bv_signed (Z_to_bv 64 z) = z.
Proof.
  intros z Hz. rewrite zb_signed. rewrite unsigned_lit_wrap.
  destruct (Z.ltb_spec (z mod 2^64) (2^63)) as [L|L].
  - destruct (Z.neg_nonneg_cases z) as [N|N]; [| rewrite Z.mod_small in * by lia; lia].
    rewrite <- (Z.mod_add _ 1) in L by lia. rewrite Z.mod_small in L by lia. lia.
  - destruct (Z.neg_nonneg_cases z) as [N|N]; [| rewrite Z.mod_small in * by lia; lia].
    rewrite <- (Z.mod_add _ 1) by lia. rewrite Z.mod_small by lia. lia.
Qed.
Lemma errno_RATP : errno_addr (Z_to_bv 64 RATP) = RERRNO.
Proof. unfold RATP, RERRNO, errno_addr. rewrite unsigned_lit by lia. reflexivity. Qed.
Lemma byte_eq_of_unsigned : forall (b : byte) z, bv_unsigned b = z -> b = Z_to_bv 8 z.
Proof. intros b z E. subst z. symmetry. apply (bitvector.definitions.Z_to_bv_bv_unsigned 8). Qed.

(* [comment removed for export] *)
Lemma nodup_id_inj : forall (LB : list block) b1 b2, List.NoDup (map blk_id LB) -> In b1 LB -> In b2 LB -> blk_id b1 = blk_id b2 -> b1 = b2.
Proof.
  induction LB as [|c LB IH]; intros b1 b2 ND H1 H2 E; [destruct H1|].
  cbn in ND. inversion ND as [|x l NI ND']; subst.
  destruct H1 as [<-|H1], H2 as [<-|H2]; [reflexivity| | | apply IH; assumption].
  - exfalso. apply NI. apply in_map_iff. exists b2. split; [symmetry; exact E| exact H2].
  - exfalso. apply NI. apply in_map_iff. exists b1. split; [exact E| exact H1].
Qed.

(* [comment removed for export] *)
Lemma disjoint_from_sub : forall W A n A' n', disjoint_from W A n -> A <= A' -> A' + n' <= A + n -> 0 <= n' -> disjoint_from W A' n'.
Proof.
  induction W as [|[lo hi] W IH]; cbn; intros A n A' n' D H1 H2 H3; [exact I|].
  destruct D as [D1 D2]. split; [lia| eapply IH; eauto].
Qed.

(* [comment removed for export] *)
Lemma rw_cells_recut : forall m A cs cs',
  rw_cells rsegs m A cs -> cells_wf cs' -> cells_bytes cs' = cells_bytes cs -> rw_cells rsegs m A cs'.
Proof.
  intros m A cs cs' [[WF B] W] WF' E. split; [split; [exact WF'| rewrite E; exact B]|].
  rewrite <- (cells_bytes_length cs' WF'), E, (cells_bytes_length cs WF). exact W.
Qed.

Section HCW.
  Context {HCEIL : HeapCeil}.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma rclient_range_sub : forall LB SP A n A' n',
  rclient_range LB SP A n -> A <= A' -> A' + n' <= A + n -> 0 <= n' -> rclient_range LB SP A' n'.
Proof.
  intros LB SP A n A' n' HR H1 H2 H3. destruct HR as [K|[K|(b & Hb & K1 & K2)]].
  - left. lia.
  - right; left. unfold RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP, RVMLOCK in *. lia.
  - right; right. exists b. split; [exact Hb| lia].
Qed.

Lemma rclient_range_LB_mono : forall LB LB' SP A n,
  rclient_range LB SP A n -> (forall b, In b LB -> In b LB') -> rclient_range LB' SP A n.
Proof.
  intros LB LB' SP A n HR HL. destruct HR as [K|[K|(b & Hb & K1 & K2)]]; [left; exact K| right; left; exact K| right; right].
  exists b. split; [apply HL; exact Hb| lia].
Qed.

Lemma rclient_addr_range : forall LB SP a, rclient_addr LB SP a -> rclient_range LB SP a 1.
Proof.
  intros LB SP a [K|[K|(b & Hb & K1)]]; [left; lia| right; left| right; right].
  - unfold ralloc_static, RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP, RVMLOCK in *. lia.
  - exists b. split; [exact Hb| lia].
Qed.

Lemma rclient_range_block : forall LB SP b A n,
  In b LB -> blk_addr b <= A -> A + n <= blk_addr b + blk_size b -> rclient_range LB SP A n.
Proof. intros LB SP b A n Hb H1 H2. right; right. exists b. split; [exact Hb| split; assumption]. Qed.

Lemma xpres_of_munch_gen : forall LB SP X W m m',
  munch W m m' -> wmono rsegs m m' ->
  (forall a, 0 <= a < 2^64 -> xclient LB SP X a -> outside W a) ->
  xpres LB SP X m m'.
Proof.
  intros LB SP X W m m' MU WM HO a Ha Hc. split.
  - unfold wa. apply MU. rewrite unsigned_lit by lia. apply HO; assumption.
  - intros Hw. apply WM. exact Hw.
Qed.

Lemma rclient_write_ok_cons : forall LB b iv, rclient_write_ok LB iv -> rclient_write_ok (b :: LB) iv.
Proof.
  intros LB b iv [K|[K|(b' & Hb & K1 & K2)]]; [left; exact K| right; left; exact K| right; right].
  exists b'. split; [right; exact Hb| split; assumption].
Qed.

Lemma xpres_u32arr : forall LB SP X m m' A ws,
  xpres LB SP X m m' -> u32arr rsegs m A ws -> xclient_range LB SP X A (4 * Z.of_nat (length ws)) -> u32arr rsegs m' A ws.
Proof.
  intros LB SP X m m' A ws XP [B W] R. split.
  - eapply xpres_bytes_at; [exact XP| exact B|]. rewrite u32s_length. replace (Z.of_nat (4 * length ws)) with (4 * Z.of_nat (length ws)) by lia. exact R.
  - eapply xpres_wr_at; [exact XP| exact W| exact R].
Qed.

Lemma xpres_u64arr : forall LB SP X m m' A ws,
  xpres LB SP X m m' -> u64arr rsegs m A ws -> xclient_range LB SP X A (8 * Z.of_nat (length ws)) -> u64arr rsegs m' A ws.
Proof.
  intros LB SP X m m' A ws XP [B W] R. split.
  - eapply xpres_bytes_at; [exact XP| exact B|]. rewrite u64s_length. replace (Z.of_nat (8 * length ws)) with (8 * Z.of_nat (length ws)) by lia. exact R.
  - eapply xpres_wr_at; [exact XP| exact W| exact R].
Qed.

(* [comment removed for export] *)
Lemma xpres_reLB : forall LB LB1 SP SP1 X X1 m m',
  xpres LB1 SP1 X1 m m' ->
  (forall a, 0 <= a < 2^64 -> rclient_addr LB SP a -> ~ rin_ivs X a -> rclient_addr LB1 SP1 a /\ ~ rin_ivs X1 a) ->
  xpres LB SP X m m'.
Proof. intros LB LB1 SP SP1 X X1 m m' XP HC a Ha [C NX]. apply XP; [exact Ha|]. destruct (HC a Ha C NX) as [C1 N1]. split; assumption. Qed.

(* [comment removed for export] *)
Lemma xpres_X_mono : forall LB SP X X' m m',
  xpres LB SP X m m' -> (forall a, rin_ivs X a -> rin_ivs X' a) -> xpres LB SP X' m m'.
Proof. intros LB SP X X' m m' XP HX. eapply xpres_weaken; [exact XP| lia| auto| exact HX]. Qed.

Lemma xpres_nil_X : forall LB SP X m m', xpres LB SP [] m m' -> xpres LB SP X m m'.
Proof. intros LB SP X m m' XP. eapply xpres_X_mono; [exact XP|]. intros a K. destruct K. Qed.

(* [comment removed for export] *)
Lemma xpres_rw_cells' : forall LB SP X m m' A cs,
  xpres LB SP X m m' -> rw_cells rsegs m A cs -> rclient_range LB SP A (Z.of_nat (cells_size cs)) ->
  Forall (fun iv : Z * Z => A + Z.of_nat (cells_size cs) <= fst iv \/ snd iv <= A) X ->
  rw_cells rsegs m' A cs.
Proof. intros LB SP X m m' A cs XP HC HR HX. eapply xpres_rw_cells; [exact XP| exact HC| split; [exact HR| exact HX]]. Qed.

Lemma xpres_bytes_at' : forall LB SP X m m' A bs,
  xpres LB SP X m m' -> bytes_at rsegs m A bs -> rclient_range LB SP A (Z.of_nat (length bs)) ->
  Forall (fun iv : Z * Z => A + Z.of_nat (length bs) <= fst iv \/ snd iv <= A) X ->
  bytes_at rsegs m' A bs.
Proof. intros LB SP X m m' A bs XP HC HR HX. eapply xpres_bytes_at; [exact XP| exact HC| split; [exact HR| exact HX]]. Qed.

(* [comment removed for export] *)
Lemma rclient_range_write_ok : forall LB SP A n, rclient_range LB SP A n -> hceil <= SP -> rclient_write_ok LB (A, A + n).
Proof.
  intros LB SP A n HR CE. destruct HR as [K|[K|(b & Hb & K1 & K2)]]; [left; cbn; lia| right; left; cbn| right; right].
  - unfold RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP, RVMLOCK in *. lia.
  - exists b. cbn. split; [exact Hb| lia].
Qed.

Section Fresh.
  Context (RHEAP : PState -> list block -> mem -> Prop).
  Hypothesis RHEAP_blocks : RHEAP_block_range_stmt RHEAP.
  Hypothesis RHEAP_disj : RHEAP_blocks_disjoint_stmt RHEAP.
  Hypothesis RHEAP_nodup : RHEAP_blocks_nodup_stmt RHEAP.

  Lemma fresh_block_outside : forall s' LB m' p A n SP a,
    RHEAP s' ((p, A, n) :: LB) m' -> hceil <= SP -> rclient_addr LB SP a -> a + 1 <= A \/ A + n <= a.
  Proof.
    intros s' LB m' p A n SP a HP CE HC.
    eapply (fresh_block_disjoint_client RHEAP RHEAP_blocks RHEAP_disj RHEAP_nodup); [exact HP| | exact CE| lia].
    apply rclient_addr_range. exact HC.
  Qed.

  Lemma rclient_range_off_frame : forall s LB m SP A n lo,
    RHEAP s LB m -> rclient_range LB SP A n -> hceil <= lo -> 0 <= n -> A + n <= lo \/ SP <= A.
  Proof.
    intros s LB m SP A n lo HP HR CE Hn. destruct HR as [K|[K|(b & Hb & K1 & K2)]]; [right; exact K| left |left].
    - hcb. lia.
    - destruct (RHEAP_blocks _ _ _ b HP Hb) as (_ & _ & _ & R4 & _). lia.
  Qed.

  Lemma rclient_range_off_errno : forall s LB m SP A n,
    RHEAP s LB m -> rclient_range LB SP A n -> hceil <= SP -> 0 <= n -> A + n <= RERRNO \/ RERRNO + 4 <= A.
  Proof.
    intros s LB m SP A n HP HR CE Hn. unfold RERRNO. hcb.
    destruct HR as [K|[K|(b & Hb & K1 & K2)]]; [right; lia| |].
    - unfold RERRNO in K. lia.
    - destruct (RHEAP_blocks _ _ _ b HP Hb) as (_ & _ & _ & R4 & R5). hcb. lia.
  Qed.

  Lemma rclient_range_off_auxv : forall s LB m SP A n,
    RHEAP s LB m -> rclient_range LB SP A n -> hceil <= SP -> 0 <= n -> A + n <= RAUXV_CELL \/ RAUXV_CELL + 8 <= A.
  Proof.
    intros s LB m SP A n HP HR CE Hn. unfold RAUXV_CELL. hcb.
    destruct HR as [K|[K|(b & Hb & K1 & K2)]]; [right; lia| |].
    - unfold RLIBC, RCTX in K. lia.
    - destruct (RHEAP_blocks _ _ _ b HP Hb) as (_ & _ & _ & R4 & R5). hcb. lia.
  Qed.

  Lemma blocks_below_hceil : forall s LB m, RHEAP s LB m -> forall b, In b LB -> blk_addr b + blk_size b <= hceil.
  Proof. intros s LB m HP b Hb. destruct (RHEAP_blocks _ _ _ b HP Hb) as (_ & _ & _ & R4 & _). exact R4. Qed.

  Lemma blocks_nonneg : forall s LB m, RHEAP s LB m -> forall b, In b LB -> 0 <= blk_size b.
  Proof. intros s LB m HP b Hb. destruct (RHEAP_blocks _ _ _ b HP Hb) as (_ & _ & R3 & _). exact R3. Qed.

  Lemma lb_bytes_nonneg_heap : forall s LB m, RHEAP s LB m -> 0 <= lb_bytes LB.
  Proof.
    intros s LB m HP. apply lb_bytes_nonneg. apply Forall_forall. intros b Hb. eapply blocks_nonneg; [exact HP| exact Hb].
  Qed.
End Fresh.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section HH.
  Variable H : hsr.
  Hypothesis HH : heap_sr_hyps H.

  Lemma HH_blocks_below : forall s LB m, hs_RHEAP H s LB m -> forall b, In b LB -> blk_addr b + blk_size b <= hceil.
  Proof. exact (blocks_below_hceil (hs_RHEAP H) (HH_RHEAP_block_range H HH)). Qed.

  Lemma HH_fresh_outside : forall s' LB m' p A n SP a,
    hs_RHEAP H s' ((p, A, n) :: LB) m' -> hceil <= SP -> rclient_addr LB SP a -> a + 1 <= A \/ A + n <= a.
  Proof. exact (fresh_block_outside (hs_RHEAP H) (HH_RHEAP_block_range H HH) (HH_RHEAP_blocks_disjoint H HH) (HH_RHEAP_blocks_nodup H HH)). Qed.

  Lemma HH_fresh_disjoint_client : forall s' LB m' p A n SP a k,
    hs_RHEAP H s' ((p, A, n) :: LB) m' -> rclient_range LB SP a k -> hceil <= SP -> 0 <= k -> a + k <= A \/ A + n <= a.
  Proof. exact (fresh_block_disjoint_client (hs_RHEAP H) (HH_RHEAP_block_range H HH) (HH_RHEAP_blocks_disjoint H HH) (HH_RHEAP_blocks_nodup H HH)). Qed.

  Lemma HH_alloc_ok : forall s LB m n,
    hs_RHEAP H s LB m -> 0 <= n -> lb_bytes LB + n <= hs_LIVE_MAX H ->
    Z.of_nat (length LB) + 1 <= hs_LIVE_CNT_MAX H -> lb_big LB + big1 n <= hs_LIVE_BIG_MAX H -> hs_alloc_ok H s LB n.
  Proof. exact (ECH_SR.HH_alloc_ok H HH). Qed.

  (* [comment removed for export] *)
  Lemma xpres_of_munch_fresh : forall s' LB m0 m m' p A n SP X W,
    hs_RHEAP H s' ((p, A, n) :: LB) m0 -> hceil <= SP ->
    munch W m m' -> wmono rsegs m m' ->
    Forall (fun iv : Z * Z => (hceil <= fst iv /\ snd iv <= SP) \/ (A <= fst iv /\ snd iv <= A + n)
                              \/ (forall a, fst iv <= a < snd iv -> rin_ivs X a)) W ->
    xpres LB SP X m m'.
  Proof.
    intros s' LB m0 m m' p A n SP X W HP CE MU WM FW.
    eapply xpres_of_munch_gen; [exact MU| exact WM|].
    intros a Ha [HC HX].
    pose proof (HH_fresh_outside _ _ _ _ _ _ _ a HP CE HC) as OUT.
    assert (HB : forall b, In b LB -> blk_addr b + blk_size b <= hceil).
    { intros b Hb. eapply HH_blocks_below; [exact HP| right; exact Hb]. }
    clear MU WM. induction W as [|[lo hi] W IH]; [exact I|]. cbn.
    pose proof (Forall_inv FW) as K1. cbn in K1.
    split; [| apply IH; apply (Forall_inv_tail FW)].
    destruct K1 as [[K1 K2]|[[K1 K2]|K1]].
    - destruct HC as [HC|[[HC _]|(b & Hb & Hr)]]; [lia| hcb; lia|]. pose proof (HB b Hb). lia.
    - lia.
    - intros R. apply HX. apply K1. exact R.
  Qed.

  (* [comment removed for export] *)
  Lemma lb_remove_exact : forall p A n LB,
    List.NoDup (map blk_id LB) -> In (p, A, n) LB ->
    lb_bytes (hs_lb_remove H p LB) = lb_bytes LB - n
    /\ (S (length (hs_lb_remove H p LB)) = length LB)%nat
    /\ (forall b, In b (hs_lb_remove H p LB) <-> (In b LB /\ blk_id b <> p)).
  Proof.
    pose proof (HH_lb_remove H HH) as (L1 & L2 & L3).
    intros p A n LB. induction LB as [|c LB IH]; intros ND Hin; [destruct Hin|].
    cbn in ND. inversion ND as [|x l NI ND']; subst.
    destruct Hin as [->|Hin].
    - cbn in NI. rewrite L1 by exact NI. rewrite lb_bytes_cons. cbn [blk_size snd length].
      split; [lia|]. split; [reflexivity|].
      intros b. split.
      + intros Hb. split; [right; exact Hb|]. intros E. apply NI. apply in_map_iff. exists b. split; [exact E| exact Hb].
      + intros [[<-|Hb] NE]; [cbn in NE; congruence| exact Hb].
    - assert (NE : blk_id c <> p).
      { intros E. apply NI. apply in_map_iff. exists (p, A, n). split; [symmetry; exact E| exact Hin]. }
      rewrite L2 by exact NE. rewrite !lb_bytes_cons. cbn [length].
      destruct (IH ND' Hin) as (B1 & B2 & B3). split; [lia|]. split; [lia|].
      intros b. split.
      + intros [<-|Hb]; [split; [left; reflexivity| exact NE]|]. destruct (proj1 (B3 b) Hb) as [K1 K2]. split; [right; exact K1| exact K2].
      + intros [[<-|Hb] NEb]; [left; reflexivity| right]. apply (proj2 (B3 b)). split; [exact Hb| exact NEb].
  Qed.

  Lemma lb_remove_big : forall p A n LB,
    List.NoDup (map blk_id LB) -> In (p, A, n) LB -> lb_big (hs_lb_remove H p LB) = lb_big LB - big1 n.
  Proof.
    pose proof (HH_lb_remove H HH) as (L1 & L2 & L3).
    intros p A n LB. induction LB as [|c LB IH]; intros ND Hin; [destruct Hin|].
    cbn in ND. inversion ND as [|x l NI ND']; subst.
    destruct Hin as [->|Hin].
    - cbn in NI. rewrite L1 by exact NI. rewrite lb_big_cons. cbn [blk_size snd]. lia.
    - assert (NE : blk_id c <> p).
      { intros E. apply NI. apply in_map_iff. exists (p, A, n). split; [symmetry; exact E| exact Hin]. }
      rewrite L2 by exact NE. rewrite !lb_big_cons. rewrite (IH ND' Hin). lia.
  Qed.

  (* [comment removed for export] *)
  Lemma lb_remove_heap : forall s LB m p A n,
    hs_RHEAP H s LB m -> In (p, A, n) LB ->
    lb_bytes (hs_lb_remove H p LB) = lb_bytes LB - n
    /\ (S (length (hs_lb_remove H p LB)) = length LB)%nat
    /\ lb_big (hs_lb_remove H p LB) = lb_big LB - big1 n
    /\ (forall b, In b (hs_lb_remove H p LB) <-> (In b LB /\ blk_id b <> p)).
  Proof.
    intros s LB m p A n HP Hin. pose proof (HH_RHEAP_blocks_nodup H HH _ _ _ HP) as ND.
    destruct (lb_remove_exact p A n LB ND Hin) as (B1 & B2 & B3).
    split; [exact B1|]. split; [exact B2|]. split; [apply (lb_remove_big p A n LB ND Hin)| exact B3].
  Qed.

  (* [comment removed for export] *)
  Lemma fresh_id_ne : forall s p' A' n' LBr m q,
    hs_RHEAP H s ((p', A', n') :: LBr) m -> In q (map blk_id LBr) -> p' <> q.
  Proof.
    intros s p' A' n' LBr m q HP Hq E. subst q. pose proof (HH_RHEAP_blocks_nodup H HH _ _ _ HP) as ND. cbn in ND. inversion ND; subst. contradiction.
  Qed.

  (* [comment removed for export] *)
  Lemma lb_remove_perm : forall s LB m p A n,
    hs_RHEAP H s LB m -> In (p, A, n) LB -> Permutation ((p, A, n) :: hs_lb_remove H p LB) LB.
  Proof.
    intros s LB m p A n HP Hin. pose proof (HH_RHEAP_blocks_nodup H HH _ _ _ HP) as ND. clear HP.
    pose proof (HH_lb_remove H HH) as (L1 & L2 & L3).
    revert ND Hin. induction LB as [|c LB IH]; intros ND Hin; [destruct Hin|].
    cbn in ND. inversion ND as [|x l NI ND']; subst.
    destruct Hin as [->|Hin].
    - cbn in NI. rewrite L1 by exact NI. apply Permutation_refl.
    - assert (NE : blk_id c <> p).
      { intros E. apply NI. apply in_map_iff. exists (p, A, n). split; [symmetry; exact E| exact Hin]. }
      rewrite L2 by exact NE. eapply Permutation_trans; [apply perm_swap| apply perm_skip]. apply IH; assumption.
  Qed.

  (* [comment removed for export] *)
  Lemma lb_remove_fresh : forall s p A n LB m,
    hs_RHEAP H s ((p, A, n) :: LB) m -> hs_lb_remove H p ((p, A, n) :: LB) = LB.
  Proof.
    intros s p A n LB m HP. pose proof (HH_lb_remove H HH) as (L1 & _ & _). apply L1.
    pose proof (HH_RHEAP_blocks_nodup H HH _ _ _ HP) as ND. cbn in ND. inversion ND; subst. assumption.
  Qed.
End HH.

End HCW.
