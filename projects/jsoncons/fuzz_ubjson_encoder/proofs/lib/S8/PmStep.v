(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg HeapIface
     AxSymExec3 AxSymExec3Sound L5Defs L5Core L5CoreKit.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import BMode.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.

Module PMK.

Ltac keep_arith := lazymatch goal with |- _ => L5FastLia.prune_arith end.
Ltac clear_disj_but H := repeat match goal with H' : _ \/ _ |- _ => tryif constr_eq H' H then fail else clear H' end.
Ltac alia0 := first [ lia | match goal with H : _ \/ _ |- _ => clear_disj_but H; destruct H; lia end ].
Ltac alia := keep_arith; first [ (repeat match goal with H : _ \/ _ |- _ => clear H end); lia | alia0 ].

Ltac feed_concl T := lazymatch T with ?A -> ?B => feed_concl B | _ => T end.
Ltac feed P tac :=
  let T := type of P in
  lazymatch T with
  | ?A0 -> _ =>
      let C := feed_concl T in
      let Q := fresh "SC" in
      assert (Q : C) by (apply P; clear P; first [ tac | lazymatch goal with |- ?A => fail 1 "feed: cannot prove premise" A end ]);
      move Q after P; clear P; rename Q into P
  | _ => idtac
  end.
Ltac greg :=
  lazymatch goal with |- getr ?R ?x = ?rhs =>
    match goal with H : getr R ?y = ?rhs' |- _ =>
      first [ constr_eq x y | replace x with y by (apply bv_eq; vm_compute; reflexivity) ];
      first [ exact H
            | lazymatch rhs with Z_to_bv 64 ?z => lazymatch rhs' with Z_to_bv 64 ?z' => replace z with z' by (clear; lia); exact H end end ]
    end
  end.
Ltac gmem :=
  lazymatch goal with
  | |- L5.u64_at ?sg ?M ?a ?v => match goal with H : L5.u64_at sg M ?b ?v' |- _ => first [constr_eq a b | replace a with b by (clear; lia)]; first [exact H | replace v with v' by (clear; lia); exact H] end
  | |- L5.u32_at ?sg ?M ?a ?v => match goal with H : L5.u32_at sg M ?b ?v' |- _ => first [constr_eq a b | replace a with b by (clear; lia)]; first [exact H | replace v with v' by (clear; lia); exact H] end
  | |- L5.u8_at ?sg ?M ?a ?v => match goal with H : L5.u8_at sg M ?b ?v' |- _ => first [constr_eq a b | replace a with b by (clear; lia)]; first [exact H | replace v with v' by (clear; lia); exact H] end
  | |- L5.defined ?M ?a ?n => match goal with H : L5.defined M ?b ?m |- _ => apply (L5.defined_sub M b m a n H); clear; lia end
  | |- L5.writable ?sg ?M ?a ?n => match goal with H : L5.writable sg M ?b ?m |- _ => apply (L5.writable_sub sg M b m a n H); clear; lia end
  | |- L5.img_clear ?M ?lo ?hi => match goal with H : L5.img_clear M ?lo' ?hi' |- _ => first [exact H | (intros ? ?; apply H; clear - H; lia)] end
  end.
Ltac arith_shape :=
  lazymatch goal with
  | |- (_ <= _)%Z => idtac | |- (_ < _)%Z => idtac | |- (_ <= _ <= _)%Z => idtac | |- (_ <= _ < _)%Z => idtac | |- (_ < _ <= _)%Z => idtac | |- (_ < _ < _)%Z => idtac
  | |- @eq Z _ _ => idtac | |- (_ \/ _) => idtac | |- (~ _)%type => idtac | |- (_ /\ _) => idtac
  | |- le _ _ => idtac | |- lt _ _ => idtac | |- @eq nat _ _ => idtac
  end.
Ltac arith_goal := first [ arith_shape | red; arith_shape ].
Ltac sc0 := first [ assumption | greg | gmem | arith_goal; first [assumption | alia] ].

Ltac xfer AG C :=
  first [ eapply L5C.u64_at_agree; [intros ? ?; apply AG; alia | alia | alia | exact C]
        | eapply L5C.u8_at_agree; [intros ? ?; apply AG; alia | alia | alia | exact C]
        | eapply L5C.defined_agree; [intros ? ?; apply AG; alia | exact C] ].

Ltac inl := apply L5K.In_of_mem; vm_compute; reflexivity.

Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).

Definition cs_all : list nat := [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat.
Lemma preserved_by_index (R R' : bvmap 5 word) : (forall k, In k cs_all -> getr R' (reg k) = getr R (reg k)) -> regs_preserved R R'.
Proof.
  intros KR x Hx. rewrite <- (AX2S.ridx_roundtrip x). apply KR.
  unfold callee_saved_idx in Hx. unfold AX2.ridx. set (z := bv_unsigned x) in *. cbn in Hx.
  repeat (destruct Hx as [Hx|Hx]; [rewrite <- Hx; cbn; tauto|]). destruct Hx.
Qed.
Lemma cs_of_preserved (R R' : bvmap 5 word) k : regs_preserved R R' -> In k cs_all -> getr R' (reg k) = getr R (reg k).
Proof.
  intros RP Hk. apply RP. unfold callee_saved_idx. cbn in Hk.
  repeat (destruct Hk as [<-|Hk]; [cbn; tauto|]). destruct Hk.
Qed.
Lemma regs_preserved_trans R1 R2 R3 : regs_preserved R1 R2 -> regs_preserved R2 R3 -> regs_preserved R1 R3.
Proof. intros H1 H2 x Hx. rewrite (H2 x Hx). apply H1. exact Hx. Qed.

Ltac rk :=
  first [ reflexivity | greg
        | match goal with K : forall x, In x _ -> getr ?Rb (reg x) = getr ?Ra (reg x) |- getr ?Rb' (Z_to_bv 5 (Z.of_nat ?k)) = _ =>
            constr_eq Rb Rb'; rewrite (K k) by inl; rk end
        | match goal with RP : regs_preserved ?Ra ?Rb |- getr ?Rb' (Z_to_bv 5 (Z.of_nat ?k)) = _ =>
            constr_eq Rb Rb'; rewrite (cs_of_preserved Ra Rb k RP) by inl; rk end ].
Ltac sc := first [ assumption | rk | gmem | arith_goal; first [assumption | alia] ].

Ltac pvz_hg tac := lazymatch goal with |- ?G0 => let PG := fresh "PGoal" in set (PG := G0); tac; subst PG end.
Ltac pvz_fold B k := lazymatch B with | ?A2 /\ ?B2 => pvz_fold B2 ltac:(fun T2 => let T := fresh "pvzT" in pose (T := A2 /\ T2); k T) | _ => k B end.
Ltac pvz_lin P := lazymatch type of P with ?A /\ ?B => pvz_fold B ltac:(fun T => change_no_check (A /\ T) in P) | _ => idtac end.
Ltac pvz_clrT := repeat match goal with T := (_ /\ _) : Prop |- _ => clear T end.

Lemma land_m2_even r : 0 <= r -> r mod 2 = 0 -> Z.land r (-2) = r.
Proof.
  intros Hr He. apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec.
  change (-2) with (Z.lnot 1). rewrite Z.lnot_spec by lia.
  destruct (Z.eq_dec i 0) as [->|NZ].
  - rewrite Z.bit0_eqb. change (Z.testbit 1 0) with true. cbn [negb]. rewrite Bool.andb_false_r. symmetry. apply Z.eqb_neq. lia.
  - replace (Z.testbit 1 i) with false. rewrite Bool.andb_true_r. reflexivity. symmetry. rewrite <- (Z.pow_0_r 2). rewrite Z.pow2_bits_eqb by lia. apply Z.eqb_neq. lia.
Qed.

Lemma ret_to (segs : list Segment) fx R M (pc : Z) (W : bv 32) r :
  fetch_word segs (Z_to_bv 64 pc) = Some W -> is_ecall W = false -> decode_any W = Some (Jalr 0 1 0, 4%Z) ->
  getr R (reg 1) = Z_to_bv 64 r -> 0 <= r < 2 ^ 47 -> r mod 2 = 0 ->
  msteps segs (@mkst fx R (Z_to_bv 64 pc) M (seg_rom segs)) (@mkst fx R (Z_to_bv 64 r) M (seg_rom segs)).
Proof.
  intros HF HEC HD H1 Hr He. eapply mst_step; [reflexivity | | apply mst_refl].
  assert (D: decode_any W = Some (Jalr 0 (reg 1) (0%bv : bv 12), 4%Z)). { rewrite HD. repeat f_equal; apply bv_eq; reflexivity. }
  rewrite (step_jalr_x0 segs R _ M (seg_rom segs) _ (reg 1) (0%bv : bv 12) (Z_to_bv 64 r) HF HEC D H1).
  f_equal. f_equal. unfold v_jalr. f_equal. unfold jalr_tgtZ. change (bv_signed (0%bv : bv 12)) with 0. rewrite Z.add_0_r.
  rewrite L5.unsigned_lit by lia. apply land_m2_even; lia.
Qed.

Section Kit.
Context {SCFG_P : ScfgP}. Context {bmK : BMode}.
Variable segs : list Segment.
Variable L : heap_layout.
Variable HI : heap_iface.

Record klayout : Prop := KLAY {
  kl_segs : hl_segs L = segs;
  kl_ro : forall a, hl_alloc_ro L a -> (hl_img_lo L <= a < hl_img_hi L) \/ hl_sptop L <= a;
  kl_img : 0 <= hl_img_lo L /\ hl_img_hi L <= 0x7fff7f800000;
  kl_errno : hl_img_lo L <= hl_errno L /\ hl_errno L + 4 <= hl_img_hi L
}.
Hypothesis KL : klayout.
Hypothesis HIok : heap_iface_ok L SCFG HI.

Abbreviation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom segs)).
Definition cfg {fx : FPState} (R : bvmap 5 word) (pc : Z) (M : word -> option byte) (model : Model) : config :=
  mkCfg (@mkst fx R (Z_to_bv 64 pc) M (seg_rom segs)) model.

Definition cwr (LB : list (Z * Z)) (a : Z) : Prop :=
  (hl_ceil L <= a < hl_sptop L) \/ in_block LB a \/ (hl_img_lo L <= a < hl_img_hi L /\ ~ hl_alloc_static L a /\ ~ hl_alloc_ro L a).

Lemma hi_heap_stretch LB cr M M' VM :
  hi_heap HI LB cr M VM -> 0x7fff80000000 <= hl_sptop L ->
  (forall a, 0 <= a < 2 ^ 64 -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a) \/ cwr LB a) ->
  mem_grows M M' -> hi_heap HI LB cr M' VM.
Proof.
  intros HH Hsp Hchg Hgr. eapply (hio_frame L SCFG HI HIok). exact HH.
  - intros a Ha Hpriv. destruct (Hchg a Ha) as [E|[S|[B|(I1 & I2 & I3)]]]. exact E.
    + exfalso. destruct Hpriv as [(P1 & P2 & P3)|P]. lia. apply (kl_ro KL) in P. pose proof (kl_img KL). lia.
    + exfalso. destruct Hpriv as [(P1 & P2 & P3)|P]. exact (P2 B). apply (kl_ro KL) in P.
      destruct B as (b & Hb & Hin). pose proof (proj1 (hio_wf L SCFG HI HIok LB cr M VM HH) b Hb) as ((R0 & R1 & R2 & R3 & R4) & _).
      pose proof (kl_img KL). lia.
    + exfalso. destruct Hpriv as [(P1 & P2 & P3)|P]. apply P3. split; assumption. exact (I3 P).
  - intros x Hx. apply Hgr. exact Hx.
Qed.

Lemma spiece LB cr M model (fx fx1 : FPState) R (pc : Z) R1 (pc1 : Z) (M1 : word -> option byte) (W : Z -> Prop) K :
  hi_heap HI LB cr M (m_vmmaps model) -> m_halted model = None -> m_vm_lazy model = [] -> 0x7fff80000000 <= hl_sptop L ->
  msteps segs (st fx R pc M) (st fx1 R1 pc1 M1) -> mem_grows M M1 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ W a -> M1 (Z_to_bv 64 a) = M (Z_to_bv 64 a)) ->
  (forall a, W a -> cwr LB a) -> (forall a, {W a} + {~ W a}) ->
  (hi_heap HI LB cr M1 (m_vmmaps model) -> srealizes segs SCFG (@cfg fx1 R1 pc1 M1 model) K) ->
  srealizes segs SCFG (@cfg fx R pc M model) K.
Proof.
  intros HH Hh Hl Hsp MS MG FR WC DEC KONT. unfold cfg.
  eapply (L5.cps_of_msteps segs); [exact Hh| exact Hl| exact MS|].
  apply KONT. apply (hi_heap_stretch LB cr M M1 _ HH Hsp); [|exact MG].
  intros a Ha. destruct (DEC a) as [Y|N]; [right; apply WC; exact Y| left; apply FR; assumption].
Qed.

Lemma spiece_ro model (fx fx1 : FPState) R (pc : Z) R1 (pc1 : Z) (M : word -> option byte) K :
  m_halted model = None -> m_vm_lazy model = [] ->
  msteps segs (st fx R pc M) (st fx1 R1 pc1 M) ->
  srealizes segs SCFG (@cfg fx1 R1 pc1 M model) K -> srealizes segs SCFG (@cfg fx R pc M model) K.
Proof. intros Hh Hl MS KONT. unfold cfg in *. eapply (L5.cps_of_msteps segs); eauto. Qed.

Lemma rng_dec a lo hi : {lo <= a < hi} + {~ (lo <= a < hi)}.
Proof. destruct (Z_lt_le_dec a lo); [right; lia|]. destruct (Z_lt_le_dec a hi); [left; lia | right; lia]. Qed.
Lemma or_dec (P Q : Prop) : {P} + {~ P} -> {Q} + {~ Q} -> {P \/ Q} + {~ (P \/ Q)}.
Proof. intros [p|np] [q|nq]; [left; auto| left; auto| left; auto| right; tauto]. Qed.

Lemma cwr_stack LB M sp scr a : L5C.stk (hl_sptop L) M sp scr -> sp - scr <= a < hl_sptop L -> cwr LB a.
Proof. intros (_ & B & _ & _ & _) Ha. left. lia. Qed.
Lemma cwr_block LB B n a : In (B, n) LB -> B <= a < B + n -> cwr LB a.
Proof. intros Hin Ha. right. left. exists (B, n). split; [exact Hin| cbn; lia]. Qed.

Definition inW (W : list L5.range) (a : Z) : Prop := exists r, In r W /\ L5.in_rng r a.
Lemma inW_not_outside W a : inW W a -> ~ L5.outside W a.
Proof. intros (r & Hin & Hr) HO. exact (HO r Hin Hr). Qed.
Lemma inW_here b n W a : b <= a < b + n -> inW ((b, n) :: W) a.
Proof. intros H. exists (b, n). split; [left; reflexivity| exact H]. Qed.
Lemma inW_next r W a : inW W a -> inW (r :: W) a.
Proof. intros (r' & Hin & Hr). exists r'. split; [right; exact Hin| exact Hr]. Qed.
Lemma inW_app_l W1 W2 a : inW W1 a -> inW (W1 ++ W2) a.
Proof. intros (r & Hin & Hr). exists r. split; [apply in_or_app; left; exact Hin| exact Hr]. Qed.
Lemma inW_app_r W1 W2 a : inW W2 a -> inW (W1 ++ W2) a.
Proof. intros (r & Hin & Hr). exists r. split; [apply in_or_app; right; exact Hin| exact Hr]. Qed.

Definition ek (LB : list (Z * Z)) (sp scr : Z) (W : list L5.range) (M M' : word -> option byte) : Prop :=
  forall a, L5C.kept L LB sp scr W a -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a).
Definition dk (LB : list (Z * Z)) (sp scr : Z) (M M' : word -> option byte) : Prop :=
  forall a, 0 <= a < 2 ^ 64 -> client_addr L LB sp scr a -> ~ in_errno L a -> M (Z_to_bv 64 a) <> None -> M' (Z_to_bv 64 a) <> None.

Lemma hpres_of LB sp scr W M M' : ek LB sp scr W M M' -> L5.defined M' (sp - scr) scr -> dk LB sp scr M M' -> L5C.hpres L LB sp scr W M M'.
Proof. intros E D K. apply L5C.hpres_intro; assumption. Qed.
Lemma ek_of_hpres LB sp scr W M M' : L5C.hpres L LB sp scr W M M' -> ek LB sp scr W M M'.
Proof. intros H a Ha. apply (L5C.hpres_kept L LB sp scr W M M' a H Ha). Qed.
Lemma dk_of_hpres LB sp scr W M M' : L5C.hpres L LB sp scr W M M' -> dk LB sp scr M M'.
Proof. intros H a Ha C E D. apply (L5C.hpres_cdef L LB sp scr W M M' a H Ha C E D). Qed.

Lemma ek_refl LB sp scr W M : ek LB sp scr W M M.
Proof. intros a _. reflexivity. Qed.
Lemma ek_trans LB sp scr W M1 M2 M3 : ek LB sp scr W M1 M2 -> ek LB sp scr W M2 M3 -> ek LB sp scr W M1 M3.
Proof. intros H1 H2 a Ha. rewrite (H2 a Ha). apply H1. exact Ha. Qed.
Lemma dk_refl LB sp scr M : dk LB sp scr M M.
Proof. intros a _ _ _ D. exact D. Qed.
Lemma dk_trans LB sp scr M1 M2 M3 : dk LB sp scr M1 M2 -> dk LB sp scr M2 M3 -> dk LB sp scr M1 M3.
Proof. intros H1 H2 a Ha C E D. apply (H2 a Ha C E). apply (H1 a Ha C E D). Qed.
Lemma dk_grows LB sp scr M M' : mem_grows M M' -> dk LB sp scr M M'.
Proof. intros G a _ _ _ D. apply G. exact D. Qed.

Lemma client_mono LB LBc sp scr sp' scr' a :
  client_addr L LB sp scr a -> incl LB LBc -> (forall x, sp' - scr' <= x < sp' -> sp - scr <= x < sp) -> client_addr L LBc sp' scr' a.
Proof.
  intros [(b & Hb & Hr)|[[S1 S2]|IM]] Hi Hs.
  - left. exists b. split; [apply Hi; exact Hb| exact Hr].
  - right. left. split; [exact S1|]. intros X. apply S2. apply Hs. exact X.
  - right. right. exact IM.
Qed.
Lemma client_narrow LB sp scr sp' scr' a :
  client_addr L LB sp scr a -> ~ (sp' - scr' <= a < sp') -> client_addr L LB sp' scr' a.
Proof. intros [B|[[S1 S2]|IM]] O; [left; exact B| right; left; split; assumption| right; right; exact IM]. Qed.

Lemma ek_piece LB sp scr W M M' (P : Z -> Prop) :
  (forall a, 0 <= a < 2 ^ 64 -> ~ P a -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) ->
  (forall a, 0 <= a < 2 ^ 64 -> client_addr L LB sp scr a -> ~ in_errno L a -> L5.outside W a -> ~ P a) -> ek LB sp scr W M M'.
Proof. intros E X a (Ha & Hc & He & Ho). apply E; [exact Ha|]. apply X; assumption. Qed.

Lemma ek_piece_in LB sp scr W M M' (P : Z -> Prop) :
  (forall a, 0 <= a < 2 ^ 64 -> ~ P a -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) ->
  L5C.stk (hl_sptop L) M sp scr -> (forall b, In b LB -> fst b + snd b <= hl_ceil L) ->
  (forall a, P a -> (sp - scr <= a < sp) \/ inW W a) -> ek LB sp scr W M M'.
Proof.
  intros E (_ & Hc & _ & Hw & _) HLB FP. apply (ek_piece LB sp scr W M M' P E). intros a Ha CA NE OW Pa.
  destruct (FP a Pa) as [S|I]; [|exact (inW_not_outside W a I OW)].
  destruct CA as [(b & Hb & Hr)|[[S1 S2]|[IM _]]].
  - pose proof (HLB b Hb). lia.
  - exact (S2 S).
  - pose proof (kl_img KL). lia.
Qed.

Lemma ek_piece_in' LB sp scr W M M' (P : Z -> Prop) :
  (forall a, 0 <= a < 2 ^ 64 -> ~ P a -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) ->
  hl_ceil L <= sp - scr -> 0x7fff80000000 <= hl_sptop L -> (forall b, In b LB -> fst b + snd b <= hl_ceil L) ->
  (forall a, P a -> (sp - scr <= a < sp) \/ inW W a) -> ek LB sp scr W M M'.
Proof.
  intros E Hc Hw HLB FP. apply (ek_piece LB sp scr W M M' P E). intros a Ha CA NE OW Pa.
  destruct (FP a Pa) as [S|I]; [|exact (inW_not_outside W a I OW)].
  destruct CA as [(b & Hb & Hr)|[[S1 S2]|[IM _]]].
  - pose proof (HLB b Hb). lia.
  - exact (S2 S).
  - pose proof (kl_img KL). lia.
Qed.

Lemma ek_heap LB LBc sp scr sp' W M M' :
  heap_pres_core L LBc sp' M M' -> incl LB LBc -> sp - scr <= sp' - hl_stack L -> sp' <= sp -> ek LB sp scr W M M'.
Proof.
  intros [P _] Hi H1 H2 a (Ha & Hc & He & _). apply P; [exact Ha| |exact He].
  apply (client_mono LB LBc sp scr sp' (hl_stack L) a Hc Hi). intros x Hx. lia.
Qed.
Lemma dk_heap LB LBc sp scr sp' M M' :
  heap_pres_core L LBc sp' M M' -> incl LB LBc -> sp - scr <= sp' - hl_stack L -> sp' <= sp -> dk LB sp scr M M'.
Proof.
  intros [P D] Hi H1 H2 a Ha Hc He HM. destruct (rng_dec a (sp' - hl_stack L) sp') as [I|O]; [apply D; exact I|].
  rewrite P; [exact HM| exact Ha| | exact He]. apply (client_narrow LBc sp scr sp' (hl_stack L) a); [|exact O].
  apply (client_mono LB LBc sp scr sp scr a Hc Hi). intros x Hx. exact Hx.
Qed.

Lemma ek_callee LB LBc sp scr sp' scr' W W' M M' :
  L5C.hpres L LBc sp' scr' W' M M' -> incl LB LBc -> sp - scr <= sp' - scr' -> sp' <= sp ->
  (forall a, client_addr L LB sp scr a -> L5.outside W a -> L5.outside W' a) -> ek LB sp scr W M M'.
Proof.
  intros HP Hi H1 H2 HW a (Ha & Hc & He & Ho). apply (L5C.hpres_kept L LBc sp' scr' W' M M' a HP).
  split; [exact Ha|]. split; [|split; [exact He| apply HW; assumption]].
  apply (client_mono LB LBc sp scr sp' scr' a Hc Hi). intros x Hx. lia.
Qed.
Lemma dk_callee LB LBc sp scr sp' scr' W' M M' :
  L5C.hpres L LBc sp' scr' W' M M' -> incl LB LBc -> sp - scr <= sp' - scr' -> sp' <= sp -> dk LB sp scr M M'.
Proof.
  intros HP Hi H1 H2 a Ha Hc He HM. destruct (rng_dec a (sp' - scr') sp') as [I|O].
  - pose proof (L5C.hpres_defined L LBc sp' scr' W' M M' HP) as D. replace a with (sp' - scr' + (a - (sp' - scr'))) by lia. apply D. lia.
  - apply (L5C.hpres_cdef L LBc sp' scr' W' M M' a HP Ha); [|exact He| exact HM].
    apply (client_narrow LBc sp scr sp' scr' a); [|exact O]. apply (client_mono LB LBc sp scr sp scr a Hc Hi). intros x Hx. exact Hx.
Qed.

Lemma ek_callee_in LB LBc sp scr sp' scr' W W' M0 M M' :
  L5C.hpres L LBc sp' scr' W' M M' -> incl LB LBc -> sp - scr <= sp' - scr' -> sp' <= sp ->
  L5C.stk (hl_sptop L) M0 sp scr -> (forall b, In b LB -> fst b + snd b <= hl_ceil L) ->
  (forall a, inW W' a -> (sp - scr <= a < sp) \/ inW W a) -> ek LB sp scr W M M'.
Proof.
  intros HP Hi H1 H2 (_ & Hc & _ & Hw & _) HLB FP. apply (ek_callee LB LBc sp scr sp' scr' W W' M M' HP Hi H1 H2).
  intros a CA OW r Hr Hin. destruct (FP a (ex_intro _ r (conj Hr Hin))) as [S|I]; [|exact (inW_not_outside W a I OW)].
  destruct CA as [(b & Hb & Hrb)|[[S1 S2]|[IM _]]].
  - pose proof (HLB b Hb). lia.
  - exact (S2 S).
  - pose proof (kl_img KL). lia.
Qed.
Lemma ek_callee_in' LB LBc sp scr sp' scr' W W' M M' :
  L5C.hpres L LBc sp' scr' W' M M' -> incl LB LBc -> sp - scr <= sp' - scr' -> sp' <= sp ->
  hl_ceil L <= sp - scr -> 0x7fff80000000 <= hl_sptop L -> (forall b, In b LB -> fst b + snd b <= hl_ceil L) ->
  (forall a, inW W' a -> (sp - scr <= a < sp) \/ inW W a) -> ek LB sp scr W M M'.
Proof.
  intros HP Hi H1 H2 Hc Hw HLB FP. apply (ek_callee LB LBc sp scr sp' scr' W W' M M' HP Hi H1 H2).
  intros a CA OW r Hr Hin. destruct (FP a (ex_intro _ r (conj Hr Hin))) as [S|I]; [|exact (inW_not_outside W a I OW)].
  destruct CA as [(b & Hb & Hrb)|[[S1 S2]|[IM _]]].
  - pose proof (HLB b Hb). lia.
  - exact (S2 S).
  - pose proof (kl_img KL). lia.
Qed.

Lemma ek_weaken LB LB2 sp scr sp2 scr2 W W2 M M' :
  ek LB2 sp2 scr2 W2 M M' -> incl LB LB2 -> (forall x, sp2 - scr2 <= x < sp2 -> sp - scr <= x < sp) ->
  (forall a, L5.outside W a -> L5.outside W2 a) -> ek LB sp scr W M M'.
Proof.
  intros E Hi Hs HW a (Ha & Hc & He & Ho). apply E. split; [exact Ha|]. split; [|split; [exact He| apply HW; exact Ho]].
  apply (client_mono LB LB2 sp scr sp2 scr2 a Hc Hi Hs).
Qed.

Lemma stk_call M sp scr sp' scr' :
  L5C.stk (hl_sptop L) M sp scr -> sp' <= sp -> sp - scr <= sp' - scr' -> 0 <= scr' -> sp' mod 16 = 0 -> L5C.stk (hl_sptop L) M sp' scr'.
Proof.
  intros (A16 & B & C & D & W) H1 H2 H3 H4. split; [exact H4|]. split; [lia|]. split; [lia|]. split; [exact D|].
  apply (L5.defined_sub M (sp - scr) scr); [exact W| lia| lia].
Qed.
Lemma stk_after LBc M M' sp scr sp' scr' W' :
  L5C.stk (hl_sptop L) M sp scr -> L5C.hpres L LBc sp' scr' W' M M' -> sp' <= sp -> sp - scr <= sp' - scr' -> 0 <= scr' ->
  L5C.stk (hl_sptop L) M' sp scr.
Proof.
  intros (A16 & B & C & D & W) HP H1 H2 H3. split; [exact A16|]. split; [exact B|]. split; [exact C|]. split; [exact D|].
  intros i Hi. set (a := sp - scr + i). destruct (rng_dec a (sp' - scr') sp') as [I|O].
  - pose proof (L5C.hpres_defined L LBc sp' scr' W' M M' HP) as DD. replace a with (sp' - scr' + (a - (sp' - scr'))) by lia. apply DD. lia.
  - pose proof (kl_img KL) as KI. pose proof (kl_errno KL) as KE.
    apply (L5C.hpres_cdef L LBc sp' scr' W' M M' a HP); [unfold a; lia| | unfold in_errno, a; lia| apply W; exact Hi].
    right. left. split; [unfold a; lia| exact O].
Qed.
Lemma stk_after_heap LBc M M' sp scr sp' :
  L5C.stk (hl_sptop L) M sp scr -> heap_pres_core L LBc sp' M M' -> sp' <= sp -> sp - scr <= sp' - hl_stack L -> 0 <= hl_stack L ->
  L5C.stk (hl_sptop L) M' sp scr.
Proof.
  intros (A16 & B & C & D & W) [P DD] H1 H2 H3. split; [exact A16|]. split; [exact B|]. split; [exact C|]. split; [exact D|].
  intros i Hi. set (a := sp - scr + i). destruct (rng_dec a (sp' - hl_stack L) sp') as [I|O].
  - apply DD. exact I.
  - pose proof (kl_img KL) as KI. pose proof (kl_errno KL) as KE.
    rewrite P; [apply W; exact Hi| unfold a; lia| | unfold in_errno, a; lia]. right. left. split; [unfold a; lia| exact O].
Qed.
Lemma stk_grows M M' sp scr : mem_grows M M' -> L5C.stk (hl_sptop L) M sp scr -> L5C.stk (hl_sptop L) M' sp scr.
Proof. apply L5C.stk_grows. Qed.

Lemma stack_ok_of_stk M sp scr sp' :
  L5C.stk (hl_sptop L) M sp scr -> sp' <= sp -> sp - scr <= sp' - hl_stack L -> 0 <= hl_stack L -> sp' mod 16 = 0 ->
  stack_ok L M sp'.
Proof.
  intros (A16 & B & C & D & W) H1 H2 H3 H4. unfold stack_ok. split; [exact H4|]. split; [lia|]. split; [lia|]. split; [exact D|].
  intros d m Hd Hm. rewrite (kl_segs KL).
  apply (L5C.writable_of_defined segs M (sp' - hl_stack L) (hl_stack L)); [|lia|lia|exact Hd|exact Hm].
  apply (L5.defined_sub M (sp - scr) scr); [exact W| lia| lia].
Qed.

End Kit.
End PMK.
