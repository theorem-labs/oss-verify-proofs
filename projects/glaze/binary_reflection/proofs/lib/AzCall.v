(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
#[local] Ltac Zify.zify ::= WdZS.wd_zs_stock.   (* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4 OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlan OSSVerify.Proofs.glaze.binary_reflection.lib.AzAPS OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AzGPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzIface OSSVerify.Proofs.glaze.binary_reflection.lib.AzContracts OSSVerify.Proofs.glaze.binary_reflection.lib.AzKnowLib OSSVerify.Proofs.glaze.binary_reflection.lib.AzCallLib OSSVerify.Proofs.glaze.binary_reflection.lib.AzNodesAlloc OSSVerify.Proofs.glaze.binary_reflection.lib.AzNodesAlloc2 OSSVerify.Proofs.glaze.binary_reflection.lib.AzNSpec OSSVerify.Proofs.glaze.binary_reflection.lib.AzFrame OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4.AgentLib OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlan OSSVerify.Proofs.glaze.binary_reflection.lib.AzAPS OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AzGPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzIface OSSVerify.Proofs.glaze.binary_reflection.lib.AzContracts OSSVerify.Proofs.glaze.binary_reflection.lib.AzKnowLib OSSVerify.Proofs.glaze.binary_reflection.lib.AzCallLib OSSVerify.Proofs.glaze.binary_reflection.lib.AzNodesAlloc OSSVerify.Proofs.glaze.binary_reflection.lib.AzNodesAlloc2 OSSVerify.Proofs.glaze.binary_reflection.lib.AzNSpec OSSVerify.Proofs.glaze.binary_reflection.lib.AzFrame OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import AX2S. Import AP. Import APS. Import GPS. Import GCL.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition resplit_addr (k : list kentry) (a : saddr) : saddr :=
  let '(b', k') := split_lit (a_base a) in
  if Z.eqb k' 0 then a else
  match base_range k b' with
  | Some (lo, hi) => if (Z.leb 0 (lo + k') && Z.ltb (hi + k') two64)%bool then SA b' (a_off a + k') else a
  | None => a
  end.
Definition kresplit (k : list kentry) (K : kentry) : kentry :=
  match K with
  | KWord a w v => KWord (resplit_addr k a) w v
  | KZero a n => KZero (resplit_addr k a) n
  | KBlob a n b => KBlob (resplit_addr k a) n b
  | KWr a n => KWr (resplit_addr k a) n
  | KDisj a1 n1 a2 n2 => KDisj (resplit_addr k a1) n1 (resplit_addr k a2) n2
  | KFill a n c => KFill (resplit_addr k a) n c
  | KUnk a n => KUnk (resplit_addr k a) n
  | _ => K
  end.

Section Sem.
Variable SEGS : list Segment.
Context {RC : run_ceil}.   (* [comment removed for export] *)
Context {SFL : stk_floor}.   (* [comment removed for export] *)

Lemma resplit_addr_estart : forall E M k a,
  know_ok SEGS E M k -> estart E (resplit_addr k a) = estart E a /\ adenot E (resplit_addr k a) = adenot E a.
Proof.
  intros E M k [b o] HK.
  assert (GEN : forall a', estart E a' = estart E (SA b o) -> estart E a' = estart E (SA b o) /\ adenot E a' = adenot E (SA b o)).
  { intros a' H. split; [exact H|]. unfold adenot, v_addi. unfold estart in H. apply bv_eq.
    rewrite !Z_to_bv_unsigned. cbn [a_base a_off] in *. unfold bv_wrap. f_equal. exact H. }
  apply GEN. unfold resplit_addr. cbn [a_base a_off].
  destruct (split_lit b) as [b' k'] eqn:Hsp. destruct (Z.eqb k' 0); [reflexivity|].
  destruct (base_range k b') as [[lo hi]|] eqn:Hbr; [|reflexivity].
  destruct (Z.leb 0 (lo + k') && Z.ltb (hi + k') two64)%bool eqn:Hc; [|reflexivity].
  apply andb_prop in Hc as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2. unfold two64 in H2.
  pose proof (base_range_sound SEGS E M k b' lo hi HK Hbr) as [B1 B2].
  unfold estart. cbn [a_base a_off]. rewrite (split_lit_denot E b b' k' Hsp). rewrite u64_lit by lia. lia.
Qed.

Lemma kentry_ok_kresplit : forall E M M0 k K,
  know_ok SEGS E M0 k -> kentry_ok SEGS E M K -> kentry_ok SEGS E M (kresplit k K).
Proof.
  intros E M M0 k K HK H.
  destruct K as [a w v|a n|a n kb|lo hi|x m|x lo hi|a n|a1 n1 a2 n2|a n c|a n | a n | fv flo fd]; cbn [kresplit kentry_ok] in *; try exact H;
    unfold flat in *;
    repeat match goal with |- context [estart E (resplit_addr k ?a0)] => rewrite (proj1 (resplit_addr_estart E M0 k a0 HK)) end;
    repeat match goal with |- context [adenot E (resplit_addr k ?a0)] => rewrite (proj2 (resplit_addr_estart E M0 k a0 HK)) end;
    exact H.
Qed.

End Sem.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Entails.
(* [comment removed for export] *)
#[local] Notation "a || b" := (if a then true else b) (at level 50, left associativity, only parsing) : bool_scope.
Variable segs : list Segment.
Variable A : atable.

(* [comment removed for export] *)
Definition kentails (k : list kentry) (fl : option expr) (top : expr) (bud : Z) (K : kentry) : bool :=
  kn_incl1_h A k K
  || match K with
     | KRange e lo hi => APC.kpure_entails k K   (* [comment removed for export] *)
     | KAlign e m => Z.ltb 0 m && Z.eqb (2 ^ ealign k e mod m) 0
     | KWr (SA b o) n => kwritable_x k k b o n && bflat_x k b o n
     | KUnk (SA b o) n => kn_readable_x k b o n && bflat_x k b o n
     | KZero (SA b o) n => kzero_x k k b o n && bflat_x k b o n
     | KDisj (SA b1 o1) n1 (SA b2 o2) n2 => ranges_apart_x k b1 o1 n1 b2 o2 n2
     | KWord (SA b o) w v =>
         Nat.leb 1 w && Nat.leb w 8 && flat_x k b o (ELit (Z.of_nat w))
         && match know_lookup segs k b o w false [] [] with
            | LHit v' [] _ => expr_eqb v v'
            | _ => false
            end
     | KShOk (SA b o) n => kshok_x k b o n   (* [comment removed for export] *)
     | KFpc v lo d => kfpc_entailed segs true k fl top bud v lo d       (* [comment removed for export] *)
     | _ => false
     end%bool.

Definition kentails_all_ref (k : list kentry) (fl : option expr) (top : expr) (bud : Z) (tk : list kentry) : bool := forallb (kentails k fl top bud) tk.
End Entails.

(* [comment removed for export] *)
Section EntailsB.
#[local] Notation "a || b" := (if a then true else b) (at level 50, left associativity, only parsing) : bool_scope.
#[local] Notation "a && b" := (if a then b else false) (at level 40, left associativity, only parsing) : bool_scope.
Variable segs : list Segment.
Variable A : atable.
Definition kn_readable_x_b (bc : AX2B.bctx) (k : list kentry) (rb : expr) (rk : Z) (ne : expr) : bool :=
  AX2B.existsb_lz (fun K => match K with
                    | KUnk (SA kb kk) len | KZero (SA kb kk) len | KFill (SA kb kk) len _ | KBlob (SA kb kk) len _ =>
                        AX2B.xinsideB bc rb rk ne kb kk len
                    | _ => false
                    end) k.
Lemma kn_readable_x_b_fe : forall k, kn_readable_x_b (AX2B.mkbc k) k = kn_readable_x k.
Proof. intros k. do 3 (apply functional_extensionality; intro). unfold kn_readable_x_b, kn_readable_x. rewrite AX2B.existsb_lz_fe, AX2B.xinsideB_eqf. reflexivity. Qed.
Definition kentailsB (bc : AX2B.bctx) (k : list kentry) (fl : option expr) (top : expr) (bud : Z) (K : kentry) : bool :=
  kn_incl1_hB A bc k K
  || match K with
     | KRange e lo hi => APC.kpure_entailsB bc K
     | KAlign e m => Z.ltb 0 m && Z.eqb (2 ^ AX2B.ealignB bc e mod m) 0
     | KWr (SA b o) n => kwritable_xB bc k b o n && bflat_x_b bc b o n
     | KUnk (SA b o) n => kn_readable_x_b bc k b o n && bflat_x_b bc b o n
     | KZero (SA b o) n => kzero_xB bc k b o n && bflat_x_b bc b o n
     | KDisj (SA b1 o1) n1 (SA b2 o2) n2 => AX2B.ranges_apart_xB bc b1 o1 n1 b2 o2 n2
     | KWord (SA b o) w v =>
         Nat.leb 1 w && Nat.leb w 8 && flat_xB bc b o (ELit (Z.of_nat w))
         && match AX2B.know_lookupB segs bc b o w false [] [] with
            | LHit v' [] _ => expr_eqb v v'
            | _ => false
            end
     | KShOk (SA b o) n => kshok_x k b o n
     | KFpc v lo d => kfpc_entailed segs true k fl top bud v lo d
     | _ => false
     end%bool.
(* [comment removed for export] *)
Definition kentailsBH (bc : AX2B.bctx) (kh : list (PrimInt63.int * kentry)) (k : list kentry) (fl : option expr) (top : expr) (bud : Z) (K : kentry) : bool :=
  APC.kn_incl1_hBH A bc kh k K
  || match K with
     | KRange e lo hi => APC.kpure_entailsB bc K
     | KAlign e m => Z.ltb 0 m && Z.eqb (2 ^ AX2B.ealignB bc e mod m) 0
     | KWr (SA b o) n => kwritable_xB bc k b o n && bflat_x_b bc b o n
     | KUnk (SA b o) n => kn_readable_x_b bc k b o n && bflat_x_b bc b o n
     | KZero (SA b o) n => kzero_xB bc k b o n && bflat_x_b bc b o n
     | KDisj (SA b1 o1) n1 (SA b2 o2) n2 => AX2B.ranges_apart_xB bc b1 o1 n1 b2 o2 n2
     | KWord (SA b o) w v =>
         Nat.leb 1 w && Nat.leb w 8 && flat_xB bc b o (ELit (Z.of_nat w))
         && match AX2B.know_lookupB segs bc b o w false [] [] with
            | LHit v' [] _ => expr_eqb v v'
            | _ => false
            end
     | KShOk (SA b o) n => kshok_x k b o n
     | KFpc v lo d => kfpc_entailed segs true k fl top bud v lo d
     | _ => false
     end%bool.
Lemma kentailsBH_eq : forall bc k fl top bud K, kentailsBH bc (APC.khl k) k fl top bud K = kentailsB bc k fl top bud K.
Proof. intros. unfold kentailsBH, kentailsB. rewrite APC.kn_incl1_hBH_eq. reflexivity. Qed.
Lemma kentailsB_eq : forall k fl top bud K, kentailsB (AX2B.mkbc k) k fl top bud K = kentails segs A k fl top bud K.
Proof.
  intros. unfold kentailsB, kentails.
  rewrite ?kn_incl1_hB_eq, ?APC.kpure_entailsB_eq, ?AX2B.ealignB_eqf, ?kwritable_xB_eqf, ?kzero_xB_eqf, ?AX2B.ranges_apart_xB_eqf,
          ?flat_xB_eqf, ?AX2B.know_lookupB_eqf, ?kn_readable_x_b_fe, ?bflat_x_b_fe.
  reflexivity.
Qed.
Definition kentails_all (k : list kentry) (fl : option expr) (top : expr) (bud : Z) (tk : list kentry) : bool :=
  let bc := AX2B.mkbc k in let kh := APC.khl k in AX2B.forallb_lz (kentailsBH bc kh k fl top bud) tk.   (* [comment removed for export] *)
Lemma kentails_all_eq : forall k fl top bud tk, kentails_all k fl top bud tk = kentails_all_ref segs A k fl top bud tk.
Proof.
  intros. unfold kentails_all, kentails_all_ref. cbv zeta. rewrite AX2B.forallb_lz_fe.
  induction tk as [|K tk IH]; [reflexivity|]. cbn [forallb]. rewrite IH, kentailsBH_eq, kentailsB_eq. reflexivity.
Qed.
End EntailsB.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Record gcallee : Type := GCE {
  ce_nxf : nat;            (* [comment removed for export] *)
  ce_tin : acs;            (* [comment removed for export] *)
  ce_touts : list acs;     (* [comment removed for export] *)
  ce_bcap : Z;             (* [comment removed for export] *)
  ce_ccap : Z              (* [comment removed for export] *)
}.

Section Node.
(* [comment removed for export] *)
#[local] Notation "a || b" := (if a then true else b) (at level 50, left associativity, only parsing) : bool_scope.
Variable segs : list Segment.
Variable A : atable.
Variable nx0 : nat.          (* [comment removed for export] *)
Variable bcap ccap : Z.      (* [comment removed for export] *)

Fixpoint ot_set (t : list (option expr)) (i : nat) (c : expr) {struct i} : list (option expr) :=
  match i, t with
  | O, [] => [Some c]
  | O, _ :: r => Some c :: r
  | S i', [] => None :: ot_set [] i' c
  | S i', x :: r => x :: ot_set r i' c
  end.

(* [comment removed for export] *)
Fixpoint bind_regs (nxf : nat) (tr cr : list expr) (acc : list (option expr)) : option (list (option expr)) :=
  match tr, cr with
  | [], [] => Some acc
  | t :: tr', c :: cr' =>
      match t with
      | EVar i =>
          if Nat.ltb i nxf then
            match nth i acc None with
            | None => bind_regs nxf tr' cr' (ot_set acc i c)
            | Some c0 => if expr_eqb c0 c then bind_regs nxf tr' cr' acc else None
            end
          else bind_regs nxf tr' cr' acc
      | _ => bind_regs nxf tr' cr' acc
      end
  | _, _ => None
  end.

(* [comment removed for export] *)
Fixpoint fill_args (acc : list (option expr)) (args : list expr) : option (list expr) :=
  match acc with
  | [] => match args with [] => Some [] | _ => None end
  | Some c :: r => match fill_args r args with Some th => Some (c :: th) | None => None end
  | None :: r => match args with
                 | a :: args' => match fill_args r args' with Some th => Some (a :: th) | None => None end
                 | [] => None
                 end
  end.

Definition bind (ce : gcallee) (args : list expr) (cs : acs) : option (list expr) :=
  match bind_regs (ce_nxf ce) (s_regs (a_ss (ce_tin ce))) (s_regs (a_ss cs)) (repeat None (ce_nxf ce)) with
  | Some acc => if Nat.eqb (length acc) (ce_nxf ce) then fill_args acc args else None
  | None => None
  end.

(* [comment removed for export] *)
Definition out_subst (th : list expr) (nxf ntout v : nat) : list expr :=
  th ++ map (fun j => EVar (v + j)%nat) (seq 0 (ntout - nxf)).

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition prep_ws_ref (k : list kentry) (ws : list (expr * expr)) : list ((expr * expr) * sprep) :=
  map (fun w => let '(wb, wk) := split_lit (fst w) in (w, mk_sprep k wb wk (snd w))) ws.
(* [comment removed for export] *)
Definition prep_ws (k : list kentry) (ws : list (expr * expr)) : list ((expr * expr) * sprep) :=
  let bc := AX2B.mkbc k in
  map (fun w => let '(wb, wk) := split_lit (fst w) in (w, AX2B.mk_sprepB bc wb wk (snd w))) ws.
Lemma prep_ws_eq : forall k ws, prep_ws k ws = prep_ws_ref k ws.
Proof.
  intros k ws. unfold prep_ws, prep_ws_ref. cbv zeta. apply map_ext. intros w. destruct (split_lit (fst w)) as [wb wk].
  rewrite AX2B.mk_sprepB_eqf. reflexivity.
Qed.
Definition apart_ws (k : list kentry) (wsp : list ((expr * expr) * sprep)) (b : expr) (off : Z) (n : expr) : bool :=
  forallb (fun wp => let w := fst wp in let '(wb, wk) := split_lit (fst w) in
                     (ranges_apart_p k (snd wp) wb wk (snd w) b off n || ranges_apart_x k b off n wb wk (snd w))%bool) wsp.
Definition keep_fact_call (G : gtable) (k : list kentry) (keepblocks : list (expr * expr)) (glo : list (expr * expr)) (wsp : list ((expr * expr) * sprep))
           (fl : option expr) (top : expr) (bud : Z) (sp : expr) (K : kentry) : bool :=
  match K with
  | KRange _ _ _ | KAlign _ _ | KDisj _ _ _ _ => true
  | KImg lo hi => Z.leb (g_ro_lo G) lo && Z.leb hi (g_img_hi G) && lit_disjoint lo hi (g_privx G)   (* [comment removed for export] *)
  | KWr _ _ | KUnk _ _ => false      (* [comment removed for export] *)
  | KFpc _ lo _ => lin_ge0 k [(lo, 0)] [(sp, 0)]   (* [comment removed for export] *)
  | _ => match kentry_range K with
         | Some (b, off, n) =>
             (existsb (fun bl => let '(lb, lk) := split_lit (fst bl) in xinside k b off n lb lk (snd bl)) keepblocks
              || above_sp k fl top bud sp b off n
              || img_lit_x G k b off n       (* [comment removed for export] *)
              || existsb (fun g => let '(gb, gk) := split_lit (fst g) in xinside k b off n gb gk (snd g)) glo)   (* [comment removed for export] *)
             && apart_ws k wsp b off n
         | None => false
         end
  end%bool.
(* [comment removed for export] *)
Fixpoint kcut (ws : list (expr * expr)) (k : list kentry) : list kentry :=
  match ws with
  | [] => k
  | w :: ws' => let '(wb, wk) := split_lit (fst w) in kn_cutoutM (kcut ws' k) wb wk (snd w)   (* [comment removed for export] *)
  end.

(* [comment removed for export] *)
Definition sticky_call (k : list kentry) (live : list (expr * expr)) (fl : option expr) (top : expr) (bud : Z) (sp : expr) (K : kentry) : bool :=
  match K with
  | KWr (SA b off) n | KUnk (SA b off) n => owned_x k live fl top bud b off n || above_x k top sp b off n   (* [comment removed for export] *)
  | _ => false
  end%bool.

(* [comment removed for export] *)
Definition apart_ws_b (bc : AX2B.bctx) (wsp : list ((expr * expr) * sprep)) (b : expr) (off : Z) (n : expr) : bool :=
  forallb (fun wp => let w := fst wp in let '(wb, wk) := split_lit (fst w) in
                     if AX2B.ranges_apart_pB bc (snd wp) wb wk (snd w) b off n then true else AX2B.ranges_apart_xB bc b off n wb wk (snd w)) wsp.
Lemma apart_ws_b_eq : forall k wsp b off n, apart_ws_b (AX2B.mkbc k) wsp b off n = apart_ws k wsp b off n.
Proof. intros. unfold apart_ws_b, apart_ws. rewrite AX2B.ranges_apart_pB_eqf, AX2B.ranges_apart_xB_eqf. reflexivity. Qed.
Definition keep_fact_call_b (G : gtable) (bc : AX2B.bctx) (keepblocks : list (expr * expr)) (glo : list (expr * expr)) (wsp : list ((expr * expr) * sprep))
           (fl : option expr) (top : expr) (bud : Z) (sp : expr) (K : kentry) : bool :=
  match K with
  | KRange _ _ _ | KAlign _ _ | KDisj _ _ _ _ => true
  | KImg lo hi => Z.leb (g_ro_lo G) lo && Z.leb hi (g_img_hi G) && lit_disjoint lo hi (g_privx G)
  | KWr _ _ | KUnk _ _ => false
  | KFpc _ lo _ => AX2B.lin_ge0B bc [(lo, 0)] [(sp, 0)]
  | _ => match kentry_range K with
         | Some (b, off, n) =>
             if (if (if (if exists_inside_b bc b off n keepblocks then true else above_sp_b bc fl top bud sp b off n) then true else img_lit_x_b G bc b off n)
                 then true else exists_inside_b bc b off n glo)
             then apart_ws_b bc wsp b off n else false
         | None => false
         end
  end%bool.
Lemma keep_fact_call_b_eq : forall G k keepblocks glo wsp fl top bud sp K,
  keep_fact_call_b G (AX2B.mkbc k) keepblocks glo wsp fl top bud sp K = keep_fact_call G k keepblocks glo wsp fl top bud sp K.
Proof.
  intros. unfold keep_fact_call_b, keep_fact_call.
  destruct K; try reflexivity; try (rewrite AX2B.lin_ge0B_eqf; reflexivity);
    (destruct (kentry_range _) as [[[b off] nn]|]; [|reflexivity]);
    rewrite !exists_inside_b_eq, above_sp_b_eq, img_lit_x_b_eq, apart_ws_b_eq; reflexivity.
Qed.
Definition sticky_call_b (bc : AX2B.bctx) (live : list (expr * expr)) (fl : option expr) (top : expr) (bud : Z) (sp : expr) (K : kentry) : bool :=
  match K with
  | KWr (SA b off) n | KUnk (SA b off) n => if owned_x_b bc live fl top bud b off n then true else above_x_b bc top sp b off n
  | _ => false
  end.
Lemma sticky_call_b_eq : forall k live fl top bud sp K, sticky_call_b (AX2B.mkbc k) live fl top bud sp K = sticky_call k live fl top bud sp K.
Proof. intros. unfold sticky_call_b, sticky_call. destruct K; try reflexivity; destruct a; rewrite owned_x_b_eq, above_x_b_eq; reflexivity. Qed.
Definition kept_sticky_ref (k : list kentry) (live : list (expr * expr)) (fl : option expr) (top : expr) (bud : Z) (sp : expr) (v : nat) : list kentry :=
  List.filter (fun K => kentry_vars_lt v K && sticky_call k live fl top bud sp K)%bool k.
Definition kept_sticky (k : list kentry) (live : list (expr * expr)) (fl : option expr) (top : expr) (bud : Z) (sp : expr) (v : nat) : list kentry :=
  let bc := AX2B.mkbc k in List.filter (fun K => if kentry_vars_lt v K then sticky_call_b bc live fl top bud sp K else false) k.
Lemma kept_sticky_fe : kept_sticky = kept_sticky_ref.
Proof.
  repeat (apply functional_extensionality; intros ?). unfold kept_sticky, kept_sticky_ref. cbv zeta.
  apply filter_ext; intros K; rewrite sticky_call_b_eq; reflexivity.
Qed.
Definition kept_fact_ref (G : gtable) (k : list kentry) (keepblocks glo : list (expr * expr)) (wsp : list ((expr * expr) * sprep))
           (fl : option expr) (top : expr) (bud : Z) (sp : expr) (v : nat) (ws : list (expr * expr)) : list kentry :=
  List.filter (fun K => kentry_vars_lt v K && keep_fact_call G k keepblocks glo wsp fl top bud sp K)%bool (kcut ws k).
Definition kept_fact (G : gtable) (k : list kentry) (keepblocks glo : list (expr * expr)) (wsp : list ((expr * expr) * sprep))
           (fl : option expr) (top : expr) (bud : Z) (sp : expr) (v : nat) (ws : list (expr * expr)) : list kentry :=
  let bc := AX2B.mkbc k in List.filter (fun K => if kentry_vars_lt v K then keep_fact_call_b G bc keepblocks glo wsp fl top bud sp K else false) (kcut ws k).
Lemma kept_fact_fe : kept_fact = kept_fact_ref.
Proof.
  repeat (apply functional_extensionality; intros ?). unfold kept_fact, kept_fact_ref. cbv zeta.
  apply filter_ext; intros K; rewrite keep_fact_call_b_eq; reflexivity.
Qed.

(* [comment removed for export] *)
Fixpoint remove_pair (p : expr * expr) (l : list (expr * expr)) : option (list (expr * expr)) :=
  match l with
  | [] => None
  | q :: r => if pair_eqb p q then Some r else match remove_pair p r with Some r' => Some (q :: r') | None => None end
  end.
Fixpoint remove_pairs (ps : list (expr * expr)) (l : list (expr * expr)) : option (list (expr * expr)) :=
  match ps with
  | [] => Some l
  | p :: ps' => match remove_pair p l with Some l' => remove_pairs ps' l' | None => None end
  end.

(* [comment removed for export] *)
Definition acs_eqb_nopc (t t' : acs) : bool :=
  (list_eqb expr_eqb (s_regs (a_ss t)) (s_regs (a_ss t'))
   && list_eqb kentry_eqb (kn t) (kn t')
   && Nat.eqb (nxt t) (nxt t')
   && match s_log (a_ss t), s_log (a_ss t') with [], [] => true | _, _ => false end
   && list_eqb pair_eqb (a_vis t) (a_vis t') && list_eqb pair_eqb (a_ghost t) (a_ghost t')
   && expr_eqb (a_brk t) (a_brk t') && Z.eqb (a_ylo t) (a_ylo t') && list_eqb amap_eqb (a_maps t) (a_maps t')   (* [comment removed for export] *)
   && list_eqb pair_eqb (a_fake t) (a_fake t') && expr_eqb (a_meter t) (a_meter t') && afd_eqb (a_fd t) (a_fd t')
   && expr_eqb (a_fbud t) (a_fbud t'))%bool.   (* [comment removed for export] *)
Definition touts_agree (touts : list acs) : bool :=
  match touts with
  | [] => false
  | t :: r => forallb (acs_eqb_nopc t) r
  end.

(* [comment removed for export] *)
Definition is_ret_at (p : Z) : bool :=
  match itab_lookup (mk_itab_ranges segs [(p, 1%nat)]) p with
  | Some (Jalr rd rs imm) => bv_eqb rd 0%bv && bv_eqb rs (Z_to_bv 5 1) && Z.eqb (bv_signed imm) 0
  | _ => false
  end%bool.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition kdisj_new (newbl others : list (expr * expr)) : list kentry :=
  flat_map (fun nb => map (fun ob => KDisj (SA (fst nb) 0) (snd nb) (SA (fst ob) 0) (snd ob)) others) newbl.
(* [comment removed for export] *)
Definition kdisj_gh (kn : list kentry) (newbl ghosts : list (expr * expr)) : list kentry :=
  flat_map (fun nb => match xlo kn (snd nb) with
                      | Some l => if Z.leb 1 l then map (fun g => KDisj (SA (fst nb) 0) (snd nb) (SA (fst g) 0) (snd g)) ghosts else []
                      | None => []
                      end) newbl.

(* [comment removed for export] *)
Definition wsok_ref (G : gtable) (ce : gcallee) (k : list kentry) (cs tin : acs) (th : list expr) (nxf : nat)
           (keepblocks ws : list (expr * expr)) (top sp : expr) : bool :=
  (forallb (fun w => let '(wb, wk) := split_lit (fst w) in
                            owned_sp_x k ((keepblocks ++ map ffus (a_fake cs)) ++ a_ghost cs) (acs_floor (a_maps cs)) (a_brk cs) (a_ylo cs) sp wb wk (snd w) && bflat_x k wb wk (snd w)   (* [comment removed for export] *)
                            && ranges_apart_x k wb wk (snd w) (ELit 0) (g_img_lo G) (ELit (g_img_hi G - g_img_lo G))   (* [comment removed for export] *)
                            && win_lo47 k wb wk (snd w)) ws                                       (* [comment removed for export] *)
                 && forallb (fun bl => let '(lb, lk) := split_lit (fst bl) in bflat_x k lb lk (snd bl)) ((keepblocks ++ map ffus (a_fake cs)) ++ a_ghost cs)
                 && forallb (fun bl => let '(lb, lk) := split_lit (fst bl) in bflat_x k lb lk (snd bl)) (a_fake cs)     (* [comment removed for export] *)
                 && expr_eqb top sp
                 && Z.leb 0 (a_ylo tin)
                 && (let '(spb, spk) := split_lit sp in
                     (* [comment removed for export] *)
                     let yreq := match acs_floor (a_maps tin) with None => Z.max MSTK (a_ylo tin) | Some _ => MSTK end in
                     in_floor k (acs_floor (a_maps cs)) (a_brk cs) (a_ylo cs) spb (spk - yreq) (ELit yreq) && bflat_x k spb spk (ELit 0)
                     && match acs_floor (a_maps tin) with
                        | None => true
                        | Some f' => maps_vars_lt nxf (a_maps tin) && in_floor k (acs_floor (a_maps cs)) (a_brk cs) (a_ylo cs) (tsubst th f') 0 (ELit 1)
                        end)
                 && match cost_hi k keepblocks with Some ch => Z.leb 0 ch && Z.leb (ch + ce_bcap ce) bcap | None => false end
                 && Z.leb (Z.of_nat (length keepblocks) + ce_ccap ce) ccap
                 && Z.leb 0 (ce_bcap ce) && Z.leb 0 (ce_ccap ce))%bool.
Definition kept_shadow_ref (G : gtable) (k : list kentry) (objs : list (expr * expr)) (fl : option expr) (top : expr) (bud : Z) (sp : expr) (v : nat) : list kentry :=
  List.filter (fun K => kentry_vars_lt v K && keep_shadow G k objs fl top bud sp K)%bool k.
Section WsokLazy.
#[local] Notation "a && b" := (if a then b else false) (at level 40, left associativity, only parsing) : bool_scope.
Definition owned_sp_x_b (bc : AX2B.bctx) (live : list (expr * expr)) (fl : option expr) (top : expr) (bud : Z) (sp : expr) (b : expr) (off : Z) (n : expr) : bool :=
  exists_inside_b bc b off n live || (in_floorB bc fl top bud b off n && AX2B.lin_ge0B bc [(b, off)] [(sp, 0%Z)]).
Lemma owned_sp_x_b_fe : forall k, owned_sp_x_b (AX2B.mkbc k) = owned_sp_x k.
Proof.
  intros k. do 8 (apply functional_extensionality; intro). unfold owned_sp_x_b, owned_sp_x.
  rewrite exists_inside_b_eq, in_floorB_eqf, AX2B.lin_ge0B_eqf. reflexivity.
Qed.
Definition win_lo47_b (bc : AX2B.bctx) (b : expr) (off : Z) (n : expr) : bool :=
  match AX2B.xhiB bc (eaddz b off), AX2B.xhiB bc n with Some h, Some m => Z.ltb (h + m) two64 && Z.leb (send_hi_b bc b off n (h + m)) two47 | _, _ => false end%bool.
Lemma win_lo47_b_fe : forall k, win_lo47_b (AX2B.mkbc k) = win_lo47 k.
Proof. intros k. do 3 (apply functional_extensionality; intro). unfold win_lo47_b, win_lo47. rewrite AX2B.xhiB_eqf, send_hi_b_fe. reflexivity. Qed.
Fixpoint cost_hi_b (bc : AX2B.bctx) (live : list (expr * expr)) : option Z :=
  match live with
  | [] => Some 0
  | (_, n) :: r => match AX2B.xhiB bc n, cost_hi_b bc r with Some h, Some c => Some (h + MBLK + c) | _, _ => None end
  end.
Lemma cost_hi_b_eq : forall k live, cost_hi_b (AX2B.mkbc k) live = cost_hi k live.
Proof. intros k live. induction live as [|[x n] r IH]; [reflexivity|]. cbn [cost_hi_b cost_hi]. rewrite IH, AX2B.xhiB_eqf. reflexivity. Qed.
Definition wsok (G : gtable) (ce : gcallee) (k : list kentry) (cs tin : acs) (th : list expr) (nxf : nat)
           (keepblocks ws : list (expr * expr)) (top sp : expr) : bool :=
  let bc := AX2B.mkbc k in
  (AX2B.forallb_lz (fun w => let '(wb, wk) := split_lit (fst w) in
                            owned_sp_x_b bc ((keepblocks ++ map ffus (a_fake cs)) ++ a_ghost cs) (acs_floor (a_maps cs)) (a_brk cs) (a_ylo cs) sp wb wk (snd w) && bflat_x_b bc wb wk (snd w)   (* [comment removed for export] *)
                            && AX2B.ranges_apart_xB bc wb wk (snd w) (ELit 0) (g_img_lo G) (ELit (g_img_hi G - g_img_lo G))   (* [comment removed for export] *)
                            && win_lo47_b bc wb wk (snd w)) ws                                       (* [comment removed for export] *)
                 && AX2B.forallb_lz (fun bl => let '(lb, lk) := split_lit (fst bl) in bflat_x_b bc lb lk (snd bl)) ((keepblocks ++ map ffus (a_fake cs)) ++ a_ghost cs)
                 && AX2B.forallb_lz (fun bl => let '(lb, lk) := split_lit (fst bl) in bflat_x_b bc lb lk (snd bl)) (a_fake cs)     (* [comment removed for export] *)
                 && expr_eqb top sp
                 && Z.leb 0 (a_ylo tin)
                 && (let '(spb, spk) := split_lit sp in
                     (* [comment removed for export] *)
                     let yreq := match acs_floor (a_maps tin) with None => Z.max MSTK (a_ylo tin) | Some _ => MSTK end in
                     in_floorB bc (acs_floor (a_maps cs)) (a_brk cs) (a_ylo cs) spb (spk - yreq) (ELit yreq) && bflat_x_b bc spb spk (ELit 0)
                     && match acs_floor (a_maps tin) with
                        | None => true
                        | Some f' => maps_vars_lt nxf (a_maps tin) && in_floorB bc (acs_floor (a_maps cs)) (a_brk cs) (a_ylo cs) (tsubst th f') 0 (ELit 1)
                        end)
                 && match cost_hi_b bc keepblocks with Some ch => Z.leb 0 ch && Z.leb (ch + ce_bcap ce) bcap | None => false end
                 && Z.leb (Z.of_nat (length keepblocks) + ce_ccap ce) ccap
                 && Z.leb 0 (ce_bcap ce) && Z.leb 0 (ce_ccap ce))%bool.
Lemma wsok_fe : wsok = wsok_ref.
Proof.
  do 11 (apply functional_extensionality; intro). unfold wsok, wsok_ref. cbv zeta.
  rewrite ?AX2B.forallb_lz_fe, ?owned_sp_x_b_fe, ?bflat_x_b_fe, ?AX2B.ranges_apart_xB_eqf, ?win_lo47_b_fe, ?in_floorB_eqf, ?cost_hi_b_eq.
  reflexivity.
Qed.
Definition kept_shadow (G : gtable) (k : list kentry) (objs : list (expr * expr)) (fl : option expr) (top : expr) (bud : Z) (sp : expr) (v : nat) : list kentry :=
  let bc := AX2B.mkbc k in List.filter (fun K => if kentry_vars_lt v K then keep_shadow_b G bc objs fl top bud sp K else false) k.
Lemma kept_shadow_fe : kept_shadow = kept_shadow_ref.
Proof.
  do 8 (apply functional_extensionality; intro). unfold kept_shadow, kept_shadow_ref. cbv zeta. apply filter_ext. intros K.
  rewrite keep_shadow_b_eq. destruct (kentry_vars_lt _ K); reflexivity.
Qed.
End WsokLazy.

Definition node_call (G : gtable) (ce : gcallee) (args : list expr) (cs : acs) : option acs :=
  let tin := ce_tin ce in let nxf := ce_nxf ce in
  match ce_touts ce with
  | [] => None
  | tout :: _ =>
  if negb (Z.eqb (pc cs) (pc tin) && fresh_ok nx0 cs && touts_agree (ce_touts ce)
           && forallb (fun t => is_ret_at (pc t)) (ce_touts ce)
           && Nat.eqb (length (s_regs (a_ss cs))) 32 && Nat.eqb (length (s_regs (a_ss tin))) 32
           && Nat.eqb (length (s_regs (a_ss tout))) 32
           && match s_log (a_ss tin), s_log (a_ss tout) with [], [] => true | _, _ => false end
           && Nat.leb nxf (nxt tout) && kn_vars_lt (nxt tout) (kn tout) && sr_vars_lt (nxt tout) (s_regs (a_ss tout))
           && pairs_vars_lt (nxt tout) (a_vis tout)
           && kn_vars_lt nxf (kn tin) && pairs_vars_lt nxf (a_vis tin) && pairs_vars_lt nxf (a_ghost tin)
           && expr_vars_lt nxf (a_brk tin)
           && list_eqb pair_eqb (a_ghost tin) (a_ghost tout) && expr_eqb (a_brk tin) (a_brk tout))%bool
  then None else
  (* [comment removed for export] *)
  if negb (match a_fake tin, a_fake tout with [], [] => true | _, _ => false end
           && afd_eqb (a_fd tin) FdStd && afd_eqb (a_fd tout) FdStd && afd_eqb (a_fd cs) FdStd
           && expr_vars_lt nxf (a_meter tin) && expr_vars_lt (nxt tout) (a_meter tout)
           && Z.leb 3 (ealign (kn cs) (reg cs 2))           (* [comment removed for export] *)
           && expr_vars_lt nxf (a_fbud tin) && expr_vars_lt (nxt tout) (a_fbud tout))%bool     (* [comment removed for export] *)
  then None else
  match bind ce args cs with
  | None => None
  | Some th =>
    if negb (forallb (expr_vars_lt (nxt cs)) th && Nat.eqb (length th) nxf)%bool then None else
    let k := kn cs in let sp := reg cs 2 in
    (* [comment removed for export] *)
    if negb (list_eqb expr_eqb (map (tsubst th) (s_regs (a_ss tin))) (s_regs (a_ss cs))
             && expr_eqb (tsubst th (a_meter tin)) (a_meter cs)
             && lin_ge0 k [(a_fbud cs, 0)] [(tsubst th (a_fbud tin), 0)])%bool then None else   (* [comment removed for export] *)
    (* [comment removed for export] *)
    match ret_lit cs, nth 1 (s_regs (a_ss tout)) (ELit 0), nth 1 (s_regs (a_ss tin)) (ELit 0) with
    | Some ret, EVar r1, EVar r1' =>
      if negb (Nat.eqb r1 r1' && Nat.ltb r1 nxf)%bool then None else
      (* [comment removed for export] *)
      if negb (kentails_all segs A k (acs_floor (a_maps cs)) (a_brk cs) (a_ylo cs) (map (ktsubst th) (kn tin))) then None else
      (* [comment removed for export] *)
      let passed := map (ptsubst th) (a_vis tin) in
      match remove_pairs passed (a_vis cs) with
      | None => None
      | Some keepblocks =>
        let ws := map (ptsubst th) (a_ghost tin) in
        let top := tsubst th (a_brk tin) in
        (* [comment removed for export] *)
        if negb (wsok G ce k cs tin th nxf keepblocks ws top sp)
        then None else
        (* [comment removed for export] *)
        let v := nxt cs in
        let th' := out_subst th nxf (nxt tout) v in
        let glo := ghosts_lo G k (acs_floor (a_maps cs)) (a_brk cs) (a_ylo cs) (a_ghost cs) in   (* [comment removed for export] *)
        let wsp := prep_ws k ws in                                                                 (* [comment removed for export] *)
        let kept := kept_sticky k ((keepblocks ++ a_fake cs) ++ a_ghost cs) (acs_floor (a_maps cs)) (a_brk cs) (a_ylo cs) sp v   (* [comment removed for export] *)
                    ++ kept_fact G k (keepblocks ++ a_fake cs) glo wsp (acs_floor (a_maps cs)) (a_brk cs) (a_ylo cs) sp v ws
                    ++ kept_shadow G k (keepblocks ++ a_fake cs ++ glo) (acs_floor (a_maps cs)) (a_brk cs) (a_ylo cs) sp v   (* [comment removed for export] *)
                    ++ kdisj_new (map (ptsubst th') (a_vis tout)) (keepblocks ++ a_fake cs) in   (* [comment removed for export] *)
        let post := map (kresplit k) (map (ktsubst th') (kn tout)) ++ kept in
        Some (ACS (mk_ss ret (map (tsubst th') (s_regs (a_ss tout))) (post ++ kdisj_gh post (map (ptsubst th') (a_vis tout)) (ghosts_ne k (a_ghost cs)))
                         (v + (nxt tout - nxf))%nat)
                  (a_maps cs) (a_totsz cs) (a_ylo cs) (a_eager cs)
                  (keepblocks ++ map (ptsubst th') (a_vis tout)) (a_ghost cs) (a_abytes cs) (a_brk cs) (a_fd cs) (a_tidset cs)
                  (tsubst th' (a_meter tout)) (a_fake cs) (a_fbud cs))     (* [comment removed for export] *)
      end
    | _, _, _ => None
    end
  end
  end.
(* [comment removed for export] *)
Definition call_share (G : gtable) (ce : gcallee) (args : list expr) (cs : acs) : option (bool * option (bool * (list kentry * list kentry * list kentry))) :=
  let tin := ce_tin ce in let nxf := ce_nxf ce in
  match bind ce args cs with
  | None => None
  | Some th =>
    let k := kn cs in let sp := reg cs 2 in
    Some (kentails_all segs A k (acs_floor (a_maps cs)) (a_brk cs) (a_ylo cs) (map (ktsubst th) (kn tin)),
      let passed := map (ptsubst th) (a_vis tin) in
      match remove_pairs passed (a_vis cs) with
      | None => None
      | Some keepblocks =>
        let ws := map (ptsubst th) (a_ghost tin) in
        let top := tsubst th (a_brk tin) in
        let v := nxt cs in
        let glo := ghosts_lo G k (acs_floor (a_maps cs)) (a_brk cs) (a_ylo cs) (a_ghost cs) in
        let wsp := prep_ws k ws in
        Some ((wsok G ce k cs tin th nxf keepblocks ws top sp),
              (kept_sticky k ((keepblocks ++ a_fake cs) ++ a_ghost cs) (acs_floor (a_maps cs)) (a_brk cs) (a_ylo cs) sp v,
               kept_fact G k (keepblocks ++ a_fake cs) glo wsp (acs_floor (a_maps cs)) (a_brk cs) (a_ylo cs) sp v ws,
               kept_shadow G k (keepblocks ++ a_fake cs ++ glo) (acs_floor (a_maps cs)) (a_brk cs) (a_ylo cs) sp v))
      end)
  end.
Definition node_callS (sh : option (bool * option (bool * (list kentry * list kentry * list kentry)))) (G : gtable) (ce : gcallee) (args : list expr) (cs : acs) : option acs :=
  let tin := ce_tin ce in let nxf := ce_nxf ce in
  match ce_touts ce with
  | [] => None
  | tout :: _ =>
  if negb (Z.eqb (pc cs) (pc tin) && fresh_ok nx0 cs && touts_agree (ce_touts ce)
           && forallb (fun t => is_ret_at (pc t)) (ce_touts ce)
           && Nat.eqb (length (s_regs (a_ss cs))) 32 && Nat.eqb (length (s_regs (a_ss tin))) 32
           && Nat.eqb (length (s_regs (a_ss tout))) 32
           && match s_log (a_ss tin), s_log (a_ss tout) with [], [] => true | _, _ => false end
           && Nat.leb nxf (nxt tout) && kn_vars_lt (nxt tout) (kn tout) && sr_vars_lt (nxt tout) (s_regs (a_ss tout))
           && pairs_vars_lt (nxt tout) (a_vis tout)
           && kn_vars_lt nxf (kn tin) && pairs_vars_lt nxf (a_vis tin) && pairs_vars_lt nxf (a_ghost tin)
           && expr_vars_lt nxf (a_brk tin)
           && list_eqb pair_eqb (a_ghost tin) (a_ghost tout) && expr_eqb (a_brk tin) (a_brk tout))%bool
  then None else
  (* [comment removed for export] *)
  if negb (match a_fake tin, a_fake tout with [], [] => true | _, _ => false end
           && afd_eqb (a_fd tin) FdStd && afd_eqb (a_fd tout) FdStd && afd_eqb (a_fd cs) FdStd
           && expr_vars_lt nxf (a_meter tin) && expr_vars_lt (nxt tout) (a_meter tout)
           && Z.leb 3 (ealign (kn cs) (reg cs 2))           (* [comment removed for export] *)
           && expr_vars_lt nxf (a_fbud tin) && expr_vars_lt (nxt tout) (a_fbud tout))%bool     (* [comment removed for export] *)
  then None else
  match bind ce args cs with
  | None => None
  | Some th =>
    if negb (forallb (expr_vars_lt (nxt cs)) th && Nat.eqb (length th) nxf)%bool then None else
    let k := kn cs in let sp := reg cs 2 in
    (* [comment removed for export] *)
    if negb (list_eqb expr_eqb (map (tsubst th) (s_regs (a_ss tin))) (s_regs (a_ss cs))
             && expr_eqb (tsubst th (a_meter tin)) (a_meter cs)
             && lin_ge0 k [(a_fbud cs, 0)] [(tsubst th (a_fbud tin), 0)])%bool then None else   (* [comment removed for export] *)
    (* [comment removed for export] *)
    match ret_lit cs, nth 1 (s_regs (a_ss tout)) (ELit 0), nth 1 (s_regs (a_ss tin)) (ELit 0) with
    | Some ret, EVar r1, EVar r1' =>
      if negb (Nat.eqb r1 r1' && Nat.ltb r1 nxf)%bool then None else
      (* [comment removed for export] *)
      if negb (match sh with Some (e, _) => e | None => kentails_all segs A k (acs_floor (a_maps cs)) (a_brk cs) (a_ylo cs) (map (ktsubst th) (kn tin)) end) then None else
      (* [comment removed for export] *)
      let passed := map (ptsubst th) (a_vis tin) in
      match remove_pairs passed (a_vis cs) with
      | None => None
      | Some keepblocks =>
        let ws := map (ptsubst th) (a_ghost tin) in
        let top := tsubst th (a_brk tin) in
        (* [comment removed for export] *)
        if negb (match sh with Some (_, Some (c0, _)) => c0 | _ =>
                 (wsok G ce k cs tin th nxf keepblocks ws top sp) end)
        then None else
        (* [comment removed for export] *)
        let v := nxt cs in
        let th' := out_subst th nxf (nxt tout) v in
        (* [comment removed for export] *)
        let kept := (match sh with Some (_, Some (_, (f1, _, _))) => f1 | _ => kept_sticky k ((keepblocks ++ a_fake cs) ++ a_ghost cs) (acs_floor (a_maps cs)) (a_brk cs) (a_ylo cs) sp v end)
                    ++ (match sh with Some (_, Some (_, (_, f2, _))) => f2 | _ => kept_fact G k (keepblocks ++ a_fake cs) (ghosts_lo G k (acs_floor (a_maps cs)) (a_brk cs) (a_ylo cs) (a_ghost cs)) (prep_ws k ws) (acs_floor (a_maps cs)) (a_brk cs) (a_ylo cs) sp v ws end)
                    ++ (match sh with Some (_, Some (_, (_, _, f3))) => f3 | _ => kept_shadow G k (keepblocks ++ a_fake cs ++ (ghosts_lo G k (acs_floor (a_maps cs)) (a_brk cs) (a_ylo cs) (a_ghost cs))) (acs_floor (a_maps cs)) (a_brk cs) (a_ylo cs) sp v end)
                    ++ kdisj_new (map (ptsubst th') (a_vis tout)) (keepblocks ++ a_fake cs) in   (* [comment removed for export] *)
        let post := map (kresplit k) (map (ktsubst th') (kn tout)) ++ kept in
        Some (ACS (mk_ss ret (map (tsubst th') (s_regs (a_ss tout))) (post ++ kdisj_gh post (map (ptsubst th') (a_vis tout)) (ghosts_ne k (a_ghost cs)))
                         (v + (nxt tout - nxf))%nat)
                  (a_maps cs) (a_totsz cs) (a_ylo cs) (a_eager cs)
                  (keepblocks ++ map (ptsubst th') (a_vis tout)) (a_ghost cs) (a_abytes cs) (a_brk cs) (a_fd cs) (a_tidset cs)
                  (tsubst th' (a_meter tout)) (a_fake cs) (a_fbud cs))     (* [comment removed for export] *)
      end
    | _, _, _ => None
    end
  end
  end.
(* [comment removed for export] *)
Record gcallee2 : Type := GCE2 {
  c2_nxf : nat; c2_tin : acs; c2_touts0 : list acs; c2_touts1 : list acs; c2_bcap : Z; c2_ccap : Z }.
Definition c2_class0 (c : gcallee2) : gcallee := GCE (c2_nxf c) (c2_tin c) (c2_touts0 c) (c2_bcap c) (c2_ccap c).
Definition c2_class1 (c : gcallee2) : gcallee := GCE (c2_nxf c) (c2_tin c) (c2_touts1 c) (c2_bcap c) (c2_ccap c).
Definition c2_merged (c : gcallee2) : gcallee := GCE (c2_nxf c) (c2_tin c) (c2_touts0 c ++ c2_touts1 c) (c2_bcap c) (c2_ccap c).
Definition node_call2 (G : gtable) (c : gcallee2) (args : list expr) (cs : acs) : option (acs * acs) :=
  match node_call G (c2_class0 c) args cs, node_call G (c2_class1 c) args cs with
  | Some a, Some b => Some (a, b)
  | _, _ => None
  end.
Definition node_call2F (G : gtable) (c : gcallee2) (args : list expr) (cs : acs) : option (acs * acs) :=
  let sh := call_share G (c2_class0 c) args cs in
  match node_callS sh G (c2_class0 c) args cs, node_callS sh G (c2_class1 c) args cs with
  | Some a, Some b => Some (a, b)
  | _, _ => None
  end.
(* [comment removed for export] *)
Definition node_call2_cond (G : gtable) (COND : acs -> list expr -> bool) (c : gcallee2) (args : list expr) (cs : acs) : option (acs * acs) :=
  match bind (c2_class0 c) args cs with
  | Some th => if COND cs th then node_call2 G c args cs else None
  | None => None
  end.
(* [comment removed for export] *)
Lemma node_callS_eq : forall G ce args cs, node_callS (call_share G ce args cs) G ce args cs = node_call G ce args cs.
Proof.
  intros G ce args cs. unfold node_callS, node_call, call_share. cbv zeta.
  destruct (ce_touts ce) as [|tout touts]; [reflexivity|].
  destruct (bind ce args cs) as [th|]; [|reflexivity].
  destruct (remove_pairs (map (ptsubst th) (a_vis (ce_tin ce))) (a_vis cs)) as [keepblocks|]; cbv beta iota; reflexivity.
Qed.
Lemma node_call2F_eq : forall G c args cs, node_call2F G c args cs = node_call2 G c args cs.
Proof.
  intros G c args cs. unfold node_call2F, node_call2. cbv zeta.
  rewrite (node_callS_eq G (c2_class0 c) args cs).
  change (call_share G (c2_class0 c) args cs) with (call_share G (c2_class1 c) args cs).
  rewrite (node_callS_eq G (c2_class1 c) args cs). reflexivity.
Qed.
End Node.


(* [comment removed for export] *)
Lemma apart_ws_sem : forall k ws b off n, apart_ws k (prep_ws k ws) b off n = true ->
  forall w, In w ws -> let '(wb, wk) := split_lit (fst w) in
    ranges_apart_x k wb wk (snd w) b off n = true \/ ranges_apart_x k b off n wb wk (snd w) = true.
Proof.
  intros k ws b off n H w Hin. rewrite prep_ws_eq in H. unfold apart_ws in H.
  pose proof (proj1 (forallb_forall _ _) H (let '(wb, wk) := split_lit (fst w) in (w, mk_sprep k wb wk (snd w)))
                ltac:(unfold prep_ws_ref; apply in_map_iff; exists w; split; [reflexivity | exact Hin])) as X.
  destruct (split_lit (fst w)) as [wb wk] eqn:Hs. cbn [fst snd] in X. rewrite Hs in X.
  apply orb_prop in X as [X|X]; [left | right; exact X].
  rewrite AX2S.ranges_apart_p_eq in X. exact X.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Sound.
Variable SEGS : list Segment.
Context {RC : run_ceil}.   (* [comment removed for export] *)
Context {SFL : stk_floor}.   (* [comment removed for export] *)
Variable A : atable.
Hypothesis SEGS_in_hull : forall a : word, APS.in_hull A (bv_unsigned a) = false -> find_segment SEGS (bv_unsigned a) 1 = None.
Hypothesis HULL_ok : APS.hull_ok A.
(* [comment removed for export] *)
Variable G : gtable.
Hypothesis A_img_hi : img_hi A = g_img_hi G.
Hypothesis A_img_lo : img_lo A = g_img_lo G.
Hypothesis G_img_shlo : g_img_hi G <= SHMAPLO.

(* [comment removed for export] *)

Lemma kn_readable_x_sound : forall E M k sb sk ne,
  know_ok SEGS E M k -> kn_readable_x k sb sk ne = true ->
  0 <= estart E (SA sb sk) /\ estart E (SA sb sk) + elenZ E ne <= 2 ^ 64
  /\ forall i, 0 <= i < elenZ E ne -> M (Z_to_bv 64 (estart E (SA sb sk) + i)) <> None.
Proof.
  intros E M k sb sk ne HK H. unfold kn_readable_x in H. apply existsb_exists in H as [K [HinK HKt]].
  pose proof (proj1 (Forall_forall _ _) HK K HinK) as HKK.
  pose proof (u64_range (edenot E ne)) as Hne. unfold elenZ in *.
  assert (GEN : forall kb kk len (P : option byte -> Prop),
            xinside k sb sk ne kb kk len = true ->
            flat E (SA kb kk) (bv_unsigned (edenot E len)) ->
            (forall i, 0 <= i < bv_unsigned (edenot E len) -> P (M (Z_to_bv 64 (estart E (SA kb kk) + i)))) ->
            (forall x, P x -> x <> None) ->
            0 <= estart E (SA sb sk) /\ estart E (SA sb sk) + bv_unsigned (edenot E ne) <= 2 ^ 64
            /\ forall i, 0 <= i < bv_unsigned (edenot E ne) -> M (Z_to_bv 64 (estart E (SA sb sk) + i)) <> None).
  { intros kb kk len P Hx Hfl HP HPn.
    destruct (xinside_sound SEGS E M k sb sk ne kb kk len HK Hx) as [X1 X2]. unfold elenZ in X2.
    destruct Hfl as (F1 & F2 & F3 & F4).
    split; [lia|]. split; [lia|]. intros i Hi.
    replace (estart E (SA sb sk) + i) with (estart E (SA kb kk) + (estart E (SA sb sk) - estart E (SA kb kk) + i)) by lia.
    apply HPn. apply HP. lia. }
  destruct K as [|[kb kk] len|[kb kk] len j| | | | | |[kb kk] len c|[kb kk] len | [kb kk] len | fv flo fd]; try discriminate; cbn [kentry_ok] in HKK; unfold elenZ in HKK.
  - destruct HKK as [Hfl Hz]. eapply (GEN kb kk len (fun x => x = Some (Z_to_bv 8 0))); [exact HKt | exact Hfl | exact Hz | intros x ->; discriminate].
  - destruct HKK as (Hfl & Hl & Hz). eapply (GEN kb kk len (fun x => exists b, x = Some b)); [exact HKt | exact Hfl | | intros x [b ->]; discriminate].
    intros i Hi. eexists. apply Hz. exact Hi.
  - destruct HKK as [Hfl Hz]. eapply (GEN kb kk len (fun x => x = Some (Z_to_bv 8 c))); [exact HKt | exact Hfl | exact Hz | intros x ->; discriminate].
  - destruct HKK as [Hfl Hz]. eapply (GEN kb kk len (fun x => x <> None)); [exact HKt | exact Hfl | exact Hz | intros x Hx; exact Hx].
Qed.

Lemma kentails_sound : forall E M k fl top bud K,
  know_ok SEGS E M k -> GPS.floor_sem E fl top bud -> kentails SEGS A k fl top bud K = true -> kentry_ok SEGS E M K.
Proof.
  intros E M k fl top bud K HK Hfsem H. unfold kentails in H. apply orb_prop in H as [H|H].
  { assert (H1 : kn_incl_h A k [K] = true) by (unfold kn_incl_h; cbn [forallb]; rewrite H; reflexivity).
    pose proof (kn_incl_h_sound SEGS A SEGS_in_hull HULL_ok E M k [K] HK H1) as X. exact (Forall_inv X). }
  destruct K as [[b o] w v|[b o] n|a n kb|lo hi|e m|e lo hi|[b o] n|[b1 o1] n1 [b2 o2] n2|a n c|[b o] n | [b o] n | fv flo fd]; try discriminate; cbn [kentry_ok].
  - (* [comment removed for export] *)
    apply andb_prop in H as [H Hl]. apply andb_prop in H as [H Hfl]. apply andb_prop in H as [Hw1 Hw8].
    apply Nat.leb_le in Hw1. apply Nat.leb_le in Hw8.
    destruct (know_lookup SEGS k b o w false [] []) as [v' scs hs|scs hs|] eqn:HL; try discriminate.
    destruct scs; [|discriminate]. apply expr_eqb_eq in Hl. subst v'.
    pose proof (flat_x_sound SEGS E M k b o (ELit (Z.of_nat w)) HK Hfl) as (F1 & F2 & F3).
    cbn [edenot] in F2, F3. rewrite u64_lit in F2, F3 by lia.
    assert (Hflat : flat E (SA b o) (Z.of_nat w)) by (unfold flat; lia).
    destruct (lookup_piece SEGS E M k b o w v hs HK ltac:(lia) HL Hflat) as (bs & Hrd & Hlen & Hbs).
    split; [lia|]. split; [exact Hflat|]. rewrite adenot_SA, Hrd, <- Hbs. reflexivity.
  - (* [comment removed for export] *)
    apply andb_prop in H as [H Hbf].
    destruct (kzero_x_sound SEGS E M k k b o n HK HK H) as (Hz & Z1 & Z2).
    destruct (bflat_x_sound SEGS E M k b o n HK Hbf) as (B1 & B2 & B3).
    split; [unfold flat; pose proof (u64_range (edenot E n)); unfold elenZ in *; lia | exact Hz].
  - (* [comment removed for export] *)
    apply andb_prop in H as [Hm Hd]. apply Z.ltb_lt in Hm. apply Z.eqb_eq in Hd.
    destruct (ealign_sound SEGS E M k e HK) as [A1 [q Hq]]. split; [lia|].
    apply Z.mod_divide in Hd; [|lia]. destruct Hd as [r Hr]. rewrite Hq, Hr.
    rewrite Z.mul_assoc. apply Z_mod_mult.
  - (* [comment removed for export] *)
    exact (GPS.kpure_entails_sound SEGS E M k (KRange e lo hi) HK H).
  - (* [comment removed for export] *)
    apply andb_prop in H as [H Hbf].
    destruct (kwritable_x_sound SEGS E M k k b o n HK HK H) as (W1 & W2 & W3).
    destruct (bflat_x_sound SEGS E M k b o n HK Hbf) as (B1 & B2 & B3).
    split; [unfold flat; pose proof (u64_range (edenot E n)); unfold elenZ in *; lia|].
    intros d m Hd Hdm. unfold elenZ in *. destruct m as [|m']; [reflexivity|].
    apply store_ok_of_all; [rewrite u64_lit by lia; lia|].
    intros x Hx. rewrite u64_lit in Hx by lia.
    eapply (store_ok_all SEGS M (Z.to_nat (d + Z.of_nat (S m'))) (Z_to_bv 64 (estart E (SA b o))));
      [rewrite u64_lit by lia; lia | apply W1; lia | rewrite u64_lit by lia; lia].
  - (* [comment removed for export] *)
    exact (ranges_apart_x_sound SEGS E M k b1 o1 n1 b2 o2 n2 HK H).
  - (* [comment removed for export] *)
    apply andb_prop in H as [H Hbf].
    destruct (kn_readable_x_sound E M k b o n HK H) as (R1 & R2 & R3).
    destruct (bflat_x_sound SEGS E M k b o n HK Hbf) as (B1 & B2 & B3).
    split; [unfold flat; pose proof (u64_range (edenot E n)); unfold elenZ in *; lia | exact R3].
  - (* [comment removed for export] *)
    exact (kshok_x_sound SEGS A G A_img_hi A_img_lo SEGS_in_hull G_img_shlo E M k b o n HK H).
  - (* [comment removed for export] *)
    exact (kfpc_entailed_fact_sound SEGS E M k fl top bud fv flo fd HK Hfsem H).
Qed.

Lemma kentails_all_sound : forall E M k fl top bud tk,
  know_ok SEGS E M k -> GPS.floor_sem E fl top bud -> kentails_all SEGS A k fl top bud tk = true -> know_ok SEGS E M tk.
Proof.
  intros E M k fl top bud tk HK Hfl H. rewrite kentails_all_eq in H. unfold know_ok. apply Forall_forall. intros K Hin.
  eapply kentails_sound; [exact HK | exact Hfl |]. exact (proj1 (forallb_forall _ _) H K Hin).
Qed.

End Sound.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section CallSound.
Variable SEGS : list Segment.
Context {RC : run_ceil}.   (* [comment removed for export] *)
Context {SFL : stk_floor}.   (* [comment removed for export] *)
Variable A : atable.
Hypothesis SEGS_in_hull : forall a : word, APS.in_hull A (bv_unsigned a) = false -> find_segment SEGS (bv_unsigned a) 1 = None.
Hypothesis HULL_ok : APS.hull_ok A.
Hypothesis SEGS_wx : wx_segs_nowrap SEGS.
Variable SWIN : list (Z * Z).
Variable G : gtable.
Variable FXOK : FX -> Prop.
(* [comment removed for export] *)
Variable RZ : GPS.rz_t.
Hypothesis RZ_silent1 : GPS.RZ_SILENT1 SEGS RZ.
Hypothesis RZ_exit : GPS.RZ_EXIT SEGS RZ.
Hypothesis RZ_conseq : GPS.RZ_CONSEQ RZ.
(* [comment removed for export] *)
Variable SHC : list (Z * Z).
Variable KCAP : Z.
Variable AINVH : list (Z * Z) -> list (Z * Z) -> Z -> Z -> Z -> (word -> option byte) -> Model -> Prop.
Hypothesis HP : hprops SWIN G SHC AINVH.
Hypothesis G_ro_img : g_img_lo G <= g_ro_lo G /\ g_ro_lo G <= g_ro_hi G <= g_img_hi G.
Hypothesis G_img_al : 0 <= g_img_lo G /\ g_img_lo G mod 8 = 0 /\ g_img_hi G mod 8 = 0.
Hypothesis G_img_shlo : g_img_hi G <= SHMAPLO.
Hypothesis G_priv : forall lo hi, In (lo, hi) (g_priv G) -> g_ro_hi G <= lo /\ hi <= g_img_hi G.
Hypothesis SWIN_img : forall lo hi, In (lo, hi) SWIN -> g_ro_hi G <= lo /\ hi <= g_img_hi G /\ (forall plo phi, In (plo, phi) (g_priv G) -> hi <= plo \/ phi <= lo).
Hypothesis SEGS_out : forall a : word, ~ (g_img_lo G <= bv_unsigned a < g_img_hi G) -> find_segment SEGS (bv_unsigned a) 1 = None.
(* [comment removed for export] *)
Hypothesis A_img_hi : img_hi A = g_img_hi G.
Hypothesis A_img_lo : img_lo A = g_img_lo G.
Lemma G_img_ceil : g_img_hi G <= CEIL_run.
Proof. pose proof ceil_rng. pose proof G_img_shlo. unfold SHMAPLO in *. lia. Qed.

#[local] Notation AINVf := (AINV_f SWIN G AINVH).
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition nil_of (l : list (Z * Z)) : list (Z * Z) := match l with _ => [] end.
#[local] Notation AINV0 := (AINV_f (nil_of SWIN) G AINVH).
Definition UTRUE (E : env) : Prop := True.
(* [comment removed for export] *)
Lemma hprops_nil : hprops (nil_of SWIN) G SHC AINVH.
Proof.
  destruct HP as [F V Mo L Fa Zb Zf D Df Bf P Sh Nl]. constructor; try assumption.
  intros Lx LF B C K M M' mdl HA H. eapply F; [exact HA|]. intros a Hne. destruct (H a Hne) as [Ho HD]. split; [|exact HD].
  destruct Ho as [Hb|[Hf|[Hc|[Hw|Hs]]]]; [left; exact Hb | right; left; exact Hf | right; right; left; exact Hc | | right; right; right; right; exact Hs].
  destruct Hw as (lo & hi & Hin & _). cbn in Hin. destruct Hin.
Qed.

Lemma in_wins_dec : forall W z, in_wins W z \/ ~ in_wins W z.
Proof.
  intros W z. destruct (existsb (fun p => Z.leb (fst p) z && Z.ltb z (snd p))%bool W) eqn:H.
  - left. apply existsb_exists in H as [[lo hi] [Hin Hb]]. cbn [fst snd] in Hb. apply andb_prop in Hb as [H1 H2].
    apply Z.leb_le in H1. apply Z.ltb_lt in H2. exists lo, hi. split; [exact Hin | lia].
  - right. intros (lo & hi & Hin & Hr). assert (X : existsb (fun p => Z.leb (fst p) z && Z.ltb z (snd p))%bool W = true); [|rewrite X in H; discriminate].
    apply existsb_exists. exists (lo, hi). split; [exact Hin|]. cbn [fst snd]. apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition callee_contract_when (Q : env -> Prop) (ce : gcallee) : Prop :=
  forall (PERMf : list (Z * Z)) (TOPf : Z) (HID HIDF : list (Z * Z)) (M0 : word -> option byte) (B0 C0 : Z)
         (FTOPf : Z)      (* [comment removed for export] *)
         (FS0 : Fs.Fs) E fx R M mdl (T : TSet),
    0 <= B0 -> 0 <= C0 -> B0 + ce_bcap ce <= GBUDGET -> C0 + ce_ccap ce <= GCOUNT ->
    Z.of_nat (length HIDF) + FTOPf <= FMIN ->
    Q E ->
    GPS.cs_ok SEGS PERMf TOPf FS0 SHC (VSHf HID HIDF) (AINV0 PERMf TOPf HID HIDF M0 B0 C0) KCAP FTOPf FXOK UTRUE E (ce_tin ce) fx R M mdl ->
    T [] ->
    (forall tout E' fx' R' M' mdl', In tout (ce_touts ce) -> env_agree (ce_nxf ce) E E' ->
        GPS.cs_ok SEGS PERMf TOPf FS0 SHC (VSHf HID HIDF) (AINV0 PERMf TOPf HID HIDF M0 B0 C0) KCAP FTOPf FXOK UTRUE E' tout fx' R' M' mdl' ->
        m_fs mdl' = m_fs mdl ->
        RZ (cfgF SEGS fx' R' (pc tout) M' mdl') T) ->
    RZ (cfgF SEGS fx R (pc (ce_tin ce)) M mdl) T.
Definition QTRUE (E : env) : Prop := True.
Definition callee_contract : gcallee -> Prop := callee_contract_when QTRUE.

(* [comment removed for export] *)
Variable nx0 : nat.
Variable PERMc : list (Z * Z).
Variable SPTOPc : Z.
Variable FS0 : Fs.Fs.
Variable HIDc : list (Z * Z).
Variable HIDFc : list (Z * Z).
Variable M0c : word -> option byte.
Variable B0c C0c : Z.
Hypothesis B0c_nonneg : 0 <= B0c.
Hypothesis C0c_nonneg : 0 <= C0c.
Variable FTOPc : Z.                                                   (* [comment removed for export] *)
Hypothesis FTOPc_ok : Z.of_nat (length HIDFc) + FTOPc <= FMIN.        (* [comment removed for export] *)
Variable bcap ccap : Z.
Hypothesis bcap_ok : B0c + bcap <= GBUDGET.
Hypothesis ccap_ok : C0c + ccap <= GCOUNT.
Variable UINV : env -> Prop.
Hypothesis UINV_agree : forall E E', env_agree nx0 E E' -> UINV E -> UINV E'.

#[local] Notation AINVc := (AINVf PERMc SPTOPc HIDc HIDFc M0c B0c C0c).
#[local] Notation VSHc := (VSHf HIDc HIDFc).
#[local] Notation cs_ok := (GPS.cs_ok SEGS PERMc SPTOPc FS0 SHC VSHc AINVc KCAP FTOPc FXOK UINV).
#[local] Notation node1_stmt := (GPS.node1_stmt SEGS nx0 PERMc SPTOPc FS0 SHC VSHc AINVc KCAP FTOPc FXOK UINV RZ).

(* [comment removed for export] *)

Lemma remove_pair_perm : forall p l l', remove_pair p l = Some l' -> Permutation.Permutation l (p :: l').
Proof.
  intros p l. induction l as [|q r IH]; intros l' H; cbn [remove_pair] in H; [discriminate|].
  destruct (pair_eqb p q) eqn:Heq.
  - injection H as <-. apply pair_eqb_eq in Heq. subst q. apply Permutation.Permutation_refl.
  - destruct (remove_pair p r) as [r'|] eqn:Hr; [|discriminate]. injection H as <-.
    eapply Permutation.Permutation_trans; [apply Permutation.perm_skip; apply IH; reflexivity|]. apply Permutation.perm_swap.
Qed.

Lemma remove_pairs_perm : forall ps l l', remove_pairs ps l = Some l' -> Permutation.Permutation l (ps ++ l').
Proof.
  intros ps. induction ps as [|p ps IH]; intros l l' H; cbn [remove_pairs] in H.
  - injection H as <-. apply Permutation.Permutation_refl.
  - destruct (remove_pair p l) as [l1|] eqn:Hp; [|discriminate].
    eapply Permutation.Permutation_trans; [apply remove_pair_perm; exact Hp|]. cbn [app]. apply Permutation.perm_skip. apply IH. exact H.
Qed.

Lemma remove_pairs_incl : forall ps l l' x, remove_pairs ps l = Some l' -> In x l' -> In x l.
Proof.
  intros ps l l' x H Hin. pose proof (remove_pairs_perm ps l l' H) as P.
  apply (Permutation.Permutation_in x (Permutation.Permutation_sym P)). apply in_app_iff. right. exact Hin.
Qed.

Lemma blocks_den_perm : forall E l l', Permutation.Permutation l l' -> Permutation.Permutation (blocks_den E l) (blocks_den E l').
Proof. intros. unfold blocks_den. apply Permutation.Permutation_map. assumption. Qed.

(* [comment removed for export] *)
Definition vis_ranges (VSH : list (Z * Z)) (E : env) (cs : acs) : list (Z * Z) := VSH ++ blocks_den E (a_vis cs ++ a_fake cs).
Lemma in_shv_shb : forall VSH E cs z,
  (in_shv VSH z || in_shb E (a_vis cs ++ a_fake cs) z)%bool = true <-> in_lshadow (vis_ranges VSH E cs) z.
Proof.
  intros VSH E cs z. unfold vis_ranges, in_lshadow. split.
  - intros H. apply orb_prop in H as [H|H].
    + unfold in_shv in H. apply existsb_exists in H as [[b n] [Hin Hb]]. cbn [fst snd] in Hb. apply andb_prop in Hb as [H1 H2].
      apply Z.leb_le in H1. apply Z.ltb_lt in H2. exists b, n. split; [apply in_app_iff; left; exact Hin | unfold in_shadow; lia].
    + unfold in_shb in H. apply existsb_exists in H as [[b n] [Hin Hb]]. cbn [fst snd] in Hb. apply andb_prop in Hb as [H1 H2].
      apply Z.leb_le in H1. apply Z.ltb_lt in H2. exists (uE E b), (uE E n). split; [|unfold in_shadow; lia].
      apply in_app_iff. right. unfold blocks_den. apply in_map_iff. exists (b, n). split; [reflexivity | exact Hin].
  - intros (b & n & Hin & [H1 H2]). apply in_app_iff in Hin as [Hin|Hin]; apply orb_true_intro; [left | right].
    + unfold in_shv. apply existsb_exists. exists (b, n). split; [exact Hin|]. cbn [fst snd]. apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; lia.
    + unfold blocks_den in Hin. apply in_map_iff in Hin as [[b0 n0] [Heq Hin]]. cbn [fst snd] in Heq. injection Heq as <- <-.
      unfold in_shb. apply existsb_exists. exists (b0, n0). split; [exact Hin|]. cbn [fst snd]. apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; lia.
Qed.
Lemma hid_sets : forall VSH1 VSH2 E1 E2 cs1 cs2 m,
  (forall x, In x (vis_ranges VSH1 E1 cs1) -> In x (vis_ranges VSH2 E2 cs2)) ->
  (forall x, In x (vis_ranges VSH2 E2 cs2) -> In x (vis_ranges VSH1 E1 cs1)) ->
  hid SHC VSH1 E1 cs1 m = hid SHC VSH2 E2 cs2 m.
Proof.
  intros VSH1 VSH2 E1 E2 cs1 cs2 m H12 H21. apply functional_extensionality. intros a. unfold hid, vlz. f_equal. f_equal.
  rewrite <- !orb_assoc. f_equal.
  destruct (in_shv VSH1 (bv_unsigned a) || in_shb E1 (a_vis cs1 ++ a_fake cs1) (bv_unsigned a))%bool eqn:H1;
  destruct (in_shv VSH2 (bv_unsigned a) || in_shb E2 (a_vis cs2 ++ a_fake cs2) (bv_unsigned a))%bool eqn:H2; try reflexivity.
  - apply in_shv_shb in H1. exfalso. assert (X : in_lshadow (vis_ranges VSH2 E2 cs2) (bv_unsigned a)) by (eapply in_lshadow_mono; [exact H12 | exact H1]).
    apply in_shv_shb in X. rewrite X in H2. discriminate.
  - apply in_shv_shb in H2. exfalso. assert (X : in_lshadow (vis_ranges VSH1 E1 cs1) (bv_unsigned a)) by (eapply in_lshadow_mono; [exact H21 | exact H2]).
    apply in_shv_shb in X. rewrite X in H1. discriminate.
Qed.

Lemma acs_eqb_nopc_cs_ok : forall PERM TOP FTOP FS VSH AINV UI t t' E fx R M mdl,
  acs_eqb_nopc t t' = true ->
  GPS.cs_ok SEGS PERM TOP FS SHC VSH AINV KCAP FTOP FXOK UI E t' fx R M mdl -> GPS.cs_ok SEGS PERM TOP FS SHC VSH AINV KCAP FTOP FXOK UI E t fx R M mdl.
Proof.
  intros PERM TOP FTOP FS VSH AINV UI t t' E fx R M mdl H HC. unfold acs_eqb_nopc in H.
  repeat match type of H with (_ && _)%bool = true => apply andb_prop in H as [H ?X] end.
  apply (list_eqb_eq expr_eqb expr_eqb_eq) in H. apply (list_eqb_eq kentry_eqb kentry_eqb_eq) in X10.
  apply (list_eqb_eq pair_eqb pair_eqb_eq) in X7. apply (list_eqb_eq pair_eqb pair_eqb_eq) in X6.
  apply expr_eqb_eq in X5. apply Z.eqb_eq in X4. apply (list_eqb_eq amap_eqb APS.amap_eqb_eq) in X3.
  apply (list_eqb_eq pair_eqb pair_eqb_eq) in X2. apply expr_eqb_eq in X1. apply afd_eqb_eq in X0.
  apply expr_eqb_eq in X.   (* [comment removed for export] *)
  destruct (s_log (a_ss t)) eqn:HL; [|discriminate].
  assert (HMR : Mr SHC VSH E t mdl M = Mr SHC VSH E t' mdl M) by (apply Mr_fields; assumption).
  destruct HC as [CR CL CK CH CF CD CA CU CX CP CT CK2 CFB CFL]; constructor; unfold kn in *; rewrite ?HMR, ?H, ?X10, ?X7, ?X6, ?X5, ?X4, ?X3, ?X2, ?X1, ?X0, ?X; try assumption.
Qed.

Lemma is_ret_at_sound : forall p fx R M,
  is_ret_at SEGS p = true ->
  RiscvSemantics.step SEGS (mkstF fx R (Z_to_bv 64 p) M (seg_rom SEGS))
  = MachineOk (mkstF fx R (v_jalr (getr R (Z_to_bv 5 1)) 0) M (seg_rom SEGS)).
Proof.
  intros p fx R M H. unfold is_ret_at in H.
  destruct (itab_lookup (mk_itab_ranges SEGS [(p, 1%nat)]) p) as [i|] eqn:Hit; [|discriminate].
  pose proof (mk_itab_ranges_sound SEGS [(p, 1%nat)] _ _ Hit) as Hen. unfold itab_entry in Hen.
  destruct (fetch_word SEGS (Z_to_bv 64 p)) as [w|] eqn:Hf; [|discriminate].
  destruct (is_ecall w) eqn:Hec; [discriminate|].
  destruct (decode_any w) as [[i' isz]|] eqn:Hd; [|discriminate].
  destruct (Z.eqb isz 4) eqn:Hsz; [|discriminate]. apply Z.eqb_eq in Hsz. subst isz. injection Hen as ->.
  destruct i as [ | | | rd rs imm | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | ]; try discriminate.
  apply andb_prop in H as [H Himm]. apply andb_prop in H as [Hrd Hrs].
  assert (rd = 0%bv) by (apply bv_eq; unfold bv_eqb in Hrd; apply Z.eqb_eq in Hrd; exact Hrd). subst rd.
  assert (rs = Z_to_bv 5 1) by (apply bv_eq; unfold bv_eqb in Hrs; apply Z.eqb_eq in Hrs; exact Hrs). subst rs.
  apply Z.eqb_eq in Himm.
  unfold mkstF. rewrite <- !mkstR_None.
  rewrite (stepR_jalr fx SEGS R _ M (seg_rom SEGS) None w 0%bv (Z_to_bv 5 1) imm Hf Hec Hd).
  rewrite bv_eqb_refl. rewrite Himm. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma in_blocks_ffus : forall E fk z,
  in_blocks (blocks_den E (map ffus fk)) z -> in_blocks (map fusable (blocks_den E fk)) z.
Proof.
  intros E fk z (b & n & Hin & Hz). unfold blocks_den in Hin.
  apply in_map_iff in Hin as [p [Heq Hin]]. apply in_map_iff in Hin as [[b0 n0] [Hf Hin0]]. subst p.
  assert (BAD : uE E (snd (ffus (b0, n0))) = 0 -> False).
  { intros H0. cbn [fst snd] in Heq. injection Heq as E1 E2. rewrite <- E2, H0 in Hz. lia. }
  assert (Z0 : uE E (ELit 0) = 0) by (unfold uE; cbn [edenot]; apply u64_lit; lia).
  unfold ffus in Heq, BAD. cbn [fst snd] in Heq, BAD.
  destruct n0 as [m| | | | | | |]; try (exfalso; apply BAD; exact Z0).
  destruct (Z.leb 8 m && Z.ltb m two64)%bool eqn:Hc; [|exfalso; apply BAD; exact Z0].
  apply andb_prop in Hc as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2. unfold two64 in H2.
  cbn [fst snd] in Heq. injection Heq as E1 E2. subst b n.
  exists (uE E b0), (uE E (ELit m) - 8). split.
  - apply in_map_iff. exists (uE E b0, uE E (ELit m)). split; [reflexivity|]. unfold blocks_den. apply in_map_iff.
    exists (b0, ELit m). split; [reflexivity | exact Hin0].
  - revert Hz. unfold uE. cbn [edenot]. rewrite !u64_lit by lia. lia.
Qed.

(* [comment removed for export] *)
Definition node_call_cond (COND : acs -> list expr -> bool) (ce : gcallee) (args : list expr) (cs : acs) : option acs :=
  match bind ce args cs with
  | Some th => if COND cs th then node_call SEGS A nx0 bcap ccap G ce args cs else None
  | None => None
  end.

(* [comment removed for export] *)
Lemma node_call_split : forall ce args cs cs' E fx R M model,
  cs_ok E cs fx R M model -> node_call SEGS A nx0 bcap ccap G ce args cs = Some cs' ->
  exists th keepblocks,
    bind ce args cs = Some th /\ remove_pairs (map (ptsubst th) (a_vis (ce_tin ce))) (a_vis cs) = Some keepblocks /\
    let Ef := tenv E th in
    let PERMf := wins_den Ef (a_ghost (ce_tin ce)) in let TOPf := sptop_den Ef (a_brk (ce_tin ce)) in
    let HIDf := blocks_den E keepblocks ++ HIDc in let HIDFf := blocks_den E (a_fake cs) ++ HIDFc in
    let B0f := B0c + bcost E keepblocks in let C0f := C0c + bcount keepblocks in
    let FTOPf := uE Ef (a_fbud (ce_tin ce)) in     (* [comment removed for export] *)
    GPS.cs_ok SEGS PERMf TOPf FS0 SHC (VSHf HIDf HIDFf) (AINV0 PERMf TOPf HIDf HIDFf M B0f C0f) KCAP FTOPf FXOK UTRUE Ef (ce_tin ce) fx R M model
    /\ 0 <= B0f /\ 0 <= C0f /\ B0f + ce_bcap ce <= GBUDGET /\ C0f + ce_ccap ce <= GCOUNT /\ Z.of_nat (length HIDFf) + FTOPf <= FMIN
    /\ pc cs = pc (ce_tin ce)
    /\ (forall T : TSet, T [] ->
         (forall E2 fx2 R2 M2 mdl2, env_agree nx0 E E2 /\ env_agree (nxt cs) E E2 -> cs_ok E2 cs' fx2 R2 M2 mdl2 ->
            m_fs mdl2 = m_fs model -> RZ (cfgF SEGS fx2 R2 (pc cs') M2 mdl2) T) ->
         forall toutj E' fx' R' M' mdl', In toutj (ce_touts ce) -> env_agree (ce_nxf ce) Ef E' ->
           GPS.cs_ok SEGS PERMf TOPf FS0 SHC (VSHf HIDf HIDFf) (AINV0 PERMf TOPf HIDf HIDFf M B0f C0f) KCAP FTOPf FXOK UTRUE E' toutj fx' R' M' mdl' ->
           m_fs mdl' = m_fs model -> RZ (cfgF SEGS fx' R' (pc toutj) M' mdl') T).
Proof. pose proof sfloor_ge as SFG_.
  pose proof SWIN_img as SWIN_img_kept.    (* [comment removed for export] *)
  intros ce args cs cs' E fx R M model HC Hn.
  unfold node_call in Hn. rewrite ?kept_sticky_fe, ?kept_fact_fe, ?wsok_fe, ?kept_shadow_fe in Hn. unfold kept_sticky_ref, kept_fact_ref, wsok_ref, kept_shadow_ref in Hn.
  destruct (ce_touts ce) as [|tout touts'] eqn:Htouts; [discriminate|].
  match type of Hn with (if negb ?c then _ else _) = _ => destruct c eqn:Hc1; [|discriminate] end. cbn [negb] in Hn.
  match type of Hn with (if negb ?c then _ else _) = _ => destruct c eqn:Hg1; [|discriminate] end. cbn [negb] in Hn.   (* [comment removed for export] *)
  destruct (bind ce args cs) as [th|] eqn:Hbind; [|discriminate].
  match type of Hn with (if negb ?c then _ else _) = _ => destruct c eqn:Hc2; [|discriminate] end. cbn [negb] in Hn.
  cbv zeta in Hn.
  match type of Hn with (if negb ?c then _ else _) = _ => destruct c eqn:Hregs; [|discriminate] end. cbn [negb] in Hn.
  destruct (ret_lit cs) as [ret|] eqn:Hret; [|discriminate].
  destruct (nth 1 (s_regs (a_ss tout)) (ELit 0)) as [|r1| | | | | |] eqn:Hr1; try discriminate.
  destruct (nth 1 (s_regs (a_ss (ce_tin ce))) (ELit 0)) as [|r1'| | | | | |] eqn:Hr1'; try discriminate.
  match type of Hn with (if negb ?c then _ else _) = _ => destruct c eqn:Hc3; [|discriminate] end. cbn [negb] in Hn.
  match type of Hn with (if negb ?c then _ else _) = _ => destruct c eqn:Hent; [|discriminate] end. cbn [negb] in Hn.
  destruct (remove_pairs (map (ptsubst th) (a_vis (ce_tin ce))) (a_vis cs)) as [keepblocks|] eqn:Hrm; [|discriminate].
  match type of Hn with (if negb ?c then _ else _) = _ => destruct c eqn:Hc4; [|discriminate] end. cbn [negb] in Hn.
  apply some_inj in Hn. subst cs'.
  (* [comment removed for export] *)
  repeat match type of Hc1 with (_ && _)%bool = true => apply andb_prop in Hc1 as [Hc1 ?X] end.
  rename Hc1 into Hpc. apply Z.eqb_eq in Hpc. rename X15 into Hfresh. rename X14 into Hagree. rename X13 into Hrets.
  apply Nat.eqb_eq in X12. apply Nat.eqb_eq in X11. apply Nat.eqb_eq in X10. rename X12 into Hlen. rename X11 into Hlenin. rename X10 into Hlenout.
  destruct (s_log (a_ss (ce_tin ce))) eqn:Hlogin; [|discriminate]. destruct (s_log (a_ss tout)) eqn:Hlogout; [|discriminate]. clear X9.
  apply Nat.leb_le in X8. rename X8 into Hnxf_le. rename X7 into Hknout_v. rename X6 into Hsrout_v. rename X5 into Hvisout_v.
  rename X4 into Hknin_v. rename X3 into Hvisin_v. rename X2 into Hghin_v. rename X1 into Hbrkin_v.
  apply (list_eqb_eq pair_eqb pair_eqb_eq) in X0. rename X0 into Hgh_io. apply expr_eqb_eq in X. rename X into Hbrk_io.
  (* [comment removed for export] *)
  repeat match type of Hg1 with (_ && _)%bool = true => apply andb_prop in Hg1 as [Hg1 ?X] end.
  destruct (a_fake (ce_tin ce)) eqn:Hfkin; [|discriminate]. destruct (a_fake tout) eqn:Hfkout; [|discriminate]. clear Hg1.
  apply afd_eqb_eq in X6. apply afd_eqb_eq in X5. apply afd_eqb_eq in X4. rename X6 into Hfdin. rename X5 into Hfdout. rename X4 into Hfdcs.
  rename X3 into Hmtin_v. rename X2 into Hmtout_v. apply Z.leb_le in X1. rename X1 into Hal.
  rename X0 into Hfbin_v. rename X into Hfbout_v.   (* [comment removed for export] *)
  apply andb_prop in Hc2 as [Hth_v Hth_len]. apply Nat.eqb_eq in Hth_len.
  apply andb_prop in Hregs as [Hregs Hfbud]. apply andb_prop in Hregs as [Hregs Hmeter].   (* [comment removed for export] *)
  apply (list_eqb_eq expr_eqb expr_eqb_eq) in Hregs. apply expr_eqb_eq in Hmeter.
  apply andb_prop in Hc3 as [Hr11 Hr1n]. apply Nat.eqb_eq in Hr11. subst r1'. apply Nat.ltb_lt in Hr1n.
  repeat match type of Hc4 with (_ && _)%bool = true => apply andb_prop in Hc4 as [Hc4 ?X] end.
  rename Hc4 into Hws. rename X7 into Hkbflat. rename X6 into Hfkflat. rename X5 into Htop. rename X4 into Hylo0. rename X3 into Hbt.   (* [comment removed for export] *)
  rename X2 into Hcost. apply Z.leb_le in X1. apply Z.leb_le in X0. apply Z.leb_le in X. apply Z.leb_le in Hylo0.
  rename X1 into HCcap. rename X0 into HBo0. rename X into HCo0.
  apply expr_eqb_eq in Htop.
  (* [comment removed for export] *)
  set (tin := ce_tin ce) in *. set (nxf := ce_nxf ce) in *. set (v := nxt cs) in *. set (sp := reg cs 2) in *.
  set (k := kn cs) in *.
  pose proof (co_regs HC) as HR. pose proof (co_know HC) as HK.
  destruct (fresh_ok_parts nx0 cs Hfresh) as (Fsr & Fkn & Fmaps & Fallow & Fbrk & Ffd & Fle).
  destruct (fresh_ok_parts2 nx0 cs Hfresh) as [Ffk Fmt].
  set (Ef := tenv E th).
  set (MR := Mr SHC VSHc E cs model M) in HK.
  (* [comment removed for export] *)
  assert (HRf : regs_ok Ef (s_regs (a_ss tin)) R).
  { apply (proj1 (regs_ok_tsubst E th (s_regs (a_ss tin)) R)). rewrite Hregs. exact HR. }
  assert (HKf : know_ok SEGS Ef MR (kn tin)).
  { apply (proj1 (know_ok_ktsubst SEGS E th MR (kn tin))). eapply kentails_all_sound; [exact SEGS_in_hull | exact HULL_ok | exact A_img_hi | exact A_img_lo | exact G_img_shlo | exact HK | exact (co_floor HC) | exact Hent]. }
  set (ws := map (ptsubst th) (a_ghost tin)) in *.
  set (PERMf := wins_den Ef (a_ghost tin)).
  set (TOPf := sptop_den Ef (a_brk tin)).
  assert (HPERMf : wins_den E ws = PERMf) by (unfold ws, PERMf, Ef; apply wins_den_ptsubst).
  destruct (split_lit sp) as [spb spk] eqn:Hssp. apply andb_prop in Hbt as [Hbt Hcf]. apply andb_prop in Hbt as [Hfloor Hspbf].
  pose proof (split_lit_denot E sp spb spk Hssp) as Hspd.
  assert (Hspv2 : uE E sp = bv_unsigned (edenot E spb) + spk).
  { destruct (bflat_x_sound SEGS E MR k spb spk (ELit 0) HK Hspbf) as (B1 & B2 & B3). rewrite estart_SA in B1, B3.
    unfold uE. rewrite Hspd. apply u64_lit. lia. }
  assert (Hsp8 : uE E sp mod 8 = 0).
  { destruct (ealign_sound SEGS E MR k sp HK) as [A1 [q Hq]]. unfold uE. fold k sp in Hal. rewrite Hq.
    replace (2 ^ ealign k sp) with (8 * 2 ^ (ealign k sp - 3)) by (change 8 with (2 ^ 3); rewrite <- Z.pow_add_r by lia; f_equal; lia).
    rewrite Zmult_mod, Z.mul_comm. rewrite (Zmult_mod 8). rewrite Z_mod_same_full. rewrite Z.mul_0_l. reflexivity. }
  (* [comment removed for export] *)
  set (yf := match acs_floor (a_maps tin) with None => Z.max MSTK (a_ylo tin) | Some _ => MSTK end) in Hfloor.
  assert (HyfM : MSTK <= yf) by (unfold yf; destruct (acs_floor (a_maps tin)); lia).
  assert (Hyf1 : 1 <= yf) by (unfold MSTK in HyfM; lia).
  pose proof ceil_rng as CR.
  assert (FL : forall z, bv_unsigned (edenot E spb) + (spk - yf) <= z < bv_unsigned (edenot E spb) + (spk - yf) + yf ->
               SFLOOR <= z < SPTOPc /\ SPTOPc < 2 ^ 64).
  { intros z Hz. rewrite <- (co_top HC).
    destruct (bflat_x_sound SEGS E MR k spb spk (ELit 0) HK Hspbf) as (B1 & B2 & B3). rewrite estart_SA in B1, B3.
    assert (Hz0 : 0 <= z < 2 ^ 64 /\ yf < 2 ^ 64).
    { pose proof Hfloor as Hfl'. unfold in_floor in Hfl'. destruct (split_lit (a_brk cs)) as [tb tk] eqn:Htsp.
      destruct (base_range k tb) as [[tlo thi]|] eqn:Hbr; [|destruct (acs_floor (a_maps cs)); discriminate].
      pose proof (base_range_sound SEGS E MR k tb tlo thi HK Hbr) as [T1 T2]. pose proof (u64_range (edenot E tb)) as Rtb.
      pose proof (co_floor HC) as CF0. destruct (acs_floor (a_maps cs)) as [f0|]; cbn [GPS.floor_sem] in CF0.
      - apply andb_prop in Hfl' as [Hfl' L2]. apply andb_prop in Hfl' as [Hfl' L1]. apply andb_prop in Hfl' as [Hfl' H3]. apply andb_prop in Hfl' as [H1 H2].
        apply Z.ltb_lt in H2. apply Z.ltb_lt in H3.
        pose proof (lin_ge0_sound SEGS E MR k _ _ HK L1) as X1. pose proof (lin_ge0_sound SEGS E MR k _ _ HK L2) as X2. cbn [xt_den] in X1, X2.
        cbn [edenot] in X2. rewrite (u64_lit yf) in X2 by (unfold GPS.uE, two64, MSTK in *; lia).
        unfold GPS.uE, two64, MSTK in *. lia.
      - apply andb_prop in Hfl' as [Hg Hx]. apply andb_prop in Hg as [Hg H3]. apply andb_prop in Hg as [H1 H2].
        apply Z.leb_le in H1. apply Z.leb_le in H2. apply Z.ltb_lt in H3.
        pose proof (xinside_sound SEGS E MR k spb (spk - yf) (ELit yf) tb (tk - a_ylo cs) (ELit (a_ylo cs)) HK Hx) as [X1 X2].
        rewrite !estart_SA in X1, X2. rewrite !(APS.elenZ_lit E) in X2 by (unfold CEIL, two64, MSTK in *; lia).
        unfold CEIL, two64, MSTK in *. lia. }
    pose proof (GPS.in_floor_sound SEGS E MR k (acs_floor (a_maps cs)) (a_brk cs) (a_ylo cs) spb (spk - yf) (ELit yf) (Z_to_bv 64 z) HK Hfloor (co_floor HC)) as X.
    rewrite estart_SA, (APS.elenZ_lit E) in X by lia.
    rewrite u64_lit in X by lia. apply X. lia. }
  assert (Hspv : SFLOOR + yf <= uE E sp).
  { pose proof (FL (bv_unsigned (edenot E spb) + spk - yf) ltac:(lia)). rewrite Hspv2. lia. }
  assert (HTOPf : TOPf = uE E sp).
  { unfold TOPf, Ef. rewrite <- sptop_den_tsubst, Htop. unfold sptop_den.
    destruct (Z.eqb_spec (uE E sp) 0); [unfold MSTK in *; lia | reflexivity]. }
  assert (HTOPle : uE E sp <= SPTOPc).
  { pose proof (FL (bv_unsigned (edenot E spb) + spk - 1) ltac:(unfold MSTK in *; lia)). rewrite Hspv2. lia. }
  assert (HPERMown : forall z, in_wins PERMf z ->
            (in_blocks (blocks_den E keepblocks) z \/ in_wins PERMc z \/ (uE E sp <= z /\ SFLOOR <= z < SPTOPc)   (* [comment removed for export] *)
             \/ in_blocks (map fusable (blocks_den E (a_fake cs))) z)      (* [comment removed for export] *)
            /\ ~ (g_img_lo G <= z < g_img_hi G)).                          (* [comment removed for export] *)
  { intros z Hz. rewrite <- HPERMf in Hz. destruct Hz as (lo & hi & Hin & Hz).
    unfold wins_den in Hin. apply in_map_iff in Hin as [[wb0 wn] [Heq Hin]]. cbn [fst snd] in Heq. injection Heq as <- <-.
    pose proof (proj1 (forallb_forall _ _) Hws _ Hin) as Hw. cbn [fst snd] in Hw.
    destruct (split_lit wb0) as [wb wk] eqn:Hwsp. apply andb_prop in Hw as [Hw H47]. apply andb_prop in Hw as [Hw Himg]. apply andb_prop in Hw as [Hown Hbf].
    destruct (bflat_x_sound SEGS E MR k wb wk wn HK Hbf) as (B1 & B2 & B3). rewrite estart_SA in B1, B2, B3.
    pose proof (split_lit_denot E wb0 wb wk Hwsp) as Hwd.
    assert (Hu : uE E wb0 = bv_unsigned (edenot E wb) + wk) by (unfold uE; rewrite Hwd; apply u64_lit; lia).
    rewrite Hu in Hz. unfold uE in Hz.
    pose proof (owned_sp_x_sound SEGS PERMc SPTOPc E MR k (keepblocks ++ map ffus (a_fake cs)) (a_ghost cs) (acs_floor (a_maps cs)) (a_brk cs) (a_ylo cs) sp wb wk wn (Z_to_bv 64 z)
                  HK Hkbflat (co_perm HC) (co_top HC) (co_floor HC) Hown) as Ho.
    rewrite estart_SA in Ho. unfold elenZ in Ho. rewrite u64_lit in Ho by lia. specialize (Ho Hz). split.
    - destruct Ho as [Hb|[Hp|Hs]]; [| right; left; exact Hp | right; right; left; exact Hs].
      rewrite AzNodesAlloc.blocks_den_app in Hb. apply in_blocks_app in Hb as [Hb|Hb]; [left; exact Hb|].
      right; right; right. apply in_blocks_ffus. exact Hb.
    - pose proof (ranges_apart_x_sound SEGS E MR k wb wk wn (ELit 0) (g_img_lo G) (ELit (g_img_hi G - g_img_lo G)) HK Himg) as D.
      rewrite !estart_SA in D. unfold elenZ in D. cbn [edenot] in D. rewrite (u64_lit 0) in D by lia.
      pose proof G_img_al as (GA0 & _ & _). pose proof G_ro_img as (GR0 & GR1 & GR2). pose proof G_img_shlo as GS.
      rewrite (u64_lit (g_img_hi G - g_img_lo G)) in D by (unfold SHMAPLO in GS; lia). lia. }
  (* [comment removed for export] *)
  assert (HPERM47 : forall z, in_wins PERMf z -> z < two47).
  { intros z Hz. rewrite <- HPERMf in Hz. destruct Hz as (lo & hi & Hin & Hz).
    unfold wins_den in Hin. apply in_map_iff in Hin as [[wb0 wn] [Heq Hin]]. cbn [fst snd] in Heq. injection Heq as <- <-.
    pose proof (proj1 (forallb_forall _ _) Hws _ Hin) as Hw. cbn [fst snd] in Hw.
    destruct (split_lit wb0) as [wb wk] eqn:Hwsp. apply andb_prop in Hw as [Hw H47]. apply andb_prop in Hw as [Hw Himg]. apply andb_prop in Hw as [Hown Hbf].
    destruct (bflat_x_sound SEGS E MR k wb wk wn HK Hbf) as (B1 & B2 & B3). rewrite estart_SA in B1, B2, B3.
    pose proof (split_lit_denot E wb0 wb wk Hwsp) as Hwd.
    assert (Hu : uE E wb0 = bv_unsigned (edenot E wb) + wk) by (unfold uE; rewrite Hwd; apply u64_lit; lia).
    rewrite Hu in Hz. unfold uE in Hz. unfold win_lo47 in H47.
    destruct (xhi k (eaddz wb wk)) as [h|] eqn:Hh; [|discriminate]. destruct (xhi k wn) as [m|] eqn:Hm; [|discriminate]. apply andb_prop in H47 as [H64w H47]. apply Z.ltb_lt in H64w. apply Z.leb_le in H47.   (* [comment removed for export] *)
    pose proof (xhi_sound SEGS E MR k _ h HK Hh) as Xh. pose proof (xhi_sound SEGS E MR k wn m HK Hm) as Xm.
    pose proof (u64_range (edenot E wn)) as WR.
    pose proof (AzNodesAlloc2.uE_eaddz E wb wk ltac:(unfold uE; lia)) as EQ. unfold uE in EQ, Xh. rewrite EQ in Xh.
    pose proof (AzKnowLib.send_hi_sound SEGS E MR k wb wk wn (h + m) HK ltac:(lia) ltac:(unfold two64 in *; lia) ltac:(lia)) as SH. lia. }   (* [comment removed for export] *)
  set (HIDf := blocks_den E keepblocks ++ HIDc).
  set (HIDFf := blocks_den E (a_fake cs) ++ HIDFc).
  set (B0f := B0c + bcost E keepblocks). set (C0f := C0c + bcount keepblocks).
  set (FTOPf := uE Ef (a_fbud tin)).   (* [comment removed for export] *)
  assert (HFB : FTOPf <= uE E (a_fbud cs)).
  { pose proof (lin_ge0_sound SEGS E MR k [(a_fbud cs, 0)] [(tsubst th (a_fbud tin), 0)] HK Hfbud) as L.
    cbn [xt_den] in L. unfold FTOPf, Ef, uE. rewrite tsubst_denot in L. lia. }
  assert (HFBlen : Z.of_nat (length HIDFf) + FTOPf <= FMIN).
  { unfold HIDFf. rewrite length_app. unfold blocks_den. rewrite length_map. pose proof (co_fbud HC). lia. }
  destruct (co_ainv HC) as (HA & HPo & HTc & HF & HD).
  assert (Hpermv : Permutation.Permutation (a_vis cs) (map (ptsubst th) (a_vis tin) ++ keepblocks)) by (apply remove_pairs_perm; exact Hrm).
  assert (HBC : bcost E (a_vis cs) = bcost Ef (a_vis tin) + bcost E keepblocks).
  { rewrite (bcost_perm E _ _ Hpermv), AzNodesAlloc.bcost_app, bcost_ptsubst. reflexivity. }
  assert (HCC : bcount (a_vis cs) = bcount (a_vis tin) + bcount keepblocks).
  { rewrite (bcount_perm _ _ Hpermv), AzNodesAlloc.bcount_app. unfold bcount. rewrite length_map. reflexivity. }
  destruct (cost_hi k keepblocks) as [ch|] eqn:Hch; [|discriminate]. apply andb_prop in Hcost as [Hch0 HBcap].
  apply Z.leb_le in Hch0. apply Z.leb_le in HBcap.
  destruct (AzNodesAlloc.cost_hi_sound SEGS E MR k keepblocks ch HK Hch) as [Hchle Hkb0].
  assert (Hperm_vis : Permutation.Permutation (blocks_den E (a_vis cs)) (blocks_den Ef (a_vis tin) ++ blocks_den E keepblocks)).
  { unfold Ef. rewrite <- blocks_den_ptsubst, <- AzNodesAlloc.blocks_den_app. apply blocks_den_perm. apply remove_pairs_perm. exact Hrm. }
  (* [comment removed for export] *)
  assert (VIS12 : forall x, In x (vis_ranges (VSHf HIDf HIDFf) Ef tin) -> In x (vis_ranges VSHc E cs)).
  { intros x Hx. unfold vis_ranges, VSHf in Hx |- *. rewrite Hfkin, app_nil_r in Hx. unfold HIDf, HIDFf in Hx.
    rewrite AzNodesAlloc.blocks_den_app.
    repeat (apply in_app_iff in Hx as [Hx|Hx]).
    - apply in_app_iff. right. apply in_app_iff. left. apply (Permutation.Permutation_in x (Permutation.Permutation_sym Hperm_vis)). apply in_app_iff. right. exact Hx.
    - apply in_app_iff. left. apply in_app_iff. left. exact Hx.
    - apply in_app_iff. right. apply in_app_iff. right. exact Hx.
    - apply in_app_iff. left. apply in_app_iff. right. exact Hx.
    - apply in_app_iff. right. apply in_app_iff. left. apply (Permutation.Permutation_in x (Permutation.Permutation_sym Hperm_vis)). apply in_app_iff. left. exact Hx. }
  assert (VIS21 : forall x, In x (vis_ranges VSHc E cs) -> In x (vis_ranges (VSHf HIDf HIDFf) Ef tin)).
  { intros x Hx. unfold vis_ranges, VSHf in Hx |- *. rewrite Hfkin, app_nil_r. unfold HIDf, HIDFf.
    rewrite AzNodesAlloc.blocks_den_app in Hx.
    repeat (apply in_app_iff in Hx as [Hx|Hx]).
    - apply in_app_iff. left. apply in_app_iff. left. apply in_app_iff. right. exact Hx.
    - apply in_app_iff. left. apply in_app_iff. right. apply in_app_iff. right. exact Hx.
    - apply (Permutation.Permutation_in x Hperm_vis) in Hx. apply in_app_iff in Hx as [Hx|Hx].
      + apply in_app_iff. right. exact Hx.
      + apply in_app_iff. left. apply in_app_iff. left. apply in_app_iff. left. exact Hx.
    - apply in_app_iff. left. apply in_app_iff. right. apply in_app_iff. left. exact Hx. }
  assert (HMRf : Mr SHC (VSHf HIDf HIDFf) Ef tin model M = MR).
  { unfold MR, GPS.Mr. rewrite (hid_sets (VSHf HIDf HIDFf) VSHc Ef E tin cs model VIS12 VIS21). reflexivity. }
  assert (HAf : AINV0 PERMf TOPf HIDf HIDFf M B0f C0f (blocks_den Ef (a_vis tin)) (blocks_den Ef (a_fake tin)) (bcost Ef (a_vis tin)) (bcount (a_vis tin)) (uE Ef (a_meter tin)) M model).
  { split; [|split; [|split; [|split]]].
    - unfold HIDf, HIDFf, B0f, C0f. rewrite Hfkin. cbn [blocks_den map app]. rewrite app_assoc.
      replace (B0c + bcost E keepblocks + bcost Ef (a_vis tin)) with (B0c + bcost E (a_vis cs)) by (rewrite HBC; lia).
      replace (C0c + bcount keepblocks + bcount (a_vis tin)) with (C0c + bcount (a_vis cs)) by (rewrite HCC; lia).
      replace (uE Ef (a_meter tin)) with (uE E (a_meter cs)) by (unfold Ef; rewrite <- uE_tsubst, Hmeter; reflexivity).
      eapply (hp_perm _ _ _ _ HP); [| apply Permutation.Permutation_refl | exact HA].
      apply Permutation.Permutation_app_tail. exact Hperm_vis.
    - (* [comment removed for export] *)
      split; [|exact HPERM47].
      intros z Hz. destruct (HPERMown z Hz) as [[Hb|[Hp|[Hst|Hff]]] Hnimg].
      + left. unfold HIDf. apply (in_blocks_app). left. exact Hb.
      + destruct (proj1 HPo z Hp) as [Hh|[Hf|[Ho|Hsw]]]; [left; unfold HIDf; apply in_blocks_app; right; exact Hh | | right; right; left; rewrite HTOPf; lia |].
        * right. left. unfold HIDFf. rewrite map_fusable_app. apply in_blocks_app. right. exact Hf.
        * (* [comment removed for export] *)
          exfalso. destruct (AzFrame.swin_byte SWIN G G_ro_img G_img_al SWIN_img z Hsw) as [SW _]. pose proof G_ro_img. lia.
      + right. right. left. rewrite HTOPf. lia.
      + right. left. unfold HIDFf. rewrite map_fusable_app. apply in_blocks_app. left. exact Hff.
    - rewrite HTOPf. unfold MSTK in Hspv. split; [lia | exact Hsp8].
    - intros a _. reflexivity.
    - intros a _ H0. exact H0. }
  assert (HCf : GPS.cs_ok SEGS PERMf TOPf FS0 SHC (VSHf HIDf HIDFf) (AINV0 PERMf TOPf HIDf HIDFf M B0f C0f) KCAP FTOPf FXOK UTRUE Ef tin fx R M model).
  { constructor; try assumption.
    - rewrite HMRf. exact HKf.
    - exact (co_halt HC). - exact (co_fs HC).
    - rewrite Hfdin. pose proof (co_fds HC) as X. rewrite Hfdcs in X. exact X.
    - exact I.
    - exact (co_fx HC).
    - reflexivity.
    - reflexivity.
    - unfold Ef. rewrite <- uE_tsubst, Hmeter. exact (co_kcap HC).
    - (* [comment removed for export] *) rewrite Hfkin. cbn [length Z.of_nat]. unfold FTOPf. lia.
    - (* [comment removed for export] *)
      destruct (acs_floor (a_maps tin)) as [f'|] eqn:Hft; cbn [GPS.floor_sem].
      + (* [comment removed for export] *)
        apply andb_prop in Hcf as [_ Hcf].
        unfold Ef, GPS.uE. rewrite <- tsubst_denot.
        pose proof (GPS.in_floor_sound SEGS E MR k (acs_floor (a_maps cs)) (a_brk cs) (a_ylo cs) (tsubst th f') 0 (ELit 1)
                      (edenot E (tsubst th f')) HK Hcf (co_floor HC)) as X.
        rewrite estart_SA, (APS.elenZ_lit E) in X by lia. apply X. lia.
      + unfold TOPf in HTOPf |- *. rewrite HTOPf. unfold yf in Hspv. lia. }
  (* [comment removed for export] *)
  exists th, keepblocks. split; [first [exact Hbind | reflexivity]|]. split; [first [exact Hrm | reflexivity]|].
  cbv zeta. fold Ef. fold PERMf TOPf. fold HIDf HIDFf B0f C0f. fold FTOPf.
  split; [exact HCf|]. split; [unfold B0f; lia|]. split; [unfold C0f, bcount; lia|]. split; [unfold B0f; lia|]. split; [unfold C0f, bcount; lia|].
  split; [exact HFBlen|].
  split; [first [exact Hpc | reflexivity]|].
  intros T HT Hk.
    intros toutj E' fx' R' M' mdl' Hinj Hag HCj Hfs'. try rewrite Htouts in Hinj.
    (* [comment removed for export] *)
    assert (HCo : GPS.cs_ok SEGS PERMf TOPf FS0 SHC (VSHf HIDf HIDFf) (AINV0 PERMf TOPf HIDf HIDFf M B0f C0f) KCAP FTOPf FXOK UTRUE E' tout fx' R' M' mdl').
    { destruct Hinj as [<-|Hinj]; [exact HCj|].
      unfold touts_agree in Hagree. pose proof (proj1 (forallb_forall _ _) Hagree toutj Hinj) as Heq.
      exact (acs_eqb_nopc_cs_ok _ _ _ _ _ _ _ tout toutj E' fx' R' M' mdl' Heq HCj). }
    (* [comment removed for export] *)
    pose proof (proj1 (forallb_forall _ _) Hrets toutj Hinj) as Hret_at.
    destruct (ret_lit_sound E cs R ret HR Hret) as (R1 & Rok & Rr & Re).
    assert (HR1' : getr R' (Z_to_bv 5 1) = Z_to_bv 64 ret).
    { rewrite (co_regs HCo (Z_to_bv 5 1)). unfold sr_get.
      replace (bv_eqb (Z_to_bv 5 1) 0%bv) with false by reflexivity.
      replace (ridx (Z_to_bv 5 1)) with 1%nat by reflexivity. rewrite Hr1. cbn [edenot].
      rewrite <- (proj1 Hag r1 Hr1n). unfold Ef. cbn [tenv ev]. rewrite <- Hth_len in Hr1n.
      replace (Nat.ltb r1 (length th)) with true by (symmetry; apply Nat.ltb_lt; exact Hr1n).
      rewrite <- R1. rewrite (HR (Z_to_bv 5 1)). unfold sr_get.
      replace (bv_eqb (Z_to_bv 5 1) 0%bv) with false by reflexivity. replace (ridx (Z_to_bv 5 1)) with 1%nat by reflexivity.
      rewrite <- Hregs. replace (ELit 0) with (tsubst th (ELit 0)) by reflexivity. rewrite map_nth. rewrite Hr1'.
      cbn [tsubst]. replace (Nat.ltb r1 (length th)) with true by (symmetry; apply Nat.ltb_lt; exact Hr1n). reflexivity. }
    assert (Hpctj : pc toutj = pc tout -> True) by (intros; exact I).
    eapply (restricted_run_sound SEGS A PERMf TOPf FS0 SHC (VSHf HIDf HIDFf) (AINV0 PERMf TOPf HIDf HIDFf M B0f C0f) KCAP FTOPf
              (AINV_f_lazy (nil_of SWIN) G SHC AINVH hprops_nil PERMf TOPf HIDf HIDFf M B0f C0f)
              ltac:(intros; rewrite A_img_hi, A_img_lo; eapply (AINV_f_facts (nil_of SWIN) G SHC AINVH hprops_nil); eassumption)
              FXOK UTRUE RZ RZ_silent1 SEGS_in_hull SEGS_wx E' toutj fx' R' M' mdl' _ T
              ltac:(destruct Hinj as [<-|Hinj]; [exact HCj | exact HCj])).
    { eapply msteps_one; [reflexivity|].
      change (restrict (hid SHC (VSHf HIDf HIDFf) E' toutj mdl') (mkstF fx' R' (Z_to_bv 64 (pc toutj)) M' (seg_rom SEGS)))
        with (mkstF fx' R' (Z_to_bv 64 (pc toutj)) (Mr SHC (VSHf HIDf HIDFf) E' toutj mdl' M') (seg_rom SEGS)).
      apply is_ret_at_sound. exact Hret_at. }
    intros model' Hsame Hhid Hhalt' Hfs2 Hfds2 HAm Hclean.
    unfold unrestrict. cbn [ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_mem ms_rom mkstF mkst].
    unfold GPS.Mr. rewrite munrestrict_mrestrict.
    rewrite HR1'. unfold ret_ok in Rok. rewrite Rok.
    (* [comment removed for export] *)
    set (E'' := Env (fun n => if Nat.ltb n v then ev E n else ev E' (n - v + nxf)%nat) (eb E)).
    assert (Hag'' : env_agree v E E'').
    { split; [|reflexivity]. intros n Hn. unfold E''. cbn [ev]. replace (Nat.ltb n v) with true by (symmetry; apply Nat.ltb_lt; exact Hn). reflexivity. }
    set (th' := out_subst th nxf (nxt tout) v) in *.
    assert (Hebf : eb E' = eb E) by (rewrite <- (proj2 Hag); reflexivity).
    assert (Hagout : env_agree (nxt tout) E' (tenv E'' th')).
    { split; [|cbn [tenv eb]; exact Hebf]. intros n Hn. unfold th', out_subst. cbn [tenv ev].
      rewrite length_app, length_map, length_seq, Hth_len.
      replace (Nat.ltb n (nxf + (nxt tout - nxf))) with true by (symmetry; apply Nat.ltb_lt; lia).
      destruct (Nat.ltb_spec n nxf) as [Hlt|Hge].
      - rewrite app_nth1 by lia. rewrite <- (proj1 Hag n Hlt). unfold Ef. cbn [tenv ev]. rewrite Hth_len.
        replace (Nat.ltb n nxf) with true by (symmetry; apply Nat.ltb_lt; exact Hlt).
        apply (edenot_agree' v); [exact Hag''|].
        assert (HH : (n < length th)%nat) by lia. exact (proj1 (forallb_forall _ _) Hth_v _ (nth_In th (ELit 0) HH)).
      - rewrite app_nth2 by lia. rewrite Hth_len.
        rewrite (nth_indep _ (ELit 0) (EVar (v + 0)%nat)) by (rewrite length_map, length_seq; lia).
        rewrite (map_nth (fun j : nat => EVar (v + j)%nat)). rewrite seq_nth by lia. cbn [edenot]. unfold E''. cbn [ev].
        replace (Nat.ltb (v + (0 + (n - nxf))) v) with false by (symmetry; apply Nat.ltb_ge; lia).
        f_equal. lia. }
    assert (Hagout' : env_agree (nxt tout) (tenv E'' th') E').
    { destruct Hagout as [A1 A2]. split; [intros n Hn; symmetry; apply A1; exact Hn | symmetry; exact A2]. }
    (* [comment removed for export] *)
    assert (HA2t : AINV0 PERMf TOPf HIDf HIDFf M B0f C0f (blocks_den E' (a_vis tout)) (blocks_den E' (a_fake tout))
                     (bcost E' (a_vis tout)) (bcount (a_vis tout)) (uE E' (a_meter tout)) M' model').
    { destruct Hinj as [<-|Hinj]; [exact HAm|].
      unfold touts_agree in Hagree. pose proof (proj1 (forallb_forall _ _) Hagree toutj Hinj) as Heq.
      unfold acs_eqb_nopc in Heq. repeat match type of Heq with (_ && _)%bool = true => apply andb_prop in Heq as [Heq ?X] end.
      apply (list_eqb_eq pair_eqb pair_eqb_eq) in X7. apply (list_eqb_eq pair_eqb pair_eqb_eq) in X2. apply expr_eqb_eq in X1.
      rewrite X7, X2, X1. exact HAm. }
    pose proof HA2t as (HA' & _ & _ & HF' & HD').
    (* [comment removed for export] *)
    assert (STICK : forall x : word,
      (in_blocks (blocks_den E keepblocks) (bv_unsigned x) \/ in_wins PERMc (bv_unsigned x) \/ (CEIL_run <= bv_unsigned x < SPTOPc)
       \/ in_blocks (blocks_den E (a_fake cs)) (bv_unsigned x) \/ SPTOPc <= bv_unsigned x) ->      (* [comment removed for export] *)
      M x <> None -> M' x <> None).
    { intros x Ho HMx.
      destruct (in_wins_dec PERMf (bv_unsigned x)) as [Hpf|Hnpf]; [apply HD'; [right; left; exact Hpf | exact HMx]|].
      destruct (errw_dec G (bv_unsigned x)) as [Hew|Hnew]; [apply HD'; [right; right; exact Hew | exact HMx]|].   (* [comment removed for export] *)
      assert (ZONE : forall P : Prop,
                (in_blocks HIDf (bv_unsigned x) \/ in_blocks HIDFf (bv_unsigned x) \/ TOPf <= bv_unsigned x
                 \/ (g_ro_lo G <= bv_unsigned x < g_img_hi G /\ ~ in_wins (g_privx G) (bv_unsigned x))) -> M' x <> None).
      { intros _ HZ. rewrite (HF' x); [exact HMx|]. split; [|split; [exact Hnpf | intros (lo & hi & Hin & _); cbn in Hin; destruct Hin]].
        destruct HZ as [Z1|[Z2|[Z3|Z4]]]; [left; exact Z1 | right; left; exact Z2 | right; right; left; exact Z3 | right; right; right; left; exact Z4]. }
      assert (STK : CEIL_run <= bv_unsigned x -> M' x <> None).
      { intros Hc. destruct (Z_lt_le_dec (bv_unsigned x) TOPf) as [Hlt|Hge]; [apply HD'; [left; lia | exact HMx] | apply (ZONE True); right; right; left; exact Hge]. }
      destruct Ho as [Hb|[Hp|[Hst|[Hfk|Habove]]]].
      5:{ apply (ZONE True). right; right; left. rewrite HTOPf. lia. }
      - apply (ZONE True). left. unfold HIDf. apply in_blocks_app. left. exact Hb.
      - destruct (proj1 HPo _ Hp) as [Hh|[Hf|[Hc|Hsw]]].
        + apply (ZONE True). left. unfold HIDf. apply in_blocks_app. right. exact Hh.
        + apply in_blocks_fusable in Hf as (f & m & Hinf & Hfz).
          apply (ZONE True). right. left. unfold HIDFf. apply in_blocks_app. right. exists f, m. split; [exact Hinf | clear -Hfz; lia].
        + apply STK. pose proof (proj1 HTc). lia.
        + apply (ZONE True). right; right; right. destruct (AzFrame.swin_byte SWIN G G_ro_img G_img_al SWIN_img _ Hsw) as [SW1 SW2].
          pose proof G_ro_img. split; [lia |]. intros Hpx. apply AzKnowLib.in_wins_privx in Hpx as [He|Hp']; [exact (Hnew He) | exact (SW2 Hp')].   (* [comment removed for export] *)
      - apply STK. lia.
      - apply (ZONE True). right. left. unfold HIDFf. apply in_blocks_app. left. exact Hfk. }
    (* [comment removed for export] *)
    set (post := map (kresplit k) (map (ktsubst th') (kn tout)) ++
                         (List.filter (fun K => kentry_vars_lt v K && sticky_call k ((keepblocks ++ a_fake cs) ++ a_ghost cs) (acs_floor (a_maps cs)) (a_brk cs) (a_ylo cs) sp K)%bool k
                          ++ List.filter (fun K => kentry_vars_lt v K && keep_fact_call G k (keepblocks ++ a_fake cs) (ghosts_lo G k (acs_floor (a_maps cs)) (a_brk cs) (a_ylo cs) (a_ghost cs)) (prep_ws k ws) (acs_floor (a_maps cs)) (a_brk cs) (a_ylo cs) sp K)%bool (kcut ws k)
                          ++ List.filter (fun K => kentry_vars_lt v K && keep_shadow G k (keepblocks ++ a_fake cs ++ ghosts_lo G k (acs_floor (a_maps cs)) (a_brk cs) (a_ylo cs) (a_ghost cs)) (acs_floor (a_maps cs)) (a_brk cs) (a_ylo cs) sp K)%bool k
                          ++ kdisj_new (map (ptsubst th') (a_vis tout)) (keepblocks ++ a_fake cs))).
    set (cs2 := ACS (mk_ss ret (map (tsubst th') (s_regs (a_ss tout))) (post ++ kdisj_gh post (map (ptsubst th') (a_vis tout)) (ghosts_ne k (a_ghost cs)))
                         (v + (nxt tout - nxf))%nat)
                    (a_maps cs) (a_totsz cs) (a_ylo cs) (a_eager cs) (keepblocks ++ map (ptsubst th') (a_vis tout)) (a_ghost cs) (a_abytes cs)
                    (a_brk cs) (a_fd cs) (a_tidset cs) (tsubst th' (a_meter tout)) (a_fake cs) (a_fbud cs)).
    assert (HBD1 : blocks_den E'' keepblocks = blocks_den E keepblocks).
    { eapply blocks_den_agree; [exact Hag''|]. unfold pairs_vars_lt. apply forallb_forall. intros x Hx.
      exact (proj1 (forallb_forall _ _) (pairs_vars_lt_app_l _ _ _ Fallow) x (remove_pairs_incl _ _ _ x Hrm Hx)). }
    assert (HBD2 : blocks_den E'' (map (ptsubst th') (a_vis tout)) = blocks_den E' (a_vis tout)).
    { rewrite blocks_den_ptsubst. eapply blocks_den_agree; [exact Hagout | exact Hvisout_v]. }
    assert (HBD3 : blocks_den E'' (a_fake cs) = blocks_den E (a_fake cs)) by (eapply blocks_den_agree; [exact Hag'' | exact Ffk]).
    assert (HBC1 : bcost E'' keepblocks = bcost E keepblocks).
    { eapply bcost_agree; [exact Hag''|]. unfold pairs_vars_lt. apply forallb_forall. intros x Hx.
      exact (proj1 (forallb_forall _ _) (pairs_vars_lt_app_l _ _ _ Fallow) x (remove_pairs_incl _ _ _ x Hrm Hx)). }
    assert (HBC2 : bcost E'' (map (ptsubst th') (a_vis tout)) = bcost E' (a_vis tout)).
    { rewrite bcost_ptsubst. eapply bcost_agree; [exact Hagout | exact Hvisout_v]. }
    assert (HMT2 : uE E'' (tsubst th' (a_meter tout)) = uE E' (a_meter tout)).
    { rewrite uE_tsubst. eapply uE_agree; [exact Hagout | exact Hmtout_v]. }
    assert (HMR2 : Mr SHC VSHc E'' cs2 model' M' = Mr SHC (VSHf HIDf HIDFf) E' tout model' M').
    { unfold GPS.Mr. f_equal. apply hid_sets.
      - intros x Hx. unfold vis_ranges, VSHf in Hx |- *. rewrite Hfkout, app_nil_r. unfold cs2 in Hx. cbn [a_vis a_fake] in Hx.
        rewrite !AzNodesAlloc.blocks_den_app, HBD1, HBD2, HBD3 in Hx. unfold HIDf, HIDFf.
        repeat (apply in_app_iff in Hx as [Hx|Hx]).
        + apply in_app_iff; left. apply in_app_iff; left. apply in_app_iff; right. exact Hx.
        + apply in_app_iff; left. apply in_app_iff; right. apply in_app_iff; right. exact Hx.
        + apply in_app_iff; left. apply in_app_iff; left. apply in_app_iff; left. exact Hx.
        + apply in_app_iff; right. exact Hx.
        + apply in_app_iff; left. apply in_app_iff; right. apply in_app_iff; left. exact Hx.
      - intros x Hx. unfold vis_ranges, VSHf in Hx |- *. rewrite Hfkout, app_nil_r in Hx. unfold cs2. cbn [a_vis a_fake].
        rewrite !AzNodesAlloc.blocks_den_app, HBD1, HBD2, HBD3. unfold HIDf, HIDFf in Hx.
        repeat (apply in_app_iff in Hx as [Hx|Hx]).
        + apply in_app_iff; right. apply in_app_iff; left. apply in_app_iff; left. exact Hx.
        + apply in_app_iff; left. apply in_app_iff; left. exact Hx.
        + apply in_app_iff; right. apply in_app_iff; right. exact Hx.
        + apply in_app_iff; left. apply in_app_iff; right. exact Hx.
        + apply in_app_iff; right. apply in_app_iff; left. apply in_app_iff; right. exact Hx. }
    set (MR' := Mr SHC (VSHf HIDf HIDFf) E' tout model' M') in HMR2.
    assert (EQF : a_vis tout = a_vis toutj /\ a_fake tout = a_fake toutj /\ a_ghost tout = a_ghost toutj).
    { destruct Hinj as [<-|Hinj]; [repeat split; reflexivity|].
      unfold touts_agree in Hagree. pose proof (proj1 (forallb_forall _ _) Hagree toutj Hinj) as Heq.
      unfold acs_eqb_nopc in Heq. repeat match type of Heq with (_ && _)%bool = true => apply andb_prop in Heq as [Heq ?X] end.
      apply (list_eqb_eq pair_eqb pair_eqb_eq) in X7. apply (list_eqb_eq pair_eqb pair_eqb_eq) in X6. apply (list_eqb_eq pair_eqb pair_eqb_eq) in X2.
      repeat split; assumption. }
    destruct EQF as (Q1 & Q2 & Q3).
    assert (HMR'eq : MR' = Mr SHC (VSHf HIDf HIDFf) E' tout mdl' M').
    { unfold MR', GPS.Mr.
      rewrite (hid_fields SHC (VSHf HIDf HIDFf) E' tout toutj model' (eq_sym Q1) (eq_sym Q2) (eq_sym Q3)) in Hhid.
      rewrite (hid_fields SHC (VSHf HIDf HIDFf) E' tout toutj mdl' (eq_sym Q1) (eq_sym Q2) (eq_sym Q3)) in Hhid.
      rewrite Hhid. reflexivity. }
    (* [comment removed for export] *)
    assert (KEPTB : forall x : word,
      (in_blocks (blocks_den E keepblocks) (bv_unsigned x) \/ in_blocks (blocks_den E (a_fake cs)) (bv_unsigned x) \/ TOPf <= bv_unsigned x
       \/ (g_ro_lo G <= bv_unsigned x < g_img_hi G /\ ~ in_wins (g_privx G) (bv_unsigned x))
       \/ (in_blocks HIDc (bv_unsigned x) \/ in_blocks (map fusable HIDFc) (bv_unsigned x))) ->      (* [comment removed for export] *)
      hid SHC VSHc E cs model x = false /\ hid SHC (VSHf HIDf HIDFf) E' tout model' x = false).
    { intros x Hx.
      assert (LZ : forall mdlx Lcx Lfx Bx Cx Kx Mx, AINV0 PERMf TOPf HIDf HIDFf M B0f C0f Lcx Lfx Bx Cx Kx Mx mdlx -> lz mdlx x = false).
      { intros mdlx Lcx Lfx Bx Cx Kx Mx HAX. destruct Hx as [Hb|[Hfk|[Ht|[Him|Hgh]]]].
        5:{ (* [comment removed for export] *)
            destruct Hgh as [Hb|Hf].
            - destruct Hb as (b & n & Hin & Hbz). eapply (AINV_f_nolazy (nil_of SWIN) G SHC AINVH hprops_nil); [exact HAX | | exact Hbz].
              apply in_app_iff. right. apply in_app_iff. left. unfold HIDf. apply in_app_iff. right. exact Hin.
            - apply in_blocks_fusable in Hf as (f & m & Hin & Hfz). eapply (AINV_f_nolazy (nil_of SWIN) G SHC AINVH hprops_nil); [exact HAX | |].
              + apply in_app_iff. right. apply in_app_iff. right. apply in_app_iff. right. unfold HIDFf. apply in_app_iff. right. exact Hin.
              + lia. }
        - destruct Hb as (b & n & Hin & Hbz). eapply (AINV_f_nolazy (nil_of SWIN) G SHC AINVH hprops_nil); [exact HAX | | exact Hbz].
          apply in_app_iff. right. apply in_app_iff. left. unfold HIDf. apply in_app_iff. left. exact Hin.
        - destruct Hfk as (b & n & Hin & Hbz). eapply (AINV_f_nolazy (nil_of SWIN) G SHC AINVH hprops_nil); [exact HAX | | exact Hbz].
          apply in_app_iff. right. apply in_app_iff. right. apply in_app_iff. right. unfold HIDFf. apply in_app_iff. left. exact Hin.
        - pose proof (AINV_f_facts (nil_of SWIN) G SHC AINVH hprops_nil _ _ _ _ _ _ _ _ _ _ _ _ _ _ HAX) as HLB.
          unfold lz. destruct (page_in_ranges (page_base x) (m_vm_lazy mdlx)) eqn:Hp; [|reflexivity]. exfalso.
          rewrite HTOPf in Ht. unfold MSTK in Hspv.
          (* [comment removed for export] *)
          apply existsb_exists in Hp as [iv [Hin Hb]]. apply andb_prop in Hb as [PQ1 PQ2]. apply Z.leb_le in PQ1. apply Z.leb_le in PQ2.
          pose proof (proj1 (Forall_forall _ _) HLB iv Hin) as (L0 & L1 & L2). pose proof (page_base_le' x) as (P3 & P4 & P5). unfold page_size in PQ2. lia.
        - (* [comment removed for export] *)
          pose proof (AINV_f_facts (nil_of SWIN) G SHC AINVH hprops_nil _ _ _ _ _ _ _ _ _ _ _ _ _ _ HAX) as HLB.
          unfold lz. destruct (page_in_ranges (page_base x) (m_vm_lazy mdlx)) eqn:Hp; [|reflexivity]. exfalso.
          apply existsb_exists in Hp as [iv [Hin Hb]]. apply andb_prop in Hb as [PQ1 PQ2]. apply Z.leb_le in PQ1. apply Z.leb_le in PQ2.
          pose proof (proj1 (Forall_forall _ _) HLB iv Hin) as (L0 & L1 & L2). pose proof (page_base_le' x) as (P3 & P4 & P5). unfold page_size in PQ2.
          pose proof G_ro_img as (GR0 & GR1 & GR2). lia. }
      unfold hid. rewrite (LZ model _ _ _ _ _ _ HAf). rewrite (LZ model' _ _ _ _ _ _ HAm). split; reflexivity. }
    assert (HKout : know_ok SEGS E'' MR' (map (kresplit k) (map (ktsubst th') (kn tout)))).
    { assert (HK'' : know_ok SEGS E'' MR k) by (eapply know_ok_agree'; [exact Hag'' | exact Fkn | exact HK]).
      assert (X : know_ok SEGS E'' MR' (map (ktsubst th') (kn tout))).
      { apply (proj2 (know_ok_ktsubst SEGS E'' th' MR' (kn tout))). eapply know_ok_agree'; [exact Hagout | exact Hknout_v |].
        rewrite HMR'eq. exact (co_know HCo). }
      unfold know_ok in X |- *. apply Forall_forall. intros K HinK. apply in_map_iff in HinK as [K0 [<- Hin0]].
      eapply kentry_ok_kresplit; [exact HK''|]. exact (proj1 (Forall_forall _ _) X K0 Hin0). }
    assert (HRout : regs_ok E'' (map (tsubst th') (s_regs (a_ss tout))) R').
    { apply (proj2 (regs_ok_tsubst E'' th' (s_regs (a_ss tout)) R')). eapply regs_ok_agree'; [exact Hagout | exact Hsrout_v | exact (co_regs HCo)]. }
    (* [comment removed for export] *)
    assert (ZONE : forall b off n,
      0 <= estart E (SA b off) -> estart E (SA b off) < 2 ^ 64 ->
      forall x : word, estart E (SA b off) <= bv_unsigned x < estart E (SA b off) + elenZ E n ->
      ((existsb (fun bl => let '(lb, lk) := split_lit (fst bl) in xinside k b off n lb lk (snd bl)) (keepblocks ++ a_fake cs)
        || above_sp k (acs_floor (a_maps cs)) (a_brk cs) (a_ylo cs) sp b off n
        || img_lit_x G k b off n
        || existsb (fun g => let '(gb, gk) := split_lit (fst g) in xinside k b off n gb gk (snd g)) (ghosts_lo G k (acs_floor (a_maps cs)) (a_brk cs) (a_ylo cs) (a_ghost cs)))
       && apart_ws k (prep_ws k ws) b off n)%bool = true ->
      zone (nil_of SWIN) G PERMf TOPf HIDf HIDFf x
      /\ (in_blocks (blocks_den E keepblocks) (bv_unsigned x) \/ in_blocks (blocks_den E (a_fake cs)) (bv_unsigned x) \/ TOPf <= bv_unsigned x
          \/ (g_ro_lo G <= bv_unsigned x < g_img_hi G /\ ~ in_wins (g_privx G) (bv_unsigned x))
          \/ (in_blocks HIDc (bv_unsigned x) \/ in_blocks (map fusable HIDFc) (bv_unsigned x)))).
    { intros b off n E1 E2 x Hx Hb. apply andb_prop in Hb as [HA0 HB].
      pose proof (u64_range (edenot E n)) as Hnr. unfold elenZ in Hx.
      (* [comment removed for export] *)
      assert (NP : ~ in_wins PERMf (bv_unsigned x)).
      { intros Hp. rewrite <- HPERMf in Hp. destruct Hp as (lo & hi & Hin & Hr).
        unfold wins_den in Hin. apply in_map_iff in Hin as [[wb0 wn] [Heq Hin]]. cbn [fst snd] in Heq. injection Heq as <- <-.
        pose proof (apart_ws_sem k ws b off n HB _ Hin) as Hap. cbn [fst snd] in Hap.
        pose proof (proj1 (forallb_forall _ _) Hws _ Hin) as Hw. cbn [fst snd] in Hw.
        destruct (split_lit wb0) as [wb wk] eqn:Hwsp. apply andb_prop in Hw as [Hw _]. apply andb_prop in Hw as [Hw _]. apply andb_prop in Hw as [_ Hwbf].
        destruct (bflat_x_sound SEGS E MR k wb wk wn HK Hwbf) as (B1 & B2 & B3). rewrite estart_SA in B1, B2, B3.
        assert (D : estart E (SA b off) + elenZ E n <= estart E (SA wb wk) \/ estart E (SA wb wk) + elenZ E wn <= estart E (SA b off)).
        { destruct Hap as [Hap|Hap].
          - pose proof (ranges_apart_x_sound SEGS E MR k wb wk wn b off n HK Hap) as D0. lia.
          - exact (ranges_apart_x_sound SEGS E MR k b off n wb wk wn HK Hap). }
        rewrite !estart_SA in D. unfold elenZ in D.
        rewrite estart_SA in Hx.
        assert (Hu : uE E wb0 = bv_unsigned (edenot E wb) + wk) by (unfold uE; rewrite (split_lit_denot E wb0 wb wk Hwsp); apply u64_lit; lia).
        rewrite Hu in Hr. unfold uE in Hr. lia. }
      assert (CASES : in_blocks (blocks_den E keepblocks) (bv_unsigned x) \/ in_blocks (blocks_den E (a_fake cs)) (bv_unsigned x)
                      \/ TOPf <= bv_unsigned x
                      \/ (g_ro_lo G <= bv_unsigned x < g_img_hi G /\ ~ in_wins (g_privx G) (bv_unsigned x))
                      \/ (in_blocks HIDc (bv_unsigned x) \/ in_blocks (map fusable HIDFc) (bv_unsigned x))).
      { apply orb_prop in HA0 as [HA0|HA4]; [apply orb_prop in HA0 as [HA0|HA3]; [apply orb_prop in HA0 as [HA1|HA2]|]|].
        4:{ (* [comment removed for export] *)
            right. right. right. right.
            apply existsb_exists in HA4 as [[g0 m0] [Hing Hxi]]. cbn [fst snd] in Hxi. destruct (split_lit g0) as [gb gk] eqn:Hgs.
            rewrite ghosts_lo_eq in Hing. unfold ghosts_lo_ref in Hing. apply filter_In in Hing as [Hing Hc]. cbn [fst snd] in Hc.
            destruct (xlo k m0) as [l|] eqn:Hl0; [|discriminate]. destruct (wend k (g0, m0)) as [e|] eqn:He; [|discriminate].
            rewrite Hgs in Hc. apply andb_prop in Hc as [Hc Himg0]. apply andb_prop in Hc as [Hc1 Hc2]. apply Z.leb_le in Hc1.
            pose proof (wend_sound SEGS E MR k (g0, m0) e HK He) as WE. cbn [fst snd] in WE.
            pose proof (proj1 (forallb_forall _ _) Hkbflat (g0, m0) ltac:(apply in_app_iff; right; exact Hing)) as Hgbf. cbn [fst snd] in Hgbf. rewrite Hgs in Hgbf.
            destruct (bflat_x_sound SEGS E MR k gb gk m0 HK Hgbf) as (B1 & B2 & B3). rewrite estart_SA in B1, B2, B3.
            destruct (xinside_sound SEGS E MR k b off n gb gk m0 HK Hxi) as [X1 X2]. rewrite !estart_SA in X1, X2. unfold elenZ in X2. rewrite estart_SA in Hx.
            assert (Hu : uE E g0 = bv_unsigned (edenot E gb) + gk) by (unfold uE; rewrite (split_lit_denot E g0 gb gk Hgs); apply u64_lit; lia).
            (* [comment removed for export] *)
            pose proof (AzNodesAlloc2.ghosts_lo_arm_sound SEGS E MR k (acs_floor (a_maps cs)) (a_brk cs) (a_ylo cs) (g0, m0) gb gk e l HK (co_floor HC)
                          ltac:(rewrite (co_top HC); exact (proj1 HTc)) Hgs He Hl0 Hc1 Hgbf Hc2) as GEND. cbn [fst snd] in GEND. rewrite (co_top HC) in GEND.
            assert (HW : in_wins PERMc (bv_unsigned x)).
            { rewrite <- (co_perm HC). exists (uE E g0), (uE E g0 + uE E m0). split; [|rewrite Hu; unfold uE in *; lia].
              unfold wins_den. apply in_map_iff. exists (g0, m0). split; [reflexivity | exact Hing]. }
            destruct (proj1 HPo _ HW) as [Hh|[Hf|[Hc|Hsw]]]; [left; exact Hh | right; exact Hf | exfalso; unfold uE in *; lia |].
            (* [comment removed for export] *)
            exfalso. destruct (AzFrame.swin_byte SWIN G G_ro_img G_img_al SWIN_img _ Hsw) as [SW1 _].
            pose proof (ranges_apart_x_sound SEGS E MR k gb gk m0 (ELit 0) (g_img_lo G) (ELit (g_img_hi G - g_img_lo G)) HK Himg0) as DI.
            rewrite !estart_SA in DI. unfold elenZ in DI. cbn [edenot] in DI. rewrite (u64_lit 0) in DI by lia.
            pose proof G_img_al as (GA0 & _ & _). pose proof G_ro_img as (GR0 & GR1 & GR2). pose proof G_img_shlo as GS.
            rewrite (u64_lit (g_img_hi G - g_img_lo G)) in DI by (unfold SHMAPLO in GS; lia). unfold uE in *. lia. }
        - apply existsb_exists in HA1 as [[lb0 ln] [Hin Hxi]]. cbn [fst snd] in Hxi.
          destruct (split_lit lb0) as [lb lk] eqn:Hls.
          assert (Hlbf : bflat_x k lb lk ln = true).
          { apply in_app_iff in Hin as [Hin|Hin].
            - pose proof (proj1 (forallb_forall _ _) Hkbflat (lb0, ln) ltac:(apply in_app_iff; left; apply in_app_iff; left; exact Hin)) as X. cbn [fst snd] in X. rewrite Hls in X. exact X.
            - pose proof (proj1 (forallb_forall _ _) Hfkflat (lb0, ln) Hin) as X. cbn [fst snd] in X. rewrite Hls in X. exact X. }
          destruct (bflat_x_sound SEGS E MR k lb lk ln HK Hlbf) as (B1 & B2 & B3). rewrite estart_SA in B1, B2, B3.
          destruct (xinside_sound SEGS E MR k b off n lb lk ln HK Hxi) as [X1 X2]. rewrite !estart_SA in X1, X2. unfold elenZ in X2. rewrite estart_SA in Hx.
          assert (Hu : uE E lb0 = bv_unsigned (edenot E lb) + lk) by (unfold uE; rewrite (split_lit_denot E lb0 lb lk Hls); apply u64_lit; lia).
          apply in_app_iff in Hin as [Hin|Hin]; [left | right; left];
            (eapply (in_blocks_den E _ lb0 ln); [exact Hin|]); rewrite Hu; unfold uE; lia.
        - right. right. left. unfold above_sp in HA2. rewrite Hssp in HA2. apply andb_prop in HA2 as [_ HA2].   (* [comment removed for export] *)
          assert (XX : estart E (SA spb spk) <= estart E (SA b off) /\ estart E (SA b off) + elenZ E n <= estart E (SA spb spk) + elenZ E (ELit two47)).
          { apply orb_prop in HA2 as [HA2|HA2]; [exact (xinside_sound SEGS E MR k b off n spb spk (ELit two47) HK HA2)|].
            unfold xinside0 in HA2.
            lazymatch type of HA2 with (if ?c then _ else _) = _ => destruct c eqn:HB1; [|discriminate] end.
            pose proof (lin_ge0_sound SEGS E MR k _ _ HK HB1) as LA. pose proof (lin_ge0_sound SEGS E MR k _ _ HK HA2) as LB.
            cbn [xt_den] in LA, LB. unfold estart, elenZ. cbn [a_base a_off]. lia. }
          destruct XX as [X1 X2]. rewrite !estart_SA in X1. rewrite estart_SA in Hx.
          rewrite HTOPf, Hspv2. lia.
        - right. right. right. left. exact (img_lit_x_sound SEGS G E MR k b off n x HK HA3 E1 E2 Hx). }
      split; [|exact CASES].
      split; [|split; [exact NP|]].
      - destruct CASES as [Hb|[Hfk|[Ht|[Hro|[Hgh|Hgf]]]]]; [left; unfold HIDf; apply in_blocks_app; left; exact Hb
          | right; left; unfold HIDFf; apply in_blocks_app; left; exact Hfk
          | right; right; left; exact Ht | right; right; right; left; exact Hro
          | left; unfold HIDf; apply in_blocks_app; right; exact Hgh
          | right; left; unfold HIDFf; apply in_blocks_app; right; apply in_blocks_fusable in Hgf as (f & m & Hin & Hfz); exists f, m; split; [exact Hin | lia] ].
      - intros (lo & hi & Hin & _). cbn in Hin. destruct Hin. }
    (* [comment removed for export] *)
    set (inws := fun (x : word) => existsb (fun p => Z.leb (fst p) (bv_unsigned x) && Z.ltb (bv_unsigned x) (snd p))%bool (wins_den E ws)).
    set (M1 := fun x : word => if inws x then MR' x else MR x).
    assert (HCUT : forall ws0, (forall w, In w ws0 -> In w ws) ->
              know_ok SEGS E (fun x : word => if existsb (fun p => Z.leb (fst p) (bv_unsigned x) && Z.ltb (bv_unsigned x) (snd p))%bool (wins_den E ws0)
                                              then MR' x else MR x) (kcut ws0 k)).
    { induction ws0 as [|w ws0 IH]; intros Hsub.
      - cbn [kcut wins_den map existsb]. exact HK.
      - cbn [kcut]. rewrite kn_cutoutM_eq. destruct w as [wb0 wn]. cbn [fst snd]. destruct (split_lit wb0) as [wb wk] eqn:Hwsp.
        pose proof (proj1 (forallb_forall _ _) Hws (wb0, wn) (Hsub _ (or_introl eq_refl))) as Hw. cbn [fst snd] in Hw. rewrite Hwsp in Hw.
        apply andb_prop in Hw as [Hw _]. apply andb_prop in Hw as [Hw _]. apply andb_prop in Hw as [_ Hwbf].
        destruct (bflat_x_sound SEGS E MR k wb wk wn HK Hwbf) as (B1 & B2 & B3). rewrite estart_SA in B1, B2, B3.
        assert (Hu : uE E wb0 = bv_unsigned (edenot E wb) + wk) by (unfold uE; rewrite (split_lit_denot E wb0 wb wk Hwsp); apply u64_lit; lia).
        eapply know_ok_cutout; [apply IH; intros w' Hw'; apply Hsub; right; exact Hw'|].
        intros x Hx. rewrite estart_SA in Hx. unfold elenZ in Hx. cbn [wins_den map existsb fst snd].
        rewrite Hu. unfold uE at 1 2.
        replace (Z.leb (bv_unsigned (edenot E wb) + wk) (bv_unsigned x) && Z.ltb (bv_unsigned x) (bv_unsigned (edenot E wb) + wk + bv_unsigned (edenot E wn)))%bool with false; [reflexivity|].
        symmetry. apply andb_false_iff. destruct Hx as [Hx|Hx]; [left; apply Z.leb_gt; lia | right; apply Z.ltb_ge; lia]. }
    assert (HK1 : know_ok SEGS E M1 (kcut ws k)) by (apply HCUT; intros w Hw; exact Hw).
    (* [comment removed for export] *)
    assert (KEPTM : forall x : word,
      (in_blocks (blocks_den E keepblocks) (bv_unsigned x) \/ in_blocks (blocks_den E (a_fake cs)) (bv_unsigned x) \/ TOPf <= bv_unsigned x
       \/ (g_ro_lo G <= bv_unsigned x < g_img_hi G /\ ~ in_wins (g_privx G) (bv_unsigned x))
       \/ (in_blocks HIDc (bv_unsigned x) \/ in_blocks (map fusable HIDFc) (bv_unsigned x))) ->
      zone (nil_of SWIN) G PERMf TOPf HIDf HIDFf x ->
      MR' x = MR x /\ MR x = M x /\ MR' x = M' x).
    { intros x Hx Hz. destruct (KEPTB x Hx) as [H1 H2]. unfold MR', MR, GPS.Mr, mrestrict. rewrite H1, H2.
      split; [|split; reflexivity]. apply HF'. exact Hz. }
    assert (Hflat3 : forallb (fun bl => let '(lb, lk) := split_lit (fst bl) in bflat_x k lb lk (snd bl)) ((keepblocks ++ a_fake cs) ++ a_ghost cs) = true).
    { apply forallb_forall. intros y Hy. apply in_app_iff in Hy as [Hy|Hy]; [apply in_app_iff in Hy as [Hy|Hy]|].
      - exact (proj1 (forallb_forall _ _) Hkbflat y ltac:(apply in_app_iff; left; apply in_app_iff; left; exact Hy)).
      - exact (proj1 (forallb_forall _ _) Hfkflat y Hy).
      - exact (proj1 (forallb_forall _ _) Hkbflat y ltac:(apply in_app_iff; right; exact Hy)). }
    assert (HSTICKY : forall K, In K (List.filter (fun K => kentry_vars_lt v K && sticky_call k ((keepblocks ++ a_fake cs) ++ a_ghost cs) (acs_floor (a_maps cs)) (a_brk cs) (a_ylo cs) sp K)%bool k) ->
                    kentry_ok SEGS E'' MR' K).
    { intros K HinK. apply filter_In in HinK as [HinK Hkeep]. apply andb_prop in Hkeep as [HKv Hkeep].
      pose proof (proj1 (Forall_forall _ _) HK K HinK) as HKK.
      (* [comment removed for export] *)
      assert (DEF : forall b o n x, (owned_x k ((keepblocks ++ a_fake cs) ++ a_ghost cs) (acs_floor (a_maps cs)) (a_brk cs) (a_ylo cs) b o n
                                      || above_x k (a_brk cs) sp b o n)%bool = true ->
                estart E (SA b o) <= bv_unsigned x < estart E (SA b o) + elenZ E n ->
                (MR x <> None -> MR' x <> None) /\ (~ (g_img_lo G <= bv_unsigned x < g_img_hi G) \/ MR' x = MR x \/ errw G (bv_unsigned x))).   (* [comment removed for export] *)
      { intros b o n x Hox0 Hx.
        (* [comment removed for export] *)
        assert (Ho : in_blocks (blocks_den E keepblocks) (bv_unsigned x) \/ in_wins PERMc (bv_unsigned x) \/ (CEIL_run <= bv_unsigned x < SPTOPc)
                     \/ in_blocks (blocks_den E (a_fake cs)) (bv_unsigned x) \/ SPTOPc <= bv_unsigned x).
        { apply orb_prop in Hox0 as [Hox|Habv].
          - pose proof (owned_x_sound3 SEGS PERMc SPTOPc E MR k (keepblocks ++ a_fake cs) (a_ghost cs) (acs_floor (a_maps cs)) (a_brk cs) (a_ylo cs) b o n x HK Hflat3 (co_perm HC) (co_top HC) (co_floor HC) Hox Hx) as Ho0.
            destruct Ho0 as [Hb|[Hp|Hs]]; [| right; left; exact Hp | right; right; left; pose proof sfloor_ge; lia].
            rewrite AzNodesAlloc.blocks_den_app in Hb. apply in_blocks_app in Hb as [Hb|Hb]; [left; exact Hb | right; right; right; left; exact Hb].
          - pose proof (above_x_sound SEGS SPTOPc E MR k (a_brk cs) sp b o n x HK Habv (co_top HC) Hx) as [AB1 AB2].
            right; right; right; right. exact AB1. }
        (* [comment removed for export] *)
        assert (SWC : in_wins SWIN (bv_unsigned x) -> ~ errw G (bv_unsigned x) -> MR' x = MR x).   (* [comment removed for export] *)
        { intros Hsw Hnew. destruct (AzFrame.swin_byte SWIN G G_ro_img G_img_al SWIN_img _ Hsw) as [S1 S2'].
          assert (S2 : ~ in_wins (g_privx G) (bv_unsigned x)) by (intros Hpx; apply AzKnowLib.in_wins_privx in Hpx as [He|Hp']; [exact (Hnew He) | exact (S2' Hp')]).
          assert (KX1 : in_blocks (blocks_den E keepblocks) (bv_unsigned x) \/ in_blocks (blocks_den E (a_fake cs)) (bv_unsigned x) \/ TOPf <= bv_unsigned x
                        \/ (g_ro_lo G <= bv_unsigned x < g_img_hi G /\ ~ in_wins (g_privx G) (bv_unsigned x))
                        \/ (in_blocks HIDc (bv_unsigned x) \/ in_blocks (map fusable HIDFc) (bv_unsigned x))).
          { right; right; right; left. split; [pose proof G_ro_img; lia | exact S2]. }
          assert (KX2 : zone (nil_of SWIN) G PERMf TOPf HIDf HIDFf x).
          { split; [right; right; right; left; split; [pose proof G_ro_img; lia | exact S2]|].
            split; [intros Hpf; exact (proj2 (HPERMown _ Hpf) ltac:(pose proof G_ro_img; lia)) | intros (lo & hi & Hin0 & _); cbn in Hin0; destruct Hin0]. }
          exact (proj1 (KEPTM x KX1 KX2)). }
        (* [comment removed for export] *)
        assert (IMG : ~ (g_img_lo G <= bv_unsigned x < g_img_hi G) \/ in_wins SWIN (bv_unsigned x)).
        { pose proof G_img_ceil as GC. pose proof (proj1 HTc) as HTc1. destruct Ho as [Hb|[Hp|[Hst|[Hfk|Habove]]]]; [| | left; lia | | left; lia].
          - destruct Hb as (b' & m' & Hin' & Hbz').
            assert (HinL : In (b', m') (blocks_den E (a_vis cs))).
            { unfold blocks_den in Hin' |- *. apply in_map_iff in Hin' as [y [Hy Hiny]]. apply in_map_iff. exists y. split; [exact Hy|].
              eapply remove_pairs_incl; [exact Hrm | exact Hiny]. }
            destruct (hp_zone _ _ _ _ HP _ _ _ _ _ _ _ b' m' HA ltac:(apply in_app_iff; left; exact HinL)) as [(Z1 & Z2 & Z3 & Z4) _]. left. lia.
          - destruct (proj1 HPo _ Hp) as [Hh|[Hf|[Hc|Hsw]]]; [| | left; lia | right; exact Hsw].
            + destruct Hh as (b' & m' & Hin' & Hbz').
              destruct (hp_zone _ _ _ _ HP _ _ _ _ _ _ _ b' m' HA ltac:(apply in_app_iff; right; exact Hin')) as [(Z1 & Z2 & Z3 & Z4) _]. left. lia.
            + apply in_blocks_fusable in Hf as (f & m & Hinf & Hfz).
              destruct (hp_fzone _ _ _ _ HP _ _ _ _ _ _ _ f m HA ltac:(apply in_app_iff; right; exact Hinf)) as [(Z1 & Z2 & Z3 & Z4) _]. left. lia.
          - destruct Hfk as (f' & m' & Hin' & Hbz').
            destruct (hp_fzone _ _ _ _ HP _ _ _ _ _ _ _ f' m' HA ltac:(apply in_app_iff; left; exact Hin')) as [(Z1 & Z2 & Z3 & Z4) _]. left. lia. }
        (* [comment removed for export] *)
        assert (D1 : MR x <> None -> MR' x <> None).
        { intros HMx.
          (* [comment removed for export] *)
          assert (V1 : hid SHC VSHc E cs model x = false).
          { unfold MR, GPS.Mr, mrestrict in HMx. destruct (hid SHC VSHc E cs model x); [exfalso; apply HMx; reflexivity | reflexivity]. }
          assert (HM : M x <> None) by (unfold MR, GPS.Mr, mrestrict in HMx; rewrite V1 in HMx; exact HMx).
          pose proof (STICK x Ho HM) as HM'.
          unfold MR', GPS.Mr, mrestrict.
          (* [comment removed for export] *)
          assert (NOLZ : forall b' m', In (b', m') (blocks_den E' (a_vis tout) ++ HIDf ++ blocks_den E' (a_fake tout) ++ HIDFf) ->
                    b' <= bv_unsigned x < b' + m' -> lz model' x = false).
          { intros b' m' Hin' Hbz'. eapply (AINV_f_nolazy (nil_of SWIN) G SHC AINVH hprops_nil); [exact HA2t | exact Hin' | exact Hbz']. }
          assert (HIC : CEIL_run <= bv_unsigned x -> lz model' x = false).
          { intros Hc. pose proof (AINV_f_facts (nil_of SWIN) G SHC AINVH hprops_nil _ _ _ _ _ _ _ _ _ _ _ _ _ _ HAm) as HLB.
            unfold lz. destruct (page_in_ranges (page_base x) (m_vm_lazy model')) eqn:Hpg; [|reflexivity]. exfalso.
            apply existsb_exists in Hpg as [iv [Hin Hb]]. apply andb_prop in Hb as [PQ1 PQ2]. apply Z.leb_le in PQ1. apply Z.leb_le in PQ2.
            pose proof (proj1 (Forall_forall _ _) HLB iv Hin) as (L0 & L1 & L2). pose proof (page_base_le' x) as (P3 & P4 & P5). unfold page_size in PQ2. lia. }
          assert (V2 : hid SHC (VSHf HIDf HIDFf) E' tout model' x = false).
          { unfold hid. replace (lz model' x) with false; [reflexivity|]. symmetry.
            destruct Ho as [Hb|[Hp|[Hst|[Hfk|Habove]]]].
            - destruct Hb as (b' & m' & Hin' & Hbz'). apply (NOLZ b' m'); [|exact Hbz'].
              apply in_app_iff. right. apply in_app_iff. left. unfold HIDf. apply in_app_iff. left. exact Hin'.
            - destruct (proj1 HPo _ Hp) as [Hh|[Hf|[Hc|Hsw]]].
              + destruct Hh as (b' & m' & Hin' & Hbz'). apply (NOLZ b' m'); [|exact Hbz'].
                apply in_app_iff. right. apply in_app_iff. left. unfold HIDf. apply in_app_iff. right. exact Hin'.
              + apply in_blocks_fusable in Hf as (f & m & Hinf & Hfz). apply (NOLZ f m); [|lia].
                apply in_app_iff. right. apply in_app_iff. right. apply in_app_iff. right. unfold HIDFf. apply in_app_iff. right. exact Hinf.
              + apply HIC. pose proof (proj1 HTc). lia.
              + (* [comment removed for export] *)
                destruct (AzFrame.swin_byte SWIN G G_ro_img G_img_al SWIN_img _ Hsw) as [S1 _]. pose proof G_ro_img.
                pose proof (AINV_f_facts (nil_of SWIN) G SHC AINVH hprops_nil _ _ _ _ _ _ _ _ _ _ _ _ _ _ HAm) as HLB.
                unfold lz. destruct (page_in_ranges (page_base x) (m_vm_lazy model')) eqn:Hpg; [|reflexivity]. exfalso.
                apply existsb_exists in Hpg as [iv [Hin Hb]]. apply andb_prop in Hb as [PQ1 PQ2]. apply Z.leb_le in PQ1. apply Z.leb_le in PQ2.
                pose proof (proj1 (Forall_forall _ _) HLB iv Hin) as (L0 & L1 & L2). pose proof (page_base_le' x) as (P3 & P4 & P5).
                pose proof G_img_al as (GA0 & GA1 & GA2). unfold page_size in PQ2.
                lia.
            - apply HIC. lia.
            - (* [comment removed for export] *)
              destruct Hfk as (f' & m' & Hin' & Hbz'). apply (NOLZ f' m'); [|exact Hbz'].
              apply in_app_iff. right. apply in_app_iff. right. apply in_app_iff. right. unfold HIDFf. apply in_app_iff. left. exact Hin'.
            - apply HIC. pose proof (proj1 HTc). lia. }
          rewrite V2. exact HM'. }
        split; [exact D1|].
        destruct (errw_dec G (bv_unsigned x)) as [Hew|Hnew]; [right; right; exact Hew|].
        destruct IMG as [I1|I2]; [left; exact I1 | right; left; exact (SWC I2 Hnew)]. }
      assert (AG0 : kentry_ok SEGS E MR' K).
      { unfold sticky_call in Hkeep.
        destruct K as [[b o] w vv|[b o] nn|[b o] nn kb|ilo ihi|e m|e rlo rhi|[b o] nn|a1 n1 a2 n2|[b o] nn fc|[b o] nn | [b o] nn | fv flo fd]; try discriminate.
        - (* [comment removed for export] *) apply (proj1 (kwr_bytes SEGS E MR b o nn)) in HKK as [Hfl HS]. apply (proj2 (kwr_bytes SEGS E MR' b o nn)). split; [exact Hfl|].
          intros x Hx. destruct (DEF b o nn x Hkeep Hx) as [D1 _].
          exact (AzKnowLib.store_ok1_errno SEGS MR MR' x D1 (HS x Hx)).   (* [comment removed for export] *)
        - (* [comment removed for export] *) cbn [kentry_ok] in HKK |- *. destruct HKK as [Hfl HS]. split; [exact Hfl|]. intros i Hi.
          pose proof Hfl as (F1 & F2 & F3 & F4). set (x := Z_to_bv 64 (estart E (SA b o) + i)).
          assert (Hux : bv_unsigned x = estart E (SA b o) + i) by (unfold x; apply u64_lit; lia).
          destruct (DEF b o nn x Hkeep ltac:(rewrite Hux; lia)) as [D1 D2]. apply D1. apply HS. exact Hi. }
      assert (X : know_ok SEGS E'' MR' [K]).
      { eapply know_ok_agree'; [exact Hag'' | | constructor; [exact AG0 | constructor]].
        cbn [AP.kn_vars_lt]. rewrite HKv. reflexivity. }
      exact (Forall_inv X). }
    assert (HKEPT : forall K, In K (List.filter (fun K => kentry_vars_lt v K && keep_fact_call G k (keepblocks ++ a_fake cs) (ghosts_lo G k (acs_floor (a_maps cs)) (a_brk cs) (a_ylo cs) (a_ghost cs)) (prep_ws k ws) (acs_floor (a_maps cs)) (a_brk cs) (a_ylo cs) sp K)%bool (kcut ws k)) ->
                    kentry_ok SEGS E'' MR' K).
    { intros K HinK. apply filter_In in HinK as [HinK Hkeep]. apply andb_prop in Hkeep as [HKv Hkeep].
      pose proof (proj1 (Forall_forall _ _) HK1 K HinK) as HKK.
      (* [comment removed for export] *)
      assert (AG0 : kentry_ok SEGS E MR' K).
      { eapply kentry_ok_footprint; [exact HKK|]. intros x Hx.
        unfold M1. destruct (inws x) eqn:Hinws; [reflexivity|]. unfold in_kfoot, kfoot in Hx.
        unfold keep_fact_call in Hkeep.
        assert (KZ : forall b o n, 0 <= estart E (SA b o) -> estart E (SA b o) < 2 ^ 64 ->
                  estart E (SA b o) <= bv_unsigned x < estart E (SA b o) + elenZ E n ->
                  ((existsb (fun bl => let '(lb, lk) := split_lit (fst bl) in xinside k b o n lb lk (snd bl)) (keepblocks ++ a_fake cs)
                    || above_sp k (acs_floor (a_maps cs)) (a_brk cs) (a_ylo cs) sp b o n || img_lit_x G k b o n
                    || existsb (fun g => let '(gb, gk) := split_lit (fst g) in xinside k b o n gb gk (snd g)) (ghosts_lo G k (acs_floor (a_maps cs)) (a_brk cs) (a_ylo cs) (a_ghost cs)))
                   && apart_ws k (prep_ws k ws) b o n)%bool = true ->
                  MR' x = MR x).
        { intros b o n E1 E2 Hxx Hkb. destruct (ZONE b o n E1 E2 x Hxx Hkb) as [Z1 Z2]. exact (proj1 (KEPTM x Z2 Z1)). }
        destruct K as [[b o] w vv|[b o] nn|[b o] nn kb|ilo ihi|e m|e rlo rhi|[b o] nn|a1 n1 a2 n2|[b o] nn fc|[b o] nn | [b o] nn | fv flo fd];
          cbn [kentry_range] in Hkeep; try (destruct Hx; fail); try discriminate Hkeep; cbn [kentry_ok] in HKK.
        6:{ (* [comment removed for export] *)
            destruct (APS.kfpc_test (bv_unsigned (edenot E fv)) (bv_unsigned (edenot E flo))) eqn:KT; [|destruct Hx].
            unfold APS.kfpc_test in KT. apply andb_prop in KT as [KT _]. apply andb_prop in KT as [KT _]. apply Z.leb_le in KT.
            pose proof (lin_ge0_sound SEGS E MR k _ _ HK Hkeep) as L. cbn [xt_den] in L.
            assert (HGE : TOPf <= bv_unsigned x) by (rewrite HTOPf; unfold uE in *; lia).
            assert (NP : ~ in_wins PERMf (bv_unsigned x)).
            { intros Hp. rewrite <- HPERMf in Hp. destruct Hp as (wlo & whi & Hin & Hr).
              assert (C : inws x = true); [|rewrite Hinws in C; discriminate].
              unfold inws. apply existsb_exists. exists (wlo, whi). split; [exact Hin|]. cbn [fst snd].
              apply andb_true_intro. split; [apply Z.leb_le; lia | apply Z.ltb_lt; lia]. }
            eapply (fun Hz => proj1 (KEPTM x (or_intror (or_intror (or_introl HGE))) Hz)).
            split; [right; right; left; exact HGE|]. split; [exact NP|]. intros (wlo & whi & Hin & _). cbn in Hin. destruct Hin. }
        4:{ (* [comment removed for export] *) apply andb_prop in Hkeep as [Hkeep Hdj]. apply andb_prop in Hkeep as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
            assert (Him : g_ro_lo G <= bv_unsigned x < g_img_hi G /\ ~ in_wins (g_privx G) (bv_unsigned x)).
            { split; [lia|]. eapply lit_disjoint_sound; [exact Hdj | lia]. }
            eapply (fun Hz => proj1 (KEPTM x (or_intror (or_intror (or_intror (or_introl Him)))) Hz)).
            split; [right; right; right; left; exact Him|]. split.
            - (* [comment removed for export] *)
              intros Hp. exact (proj2 (HPERMown _ Hp) ltac:(pose proof G_ro_img; lia)).
            - intros (lo & hi & Hin & _). cbn in Hin. destruct Hin. }
        1: destruct HKK as (Hw8 & Hfl & Hrd).
        all: try (destruct HKK as [Hfl HKrest]).
        all: destruct Hfl as (F1 & F2 & F3 & F4).
        1: { apply (KZ b o (ELit (Z.of_nat w))); [lia | lia | | exact Hkeep]. rewrite APS.elenZ_lit by lia. exact Hx. }
        all: apply (KZ b o nn); [lia | lia | exact Hx | exact Hkeep]. }
      (* [comment removed for export] *)
      assert (X : know_ok SEGS E'' MR' [K]).
      { eapply know_ok_agree'; [exact Hag'' | | constructor; [exact AG0 | constructor]].
        cbn [AP.kn_vars_lt]. rewrite HKv. reflexivity. }
      exact (Forall_inv X). }
    (* [comment removed for export] *)
    set (SHZ := fun x : Z => shz G E (keepblocks ++ a_fake cs ++ ghosts_lo G k (acs_floor (a_maps cs)) (a_brk cs) (a_ylo cs) (a_ghost cs)) (uE E sp) x).
    (* [comment removed for export] *)
    assert (SHZ3 : forall x, SHZ x -> shz G E (keepblocks ++ a_fake cs) (uE E sp) x
                                 \/ exists lo hi, In (lo, hi) PERMc /\ lo < hi /\ hi <= SPTOPc /\ (hi <= g_img_lo G \/ g_img_hi G <= lo) /\ in_shadow SB lo (hi - lo) x).   (* [comment removed for export] *)
    { intros x Hx. unfold SHZ, shz in Hx. destruct Hx as [Hl|[Hs|Hi]]; [|left; right; left; exact Hs | left; right; right; exact Hi].
      destruct Hl as (bb & nn & Hinb & Hsh). rewrite app_assoc, AzNodesAlloc.blocks_den_app in Hinb.
      apply in_app_iff in Hinb as [Hinb|Hinb]; [left; left; exists bb, nn; split; [exact Hinb | exact Hsh]|].
      right. rewrite ghosts_lo_eq in Hinb. unfold blocks_den, ghosts_lo_ref in Hinb. apply in_map_iff in Hinb as [[g0 m0] [Heq Hing]]. cbn [fst snd] in Heq. injection Heq as <- <-.
      apply filter_In in Hing as [Hing Hc]. cbn [fst snd] in Hc.
      destruct (xlo k m0) as [l|] eqn:Hl0; [|discriminate]. destruct (wend k (g0, m0)) as [e|] eqn:He; [|discriminate].
      destruct (split_lit g0) as [gb gk] eqn:Hgs.
      apply andb_prop in Hc as [Hc Himg0]. apply andb_prop in Hc as [Hc1 Hc2]. apply Z.leb_le in Hc1.
      pose proof (xlo_sound SEGS E MR k m0 l HK Hl0). pose proof (wend_sound SEGS E MR k (g0, m0) e HK He) as WE. cbn [fst snd] in WE.
      pose proof (proj1 (forallb_forall _ _) Hkbflat (g0, m0) ltac:(apply in_app_iff; right; exact Hing)) as Hgbf. cbn [fst snd] in Hgbf. rewrite Hgs in Hgbf.
      destruct (bflat_x_sound SEGS E MR k gb gk m0 HK Hgbf) as (B1 & B2 & B3). rewrite estart_SA in B1, B2, B3.
      assert (Hu : uE E g0 = bv_unsigned (edenot E gb) + gk) by (unfold uE; rewrite (split_lit_denot E g0 gb gk Hgs); apply u64_lit; lia).
      pose proof (AzNodesAlloc2.ghosts_lo_arm_sound SEGS E MR k (acs_floor (a_maps cs)) (a_brk cs) (a_ylo cs) (g0, m0) gb gk e l HK (co_floor HC)
                    ltac:(rewrite (co_top HC); exact (proj1 HTc)) Hgs He Hl0 Hc1 Hgbf Hc2) as GEND. cbn [fst snd] in GEND. rewrite (co_top HC) in GEND.
      pose proof (ranges_apart_x_sound SEGS E MR k gb gk m0 (ELit 0) (g_img_lo G) (ELit (g_img_hi G - g_img_lo G)) HK Himg0) as DI.
      rewrite !estart_SA in DI. unfold elenZ in DI. cbn [edenot] in DI. rewrite (u64_lit 0) in DI by lia.
      pose proof G_img_al as (GA0 & _ & _). pose proof G_ro_img as (GR0 & GR1 & GR2). pose proof G_img_shlo as GS.
      rewrite (u64_lit (g_img_hi G - g_img_lo G)) in DI by (unfold SHMAPLO in GS; lia).
      exists (uE E g0), (uE E g0 + uE E m0).
      split; [|split; [unfold uE in *; lia | split; [rewrite Hu; unfold uE in *; lia | split; [rewrite Hu; unfold uE in *; lia | replace (uE E g0 + uE E m0 - uE E g0) with (uE E m0) by lia; exact Hsh]]]].
      rewrite <- (co_perm HC). unfold wins_den. apply in_map_iff. exists (g0, m0). split; [reflexivity | exact Hing]. }
    assert (GLSH : forall x, (exists lo hi, In (lo, hi) PERMc /\ lo < hi /\ hi <= SPTOPc /\ (hi <= g_img_lo G \/ g_img_hi G <= lo) /\ in_shadow SB lo (hi - lo) x) ->
                   in_lshadow (HIDc ++ HIDFc) x /\ SB <= x < HEAPLO).
    { intros x (lo & hi & Hin & Hlt & Hhi & Hoff & Hsh). split.
      - apply (AzFrame.AINV_f_pshadow_lo SWIN G SHC AINVH HP G_ro_img G_img_al PERMc SPTOPc HIDc HIDFc M0c B0c C0c _ _ _ _ _ _ _ (co_ainv HC) lo hi x Hin Hlt Hhi); [|exact Hsh].
        intros slo shi Hsin. destruct (SWIN_img slo shi Hsin) as (SW1 & SW2 & _). pose proof G_ro_img. lia.
      - refine (proj2 (AzFrame.AINV_f_pshadow SWIN G SHC AINVH HP G_ro_img G_img_al G_img_shlo SWIN_img PERMc SPTOPc HIDc HIDFc M0c B0c C0c _ _ _ _ _ _ _ (co_ainv HC) x _)).
        exists lo, hi. split; [exact Hin | split; [exact Hlt | exact Hsh]]. }
    assert (SHVIS : forall x : word, SHZ (bv_unsigned x) ->
              hid SHC VSHc E cs model x = false /\ hid SHC (VSHf HIDf HIDFf) E' tout model' x = false).
    { intros x Hx0. unfold hid. destruct (SHZ3 _ Hx0) as [Hx|Hg].
      2:{ destruct (GLSH _ Hg) as [(gb & gn & Hgin & [GZ1 GZ2]) _].
          assert (W1 : vlz SHC VSHc E cs (bv_unsigned x) = true).
          { unfold vlz. apply orb_true_intro. left. apply orb_true_intro. right. unfold VSHf, in_shv.
            apply existsb_exists. exists (gb, gn). split; [exact Hgin|]. cbn [fst snd]. apply andb_true_intro. split; [apply Z.leb_le; lia | apply Z.ltb_lt; lia]. }
          assert (W2 : vlz SHC (VSHf HIDf HIDFf) E' tout (bv_unsigned x) = true).
          { unfold vlz. apply orb_true_intro. left. apply orb_true_intro. right. unfold VSHf, HIDf, HIDFf, in_shv.
            apply existsb_exists. exists (gb, gn). split; [|cbn [fst snd]; apply andb_true_intro; split; [apply Z.leb_le; lia | apply Z.ltb_lt; lia]].
            apply in_app_iff in Hgin as [Hgin|Hgin]; apply in_app_iff; [left | right]; apply in_app_iff; right; exact Hgin. }
          rewrite W1, W2. cbn [negb andb]. destruct (lz model x); destruct (lz model' x); split; reflexivity. }
      assert (V1 : vlz SHC VSHc E cs (bv_unsigned x) = true).
      { unfold vlz. unfold shz in Hx. rewrite AzNodesAlloc.blocks_den_app in Hx. destruct Hx as [Hl|[Hs|Hi]].
        - rewrite <- orb_assoc. apply orb_true_intro. right. apply (proj2 (in_shv_shb VSHc E cs (bv_unsigned x))).
          eapply in_lshadow_mono; [|exact Hl]. intros y Hy. unfold vis_ranges. apply in_app_iff. right. rewrite AzNodesAlloc.blocks_den_app.
          apply in_app_iff in Hy as [Hy|Hy]; apply in_app_iff; [left | right; exact Hy].
          apply (Permutation.Permutation_in y (Permutation.Permutation_sym Hperm_vis)). apply in_app_iff. right. exact Hy.
        - rewrite (hp_shc_stack _ _ _ _ HP); [reflexivity|]. exact Hs.   (* [comment removed for export] *)
        - rewrite (hp_shc_image _ _ _ _ HP); [reflexivity|]. exact Hi. }
      assert (V2 : vlz SHC (VSHf HIDf HIDFf) E' tout (bv_unsigned x) = true).
      { unfold vlz. unfold shz in Hx. rewrite AzNodesAlloc.blocks_den_app in Hx. destruct Hx as [Hl|[Hs|Hi]].
        - rewrite <- orb_assoc. apply orb_true_intro. right. apply (proj2 (in_shv_shb (VSHf HIDf HIDFf) E' tout (bv_unsigned x))).
          eapply in_lshadow_mono; [|exact Hl]. intros y Hy. unfold vis_ranges, VSHf, HIDf, HIDFf. apply in_app_iff. left.
          apply in_app_iff in Hy as [Hy|Hy]; apply in_app_iff; [left | right]; apply in_app_iff; left; exact Hy.
        - rewrite (hp_shc_stack _ _ _ _ HP); [reflexivity|]. exact Hs.   (* [comment removed for export] *)
        - rewrite (hp_shc_image _ _ _ _ HP); [reflexivity|]. exact Hi. }
      rewrite V1, V2. cbn [negb andb]. destruct (lz model x); destruct (lz model' x); split; reflexivity. }
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
    (* [comment removed for export] *)
    assert (SHLO : forall x : word, SHZ (bv_unsigned x) -> SB <= bv_unsigned x < HEAPLO).
    { intros x Hx0. destruct (SHZ3 _ Hx0) as [Hx|Hg]; [|exact (proj2 (GLSH _ Hg))].
      unfold shz in Hx. rewrite AzNodesAlloc.blocks_den_app in Hx.
      pose proof (AzFrame.band_lits G G_img_al) as (BL1 & BL2 & BL3 & BL4 & BL5 & BL6 & BL7).
      destruct Hx as [Hl|[Hs|Hi]].
      - destruct Hl as (bb & nn & Hinb & Hsh). assert (HBB : ablk_ok G bb nn).
        { unfold blocks_den in Hinb. rewrite <- map_app in Hinb. apply in_map_iff in Hinb as [[b0 n0] [Heq Hin0]]. cbn in Heq. injection Heq as <- <-.
          apply in_app_iff in Hin0 as [Hin0|Hin0].
          - pose proof (hp_zone _ _ _ _ HP _ _ _ _ _ _ _ (uE E b0) (uE E n0) HA) as Z2.
            destruct Z2 as [Z2 _]; [|exact Z2]. apply in_app_iff. left. apply (Permutation.Permutation_in _ (Permutation.Permutation_sym Hperm_vis)).
            apply in_app_iff. right. unfold blocks_den. apply in_map_iff. exists (b0, n0). split; [reflexivity | exact Hin0].
          - pose proof (hp_fzone _ _ _ _ HP _ _ _ _ _ _ _ (uE E b0) (uE E n0) HA) as Z2.
            destruct Z2 as [Z2 _]; [|exact Z2]. apply in_app_iff. left. unfold blocks_den. apply in_map_iff. exists (b0, n0). split; [reflexivity | exact Hin0]. }
        destruct (AzFrame.ablk_shadow G G_ro_img G_img_al G_img_shlo bb nn (bv_unsigned x) HBB Hsh) as (S1 & S2 & S3 & S4). unfold HEAPLO, KHI in *. lia.
      - unfold in_sshadow in Hs. lia.
      - destruct (AzFrame.ishadow_bounds G G_ro_img G_img_al G_img_shlo _ Hi) as (I1 & I2 & I3). pose proof G_img_al as (GA0 & _). unfold HEAPLO, KHI, SB in *.
        Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
        lia.
        Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false). }
    (* [comment removed for export] *)
    assert (PERMf_offband : forall z, in_wins PERMf z -> ~ (SHMAPLO <= z < KHI)).
    { intros z Hp. pose proof (AzFrame.band_lits G G_img_al) as (BL1 & BL2 & BL3 & BL4 & BL5 & BL6 & BL7).
      destruct (HPERMown _ Hp) as [[Hb|[Hpc'|[Hst|Hff]]] Hnimg].
      - destruct Hb as (b' & m' & Hin' & Hbz').
        assert (HinL : In (b', m') (blocks_den E (a_vis cs))).
        { unfold blocks_den in Hin' |- *. apply in_map_iff in Hin' as [y [Hy Hiny]]. apply in_map_iff. exists y. split; [exact Hy|].
          eapply remove_pairs_incl; [exact Hrm | exact Hiny]. }
        destruct (hp_zone _ _ _ _ HP _ _ _ _ _ _ _ b' m' HA ltac:(apply in_app_iff; left; exact HinL)) as [(Z1 & Z2 & Z3 & Z4) _]. unfold SHMAPLO, KHI in *. lia.
      - destruct (proj1 HPo _ Hpc') as [Hh|[Hf|[Hc|Hsw]]].
        + destruct Hh as (b' & m' & Hin' & Hbz'). destruct (hp_zone _ _ _ _ HP _ _ _ _ _ _ _ b' m' HA ltac:(apply in_app_iff; right; exact Hin')) as [(Z1 & Z2 & Z3 & Z4) _]. unfold SHMAPLO, KHI in *. lia.
        + apply in_blocks_fusable in Hf as (f & m & Hinf & Hfz).
          destruct (hp_fzone _ _ _ _ HP _ _ _ _ _ _ _ f m HA ltac:(apply in_app_iff; right; exact Hinf)) as [(Z1 & Z2 & Z3 & Z4) _]. unfold SHMAPLO, KHI in *. lia.
        + pose proof ceil_rng. unfold KHI in *. lia.
        + exfalso. destruct (AzFrame.swin_byte SWIN G G_ro_img G_img_al SWIN_img _ Hsw) as [SW1 _]. pose proof G_ro_img. lia.
      - pose proof ceil_rng. unfold KHI in *. lia.
      - apply in_blocks_fusable in Hff as (f & m & Hinf & Hfz).
        destruct (hp_fzone _ _ _ _ HP _ _ _ _ _ _ _ f m HA ltac:(apply in_app_iff; left; exact Hinf)) as [(Z1 & Z2 & Z3 & Z4) _]. unfold SHMAPLO, KHI in *. lia. }
    assert (SHZONE : forall x : word, SHZ (bv_unsigned x) -> zone (nil_of SWIN) G PERMf TOPf HIDf HIDFf x).
    { intros x Hx0. pose proof (SHLO x Hx0) as XLO. pose proof (AzFrame.band_lits G G_img_al) as (BL1 & BL2 & BL3 & BL4 & BL5 & BL6 & BL7).
      split; [|split; [intros Hp; apply (PERMf_offband _ Hp); unfold SHMAPLO, SB, HEAPLO, KHI in *; lia|intros (lo & hi & Hin & _); cbn in Hin; destruct Hin]].
      destruct (SHZ3 _ Hx0) as [Hx|Hg].
      2:{ destruct (GLSH _ Hg) as [Hl _]. right. right. right. right. left. eapply in_lshadow_mono; [|exact Hl]. intros y Hy. unfold HIDf, HIDFf.
          apply in_app_iff in Hy as [Hy|Hy]; apply in_app_iff; [left | right]; apply in_app_iff; right; exact Hy. }
      unfold shz in Hx. rewrite AzNodesAlloc.blocks_den_app in Hx.
      destruct Hx as [Hl|[Hs|Hi]].
      + right. right. right. right. left. eapply in_lshadow_mono; [|exact Hl]. intros y Hy. unfold HIDf, HIDFf.
        apply in_app_iff in Hy as [Hy|Hy]; apply in_app_iff; [left | right]; apply in_app_iff; left; exact Hy.
      + right. right. right. right. right. left. exact Hs.
      + right. right. right. right. right. right. left. exact Hi. }
    assert (SHM : forall x : word, SHZ (bv_unsigned x) -> MR' x = MR x).
    { intros x Hx. destruct (SHVIS x Hx) as [H1 H2]. unfold MR', MR, GPS.Mr, mrestrict. rewrite H1, H2. apply HF'. exact (SHZONE x Hx). }
    assert (HSHAD : forall K, In K (List.filter (fun K => kentry_vars_lt v K && keep_shadow G k (keepblocks ++ a_fake cs ++ ghosts_lo G k (acs_floor (a_maps cs)) (a_brk cs) (a_ylo cs) (a_ghost cs)) (acs_floor (a_maps cs)) (a_brk cs) (a_ylo cs) sp K)%bool k) ->
                    kentry_ok SEGS E'' MR' K).
    { intros K HinK. apply filter_In in HinK as [HinK Hkeep]. apply andb_prop in Hkeep as [HKv Hkeep].
      pose proof (proj1 (Forall_forall _ _) HK K HinK) as HKK.
      assert (AG0 : kentry_ok SEGS E MR' K).
      { eapply kentry_ok_footprint; [exact HKK|]. intros x Hx. apply SHM. unfold SHZ.
        exact (keep_shadow_foot SEGS G E MR k (keepblocks ++ a_fake cs ++ ghosts_lo G k (acs_floor (a_maps cs)) (a_brk cs) (a_ylo cs) (a_ghost cs)) (acs_floor (a_maps cs)) (a_brk cs) (a_ylo cs) sp K x HK HKK Hkeep (co_floor HC) Hx). }
      assert (X : know_ok SEGS E'' MR' [K]).
      { eapply know_ok_agree'; [exact Hag'' | | constructor; [exact AG0 | constructor]].
        cbn [AP.kn_vars_lt]. rewrite HKv. reflexivity. }
      exact (Forall_inv X). }
    (* [comment removed for export] *)
    assert (HKDISJ : forall K, In K (kdisj_new (map (ptsubst th') (a_vis tout)) (keepblocks ++ a_fake cs)) -> kentry_ok SEGS E'' MR' K).
    { intros K HinK. unfold kdisj_new in HinK. apply in_flat_map in HinK as [nb [Hnb HinK]]. apply in_map_iff in HinK as [ob [<- Hob]].
      change (estart E'' (SA (fst nb) 0) + elenZ E'' (snd nb) <= estart E'' (SA (fst ob) 0)
              \/ estart E'' (SA (fst ob) 0) + elenZ E'' (snd ob) <= estart E'' (SA (fst nb) 0)).
      unfold estart, elenZ. cbn [a_base a_off]. rewrite !Z.add_0_r.
      assert (Hnb' : In (uE E'' (fst nb), uE E'' (snd nb)) (blocks_den E' (a_vis tout))).
      { rewrite <- HBD2. unfold blocks_den. apply in_map_iff. exists nb. split; [reflexivity | exact Hnb]. }
      apply in_split in Hnb' as (L1 & L2 & HL).
      apply in_app_iff in Hob as [Hob|Hob].
      - assert (Hob' : In (uE E'' (fst ob), uE E'' (snd ob)) (blocks_den E keepblocks)).
        { rewrite <- HBD1. unfold blocks_den. apply in_map_iff. exists ob. split; [reflexivity | exact Hob]. }
        unfold uE in *.
        eapply (hp_disj _ _ _ _ HP _ _ _ _ _ _ _ L1 (L2 ++ HIDf) _ _ _ _ HA').
        + rewrite HL. rewrite <- app_assoc. reflexivity.
        + rewrite app_assoc. apply in_app_iff. right. unfold HIDf. apply in_app_iff. left. exact Hob'.
      - assert (Hob' : In (uE E'' (fst ob), uE E'' (snd ob)) (blocks_den E (a_fake cs))).
        { rewrite <- HBD3. unfold blocks_den. apply in_map_iff. exists ob. split; [reflexivity | exact Hob]. }
        unfold uE in *.
        eapply (hp_bfdisj _ _ _ _ HP _ _ _ _ _ _ _ _ _ _ _ HA').
        + rewrite HL. apply in_app_iff. left. apply in_app_iff. right. left. reflexivity.
        + apply in_app_iff. right. unfold HIDFf. apply in_app_iff. left. exact Hob'. }
    (* [comment removed for export] *)
    assert (HKDISJ2 : know_ok SEGS E'' MR' post ->
              forall K, In K (kdisj_gh post (map (ptsubst th') (a_vis tout)) (ghosts_ne k (a_ghost cs))) -> kentry_ok SEGS E'' MR' K).
    { intros HPOST K HinK. unfold kdisj_gh in HinK. apply in_flat_map in HinK as [nb [Hnb HinK]].
      destruct (xlo post (snd nb)) as [l0|] eqn:Hl0; [|destruct HinK].
      destruct (Z.leb_spec 1 l0) as [Hl1|Hl1]; [|destruct HinK].
      apply in_map_iff in HinK as [gw [<- Hgw]].
      pose proof (xlo_sound SEGS E'' MR' post (snd nb) l0 HPOST Hl0) as NBL.
      change (estart E'' (SA (fst nb) 0) + elenZ E'' (snd nb) <= estart E'' (SA (fst gw) 0)
              \/ estart E'' (SA (fst gw) 0) + elenZ E'' (snd gw) <= estart E'' (SA (fst nb) 0)).
      unfold estart, elenZ. cbn [a_base a_off]. rewrite !Z.add_0_r.
      assert (Hnb' : In (uE E'' (fst nb), uE E'' (snd nb)) (blocks_den E' (a_vis tout))).
      { rewrite <- HBD2. unfold blocks_den. apply in_map_iff. exists nb. split; [reflexivity | exact Hnb]. }
      (* [comment removed for export] *)
      assert (HGD : blocks_den E'' (ghosts_ne k (a_ghost cs)) = blocks_den E (ghosts_ne k (a_ghost cs))).
      { eapply blocks_den_agree; [exact Hag''|]. unfold ghosts_ne. apply pairs_vars_lt_filter. exact (pairs_vars_lt_app_r _ _ _ Fallow). }
      assert (Hgw' : In (uE E'' (fst gw), uE E'' (snd gw)) (blocks_den E (ghosts_ne k (a_ghost cs)))).
      { rewrite <- HGD. unfold blocks_den. apply in_map_iff. exists gw. split; [reflexivity | exact Hgw]. }
      destruct (ghosts_ne_in SEGS PERMc E MR k (a_ghost cs) _ _ HK (co_perm HC) Hgw') as [HW HM].
      set (b' := uE E'' (fst nb)) in *. set (l' := uE E'' (snd nb)) in *. set (g := uE E'' (fst gw)) in *. set (m := uE E'' (snd gw)) in *.
      unfold uE in *.
      destruct (hp_zone _ _ _ _ HP _ _ _ _ _ _ _ b' l' HA' ltac:(apply in_app_iff; left; exact Hnb')) as [(ZB1 & ZB2 & ZB3 & ZB4) _].
      apply in_split in Hnb' as (L1 & L2 & HL).
      destruct (Z_le_gt_dec (b' + l') g) as [D1|D1]; [left; exact D1|].
      destruct (Z_le_gt_dec (g + m) b') as [D2|D2]; [right; exact D2|].
      exfalso. set (z := Z.max b' g).
      assert (Hz1 : b' <= z < b' + l') by (subst z; lia). assert (Hz2 : g <= z < g + m) by (subst z; lia).
      destruct (proj1 HPo z ltac:(exists g, (g + m); split; [exact HW | lia])) as [Hh|[Hf|[Hc|Hsw]]].
      4:{ destruct (AzFrame.swin_byte SWIN G G_ro_img G_img_al SWIN_img _ Hsw) as [SW1 _]. pose proof G_ro_img. lia. }
      - destruct Hh as (bh & nh & Hinh & Hbz).
        assert (DJ : b' + l' <= bh \/ bh + nh <= b').
        { eapply (hp_disj _ _ _ _ HP _ _ _ _ _ _ _ L1 (L2 ++ HIDf) _ _ _ _ HA').
          + rewrite HL. rewrite <- app_assoc. reflexivity.
          + rewrite app_assoc. apply in_app_iff. right. unfold HIDf. apply in_app_iff. right. exact Hinh. }
        lia.
      - apply in_blocks_fusable in Hf as (f & mf & Hinf & Hfz).
        assert (DJ : b' + l' <= f \/ f + mf <= b').
        { eapply (hp_bfdisj _ _ _ _ HP _ _ _ _ _ _ _ _ _ _ _ HA').
          + rewrite HL. apply in_app_iff. left. apply in_app_iff. right. left. reflexivity.
          + apply in_app_iff. right. unfold HIDFf. apply in_app_iff. right. exact Hinf. }
        lia.
      - lia. }
    apply (Hk E'' fx' R' M' model').
    + split; [eapply env_agree_le; [exact Hag'' | exact Fle] | exact Hag''].
    + change (cs_ok E'' cs2 fx' R' M' model').
      constructor; unfold cs2; cbn [a_ss s_regs s_log s_know kn a_vis a_fake a_meter a_fd a_totsz a_eager a_ghost a_brk mk_ss].
      * exact HRout.
      * reflexivity.
      * fold cs2. rewrite HMR2.
        assert (HPOST : know_ok SEGS E'' MR' post).
        { unfold post, know_ok. apply Forall_app. split; [exact HKout|]. apply Forall_app. split; [apply Forall_forall; exact HSTICKY|].
          apply Forall_app. split; [apply Forall_forall; exact HKEPT|]. apply Forall_app. split; apply Forall_forall; [exact HSHAD | exact HKDISJ]. }
        apply Forall_app. split; [exact HPOST|]. apply Forall_forall. exact (HKDISJ2 HPOST).
      * exact Hhalt'.
      * rewrite Hfs2, Hfs'. exact (co_fs HC).
      * rewrite Hfdcs. eapply fds_ok_model; [exact Hfds2 | exact Hfs2 |]. pose proof (co_fds HCo) as X. rewrite Hfdout in X. exact X.
      * (* [comment removed for export] *)
        split; [|split; [exact HPo | split; [exact HTc|split]]].
        -- rewrite AzNodesAlloc.blocks_den_app, HBD1, HBD2, HBD3, AzNodesAlloc.bcost_app, AzNodesAlloc.bcount_app, HBC1, HBC2, HMT2.
           replace (B0c + (bcost E keepblocks + bcost E' (a_vis tout))) with (B0f + bcost E' (a_vis tout)) by (unfold B0f; lia).
           replace (bcount (map (ptsubst th') (a_vis tout))) with (bcount (a_vis tout)) by (unfold bcount; rewrite length_map; reflexivity).
           replace (C0c + (bcount keepblocks + bcount (a_vis tout))) with (C0f + bcount (a_vis tout)) by (unfold C0f; lia).
           rewrite Hfkout in HA'. cbn [blocks_den map app] in HA'. unfold HIDFf in HA'.
           eapply (hp_perm _ _ _ _ HP); [| apply Permutation.Permutation_refl | exact HA']. unfold HIDf. rewrite app_assoc. apply Permutation.Permutation_app_tail. apply Permutation.Permutation_app_comm.
        -- intros a Hza. rewrite <- (HF a Hza). apply HF'.
           destruct Hza as (Hz1 & Hnp & Hnsw). split; [|split; [|intros (lo & hi & Hin & _); cbn in Hin; destruct Hin]].
           ++ destruct Hz1 as [Hh|[Hhf|[Ht|[Hro|[Hlsh|[Hssh|[Hish|Hflo]]]]]]].
              ** left. unfold HIDf. apply in_blocks_app. right. exact Hh.
              ** right. left. unfold HIDFf. apply in_blocks_app. right. exact Hhf.
              ** right. right. left. rewrite HTOPf. lia.
              ** right. right. right. left. exact Hro.
              ** right. right. right. right. left. eapply in_lshadow_mono; [|exact Hlsh]. intros y Hy. unfold HIDf, HIDFf.
                 apply in_app_iff in Hy as [Hy|Hy]; apply in_app_iff; [left | right]; apply in_app_iff; right; exact Hy.
              ** right. right. right. right. right. left. exact Hssh.   (* [comment removed for export] *)
              ** right. right. right. right. right. right. left. exact Hish.
              ** right. right. right. right. right. right. right. exact Hflo.   (* [comment removed for export] *)
           ++ intros Hp. destruct (HPERMown _ Hp) as [[Hb|[Hpc'|[Hst|Hff]]] _].
              ** destruct Hb as (b & m & Hin & Hbz).
                 assert (HinL : In (b, m) (blocks_den E (a_vis cs))).
                 { unfold blocks_den in Hin |- *. apply in_map_iff in Hin as [x [Hx Hinx]]. apply in_map_iff. exists x. split; [exact Hx|].
                   eapply remove_pairs_incl; [exact Hrm | exact Hinx]. }
                 exfalso. eapply (gowned_not_zone SWIN G SHC AINVH HP G_ro_img G_img_al G_img_shlo PERMc SPTOPc HIDc HIDFc M0c B0c C0c
                                   _ _ _ _ _ _ _ (co_ainv HC) a); [|exact (conj Hz1 (conj Hnp Hnsw))].
                 left. left. apply in_blocks_app. left. exists b, m. split; [exact HinL | exact Hbz].
              ** exact (Hnp Hpc').
              ** exfalso. eapply (gowned_not_zone SWIN G SHC AINVH HP G_ro_img G_img_al G_img_shlo PERMc SPTOPc HIDc HIDFc M0c B0c C0c
                                   _ _ _ _ _ _ _ (co_ainv HC) a); [|exact (conj Hz1 (conj Hnp Hnsw))].
                 left. right. right. left. exact (proj2 Hst).
              ** (* [comment removed for export] *)
                 exfalso. eapply (gowned_not_zone SWIN G SHC AINVH HP G_ro_img G_img_al G_img_shlo PERMc SPTOPc HIDc HIDFc M0c B0c C0c
                                   _ _ _ _ _ _ _ (co_ainv HC) a); [|exact (conj Hz1 (conj Hnp Hnsw))].
                 left. left. apply in_blocks_app. right. exact Hff.
        -- (* [comment removed for export] *)
           intros a Hdz H0. destruct Hdz as [Hst|[Hp|Hew]].
           ++ apply STICK; [right; right; left; exact Hst | exact (HD a (or_introl Hst) H0)].
           ++ apply STICK; [right; left; exact Hp | exact (HD a (or_intror (or_introl Hp)) H0)].
           ++ apply HD'; [right; right; exact Hew | exact (HD a (or_intror (or_intror Hew)) H0)].
      * eapply UINV_agree; [eapply env_agree_le; [exact Hag'' | exact Fle] | exact (co_uinv HC)].
      * exact (co_fx HCo).
      * rewrite (wins_den_agree v E E'' (a_ghost cs) Hag'' (pairs_vars_lt_app_r _ _ _ Fallow)). exact (co_perm HC).
      * rewrite (sptop_den_agree v E E'' (a_brk cs) Hag'' Fbrk). exact (co_top HC).
      * rewrite HMT2. exact (co_kcap HCo).
      * (* [comment removed for export] *)
        unfold cs2. cbn [a_fake a_fbud]. rewrite (uE_agree v E E'' (a_fbud cs) Hag'' (fresh_ok_parts3 nx0 cs Hfresh)). exact (co_fbud HC).
      * (* [comment removed for export] *)
        unfold cs2. cbn [a_ylo a_maps a_brk]. eapply GPS.floor_sem_agree; [exact Hag'' | exact Fbrk | exact Fmaps | exact (co_floor HC)].
    + rewrite Hfs2, Hfs'. reflexivity.
Qed.

Theorem node_call_cond_sound : forall (Q : env -> Prop) (COND : acs -> list expr -> bool) ce args,
  callee_contract_when Q ce ->
  (forall cs th E fx R M model, bind ce args cs = Some th -> COND cs th = true -> cs_ok E cs fx R M model -> Q (tenv E th)) ->
  GPS.node1_stmtN SEGS nx0 PERMc SPTOPc FS0 SHC VSHc AINVc KCAP FTOPc FXOK UINV RZ always (node_call_cond COND ce args).
Proof.
  pose proof SEGS_out as KEEP_SEGS_out.   (* [comment removed for export] *)
  intros Q COND ce args CC HQ cs cs' E fx R M model T HT HC _ Hn Hk.
  unfold node_call_cond in Hn. destruct (bind ce args cs) as [th0|] eqn:Hbind0; [|discriminate].
  destruct (COND cs th0) eqn:Hcond; [|discriminate].
  pose proof (HQ cs th0 E fx R M model Hbind0 Hcond HC) as HQE.
  destruct (node_call_split ce args cs cs' E fx R M model HC Hn) as (th & kb & Hbind & Hrm & HCf & HB0 & HC0 & HBc & HCc & HFB & Hpc & EXIT).
  rewrite Hbind0 in Hbind. injection Hbind as ->.
  unfold cfgF. rewrite Hpc.
  apply (CC _ _ _ _ M _ _ _ FS0 (tenv E th) fx R M model T HB0 HC0 HBc HCc HFB HQE HCf HT).
  exact (EXIT T HT Hk).
Qed.

(* [comment removed for export] *)
Theorem node_call_sound : forall ce args,
  callee_contract ce -> GPS.node1_stmtN SEGS nx0 PERMc SPTOPc FS0 SHC VSHc AINVc KCAP FTOPc FXOK UINV RZ always (node_call SEGS A nx0 bcap ccap G ce args).
Proof.
  pose proof SEGS_out as KEEP_SEGS_out.   (* [comment removed for export] *)
  intros ce args CC cs cs' E fx R M model T HT HC Hp Hn Hk.
  apply (node_call_cond_sound QTRUE (fun _ _ => true) ce args CC ltac:(intros; exact I) cs cs' E fx R M model T HT HC Hp); [|exact Hk].
  unfold node_call_cond. unfold node_call in Hn |- *.
  destruct (ce_touts ce); [discriminate|].
  match type of Hn with (if negb ?c then _ else _) = _ => destruct c; [|discriminate] end. cbn [negb] in Hn |- *.
  match type of Hn with (if negb ?c then _ else _) = _ => destruct c; [|discriminate] end. cbn [negb] in Hn |- *.
  destruct (bind ce args cs); [exact Hn | discriminate].
Qed.

(* [comment removed for export] *)
Theorem node_call2_cond_sound : forall (Q : env -> Prop) (COND : acs -> list expr -> bool) c args,
  callee_contract_when Q (c2_merged c) ->
  (forall cs th E fx R M model, bind (c2_class0 c) args cs = Some th -> COND cs th = true -> cs_ok E cs fx R M model -> Q (tenv E th)) ->
  node2_stmt SEGS nx0 PERMc SPTOPc FS0 SHC VSHc AINVc KCAP FTOPc FXOK UINV RZ (node_call2_cond SEGS A nx0 bcap ccap G COND c args).
Proof.
  pose proof SEGS_out as KEEP_SEGS_out.   (* [comment removed for export] *)
  intros Q COND c args CC HQ cs csa csb E fx R M model T HC Hn HT KA KB.
  unfold node_call2_cond in Hn. destruct (bind (c2_class0 c) args cs) as [th0|] eqn:Hbind0; [|discriminate].
  destruct (COND cs th0) eqn:Hcond; [|discriminate].
  pose proof (HQ cs th0 E fx R M model Hbind0 Hcond HC) as HQE.
  unfold node_call2 in Hn.
  destruct (node_call SEGS A nx0 bcap ccap G (c2_class0 c) args cs) as [a|] eqn:Hna; [|discriminate].
  destruct (node_call SEGS A nx0 bcap ccap G (c2_class1 c) args cs) as [b|] eqn:Hnb; [|discriminate].
  injection Hn as Ea Eb. subst a b.
  destruct (node_call_split (c2_class0 c) args cs csa E fx R M model HC Hna) as (th & kb & Hbind & Hrm & HCf & HB0 & HC0 & HBc & HCc & HFB & Hpc & EXIT0).
  destruct (node_call_split (c2_class1 c) args cs csb E fx R M model HC Hnb) as (th1 & kb1 & Hbind1 & Hrm1 & _ & _ & _ & _ & _ & _ & _ & EXIT1).
  rewrite Hbind0 in Hbind. injection Hbind as Eth0. subst th0.
  cbn [c2_class0 c2_class1 c2_merged ce_nxf ce_tin ce_touts ce_bcap ce_ccap] in *.
  assert (Eth : th1 = th) by (unfold bind in Hbind0, Hbind1; cbn [ce_nxf ce_tin c2_class0 c2_class1] in Hbind0, Hbind1; rewrite Hbind0 in Hbind1; injection Hbind1 as E1; symmetry; exact E1).
  subst th1. rewrite Hrm in Hrm1. injection Hrm1 as <-.
  unfold cfgF. rewrite Hpc.
  apply (CC _ _ _ _ M _ _ _ FS0 (tenv E th) fx R M model T HB0 HC0 HBc HCc HFB HQE HCf HT).
  intros tout E' fx' R' M' mdl' Hin Hag HCo Hfs. cbn [ce_touts] in Hin. apply in_app_iff in Hin as [Hin|Hin].
  - exact (EXIT0 T HT KA tout E' fx' R' M' mdl' Hin Hag HCo Hfs).
  - exact (EXIT1 T HT KB tout E' fx' R' M' mdl' Hin Hag HCo Hfs).
Qed.

Theorem node_call2_sound : forall c args,
  callee_contract (c2_merged c) ->
  node2_stmt SEGS nx0 PERMc SPTOPc FS0 SHC VSHc AINVc KCAP FTOPc FXOK UINV RZ (node_call2 SEGS A nx0 bcap ccap G c args).
Proof.
  pose proof SEGS_out as KEEP_SEGS_out.   (* [comment removed for export] *)
  intros c args CC cs csa csb E fx R M model T HC Hn HT KA KB.
  unfold node_call2 in Hn.
  destruct (node_call SEGS A nx0 bcap ccap G (c2_class0 c) args cs) as [a|] eqn:Hna; [|discriminate].
  destruct (node_call SEGS A nx0 bcap ccap G (c2_class1 c) args cs) as [b|] eqn:Hnb; [|discriminate].
  injection Hn as Ea Eb. subst a b.
  destruct (node_call_split (c2_class0 c) args cs csa E fx R M model HC Hna) as (th & kb & Hbind & Hrm & HCf & HB0 & HC0 & HBc & HCc & HFB & Hpc & EXIT0).
  destruct (node_call_split (c2_class1 c) args cs csb E fx R M model HC Hnb) as (th1 & kb1 & Hbind1 & Hrm1 & _ & _ & _ & _ & _ & _ & _ & EXIT1).
  cbn [c2_class0 c2_class1 c2_merged ce_nxf ce_tin ce_touts ce_bcap ce_ccap] in *.
  assert (Eth : th1 = th) by (unfold bind in Hbind, Hbind1; cbn [ce_nxf ce_tin c2_class0 c2_class1] in Hbind, Hbind1; rewrite Hbind in Hbind1; injection Hbind1 as E1; symmetry; exact E1).
  subst th1. rewrite Hrm in Hrm1. injection Hrm1 as <-.
  unfold cfgF. rewrite Hpc.
  apply (CC _ _ _ _ M _ _ _ FS0 (tenv E th) fx R M model T HB0 HC0 HBc HCc HFB I HCf HT).
  intros tout E' fx' R' M' mdl' Hin Hag HCo Hfs. cbn [ce_touts] in Hin. apply in_app_iff in Hin as [Hin|Hin].
  - exact (EXIT0 T HT KA tout E' fx' R' M' mdl' Hin Hag HCo Hfs).
  - exact (EXIT1 T HT KB tout E' fx' R' M' mdl' Hin Hag HCo Hfs).
Qed.

End CallSound.
