(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Arr ZBridge CellsX TacX LiaTuning.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import AsShadow AllocRep AllocWalkKit.
From Ltac2 Require Ltac2.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition region_fam (x b : Z) : Prop := True.
Definition region_psep (b1 b2 : Z) (P : Prop) : Prop := P.
Definition region_rank (b : Z) (r : Z) : Prop := True.   (* [comment removed for export] *)
Definition region_lb (b : Z) (v : Z) : Prop := True.     (* [comment removed for export] *)
Definition region_ub (b : Z) (v : Z) : Prop := True.
Definition region_tabled : Prop := True.
(* [comment removed for export] *)
Definition region_side (b : Z) (P : Prop) : Prop := P.
Lemma region_side_intro : forall b (P : Prop), P -> region_side b P.
Proof. intros b P p. exact p. Qed.
(* [comment removed for export] *)
Definition region_hull (lo hi : Z) : Prop := 12599296 <= lo \/ hi <= 65536.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac rx_is_lit a := lazymatch a with Z0 => idtac | Zpos _ => idtac | Zneg _ => idtac end.
Ltac rx_lit_b a := lazymatch a with Z0 => true | Zpos _ => true | Zneg _ => true | _ => false end.

(* [comment removed for export] *)
Ltac rx_offset_like y :=
  lazymatch y with Z.of_nat _ => true | Z.mul _ _ => true | Z.opp _ => true | _ => rx_lit_b y end.
Ltac rx_base e :=
  lazymatch e with
  | Z.add ?x ?y => lazymatch rx_lit_b x with
                 | true => lazymatch rx_offset_like y with true => x | false => rx_base y end
                 | false => rx_base x end
  | Z.sub ?x ?y => lazymatch rx_lit_b x with
                 | true => lazymatch rx_offset_like y with true => x | false => rx_base y end
                 | false => rx_base x end
  | _ => e
  end.

(* [comment removed for export] *)
Ltac rx_fam b := match goal with H : region_fam b ?b' |- _ => b' | _ => b end.
(* [comment removed for export] *)
Ltac rx_resolve_fams :=
  repeat match goal with
         | H : region_fam ?x ?b, H' : region_fam ?b ?c |- _ => clear H; pose proof (I : region_fam x c) as H
         end.
Ltac rx_same_fam b1 b2 :=
  first [ constr_eq b1 b2
        | rx_is_lit b1; rx_is_lit b2
        | let f1 := rx_fam b1 in let f2 := rx_fam b2 in constr_eq f1 f2 ].

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac rx_lia3 :=
  dle_wrap ltac:(first [ zify_prune; zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker
        | zify_prune; Zify.zify; xlia zchecker
        | Zify.zify; xlia zchecker ]).
(* [comment removed for export] *)
(* [comment removed for export] *)
Module RxPrune.
  Import Ltac2.
  Ltac2 rec plain (t : constr) : bool :=
    match Constr.Unsafe.kind t with
    | Constr.Unsafe.App h args =>
        match Constr.Unsafe.kind h with
        | Constr.Unsafe.Constant _ _ =>
            if Constr.equal h '@Z.le then true else if Constr.equal h '@Z.lt then true
            else if Constr.equal h '@Z.ge then true else if Constr.equal h '@Z.gt then true
            else if Constr.equal h '@lt then true else if Constr.equal h '@le then true
            (* [comment removed for export] *)
            else if Constr.equal h '@akobj then true else if Constr.equal h '@aapp then true
            else if Constr.equal h '@alow1 then true else if Constr.equal h '@aapp_lo then true
            else if Constr.equal h '@aapp_hi then true else false
        | Constr.Unsafe.Ind _ _ =>
            if Constr.equal h '@and then (if plain (Array.get args 0) then plain (Array.get args 1) else false)
            else if Constr.equal h '@eq then
              (let ty := Array.get args 0 in if Constr.equal ty 'Z then true else Constr.equal ty 'nat)
            else false
        | _ => false
        end
    | _ => false
    end.
  Ltac2 rec codomain (t : constr) : constr :=
    match Constr.Unsafe.kind t with
    | Constr.Unsafe.Prod _ b => codomain b
    | Constr.Unsafe.LetIn _ _ b => codomain b
    | Constr.Unsafe.Cast c _ _ => codomain c
    | _ => t
    end.
  Ltac2 rec head (t : constr) : constr :=
    match Constr.Unsafe.kind t with
    | Constr.Unsafe.App f _ => head f
    | Constr.Unsafe.Cast c _ _ => head c
    | _ => t
    end.
  Ltac2 sort_is_prop (ty : constr) : bool :=
    lazy_match! codomain ty with Prop => true | _ => false end.
  Ltac2 is_prop (ty : constr) : bool :=
    let h := head (codomain ty) in
    match Constr.Unsafe.kind h with
    | Constr.Unsafe.Constant _ _ => sort_is_prop (Constr.type h)
    | Constr.Unsafe.Ind _ _ => sort_is_prop (Constr.type h)
    | Constr.Unsafe.Var _ => sort_is_prop (Constr.type h)
    | _ => false
    end.
  Ltac2 prune () : unit :=
    let hs := Control.hyps () in
    let ids := List.map_filter (fun h => let (id, body, ty) := h in
                  match body with
                  | Some _ => None
                  | None => if plain ty then None else if is_prop ty then Some id else None
                  end) hs in
    match ids with [] => () | _ :: _ => Std.clear ids end.

End RxPrune.
Ltac rx_prune := first [ ltac2:(Control.enter RxPrune.prune) | zify_prune ].
(* [comment removed for export] *)
Ltac qlia1 := dle_wrap ltac:(zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker).
Ltac qlia := rx_prune; qlia1.
Ltac qlia_or_lia := first [ qlia | rx_lia3 ].
(* [comment removed for export] *)
Ltac rx_clear_all := repeat match goal with H : _ |- _ => clear H end.
Ltac lia0 := solve [ clear; qlia ].
(* [comment removed for export] *)
Definition rx_in_fallback : Prop := True.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac rx_is_sum e := lazymatch e with Z.add _ _ => idtac | Z.sub _ _ => idtac end.
Ltac rx_addr_atom b := lazymatch b with Z.mul _ _ => fail | Z.of_nat _ => fail | Z.opp _ => fail | _ => idtac end.
Ltac rx_note_eq X rhs :=
  rx_is_sum rhs;
  let b := rx_base rhs in
  first [ rx_is_lit b
        | constr_eq X b
        | rx_addr_atom b;
          lazymatch goal with
          | _ : region_fam X _ |- _ => idtac
          | _ => let H := fresh "RXF" in pose proof (I : region_fam X b) as H
          end
        | idtac ].
(* [comment removed for export] *)
Ltac rx_lit_rank b :=
  lazymatch eval vm_compute in (b <? 12599296) with
  | true => constr:(0%Z)
  | false => lazymatch eval vm_compute in (b <? 17594333495296) with true => constr:(1%Z) | false => constr:(2%Z) end
  end.
Ltac rx_rank_of b := lazymatch rx_lit_b b with true => rx_lit_rank b | false => match goal with H : region_rank b ?r |- _ => r | _ => constr:(9%Z) end end.
(* [comment removed for export] *)
Ltac rx_rank_cmp k1 k2 :=
  lazymatch k1 with
  | 9%Z => Eq
  | 5%Z => lazymatch k2 with 3%Z => Lt | _ => Eq end
  | 6%Z => lazymatch k2 with 3%Z => Lt | 0%Z => Gt | _ => Eq end
  | _ => lazymatch k2 with
         | 9%Z => Eq
         | 5%Z => lazymatch k1 with 3%Z => Gt | _ => Eq end
         | 6%Z => lazymatch k1 with 3%Z => Gt | 0%Z => Lt | _ => Eq end
         | _ => eval vm_compute in (Z.compare k1 k2)
         end
  end.
Ltac rx_set_rank b r :=
  first [ rx_is_lit b
        | lazymatch goal with
          | _ : region_rank b _ |- _ => idtac
          | _ => let H := fresh "RXR" in pose proof (I : region_rank b r) as H
          end ].
(* [comment removed for export] *)
Ltac rx_eval_sum e :=
  lazymatch e with
  | Z.add ?x ?y => let x' := rx_eval_sum x in let y' := rx_eval_sum y in constr:(Z.add x' y')
  | Z.sub ?x ?y => let x' := rx_eval_sum x in let y' := rx_eval_sum y in constr:(Z.sub x' y')
  | Z.mul ?x ?y => let x' := rx_eval_sum x in let y' := rx_eval_sum y in constr:(Z.mul x' y')
  | _ => match e with
         | _ => let _ := match goal with _ => is_const e end in
                let v := eval vm_compute in e in
                let _ := match goal with _ => rx_is_lit v end in v
         | _ => e
         end
  end.
Ltac rx_eval_consts_t t :=
  lazymatch t with
  | ?a <= ?b \/ ?c <= ?d => let a' := rx_eval_sum a in let b' := rx_eval_sum b in let c' := rx_eval_sum c in let d' := rx_eval_sum d in
                           constr:(a' <= b' \/ c' <= d')
  | ?a <= ?b => let a' := rx_eval_sum a in let b' := rx_eval_sum b in constr:(a' <= b')
  | _ => rx_eval_sum t
  end.

(* [comment removed for export] *)
Ltac rx_off e :=
  lazymatch e with
  | Z.add ?x ?y =>
      lazymatch rx_lit_b x with
      | true => lazymatch rx_offset_like y with
                | true => lazymatch rx_lit_b y with true => constr:(Some y) | false => constr:(@None Z) end
                | false => let oy := rx_off y in lazymatch oy with Some ?k => constr:(Some (x + k)) | _ => oy end
                end
      | false => let ox := rx_off x in
                 lazymatch ox with
                 | Some ?k => lazymatch rx_lit_b y with true => constr:(Some (k + y)) | false => constr:(@None Z) end
                 | _ => ox
                 end
      end
  | Z.sub ?x ?y =>
      let ox := rx_off x in
      lazymatch ox with
      | Some ?k => lazymatch rx_lit_b y with true => constr:(Some (k - y)) | false => constr:(@None Z) end
      | _ => ox
      end
  | _ => lazymatch rx_lit_b e with true => constr:(Some 0) | false => lazymatch rx_offset_like e with true => constr:(@None Z) | false => constr:(Some 0) end end
  end.
Ltac rx_set_lb b v := first [ rx_is_lit b | lazymatch goal with _ : region_lb b _ |- _ => idtac | _ => let H := fresh "RXR" in pose proof (I : region_lb b v) as H end ].
Ltac rx_set_ub b v := first [ rx_is_lit b | lazymatch goal with _ : region_ub b _ |- _ => idtac | _ => let H := fresh "RXR" in pose proof (I : region_ub b v) as H end ].
(* [comment removed for export] *)
Ltac rx_note_le hid l0 r0 :=
  let l := lazymatch hid with true => rx_eval_consts_t l0 | false => l0 end in
  let r := lazymatch hid with true => rx_eval_consts_t r0 | false => r0 end in
  let bl := rx_base l in let br := rx_base r in
  lazymatch rx_lit_b bl with
  | true => lazymatch rx_lit_b br with
            | true => idtac
            | false =>
                (* [comment removed for export] *)
                (try (lazymatch rx_off l with Some ?kl => lazymatch rx_off r with Some ?kr =>
                       let v := eval vm_compute in (bl + kl - kr) in rx_set_lb br v end end));
                lazymatch eval vm_compute in (140735332483072 <=? bl) with
                | true => rx_set_rank br constr:(3%Z)
                | false => lazymatch eval vm_compute in (17594333495296 <=? bl) with
                           | true => rx_set_rank br constr:(2%Z) | false => idtac end
                end
            end
  | false => lazymatch rx_lit_b br with
             | true =>
                (* [comment removed for export] *)
                (try (lazymatch rx_off l with Some ?kl => let v := eval vm_compute in (br - kl) in rx_set_ub bl v end));
                lazymatch eval vm_compute in (br <=? 12599296) with
                | true => rx_set_rank bl constr:(0%Z)
                | false => lazymatch eval vm_compute in (br <=? 17594333495296) with
                           | true => rx_set_rank bl constr:(1%Z) | false => idtac end
                end
             | false => lazymatch rx_rank_of bl with 3%Z => rx_set_rank br constr:(3%Z) | _ => idtac end
             end
  end.
Ltac rx_is_atomZ X := lazymatch X with Z.add _ _ => fail | Z.sub _ _ => fail | Z.mul _ _ => fail | _ => idtac end.

Lemma rx_unhide : forall P : Prop, hidden P -> P.
Proof. intros P [p]. exact p. Qed.

(* [comment removed for export] *)
Ltac rx_have_le l r :=
  match goal with
  | H : context [l <= r] |- _ =>
      lazymatch type of H with hidden _ => fail | region_side _ _ => fail | region_psep _ _ _ => fail | _ => idtac end
  end.
Ltac rx_pose_band lo X k pfenv :=
  tryif rx_have_le lo X then idtac
  else (let H := fresh "RXb" in pose proof (pfenv : lo <= X /\ X + k <= aceil) as H).
Ltac rx_note_side X k pf :=
  lazymatch goal with
  | _ : region_side X _ |- _ => idtac
  | _ =>
    lazymatch type of pf with
    | akobj X k =>
        let H := fresh "RXS" in
        pose proof (region_side_intro X _ (akobj_lit X k pf)) as H;
        rx_set_rank X constr:(5%Z);
        try rx_pose_band 4096 X k constr:(akobj_env X k pf ltac:(first [lia0 | qlia | rx_lia3]))
    | aapp X k =>
        let H := fresh "RXS" in
        pose proof (region_side_intro X _ (aapp_lit X k pf)) as H;
        rx_set_rank X constr:(6%Z);
        try rx_pose_band 12599296 X k constr:(aapp_env X k pf ltac:(first [lia0 | qlia | rx_lia3]));
        try (lazymatch goal with
             | _ : region_side (sh X) _ |- _ => idtac
             | _ => let H2 := fresh "RXS" in
                    pose proof (region_side_intro (sh X) _ (aapp_sh_lit_div X k pf ltac:(first [lia0 | qlia | rx_lia3]))) as H2;
                    rx_set_rank (sh X) constr:(1%Z)
             end)
    end
  end.

(* [comment removed for export] *)
Ltac rx_tscan hid pf T :=
  lazymatch T with
  | ?A /\ ?B => rx_tscan hid constr:(@proj1 A B pf) A; rx_tscan hid constr:(@proj2 A B pf) B
  | @eq Z ?X ?rhs => try (rx_is_atomZ X; rx_note_eq X rhs)
  | akobj ?X ?k => try (rx_note_side X k pf)
  | aapp ?X ?k => try (rx_note_side X k pf)
  | ?l1 <= ?r1 \/ ?l2 <= ?r2 =>
      try (let T' := rx_eval_consts_t T in
           lazymatch T' with
           | ?k1 <= ?q1 \/ ?k2 <= ?q2 =>
               let b1 := rx_base k1 in let c1 := rx_base q1 in let b2 := rx_base k2 in let c2 := rx_base q2 in
               constr_eq b1 c2; constr_eq c1 b2;
               tryif constr_eq b1 c1 then idtac
               else lazymatch goal with
                    | _ : region_psep b1 c1 _ |- _ => idtac
                    | _ : region_psep c1 b1 _ |- _ => idtac
                    | _ => let H := fresh "RXP" in pose proof (pf : region_psep b1 c1 T') as H
                    end
           end)
  | ?l <= ?r =>
      (* [comment removed for export] *)
      lazymatch hid with
      | true => try (let l' := rx_eval_consts_t l in let r' := rx_eval_consts_t r in
                     let bl := rx_base l' in let br := rx_base r' in
                     first [ rx_is_lit bl; lazymatch goal with _ : region_lb br _ |- _ => fail | _ => idtac end
                           | rx_is_lit br; lazymatch goal with _ : region_ub bl _ |- _ => fail | _ => idtac end ];
                     lazymatch goal with
                     | _ : l' <= r' |- _ => idtac
                     | _ => let H := fresh "RXh" in pose proof (pf : l' <= r') as H
                     end)
      | false => idtac
      end;
      try (rx_note_le hid l r)
  | ?l < ?r => idtac
  | _ => idtac
  end.

(* [comment removed for export] *)
Ltac rx_not_in H acc := lazymatch acc with | (?a, ?rest) => (tryif constr_eq H a then fail else rx_not_in H rest) | tt => idtac end.
Ltac rx_scan_hidden acc :=
  match goal with
  | H : hidden ?P |- _ =>
      rx_not_in H acc; try (let P' := eval hnf in P in rx_tscan true constr:(rx_unhide P H) P'); rx_scan_hidden (H, acc)
  | _ => idtac
  end.
Ltac rx_scan_conjs acc :=
  match goal with
  | H : ?A /\ ?B |- _ => rx_not_in H acc; try (rx_tscan false H (A /\ B)); rx_scan_conjs (H, acc)
  | _ => idtac
  end.
Ltac rx_scan_atoms acc :=
  match goal with
  | H : @eq Z ?X ?rhs |- _ => rx_not_in H acc; try (rx_is_atomZ X; rx_note_eq X rhs); rx_scan_atoms (H, acc)
  | H : ?l <= ?r |- _ => rx_not_in H acc; try (rx_note_le false l r); rx_scan_atoms (H, acc)
  (* [comment removed for export] *)
  | H : ?l1 <= ?r1 \/ ?l2 <= ?r2 |- _ => rx_not_in H acc; try (rx_tscan false H (l1 <= r1 \/ l2 <= r2)); rx_scan_atoms (H, acc)
  | _ => idtac
  end.
(* [comment removed for export] *)
Ltac rx_seed_stack :=
  try match goal with
      | _ : munch ((?lo, ?hi) :: _) _ _ |- _ =>
          let bh := rx_base hi in
          lazymatch bh with
          | bv_unsigned _ => rx_set_rank ltac:(rx_base lo) constr:(3%Z); rx_set_rank bh constr:(3%Z)
          end
      end.
(* [comment removed for export] *)
Ltac rx_rescan_eqs :=
  repeat match goal with
  | H : @eq Z ?X ?rhs |- _ =>
      rx_is_atomZ X;
      lazymatch goal with
      | _ : region_fam X _ |- _ => fail
      | _ => rx_is_sum rhs;
             let b := rx_base rhs in
             rx_addr_atom b; (tryif rx_is_lit b then fail else idtac); (tryif constr_eq X b then fail else idtac);
             let b' := rx_fam b in
             let F := fresh "RXF" in pose proof (I : region_fam X b') as F
      end
  end.
(* [comment removed for export] *)
Ltac rx_tscan_sides pf T :=
  lazymatch T with
  | ?A /\ ?B => rx_tscan_sides constr:(@proj1 A B pf) A; rx_tscan_sides constr:(@proj2 A B pf) B
  | akobj ?X ?k => try (rx_note_side X k pf)
  | aapp ?X ?k => try (rx_note_side X k pf)
  | _ => idtac
  end.
Ltac rx_scan_sides_hidden acc :=
  match goal with
  | H : hidden ?P |- _ =>
      rx_not_in H acc; try (let P' := eval hnf in P in rx_tscan_sides constr:(rx_unhide P H) P'); rx_scan_sides_hidden (H, acc)
  | _ => idtac
  end.
Ltac rx_scan_sides_conjs acc :=
  match goal with
  | H : ?A /\ ?B |- _ => rx_not_in H acc; try (rx_tscan_sides H (A /\ B)); rx_scan_sides_conjs (H, acc)
  | _ => idtac
  end.
Ltac rx_scan_sides_atoms :=
  repeat match goal with
         | H : akobj ?X ?k |- _ => lazymatch goal with _ : region_side X _ |- _ => fail | _ => rx_note_side X k H end
         | H : aapp ?X ?k |- _ => lazymatch goal with _ : region_side X _ |- _ => fail | _ => rx_note_side X k H end
         end.
(* [comment removed for export] *)
Ltac region_sides := rx_scan_sides_atoms; rx_scan_sides_conjs tt; rx_scan_sides_hidden tt.

(* [comment removed for export] *)
Ltac region_table :=
  lazymatch goal with
  | _ : region_tabled |- _ => rx_seed_stack; rx_rescan_eqs; rx_resolve_fams
  | _ => rx_seed_stack; rx_scan_sides_atoms; rx_scan_conjs tt; rx_scan_atoms tt; rx_scan_hidden tt; rx_resolve_fams;
         let M := fresh "RXT" in pose proof (I : region_tabled) as M
  end.

(* [comment removed for export] *)
Ltac rx_cmp_b x y := let c := eval vm_compute in (x <=? y) in c.
Ltac rx_orient b1 b2 :=
  let f1 := rx_fam b1 in let f2 := rx_fam b2 in
  let k1 := rx_rank_of f1 in let k2 := rx_rank_of f2 in
  let k1 := lazymatch k1 with 9%Z => rx_rank_of b1 | _ => k1 end in
  let k2 := lazymatch k2 with 9%Z => rx_rank_of b2 | _ => k2 end in
  let byrank := rx_rank_cmp k1 k2 in
  lazymatch byrank with
  | Eq =>
      lazymatch rx_lit_b b1 with
      | true =>
          match goal with
          | _ : region_lb b2 ?v |- _ => lazymatch rx_cmp_b b1 v with true => Lt end
          | _ : region_lb f2 ?v |- _ => lazymatch rx_cmp_b b1 v with true => Lt end
          | _ : region_ub b2 ?v |- _ => lazymatch rx_cmp_b v b1 with true => Gt end
          | _ : region_ub f2 ?v |- _ => lazymatch rx_cmp_b v b1 with true => Gt end
          | _ => Eq
          end
      | false =>
          lazymatch rx_lit_b b2 with
          | true =>
              match goal with
              | _ : region_lb b1 ?v |- _ => lazymatch rx_cmp_b b2 v with true => Gt end
              | _ : region_lb f1 ?v |- _ => lazymatch rx_cmp_b b2 v with true => Gt end
              | _ : region_ub b1 ?v |- _ => lazymatch rx_cmp_b v b2 with true => Lt end
              | _ : region_ub f1 ?v |- _ => lazymatch rx_cmp_b v b2 with true => Lt end
              | _ => Eq
              end
          | false =>
              match goal with
              | _ : region_ub b1 ?u, _ : region_lb b2 ?v |- _ => lazymatch rx_cmp_b u v with true => Lt end
              | _ : region_ub f1 ?u, _ : region_lb f2 ?v |- _ => lazymatch rx_cmp_b u v with true => Lt end
              | _ : region_ub b2 ?u, _ : region_lb b1 ?v |- _ => lazymatch rx_cmp_b u v with true => Gt end
              | _ : region_ub f2 ?u, _ : region_lb f1 ?v |- _ => lazymatch rx_cmp_b u v with true => Gt end
              | _ => Eq
              end
          end
      end
  | _ => byrank
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac rx_by_psep f1 f2 :=
  let use H :=
    let C := fresh "RXs" in pose proof H as C; unfold region_psep in C;
    let C1 := fresh "RXs1" in let C2 := fresh "RXs2" in
    destruct C as [C1 | C2];
    [ lazymatch type of C1 with ?l <= _ =>
        let g := rx_fam ltac:(rx_base l) in
        tryif constr_eq g f1 then (left; qlia_or_lia) else (right; qlia_or_lia) end
    | lazymatch type of C2 with ?l <= _ =>
        let g := rx_fam ltac:(rx_base l) in
        tryif constr_eq g f1 then (left; qlia_or_lia) else (right; qlia_or_lia) end ] in
  match goal with
  | H : region_psep ?k1 ?k2 _ |- _ =>
      let g1 := rx_fam k1 in let g2 := rx_fam k2 in
      first [ constr_eq g1 f1; constr_eq g2 f2 | constr_eq g1 f2; constr_eq g2 f1 ];
      use H
  end.

(* [comment removed for export] *)
Ltac rx_side_cases C k :=
  lazymatch type of C with
  | _ \/ _ => let C1 := fresh "RXsd" in let C2 := fresh "RXsd" in
             destruct C as [C1 | C2]; [ rx_side_cases C1 k | rx_side_cases C2 k ]
  | _ => k
  end.
Ltac rx_has_side f := match goal with H : region_side ?b _ |- _ => constr_eq ltac:(rx_fam b) f end.
Ltac rx_by_side1 f k :=
  match goal with
  | H : region_side ?b ?P |- _ =>
      constr_eq ltac:(rx_fam b) f;
      let C := fresh "RXsd" in pose proof (H : P) as C; rx_side_cases C k
  end.
Ltac rx_lr := first [ left; qlia | right; qlia ].
Ltac rx_by_side f1 f2 :=
  first [ rx_by_side1 f1 ltac:(rx_lr)
        | rx_by_side1 f2 ltac:(rx_lr)
        | rx_has_side f1; rx_has_side f2; rx_by_side1 f1 ltac:(rx_by_side1 f2 ltac:(rx_lr)) ].
(* [comment removed for export] *)
Ltac rx_atom_by_side f1 f2 :=
  first [ rx_by_side1 f1 ltac:(qlia)
        | rx_by_side1 f2 ltac:(qlia)
        | rx_has_side f1; rx_has_side f2; rx_by_side1 f1 ltac:(rx_by_side1 f2 ltac:(qlia)) ].

(* [comment removed for export] *)

(* [comment removed for export] *)
Ltac rx_overlap_then_fail :=
  lazymatch goal with
  | |- ?l1 <= ?r1 \/ ?l2 <= ?r2 =>
      tryif (let O1 := fresh "RXo" in let O2 := fresh "RXo" in
             assert (O1 : r1 < l1) by (first [lia0 | qlia]); assert (O2 : r2 < l2) by (first [lia0 | qlia]))
      then fail else idtac
  end.
(* [comment removed for export] *)
Ltac rx_by_hull :=
  lazymatch goal with
  | |- ?l1 <= ?lo \/ ?hi <= ?A =>
      rx_is_lit A;   (* [comment removed for export] *)
      match goal with
      | H : region_hull lo hi |- _ =>
          let C := fresh "RXh" in pose proof H as C; unfold region_hull in C;
          destruct C as [C | C]; [ left; solve [ clear - C; qlia1 ] | right; solve [ clear - C; qlia1 ] ]
      end
  end.
Ltac region_decide_or :=
  lazymatch goal with
  | |- ?l1 <= ?r1 \/ ?l2 <= ?r2 =>
      first [ left; assumption | right; assumption | rx_by_hull |
      let b1 := rx_base l1 in let b2 := rx_base r1 in
      tryif constr_eq b1 b2 then
        first [ left; lia0 | right; lia0 | left; qlia | right; qlia | fail ]
      else tryif rx_same_fam b1 b2 then
        first [ left; qlia | right; qlia | fail ]
      else
        let f1 := rx_fam b1 in let f2 := rx_fam b2 in
        lazymatch rx_orient b1 b2 with
        | Lt => first [ left; qlia | right; qlia ]    (* [comment removed for export] *)
        | Gt => first [ right; qlia | left; qlia ]
        | Eq => first [ rx_by_psep f1 f2
                      | rx_by_side f1 f2
                      | left; qlia | right; qlia
                      | rx_overlap_then_fail;   (* [comment removed for export] *)
                        let M := fresh "RXnf" in pose proof (I : rx_in_fallback) as M; slia ]
        end ]
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac rx_inside_pick ba :=
  lazymatch goal with
  | |- (?lo <= _ /\ _ <= ?hi) \/ _ =>
      first [ first [ rx_same_fam ltac:(rx_base lo) ba | rx_same_fam ltac:(rx_base hi) ba ];
              left; first [ lia0 | qlia ]
            | right; rx_inside_pick ba ]
  | |- ?lo <= _ /\ _ <= ?hi => first [ lia0 | qlia ]
  end.
Ltac region_inside :=
  lazymatch goal with
  | |- inside ?W ?a ?n => cbn [inside]; let ba := rx_base a in first [ rx_inside_pick ba | slia ]
  | |- _ => let a := lazymatch goal with |- (_ <= ?a /\ _) \/ _ => a | |- _ <= ?a /\ _ => a end in
            let ba := rx_base a in first [ rx_inside_pick ba | slia ]
  end.

(* [comment removed for export] *)
Ltac rx_arr_sizes := rewrite ?u32s_length, ?u64s_length, ?upd_length, ?repeat_length, ?length_map, ?length_app.

(* [comment removed for export] *)
Ltac region_decide_rec :=
  lazymatch goal with
  | |- True => exact I
  | |- _ /\ _ => split; region_decide_rec
  | |- _ \/ _ => region_decide_or
  | |- _ => first [ lia0 | qlia | slia ]
  end.
(* [comment removed for export] *)
Ltac region_decide := region_table; region_decide_rec.

(* [comment removed for export] *)
Ltac rx_hull_decide :=
  lazymatch goal with
  | |- ?l1 <= ?r1 \/ ?l2 <= ?r2 =>
      first [ left; assumption | right; assumption |
      let b1 := rx_base l1 in let b2 := rx_base r1 in
      let f1 := rx_fam b1 in let f2 := rx_fam b2 in
      lazymatch rx_orient b1 b2 with
      | Lt => first [ left; qlia | right; qlia ]
      | Gt => first [ right; qlia | left; qlia ]
      | Eq => first [ rx_by_psep f1 f2 | rx_by_side f1 f2 | left; qlia | right; qlia ]
      end ]
  end.
Ltac rx_hull_memo1 lo hi :=
  lazymatch rx_lit_b ltac:(rx_base lo) with
  | true => idtac
  | false =>
      lazymatch goal with
      | _ : region_hull lo hi |- _ => idtac
      | _ => let M := fresh "RXhull" in
             first [ assert (M : region_hull lo hi) by (unfold region_hull; rx_hull_decide) | idtac ]
      end
  end.
Ltac region_hull_memo W :=
  lazymatch W with
  | (?lo, ?hi) :: ?W' => rx_hull_memo1 lo hi; region_hull_memo W'
  | _ => idtac
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Ltac rx_range_facts a bs HA HL :=
  first [ assert (HA : 0 <= a) by (first [qlia | lia]);
          assert (HL : a + Z.of_nat (length bs) <= 2^64) by (simpl_sizes; first [qlia | lia])
        | idtac ].
Ltac rx_exactL HL := first [ exact HL | simpl_sizes; first [ exact HL | region_decide ] ].

Ltac transport_chunks segs m a bs ::=
  region_table;
  let HA := fresh "RXA" in let HL := fresh "RXL" in
  rx_range_facts a bs HA HL;
  repeat match goal with
  | H : bytes_at segs m ?A2 ?bs2 |- _ =>
      first [ apply (bytes_at_write_other segs m a bs A2 bs2) in H;
              [ | first [exact HA | lia] | rx_exactL HL | simpl_sizes; rx_arr_sizes; region_decide ]
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  | H : wr_at segs m ?A2 ?n2 |- _ => apply (wr_at_write segs m A2 n2 (wa a) bs) in H
  | H : rw_cells segs m ?A2 ?cs2 |- _ =>
      first [ apply (rw_cells_frame segs m A2 cs2 a bs) in H;
              [ | first [exact HA | lia] | rx_exactL HL | simpl_sizes; region_decide ]
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  | H : ro_cells segs m ?A2 ?cs2 |- _ =>
      first [ apply (ro_cells_frame segs m A2 cs2 a bs) in H;
              [ | first [exact HA | lia] | rx_exactL HL | simpl_sizes; region_decide ]
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  | H : u8arr segs m ?A2 ?xs |- _ =>
      first [ apply (u8arr_frame segs m A2 xs a bs) in H;
              [ | first [exact HA | lia] | rx_exactL HL | simpl_sizes; rx_arr_sizes; region_decide ]
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  | H : u32arr segs m ?A2 ?xs |- _ =>
      first [ apply (u32arr_frame segs m A2 xs a bs) in H;
              [ | first [exact HA | lia] | rx_exactL HL | simpl_sizes; rx_arr_sizes; region_decide ]
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  | H : u64arr segs m ?A2 ?xs |- _ =>
      first [ apply (u64arr_frame segs m A2 xs a bs) in H;
              [ | first [exact HA | lia] | rx_exactL HL | simpl_sizes; rx_arr_sizes; region_decide ]
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  | H : u8ro segs m ?A2 ?xs |- _ =>
      first [ apply (u8ro_frame segs m A2 xs a bs) in H;
              [ | first [exact HA | lia] | rx_exactL HL | simpl_sizes; rx_arr_sizes; region_decide ]
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  end;
  try clear HA; try clear HL.

Ltac footprint_after_store segs m a bs ::=
  let HA := fresh "RXA" in let HL := fresh "RXL" in
  rx_range_facts a bs HA HL;
  repeat match goal with
  | MU : munch ?Wq ?mq m |- _ =>
      first [ apply (munch_write Wq mq m a bs) in MU;
              [ | first [exact HA | lia] | rx_exactL HL | simpl_sizes; region_inside ]
            | fail 100 "store outside the declared footprint:" a ]
  | WMo : wmono segs ?mq m |- _ => apply (wmono_write segs mq m (wa a) bs) in WMo
  | STq : stk segs m ?loq ?hiq |- _ =>
      first [ apply (stk_write segs m loq hiq a bs) in STq; [ | first [exact HA | lia] | rx_exactL HL ]
            | fail 100 "cannot transport stk hypothesis" STq ]
  end;
  try clear HA; try clear HL.

(* [comment removed for export] *)
Lemma rx_not_in_sub : forall l h l' h' x : Z, l' <= l -> h <= h' -> ~ (l' <= x < h') -> ~ (l <= x < h).
Proof. intros; lia. Qed.
Ltac rx_lia_with_neg H := (repeat match goal with Hq : ~ _ |- _ => tryif constr_eq H Hq then fail else clear Hq end); rx_lia3.
(* [comment removed for export] *)
Ltac rx_sub_fp_leaf :=
  lazymatch goal with
  | |- ~ (?l <= ?x < ?h) =>
      let b := rx_base l in let f := rx_fam b in let k := rx_rank_of f in
      let via H l' h' := apply (rx_not_in_sub l h l' h' x); [ first [lia0 | qlia] | first [lia0 | qlia] | exact H ] in
      first [ match goal with
              | H : ~ (?l' <= x < ?h') |- _ => rx_same_fam b ltac:(rx_base l'); via H l' h'
              end
            | match goal with
              | H : ~ (?l' <= x < ?h') |- _ =>
                  let k' := rx_rank_of ltac:(rx_fam ltac:(rx_base l')) in constr_eq k k'; via H l' h'
              end
            | match goal with
              | H : ~ (?l' <= x < ?h') |- _ => via H l' h'
              end
            | match goal with H : ~ _ |- _ => rx_lia_with_neg H end
            | rx_lia3 ]
  | |- _ => first [ assumption | exact I | rx_lia3 ]
  end.
Ltac rx_sub_fp_struct :=
  let x := fresh "ox" in let Hx := fresh "OX" in
  unfold sub_fp; cbn [outside fst snd]; intros x Hx;
  repeat (lazymatch type of Hx with _ /\ _ => let H := fresh "OW" in destruct Hx as [H Hx] end);
  repeat (lazymatch goal with |- _ /\ _ => split end);
  first [ assumption | exact I | rx_sub_fp_leaf ].

Ltac transport_after_call segs m m' MU WM ::=
  region_table;
  let W := lazymatch type of MU with munch ?W _ _ => W end in
  region_hull_memo W;   (* [comment removed for export] *)
  repeat match goal with
  | H : bytes_at segs m ?A2 ?bs2 |- _ =>
      first [ apply (bytes_at_transport segs W m m' A2 bs2) in H; [ | exact MU | cbn [disjoint_from]; simpl_sizes; region_decide ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : wr_at segs m ?A2 ?n2 |- _ => apply (wr_at_transport segs m m' A2 n2) in H; [ | exact WM ]
  | H : rw_cells segs m ?A2 ?cs2 |- _ =>
      first [ apply (rw_cells_transport segs W m m' A2 cs2) in H; [ | exact MU | exact WM | cbn [disjoint_from]; simpl_sizes; region_decide ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : ro_cells segs m ?A2 ?cs2 |- _ =>
      first [ apply (ro_cells_transport segs W m m' A2 cs2) in H; [ | exact MU | cbn [disjoint_from]; simpl_sizes; region_decide ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : u8arr segs m ?A2 ?xs |- _ =>
      first [ apply (u8arr_transport segs W m m' A2 xs) in H; [ | exact MU | exact WM | cbn [disjoint_from]; simpl_sizes; rx_arr_sizes; region_decide ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : u32arr segs m ?A2 ?xs |- _ =>
      first [ apply (u32arr_transport segs W m m' A2 xs) in H; [ | exact MU | exact WM | cbn [disjoint_from]; simpl_sizes; rx_arr_sizes; region_decide ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : u64arr segs m ?A2 ?xs |- _ =>
      first [ apply (u64arr_transport segs W m m' A2 xs) in H; [ | exact MU | exact WM | cbn [disjoint_from]; simpl_sizes; rx_arr_sizes; region_decide ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : u8ro segs m ?A2 ?xs |- _ =>
      first [ apply (u8ro_transport segs W m m' A2 xs) in H; [ | exact MU | cbn [disjoint_from]; simpl_sizes; rx_arr_sizes; region_decide ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : stk segs m ?loq ?hiq |- _ =>
      first [ apply (stk_transport_disjoint segs W m m' loq hiq) in H; [ | exact MU | exact WM | cbn [disjoint_from]; region_decide ]
            | clear H ]
  | H : munch ?Wq ?mq m |- _ =>
      first [ apply (munch_trans Wq mq m m') in H; [ | eapply (munch_weaken W Wq m m'); [ rx_sub_fp_struct | exact MU ] ]
            | fail 100 "callee footprint not inside caller footprint" ]
  | H : wmono segs ?mq m |- _ => apply (wmono_trans segs mq m m') in H; [ | exact WM ]
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac region_decide_or_core :=
  lazymatch goal with
  | |- ?l1 <= ?r1 \/ ?l2 <= ?r2 =>
      first [ left; assumption | right; assumption | rx_by_hull |
      let b1 := rx_base l1 in let b2 := rx_base r1 in
      tryif constr_eq b1 b2 then
        first [ left; lia0 | right; lia0 | left; qlia | right; qlia ]
      else tryif rx_same_fam b1 b2 then
        first [ left; qlia | right; qlia ]
      else
        let f1 := rx_fam b1 in let f2 := rx_fam b2 in
        lazymatch rx_orient b1 b2 with
        | Lt => first [ left; qlia | right; qlia ]
        | Gt => first [ right; qlia | left; qlia ]
        | Eq => first [ rx_by_psep f1 f2 | rx_by_side f1 f2 | left; qlia | right; qlia ]
        end ]
  end.
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac rx_atom_decide l r :=
  let b1 := rx_base l in let b2 := rx_base r in
  tryif constr_eq b1 b2 then first [ lia0 | qlia | rx_lia3 ]
  else tryif rx_same_fam b1 b2 then first [ qlia | rx_lia3 ]
  else
    lazymatch rx_orient b1 b2 with
    | Lt => first [ qlia | rx_lia3 ]
    | Gt => rx_lia3
    | Eq => let f1 := rx_fam b1 in let f2 := rx_fam b2 in
            first [ qlia | rx_atom_by_side f1 f2 | rx_lia3 ]
    end.
(* [comment removed for export] *)
Ltac rx_addrlike b :=
  first [ rx_is_lit b
        | lazymatch b with bv_unsigned _ => idtac end
        | lazymatch goal with _ : region_fam b _ |- _ => idtac | _ : region_rank b _ |- _ => idtac end ].
Ltac rx_sumlike e := lazymatch e with Z.add _ _ => idtac | Z.sub _ _ => idtac | bv_unsigned _ => idtac end.
Ltac rx_lia_atom l r :=
  let b1 := rx_base l in let b2 := rx_base r in
  tryif (rx_addrlike b1; rx_addrlike b2) then rx_atom_decide l r else rx_lia3.
(* [comment removed for export] *)
Ltac rx_split_one H P k :=
  let C := fresh "RXsd" in pose proof (H : P) as C; clear H; rx_side_cases C k.
Ltac rx_split_sides k :=
  first [ match goal with
          | H : region_side (sh ?x) ?P |- context [sh ?x] => rx_split_one H P ltac:(first [ k | rx_split_sides k ])
          end
        | match goal with
          | H : region_side ?b ?P |- context [?b] => rx_split_one H P ltac:(first [ k | rx_split_sides k ])
          end ].
(* [comment removed for export] *)
Ltac rx_conj_lia :=
  lazymatch goal with
  | |- _ /\ _ => split; rx_conj_lia
  | |- True => exact I
  | |- _ => lia
  end.
Ltac lia ::=
  lazymatch goal with
  | _ : rx_in_fallback |- _ => rx_lia3
  | _ : region_tabled |- _ /\ _ => first [ rx_conj_lia | rx_lia3 ]
  | _ : region_side _ _ |- _ /\ _ => first [ rx_conj_lia | rx_lia3 ]
  | _ : region_tabled |- _ <= _ \/ _ <= _ => first [ region_decide_or_core | rx_lia3 ]
  | _ : region_tabled |- ?l <= ?r => rx_lia_atom l r
  | _ : region_side _ _ |- _ <= _ \/ _ <= _ =>
      first [ left; qlia | right; qlia | rx_split_sides ltac:(rx_lr)
            | region_table; region_decide_or_core   (* [comment removed for export] *)
            | rx_lia3 ]
  | _ : region_side _ _ |- ?l <= ?r =>
      (* [comment removed for export] *)
      tryif first [ rx_sumlike l | rx_sumlike r ]
      then first [ qlia | rx_split_sides ltac:(qlia) | rx_lia3 ]
      else rx_lia3
  | |- ?l <= ?r =>
      (* [comment removed for export] *)
      tryif first [ rx_sumlike l | rx_sumlike r ] then first [ qlia | rx_lia3 ] else rx_lia3
  | |- _ => rx_lia3
  end.
