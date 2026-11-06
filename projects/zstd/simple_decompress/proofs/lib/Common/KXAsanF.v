(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame.
From OSSVerify.Proofs.zstd.simple_decompress.lib.LibA Require Import ExecF StepF.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Common Require Import KXStepR KXExec KXSound KXFull KXBridge KXTac KXTree.
Import ListNotations.
Import KXS.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition KXSHLO : Z := 0x7fff8000.        (* [comment removed for export] *)
Definition KXSHHI : Z := 0x10007fff8000.    (* [comment removed for export] *)
Definition KXKEND : Z := 0x800000000000.    (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Inductive aent : Type :=
| AUnp (a : saddr) (n : expr)      (* [comment removed for export] *)
| AApp (a : saddr) (n : expr)      (* [comment removed for export] *)
| AShp (s : saddr) (x : expr).     (* [comment removed for export] *)

Definition granok (need : Z) (b : byte) : Prop := bv_signed b = 0 \/ (need <= bv_signed b /\ bv_signed b <= 7).

Section AentOk.
Variable RNG : footprint.
Variable E : env.
Variable base : word -> option byte.

(* [comment removed for export] *)
Definition unpZ (lo hi : Z) : Prop :=
  0 <= lo /\ hi <= KXKEND /\
  forall G, lo < hi -> lo <= 8 * G + 7 -> 8 * G < hi ->
    exists b, base (Z_to_bv 64 (KXSHLO + G)) = Some b /\ granok (Z.min (8 * G + 8) hi - 8 * G) b.

Definition shspanZ (A n : Z) : Z := (A + n + 7) / 8 - A / 8.

Definition aent_ok (K : aent) : Prop :=
  match K with
  | AUnp a n => unpZ (estart E a) (estart E a + elenZ E n) /\
                (0 < elenZ E n -> rng RNG (KXSHLO + estart E a / 8) (shspanZ (estart E a) (elenZ E n)))
  | AApp a n => flat E a (elenZ E n) /\ estart E a + elenZ E n <= KXKEND /\
                (estart E a + elenZ E n <= KXSHLO \/ KXSHHI <= estart E a)
  | AShp s x => estart E s = KXSHLO + elenZ E x / 8
  end.
Definition aknow_ok (akn : list aent) : Prop := Forall aent_ok akn.
End AentOk.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Chk.
Variable segs : list Segment.

Definition instr_at (pc : Z) : option instr :=
  match fetch_word segs (Z_to_bv 64 pc) with
  | None => None
  | Some w => if is_ecall w then None else
              match decode_any w with
              | Some (i, sz) => if Z.eqb sz 4 then Some i else None
              | None => None
              end
  end.

Definition br_target (p : Z) (imm : bv 13) : Z := bv_unsigned (Z_to_bv 64 (p + bv_signed imm)).
Definition j_target (p : Z) (imm : bv 21) : Z := bv_unsigned (Z_to_bv 64 (p + bv_signed imm)).

(* [comment removed for export] *)
Fixpoint find_rb (j : nat) (scs : list sidecond) : option (saddr * nat * bool) :=
  match scs with
  | [] => None
  | SCReadBase a n sx (EVar j') :: r => if Nat.eqb j j' then Some (a, n, sx) else find_rb j r
  | _ :: r => find_rb j r
  end.

(* [comment removed for export] *)
Definition parse_slow (slow : Z) : option (reg * reg * Z * bool * Z) :=
  match instr_at slow with
  | Some (OpImm ALU_AND u x imm7) =>
      if Z.eqb (bv_signed imm7) 7 then
        match instr_at (slow + 4) with
        | Some (OpImm ALU_ADD u1 u2 immc) =>
            if (bv_eqb u1 u && bv_eqb u2 u)%bool then Some (u, x, bv_signed immc, true, slow + 8) else None
        | Some (Branch BC_LT _ _ _) => Some (u, x, 0, false, slow + 4)
        | Some (Branch BC_GE _ _ _) => Some (u, x, 0, false, slow + 4)   (* [comment removed for export] *)
        | _ => None
        end
      else None
  | _ => None
  end.

(* [comment removed for export] *)
Definition unp_cover (akn : list aent) (kn : list kentry) (ex : expr) (len : Z) : bool :=
  existsb (fun K => match K with
                    | AUnp a n => xinside kn ex 0 (ELit len) (a_base a) (a_off a) n
                    | AApp _ _ => false
                    | AShp _ _ => false
                    end) akn.

(* [comment removed for export] *)
Definition shadow_saddr (fk : list kentry) (ex : expr) : saddr :=
  to_saddrK fk (mkAluK fk ALU_ADD (mkAluK fk ALU_SRL ex (ELit 3)) (ELit KXSHLO)) 0.

(* [comment removed for export] *)
Definition shmatch (akn : list aent) (fk : list kentry) (ex : expr) (a : saddr) : bool :=
  saddr_eqb (shadow_saddr fk ex) a
  || existsb (fun K => match K with AShp s x => saddr_eqb s a && expr_eqb x ex | _ => false end) akn.

(* [comment removed for export] *)
Definition merge_u (old e2 : expr) (j : nat) : expr :=   (* [comment removed for export] *)
  EAlu ALU_ADD (EMd M_MUL (EAlu ALU_SLTU (EVar j) (ELit 1)) old) (EMd M_MUL (EAlu ALU_SLTU (ELit 0) (EVar j)) e2).

Record chkinfo : Type := CI {
  ci_j : nat;        (* [comment removed for export] *)
  ci_a : saddr;      (* [comment removed for export] *)
  ci_x : expr;       (* [comment removed for export] *)
  ci_c : Z;          (* [comment removed for export] *)
  ci_u : reg;        (* [comment removed for export] *)
  ci_e2 : expr;      (* [comment removed for export] *)
  ci_neg : bool;     (* [comment removed for export] *)
  ci_slow : Z;       (* [comment removed for export] *)
  ci_addi : bool;    (* [comment removed for export] *)
  ci_blt : Z         (* [comment removed for export] *)
}.

(* [comment removed for export] *)
Definition chk_site (p : Z) (i : instr) : option (reg * bool * Z * Z) :=
  match i with
  | Branch BC_NE t z imm => if bv_eqb z 0 then Some (t, false, br_target p imm, p + 4) else None
  | Branch BC_EQ t z imm =>
      if bv_eqb z 0 then
        match instr_at (p + 4) with
        | Some (Jal rd immj) => if bv_eqb rd 0 then Some (t, true, j_target (p + 4) immj, br_target p imm) else Some (t, true, p + 4, br_target p imm)
        | _ => Some (t, true, p + 4, br_target p imm)
        end
      else None
  | _ => None
  end.

(* [comment removed for export] *)
Definition blt_ok (ib : instr) (ss3 : sym_state) (ok : Z) : bool :=
  match sym_step segs ib ss3 scr_nil with
  | SStop => true
  | SOk ss4 scs _ => match scs with [] => Z.eqb (s_pc ss4) ok | _ :: _ => false end
  end.

(* [comment removed for export] *)
Definition asan_chkA (akn : list aent) (ss : sym_state) (acc : list sidecond) (i : instr) : option (sym_state * chkinfo) :=
  let p := s_pc ss in
  let regs := s_regs ss in
  match chk_site p i with
  | None => None
  | Some (t, neg, slow, ok) =>
      match sr_get regs t with
      | EVar j =>
          match find_rb j acc with
          | Some (a, 1%nat, true) =>
              match parse_slow slow with
              | Some (u, x', c, hasaddi, bltpc) =>
                  match instr_at bltpc with
                  | Some (Branch BC_LT bu bt off) =>
                      if (bv_eqb bu u && bv_eqb bt t && Z.eqb (br_target bltpc off) ok
                          && negb (bv_eqb u 0) && negb (bv_eqb u t) && negb (bv_eqb t 0)
                          && Z.leb 0 c && Z.leb c 7)%bool then
                        let kn := s_know ss in let fk := facts_of kn in
                        let ex := sr_get regs x' in
                        let ss1 := sjump ss slow in
                        let ss2 := sset ss1 u (mkAluK fk ALU_AND ex (ELit 7)) (slow + 4) in
                        let ss3 := if hasaddi then sset ss2 u (mkAluK fk ALU_ADD (sr_get (s_regs ss2) u) (ELit c)) (slow + 8) else ss2 in
                        let e2 := sr_get (s_regs ss3) u in
                        if (shmatch akn fk ex a && unp_cover akn kn ex (c + 1)
                            && blt_ok (Branch BC_LT u t off) ss3 ok)%bool then
                          Some (SSR ok (sr_upd regs (ridx u) (merge_u (sr_get regs u) e2 j)) (s_log ss) kn (s_next ss) (s_resv ss),
                                CI j a ex c u e2 neg slow hasaddi bltpc)
                        else None
                      else None
                  | _ => None
                  end
              | None => None
              end
          | _ => None
          end
      | _ => None
      end
  end.

(* [comment removed for export] *)
Definition bge_ok (ib : instr) (ss3 : sym_state) (nt : Z) : bool :=
  match sym_step segs ib ss3 scr_nil with
  | SStop => true
  | SOk ss4 scs _ => match scs with [] => Z.eqb (s_pc ss4) nt | _ :: _ => false end
  end.

Definition jal_to (p ok : Z) : bool :=
  match instr_at p with
  | Some (Jal rd immj) => (bv_eqb rd 0 && Z.eqb (j_target p immj) ok)%bool
  | _ => false
  end.

Definition asan_chkG (akn : list aent) (ss : sym_state) (acc : list sidecond) (i : instr) : option (sym_state * chkinfo) :=
  let p := s_pc ss in
  let regs := s_regs ss in
  match chk_site p i with
  | None => None
  | Some (t, neg, slow, ok) =>
      match sr_get regs t with
      | EVar j =>
          match find_rb j acc with
          | Some (a, 1%nat, true) =>
              match parse_slow slow with
              | Some (u, x', c, hasaddi, bltpc) =>
                  match instr_at bltpc with
                  | Some (Branch BC_GE bu bt off) =>
                      if (bv_eqb bu u && bv_eqb bt t && jal_to (bltpc + 4) ok   (* [comment removed for export] *)
                          && negb (bv_eqb u 0) && negb (bv_eqb u t) && negb (bv_eqb t 0)
                          && Z.leb 0 c && Z.leb c 7)%bool then
                        let kn := s_know ss in let fk := facts_of kn in
                        let ex := sr_get regs x' in
                        let ss1 := sjump ss slow in
                        let ss2 := sset ss1 u (mkAluK fk ALU_AND ex (ELit 7)) (slow + 4) in
                        let ss3 := if hasaddi then sset ss2 u (mkAluK fk ALU_ADD (sr_get (s_regs ss2) u) (ELit c)) (slow + 8) else ss2 in
                        let e2 := sr_get (s_regs ss3) u in
                        if (shmatch akn fk ex a && unp_cover akn kn ex (c + 1)
                            && bge_ok (Branch BC_GE u t off) ss3 (bltpc + 4))%bool then
                          Some (SSR ok (sr_upd regs (ridx u) (merge_u (sr_get regs u) e2 j)) (s_log ss) kn (s_next ss) (s_resv ss),
                                CI j a ex c u e2 neg slow hasaddi bltpc)
                        else None
                      else None
                  | _ => None
                  end
              | None => None
              end
          | _ => None
          end
      | _ => None
      end
  end.

(* [comment removed for export] *)
Definition all_regs : list reg :=
  map (fun k => Z_to_bv 5 k) [1;2;3;4;5;6;7;8;9;10;11;12;13;14;15;16;17;18;19;20;21;22;23;24;25;26;27;28;29;30;31].

Definition chk_siteZ (p : Z) (i : instr) : option (reg * bool * Z) :=
  match i with
  | Branch BC_NE t z imm => if bv_eqb z 0 then Some (t, false, p + 4) else None
  | Branch BC_EQ t z imm => if bv_eqb z 0 then Some (t, true, br_target p imm) else None
  | _ => None
  end.

Definition candZ (fk : list kentry) (regs : list expr) (ok : Z) : list expr :=
  (match instr_at ok with
   | Some (Load _ _ _ rs imm) => [mkAluK fk ALU_ADD (sr_get regs rs) (ELit (bv_signed imm))]
   | Some (Store _ rs _ imm) => [mkAluK fk ALU_ADD (sr_get regs rs) (ELit (bv_signed imm))]
   | _ => []
   end) ++ map (sr_get regs) all_regs.

Definition asan_chkZ (akn : list aent) (ss : sym_state) (acc : list sidecond) (i : instr) : option (sym_state * chkinfo) :=
  let p := s_pc ss in
  let regs := s_regs ss in
  match chk_siteZ p i with
  | None => None
  | Some (t, neg, ok) =>
      if bv_eqb t 0 then None else
      match sr_get regs t with
      | EVar j =>
          match find_rb j acc with
          | Some (a, 1%nat, sx) =>
              let kn := s_know ss in let fk := facts_of kn in
              match find (fun ex => (shmatch akn fk ex a && Z.leb 3 (ealign kn ex) && unp_cover akn kn ex 8)%bool)
                         (candZ fk regs ok) with
              | Some ex => Some (SSR ok (sr_upd regs (ridx t) (ELit 0)) (s_log ss) kn (s_next ss) (s_resv ss),
                                 CI j a ex 7 t (ELit 0) neg 0 false 0)
              | None => None
              end
          | _ => None
          end
      | _ => None
      end
  end.

Definition asan_chk (akn : list aent) (ss : sym_state) (acc : list sidecond) (i : instr) : option (sym_state * chkinfo) :=
  match asan_chkA akn ss acc i with
  | Some r => Some r
  | None =>
      match asan_chkG akn ss acc i with     (* [comment removed for export] *)
      | Some r => Some r
      | None => asan_chkZ akn ss acc i
      end
  end.

End Chk.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Inductive ktreeA : Type :=
| KALeaf (ss : sym_state) (scs : list sidecond) (accs : list (saddr * nat))
| KAFork (c : branch_cond) (a b : expr) (scs : list sidecond) (accs : list (saddr * nat)) (t1 t2 : ktreeA)
| KASplit (x : expr) (v : Z) (scs : list sidecond) (accs : list (saddr * nat)) (t1 t2 : ktreeA)
| KAChk (ss : sym_state) (ci : chkinfo) (t1 : ktreeA).
    (* [comment removed for export] *)

Fixpoint kta_next (t : ktreeA) : nat :=
  match t with
  | KALeaf ss _ _ => s_next ss
  | KAFork _ _ _ _ _ t1 t2 => Nat.max (kta_next t1) (kta_next t2)
  | KASplit _ _ _ _ t1 t2 => Nat.max (kta_next t1) (kta_next t2)
  | KAChk _ _ t1 => kta_next t1
  end.

Section TreeA.
Variable segs : list Segment.
Variable vmax : Z.
Variable akn : list aent.

Fixpoint kx_treeA (fuel : nat) (first : bool) (stops : list Z) (scalls : bool) (ss : sym_state)
                  (acc : list sidecond) (accs : list (saddr * nat)) (pacc : list sidecond) : ktreeA :=
  match fuel with
  | O => KALeaf ss acc accs
  | S f =>
      if (negb first && existsb (Z.eqb (s_pc ss)) stops)%bool then KALeaf ss acc accs else
      match fetch_word segs (Z_to_bv 64 (s_pc ss)) with
      | None => KALeaf ss acc accs
      | Some w =>
          if is_ecall w then KALeaf ss acc accs else
          match decode_any w with
          | None => KALeaf ss acc accs
          | Some (i, sz) =>
              if negb (Z.eqb sz 4) then KALeaf ss acc accs else
              match (match sym_step segs i ss scr_nil with SStop => asan_chk segs akn ss pacc i | SOk _ _ _ => None end) with
              | Some (ss', ci) => KAChk ss ci (kx_treeA f false stops scalls ss' acc accs pacc)
              | None =>
              match split_hint vmax i ss with
              | Some (x, v) =>
                  let t1 := kx_treeA f first stops scalls (kt_enter ss 0 (split_know (s_know ss) true x v)) [] [] pacc in
                  let t2 := kx_treeA f first stops scalls (kt_enter ss (kta_next t1) (split_know (s_know ss) false x v)) [] [] pacc in
                  KASplit x v acc accs t1 t2
              | None =>
              match acc_sym (facts_of (s_know ss)) i ss with
              | None => KALeaf ss acc accs
              | Some la =>
                  match sym_step segs i ss scr_nil with
                  | SOk ss' scs _ =>
                      if s_clean ss' then
                        (if (scalls && is_call i)%bool then KALeaf ss' (sc_add scs acc) (la ++ accs)
                         else kx_treeA f false stops scalls ss' (sc_add scs acc) (la ++ accs) (scs ++ pacc))
                      else KALeaf ss acc accs
                  | SStop =>
                      match sym_step segs i ss (SCR [true] [] []), sym_step segs i ss (SCR [false] [] []) with
                      | SOk sst scst _, SOk ssf scsf _ =>
                          match sc_is_br true scst, sc_is_br false scsf with
                          | Some (c, a, b), Some (c', a', b') =>
                              if (bc_eqb c c' && expr_eqb a a' && expr_eqb b b' && s_clean sst && s_clean ssf)%bool then
                                let t1 := kx_treeA f false stops scalls (kt_enter sst 0 (br_know (s_know ss) true c a b)) [] [] (scst ++ pacc) in
                                let t2 := kx_treeA f false stops scalls (kt_enter ssf (kta_next t1) (br_know (s_know ss) false c a b)) [] [] (scsf ++ pacc) in
                                KAFork c a b acc (la ++ accs) t1 t2
                              else KALeaf ss acc accs
                          | _, _ => KALeaf ss acc accs
                          end
                      | _, _ => KALeaf ss acc accs
                      end
                  end
              end
              end
              end
          end
      end
  end.

End TreeA.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section SoundA.
Variable segs : list Segment.

Lemma asan_chkA_shape : forall akn ss acc i ss1 ci, asan_chkA segs akn ss acc i = Some (ss1, ci) ->
  s_log ss1 = s_log ss /\ s_know ss1 = s_know ss /\ s_next ss1 = s_next ss /\ s_resv ss1 = s_resv ss.
Proof.
  intros akn ss acc i ss1 ci H. unfold asan_chkA in H.
  destruct (chk_site segs (s_pc ss) i) as [[[[t neg] slow] ok]|]; [|discriminate H].
  destruct (sr_get (s_regs ss) t) as [|j| | | | | |]; try discriminate H.
  destruct (find_rb j acc) as [[[a [|[|n]]] [|]]|]; try discriminate H.
  destruct (parse_slow segs slow) as [[[[[u x'] c] hasaddi] bltpc]|]; [|discriminate H].
  destruct (instr_at segs bltpc) as [ib|]; [|discriminate H]. destruct ib; try discriminate H. destruct c0; try discriminate H.
  lazymatch type of H with (if ?cnd then _ else _) = _ => destruct cnd; [|discriminate H] end.
  lazymatch type of H with (if ?cnd then _ else _) = _ => destruct cnd; [|discriminate H] end.
  injection H as <- <-. cbn [s_log s_know s_next s_resv]. repeat split; reflexivity.
Qed.

Lemma asan_chkG_shape : forall akn ss acc i ss1 ci, asan_chkG segs akn ss acc i = Some (ss1, ci) ->
  s_log ss1 = s_log ss /\ s_know ss1 = s_know ss /\ s_next ss1 = s_next ss /\ s_resv ss1 = s_resv ss.
Proof.
  intros akn ss acc i ss1 ci H. unfold asan_chkG in H.
  destruct (chk_site segs (s_pc ss) i) as [[[[t neg] slow] ok]|]; [|discriminate H].
  destruct (sr_get (s_regs ss) t) as [|j| | | | | |]; try discriminate H.
  destruct (find_rb j acc) as [[[a [|[|n]]] [|]]|]; try discriminate H.
  destruct (parse_slow segs slow) as [[[[[u x'] c] hasaddi] bltpc]|]; [|discriminate H].
  destruct (instr_at segs bltpc) as [ib|]; [|discriminate H]. destruct ib; try discriminate H. destruct c0; try discriminate H.
  lazymatch type of H with (if ?cnd then _ else _) = _ => destruct cnd; [|discriminate H] end.
  lazymatch type of H with (if ?cnd then _ else _) = _ => destruct cnd; [|discriminate H] end.
  injection H as <- <-. cbn [s_log s_know s_next s_resv]. repeat split; reflexivity.
Qed.

Lemma asan_chkZ_shape : forall akn ss acc i ss1 ci, asan_chkZ segs akn ss acc i = Some (ss1, ci) ->
  s_log ss1 = s_log ss /\ s_know ss1 = s_know ss /\ s_next ss1 = s_next ss /\ s_resv ss1 = s_resv ss.
Proof.
  intros akn ss acc i ss1 ci H. unfold asan_chkZ in H.
  destruct (chk_siteZ (s_pc ss) i) as [[[t neg] ok]|]; [|discriminate H].
  destruct (bv_eqb t 0); [discriminate H|].
  destruct (sr_get (s_regs ss) t) as [|j| | | | | |]; try discriminate H.
  destruct (find_rb j acc) as [[[a [|[|n]]] sx]|]; try discriminate H.
  lazymatch type of H with match ?fd with _ => _ end = _ => destruct fd as [ex|]; [|discriminate H] end.
  injection H as <- <-. cbn [s_log s_know s_next s_resv]. repeat split; reflexivity.
Qed.

Lemma asan_chk_shape : forall akn ss acc i ss1 ci, asan_chk segs akn ss acc i = Some (ss1, ci) ->
  s_log ss1 = s_log ss /\ s_know ss1 = s_know ss /\ s_next ss1 = s_next ss /\ s_resv ss1 = s_resv ss.
Proof.
  intros akn ss acc i ss1 ci H. unfold asan_chk in H.
  destruct (asan_chkA segs akn ss acc i) as [[s1 c1]|] eqn:HA.
  - injection H as <- <-. exact (asan_chkA_shape _ _ _ _ _ _ HA).
  - destruct (asan_chkG segs akn ss acc i) as [[s2 c2]|] eqn:HG.
    + injection H as <- <-. exact (asan_chkG_shape _ _ _ _ _ _ HG).
    + exact (asan_chkZ_shape _ _ _ _ _ _ H).
Qed.


Lemma instr_at_inv : forall pc i, instr_at segs pc = Some i ->
  exists w, fetch_word segs (Z_to_bv 64 pc) = Some w /\ is_ecall w = false /\ decode_any w = Some (i, 4).
Proof.
  intros pc i H. unfold instr_at in H.
  destruct (fetch_word segs (Z_to_bv 64 pc)) as [w|]; [|discriminate H].
  destruct (is_ecall w) eqn:He; [discriminate H|].
  destruct (decode_any w) as [[i1 sz]|] eqn:Hd; [|discriminate H].
  destruct (Z.eqb sz 4) eqn:Hs; [|discriminate H]. apply Z.eqb_eq in Hs. subst sz.
  injection H as ->. exists w. split; [reflexivity|]. split; [exact He|exact Hd].
Qed.

Lemma sym_step_branch_scripted : forall c r1 r2 imm ss d,
  sym_step segs (Branch c r1 r2 imm) ss scr_nil = SStop ->
  sym_step segs (Branch c r1 r2 imm) ss (SCR [d] [] []) =
    SOk (sjump ss (if d then br_target (s_pc ss) imm else s_pc ss + 4))
        [SCBr d c (sr_get (s_regs ss) r1) (sr_get (s_regs ss) r2)] (SCR [] [] []).
Proof.
  intros c r1 r2 imm ss d H. unfold sym_step in *. unfold scr_nil in H. cbn [sc_dirs sc_reads sc_hints] in *.
  lazymatch goal with |- match ?dec with _ => _ end = _ => destruct dec as [t|] eqn:Hd end; [discriminate H|].
  reflexivity.
Qed.

Lemma chk_site_inv : forall p i t neg slow ok, chk_site segs p i = Some (t, neg, slow, ok) ->
  (neg = false /\ ok = p + 4 /\ exists imm, i = Branch BC_NE t 0 imm /\ slow = br_target p imm) \/
  (neg = true /\ exists imm immj, i = Branch BC_EQ t 0 imm /\ ok = br_target p imm /\
     instr_at segs (p + 4) = Some (Jal 0 immj) /\ slow = j_target (p + 4) immj) \/
  (neg = true /\ slow = p + 4 /\ exists imm, i = Branch BC_EQ t 0 imm /\ ok = br_target p imm).
Proof.
  intros p i t neg slow ok H. unfold chk_site in H. destruct i; try discriminate H. destruct c; try discriminate H.
  - destruct (bv_eqb rs2 0) eqn:Hz; [|discriminate H].
    assert (rs2 = 0%bv) as -> by (apply bv_eq; unfold bv_eqb in Hz; apply Z.eqb_eq in Hz; exact Hz).
    destruct (instr_at segs (p + 4)) as [ij|] eqn:Hj.
    + destruct ij; try (injection H as <- <- <- <-; right; right; split; [reflexivity|]; split; [reflexivity|]; exists imm; split; reflexivity).
      destruct (bv_eqb rd 0) eqn:Hrd.
      * injection H as <- <- <- <-.
        assert (rd = 0%bv) as -> by (apply bv_eq; unfold bv_eqb in Hrd; apply Z.eqb_eq in Hrd; exact Hrd).
        right. left. split; [reflexivity|]. exists imm, imm0. repeat split; assumption || reflexivity.
      * injection H as <- <- <- <-. right; right. split; [reflexivity|]. split; [reflexivity|]. exists imm; split; reflexivity.
    + injection H as <- <- <- <-. right; right. split; [reflexivity|]. split; [reflexivity|]. exists imm; split; reflexivity.
  - destruct (bv_eqb rs2 0) eqn:Hz; [|discriminate H]. injection H as <- <- <- <-.
    assert (rs2 = 0%bv) as -> by (apply bv_eq; unfold bv_eqb in Hz; apply Z.eqb_eq in Hz; exact Hz).
    left. split; [reflexivity|]. split; [reflexivity|]. exists imm. split; reflexivity.
Qed.

Lemma parse_slow_inv : forall slow u x c hasaddi bltpc, parse_slow segs slow = Some (u, x, c, hasaddi, bltpc) ->
  exists imm7, instr_at segs slow = Some (OpImm ALU_AND u x imm7) /\ bv_signed imm7 = 7 /\
  ((hasaddi = false /\ c = 0 /\ bltpc = slow + 4) \/
   (hasaddi = true /\ bltpc = slow + 8 /\ exists immc, instr_at segs (slow + 4) = Some (OpImm ALU_ADD u u immc) /\ bv_signed immc = c)).
Proof.
  intros slow u x c hasaddi bltpc H. unfold parse_slow in H.
  destruct (instr_at segs slow) as [ia|] eqn:Ha; [|discriminate H]. destruct ia; try discriminate H. destruct op; try discriminate H.
  destruct (Z.eqb_spec (bv_signed imm) 7) as [H7|H7]; [|discriminate H].
  exists imm.
  destruct (instr_at segs (slow + 4)) as [ib|] eqn:Hb; [|discriminate H]. destruct ib; try discriminate H.
  - destruct c0; try discriminate H; injection H as <- <- <- <- <-; (split; [reflexivity|]; split; [exact H7|]; left; repeat split; reflexivity).
  - destruct op; try discriminate H.
    destruct (bv_eqb rd0 rd) eqn:E1; [|discriminate H]. destruct (bv_eqb rs0 rd) eqn:E2; [|discriminate H]. cbn [andb] in H.
    injection H as <- <- <- <- <-.
    assert (rd0 = rd) as -> by (apply bv_eq; unfold bv_eqb in E1; apply Z.eqb_eq in E1; exact E1).
    assert (rs0 = rd) as -> by (apply bv_eq; unfold bv_eqb in E2; apply Z.eqb_eq in E2; exact E2).
    split; [reflexivity|]. split; [exact H7|]. right. split; [reflexivity|]. split; [reflexivity|]. exists imm0. split; reflexivity.
Qed.
Lemma merge_word : forall (old e2v tv : word),
  alu64 ALU_ADD (mul_div M_MUL (alu64 ALU_SLTU tv (Z_to_bv 64 1)) old) (mul_div M_MUL (alu64 ALU_SLTU (Z_to_bv 64 0) tv) e2v)
  = (if bv_eqb tv (Z_to_bv 64 0) then old else e2v).
Proof.
  intros old e2v tv. unfold alu64, alu, mul_div. unfold bv_ltu, bv_eqb. rewrite !Z_to_bv_unsigned. change (bv_wrap 64 0) with 0.
  change (bv_wrap 64 1) with 1.
  pose proof (bv_unsigned_in_range _ tv) as R.
  pose proof (bv_unsigned_in_range _ old) as R1. pose proof (bv_unsigned_in_range _ e2v) as R2.
  unfold bv_modulus in R, R1, R2. change (2 ^ Z.of_N 64) with 18446744073709551616 in R, R1, R2.
  destruct (Z.ltb_spec 0 (bv_unsigned tv)) as [L|L]; destruct (Z.ltb_spec (bv_unsigned tv) 1) as [L1|L1];
    destruct (Z.eqb_spec (bv_unsigned tv) 0) as [Q|Q]; try lia.
  - apply bv_eq. rewrite bv_add_unsigned, !bv_mul_unsigned, !Z_to_bv_unsigned.
    unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with 18446744073709551616.
    change (1 mod 18446744073709551616) with 1. change (0 mod 18446744073709551616) with 0.
    rewrite Z.mul_1_l, Z.mul_0_l. rewrite (Z.mod_small (bv_unsigned e2v)) by lia. change (0 mod 18446744073709551616) with 0.
    rewrite Z.add_0_l. apply Z.mod_small; lia.
  - apply bv_eq. rewrite bv_add_unsigned, !bv_mul_unsigned, !Z_to_bv_unsigned.
    unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with 18446744073709551616.
    change (1 mod 18446744073709551616) with 1. change (0 mod 18446744073709551616) with 0.
    rewrite Z.mul_1_l, Z.mul_0_l. rewrite (Z.mod_small (bv_unsigned old)) by lia. change (0 mod 18446744073709551616) with 0.
    rewrite Z.add_0_r. apply Z.mod_small; lia.
Qed.
Lemma unpZ_byte : forall base lo hi x, unpZ base lo hi -> lo <= x -> x < hi ->
  exists b, base (Z_to_bv 64 (KXSHLO + x / 8)) = Some b /\ granok (Z.min (8 * (x / 8) + 8) hi - 8 * (x / 8)) b.
Proof.
  intros base lo hi x (H0 & H1 & H) Hlo Hhi.
  exact (H (x / 8) ltac:(lia) ltac:(Z.div_mod_to_equations; lia) ltac:(Z.div_mod_to_equations; lia)).
Qed.

Lemma unpZ_slow : forall base lo hi x c b, unpZ base lo hi -> lo <= x -> 0 <= c -> x + c + 1 <= hi ->
  base (Z_to_bv 64 (KXSHLO + x / 8)) = Some b -> bv_signed b <> 0 ->
  x mod 8 + c < bv_signed b /\ bv_signed b <= 7.
Proof.
  intros base lo hi x c b U Hlo Hc Hhi Hb Hnz.
  destruct (unpZ_byte base lo hi x U Hlo ltac:(lia)) as (b' & Hb' & G).
  rewrite Hb in Hb'. injection Hb' as <-.
  destruct G as [G|G]; [contradiction|]. Z.div_mod_to_equations. lia.
Qed.

Lemma sbyte_val : forall b : byte, Z_to_bv 64 (extz true 1 (bytes_le_to_Z [b])) = Z_to_bv 64 (bv_signed b).
Proof.
  intros b. unfold extz. cbn [bytes_le_to_Z]. f_equal.
  change (0 ≪ 8) with 0. rewrite Z.lor_0_r. change (8 * N.of_nat 1)%N with 8%N. reflexivity.
Qed.

Lemma sbyte_signed : forall b : byte, bv_signed (Z_to_bv 64 (bv_signed b)) = bv_signed b.
Proof.
  intros b. pose proof (bv_signed_in_range _ b) as R. unfold bv_half_modulus in R. cbn in R.
  rewrite (zb_signed (Z_to_bv 64 (bv_signed b))), Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
  change (2 ^ Z.of_N 64) with 18446744073709551616.
  specialize (R ltac:(discriminate)). unfold bv_modulus in R. change (2 ^ Z.of_N 8 / 2) with 128 in R.
  change (2^63) with 9223372036854775808. change (2^64) with 18446744073709551616.
  destruct (Z.ltb_spec ((bv_signed b) mod 18446744073709551616) 9223372036854775808); Z.div_mod_to_equations; lia.
Qed.
Lemma sbyte_zero : forall b : byte, bv_eqb (Z_to_bv 64 (bv_signed b)) (Z_to_bv 64 0) = Z.eqb (bv_signed b) 0.
Proof.
  intros b. pose proof (bv_signed_in_range _ b ltac:(discriminate)) as R. unfold bv_half_modulus, bv_modulus in R.
  change (2 ^ Z.of_N 8 / 2) with 128 in R.
  unfold bv_eqb. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with 18446744073709551616.
  change (0 mod 18446744073709551616) with 0.
  destruct (Z.eqb_spec (bv_signed b) 0) as [E|E]; [rewrite E; reflexivity|].
  apply Z.eqb_neq. Z.div_mod_to_equations; lia.
Qed.
Lemma find_rb_In : forall j scs a n sx, find_rb j scs = Some (a, n, sx) -> In (SCReadBase a n sx (EVar j)) scs.
Proof.
  induction scs as [|sc r IH]; intros a n sx H; [discriminate H|]. cbn [find_rb] in H.
  destruct sc as [| | | | | a' n' sx' e |]; try (right; exact (IH _ _ _ H)).
  destruct e; try (right; exact (IH _ _ _ H)).
  destruct (Nat.eqb_spec j n0) as [<-|NE]; [injection H as <- <- <-; left; reflexivity | right; exact (IH _ _ _ H)].
Qed.

Lemma sr_get_upd_same : forall sr u e, bv_eqb u 0 = false -> sr_get (sr_upd sr (ridx u) e) u = e.
Proof. intros sr u e Hu. unfold sr_get. rewrite Hu, nth_sr_upd, Nat.eqb_refl. reflexivity. Qed.

Lemma sr_get_upd_other : forall sr u e r, r <> u -> sr_get (sr_upd sr (ridx u) e) r = sr_get sr r.
Proof.
  intros sr u e r Hr. unfold sr_get. destruct (bv_eqb r 0); [reflexivity|]. rewrite nth_sr_upd.
  destruct (Nat.eqb_spec (ridx r) (ridx u)) as [Eq|Ne]; [exfalso; apply Hr; apply ridx_inj; exact Eq | reflexivity].
Qed.

Lemma regs_ok_ext : forall E sr1 sr2 R, regs_ok E sr1 R ->
  (forall r, bv_eqb r 0 = false -> edenot E (sr_get sr2 r) = edenot E (sr_get sr1 r)) -> regs_ok E sr2 R.
Proof.
  intros E sr1 sr2 R H1 H2 r. rewrite (H1 r). destruct (bv_eqb r 0) eqn:Hr0.
  - unfold sr_get. rewrite Hr0. reflexivity.
  - symmetry. apply H2. exact Hr0.
Qed.

Section ChkSound.
Variables (F : bvmap 5 word) (fc : bv 32).
Variable E : env.
Variables base rom : word -> option byte.
Variable RNG : footprint.
Variable Q : machine_state -> Prop.
Variable akn : list aent.
Hypothesis HAK : aknow_ok RNG E base akn.

Lemma shadow_saddr_u : forall kn ex, know_ok segs E base kn ->
  bv_unsigned (adenot E (shadow_saddr (facts_of kn) ex)) = KXSHLO + bv_unsigned (edenot E ex) / 8.
Proof.
  intros kn ex Hkn. pose proof (facts_of_ok segs E base _ Hkn) as Hfk. unfold shadow_saddr.
  rewrite (to_saddrK_denot segs E base _ _ _ Hfk).
  rewrite !(mkAluK_denot segs E base _ _ _ _ Hfk). unfold alu64, alu.
  cbn [edenot]. unfold PropExec.v_addi.
  rewrite Z_to_bv_unsigned, bv_add_unsigned, bv_shiftr_unsigned, bv_and_unsigned, !Z_to_bv_unsigned.
  pose proof (bv_unsigned_in_range _ (edenot E ex)) as R. unfold bv_modulus in R.
  unfold bv_wrap, bv_modulus, KXSHLO. change (2 ^ Z.of_N 64) with 18446744073709551616 in *.
  change (Z.land (3 mod 18446744073709551616) (63 mod 18446744073709551616)) with 3.
  rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8.
  change (2147450880 mod 18446744073709551616) with 2147450880. rewrite Z.add_0_r.
  rewrite (Z.mod_small (_ + 2147450880)) by (Z.div_mod_to_equations; lia). rewrite Z.mod_small by (Z.div_mod_to_equations; lia). lia.
Qed.

(* [comment removed for export] *)
Lemma shmatch_u : forall kn ex a, know_ok segs E base kn -> shmatch akn (facts_of kn) ex a = true ->
  bv_unsigned (adenot E a) = KXSHLO + bv_unsigned (edenot E ex) / 8.
Proof.
  intros kn ex a Hkn H. unfold shmatch in H. apply orb_prop in H. destruct H as [H|H].
  - apply saddr_eqb_eq in H. rewrite <- H. exact (shadow_saddr_u kn ex Hkn).
  - apply existsb_exists in H as (K & Hin & HK). destruct K as [s0 n|s0 n|s0 x]; try discriminate HK.
    apply andb_prop in HK as [Hs Hx]. apply saddr_eqb_eq in Hs. apply expr_eqb_eq in Hx. subst a ex.
    assert (HAok : aent_ok RNG E base (AShp s0 x)) by (unfold aknow_ok in HAK; rewrite Forall_forall in HAK; exact (HAK _ Hin)).
    cbn [aent_ok] in HAok. unfold estart, elenZ in HAok.
    pose proof (bv_unsigned_in_range _ (edenot E x)) as R. unfold bv_modulus in R. change (2 ^ Z.of_N 64) with 18446744073709551616 in R.
    rewrite adenot_estart, Z_to_bv_unsigned. unfold estart. rewrite HAok. apply bv_wrap_small.
    unfold bv_modulus, KXSHLO. change (2 ^ Z.of_N 64) with 18446744073709551616. Z.div_mod_to_equations. lia.
Qed.
Lemma unp_cover_sound : forall kn ex len, know_ok segs E base kn -> unp_cover akn kn ex len = true -> 0 <= len < 2^64 ->
  exists A n, In (AUnp A n) akn /\ estart E A <= bv_unsigned (edenot E ex) /\
              bv_unsigned (edenot E ex) + len <= estart E A + elenZ E n.
Proof.
  intros kn ex len Hkn H Hlen. unfold unp_cover in H. apply existsb_exists in H as (K & Hin & HK).
  destruct K as [A n|A n|A n]; [|discriminate HK|discriminate HK]. exists A, n. split; [exact Hin|].
  pose proof (xinside_sound segs E base kn _ _ _ _ _ _ Hkn HK) as [X1 X2].
  unfold estart in X1, X2 |- *. cbn [a_base a_off] in X1, X2. unfold elenZ in X2 |- *. cbn [edenot] in X2.
  rewrite Z_to_bv_unsigned, bv_wrap_small in X2 by (unfold bv_modulus; change (2 ^ Z.of_N 64) with (2^64); lia).
  destruct A as [Ab Ao]. cbn [a_base a_off] in *. lia.
Qed.

Lemma rdn_one : forall (m : word -> option byte) a b, m a = Some b -> rdn segs m a 1 = Some [b].
Proof. intros m a b H. cbn [rdn]. rewrite H. reflexivity. Qed.

Lemma sr_get_x0 : forall sr, sr_get sr 0 = ELit 0.
Proof. intros sr. reflexivity. Qed.
Lemma sym_step_branch_shape : forall c r1 r2 imm ss scr ss' scs scr',
  sym_step segs (Branch c r1 r2 imm) ss scr = SOk ss' scs scr' -> exists npc, ss' = sjump ss npc.
Proof.
  intros c r1 r2 imm ss scr ss' scs scr' H. unfold sym_step in H.
  lazymatch type of H with match ?dec with _ => _ end = _ => destruct dec as [tk|] end.
  - injection H as <- _ _. eexists. reflexivity.
  - destruct (sc_dirs scr) as [|d ds]; [discriminate H|]. injection H as <- _ _. eexists. reflexivity.
Qed.

Lemma bv_eqb_false_ne : forall (r u : reg), bv_eqb r u = false -> r <> u.
Proof. intros r u H ->. unfold bv_eqb in H. rewrite Z.eqb_refl in H. discriminate H. Qed.
Lemma bv_eqb_true_eq : forall (r u : reg), bv_eqb r u = true -> r = u.
Proof. intros r u H. apply bv_eq. apply Z.eqb_eq. exact H. Qed.

Lemma asan_chkA_sound : forall ss acc i ss' ci w regs,
  fetch_word segs (Z_to_bv 64 (s_pc ss)) = Some w -> is_ecall w = false -> decode_any w = Some (i, 4) ->
  sym_step segs i ss scr_nil = SStop ->
  asan_chkA segs akn ss acc i = Some (ss', ci) ->
  s_resv ss = None ->
  scs_denot segs base E acc ->
  regs_ok E (s_regs ss) regs -> rfull regs -> log_flat E (s_log ss) -> know_ok segs E base (s_know ss) ->
  (forall regs', regs_ok E (s_regs ss') regs' -> rfull regs' ->
      evtF segs RNG Q (MS regs' F (Z_to_bv 64 (s_pc ss')) fc None (mem_denot E base (s_log ss)) rom)) ->
  evtF segs RNG Q (MS regs F (Z_to_bv 64 (s_pc ss)) fc None (mem_denot E base (s_log ss)) rom).
Proof.
  intros ss acc i ss' ci w regs Hf He Hd Hstop H Hc Hacc Hr Hfu Hlf Hkn K.
  unfold asan_chkA in H.
  destruct (chk_site segs (s_pc ss) i) as [[[[t neg] slow] ok]|] eqn:Hsite; [|discriminate H].
  destruct (sr_get (s_regs ss) t) as [|j| | | | | |] eqn:Ht; try discriminate H.
  destruct (find_rb j acc) as [[[a [|[|n]]] [|]]|] eqn:Hrb; try discriminate H.
  destruct (parse_slow segs slow) as [[[[[u x'] c] hasaddi] bltpc]|] eqn:Hps; [|discriminate H].
  destruct (instr_at segs bltpc) as [ib|] eqn:Hib; [|discriminate H]. destruct ib; try discriminate H.
  destruct c0; try discriminate H.
  lazymatch type of H with (if ?cnd then _ else _) = _ => destruct cnd eqn:Hcond; [|discriminate H] end.
  lazymatch type of H with (if ?cnd then _ else _) = _ => destruct cnd eqn:Hcond2; [|discriminate H] end.
  apply andb_prop in Hcond as [Hcond Hc7]. apply andb_prop in Hcond as [Hcond Hc0]. apply andb_prop in Hcond as [Hcond Ht0].
  apply andb_prop in Hcond as [Hcond Hut]. apply andb_prop in Hcond as [Hcond Hu0]. apply andb_prop in Hcond as [Hcond Hok].
  apply andb_prop in Hcond as [Hbu Hbt].
  apply andb_prop in Hcond2 as [Hcond2 Hblt]. apply andb_prop in Hcond2 as [Hsha Hcov].
  injection H as <- <-. cbn [s_pc s_regs s_log] in K.
  apply bv_eqb_true_eq in Hbu. apply bv_eqb_true_eq in Hbt. subst rs1 rs2.
  apply Z.eqb_eq in Hok. apply Z.leb_le in Hc0. apply Z.leb_le in Hc7.
  apply negb_true_iff in Hu0. apply negb_true_iff in Hut. apply negb_true_iff in Ht0.
  pose proof (bv_eqb_false_ne _ _ Hut) as Hne_ut. assert (Hne_tu : t <> u) by (intros X; apply Hne_ut; symmetry; exact X).
  set (kn := s_know ss) in *. set (fk := facts_of kn) in *. set (sr := s_regs ss) in *. set (ex := sr_get sr x') in *.
  set (e1 := mkAluK fk ALU_AND ex (ELit 7)) in *.
  (* [comment removed for export] *)
  pose proof (find_rb_In _ _ _ _ _ Hrb) as Hin.
  unfold scs_denot in Hacc. rewrite Forall_forall in Hacc. pose proof (Hacc _ Hin) as Hrd. cbn [sc_denot edenot] in Hrd.
  destruct Hrd as (bs & Hrdn & Hval).
  (* [comment removed for export] *)
  pose proof (shmatch_u kn ex a Hkn Hsha) as Hsh.
  set (xv := bv_unsigned (edenot E ex)) in *.
  (* [comment removed for export] *)
  destruct (unp_cover_sound kn ex (c + 1) Hkn Hcov ltac:(lia)) as (A & n & HinA & HA1 & HA2). fold xv in HA1, HA2.
  assert (HAok : aent_ok RNG E base (AUnp A n)) by (unfold aknow_ok in HAK; rewrite Forall_forall in HAK; exact (HAK _ HinA)).
  cbn [aent_ok] in HAok. destruct HAok as [HU HRNG].
  (* [comment removed for export] *)
  destruct (unpZ_byte base _ _ xv HU HA1 ltac:(lia)) as (b0 & Hb0 & Hgran).
  assert (Ea : adenot E a = Z_to_bv 64 (KXSHLO + xv / 8)).
  { apply bv_eq. rewrite Hsh, Z_to_bv_unsigned. symmetry. apply bv_wrap_small.
    unfold bv_modulus, KXSHLO. change (2 ^ Z.of_N 64) with 18446744073709551616.
    pose proof (bv_unsigned_in_range _ (edenot E ex)) as R. unfold bv_modulus in R. change (2 ^ Z.of_N 64) with 18446744073709551616 in R.
    subst xv. Z.div_mod_to_equations. lia. }
  rewrite Ea in Hrdn. cbn [AS.PropExec.rdn] in Hrdn. rewrite Hb0 in Hrdn. injection Hrdn as <-. rewrite sbyte_val in Hval. symmetry in Hval.
  (* [comment removed for export] *)
  assert (Hmrg : forall e2, edenot E (merge_u (sr_get sr u) e2 j) =
                 if Z.eqb (bv_signed b0) 0 then edenot E (sr_get sr u) else edenot E e2).
  { intros e2. unfold merge_u. cbn [edenot]. rewrite Hval. rewrite merge_word, sbyte_zero. reflexivity. }
  assert (Hej : bv_signed (edenot E (EVar j)) = bv_signed b0) by (cbn [edenot]; rewrite Hval; apply sbyte_signed).
  assert (He1 : bv_signed (edenot E e1) = xv mod 8).
  { unfold e1, fk. rewrite (mkAluK_denot segs E base _ _ _ _ (facts_of_ok segs E base _ Hkn)). unfold alu64, alu. cbn [edenot].
    rewrite (zb_signed (bv_and _ _)), bv_and_unsigned, Z_to_bv_unsigned. change (bv_wrap 64 7) with (Z.ones 3).
    rewrite Z.land_ones by lia. change (2^3) with 8. fold xv.
    destruct (Z.ltb_spec (xv mod 8) (2^63)); Z.div_mod_to_equations; lia. }
  (* [comment removed for export] *)
  assert (BLT : forall (e2 : expr) (ss3 : sym_state) (regsX : bvmap 5 word),
            s_regs ss3 = sr_upd sr (ridx u) e2 -> s_log ss3 = s_log ss -> s_know ss3 = kn -> s_resv ss3 = None -> s_pc ss3 = bltpc ->
            blt_ok segs (Branch BC_LT u t imm) ss3 ok = true ->
            bv_signed b0 <> 0 -> bv_signed (edenot E e2) = xv mod 8 + c ->
            regs_ok E (s_regs ss3) regsX -> rfull regsX ->
            (forall regs', regs_ok E (sr_upd sr (ridx u) (merge_u (sr_get sr u) e2 j)) regs' -> rfull regs' ->
                evtF segs RNG Q (MS regs' F (Z_to_bv 64 ok) fc None (mem_denot E base (s_log ss)) rom)) ->
            evtF segs RNG Q (MS regsX F (Z_to_bv 64 bltpc) fc None (mem_denot E base (s_log ss)) rom)).
  { intros e2 ss3 regsX S3r S3l S3k S3v S3p Hbo NZ He2 HrX HfuX KX.
    destruct (unpZ_slow base _ _ xv c b0 HU HA1 ltac:(lia) ltac:(lia) Hb0 NZ) as [Hlt Hle7].
    destruct (instr_at_inv _ _ Hib) as (w3 & Hf3 & He3 & Hd3). rewrite <- S3p in Hf3.
    assert (HlfX : log_flat E (s_log ss3)) by (rewrite S3l; exact Hlf).
    assert (HknX : know_ok segs E base (s_know ss3)) by (rewrite S3k; exact Hkn).
    assert (Hgu : sr_get (s_regs ss3) u = e2) by (rewrite S3r; apply sr_get_upd_same; exact Hu0).
    assert (Hgt : sr_get (s_regs ss3) t = EVar j) by (rewrite S3r, sr_get_upd_other by exact Hne_tu; exact Ht).
    assert (POST : forall regs3, regs_ok E (s_regs ss3) regs3 -> rfull regs3 ->
                     evtF segs RNG Q (MS regs3 F (Z_to_bv 64 ok) fc None (mem_denot E base (s_log ss)) rom)).
    { intros regs3 Hr3 Hfu3. apply KX; [|exact Hfu3]. rewrite S3r in Hr3. eapply regs_ok_ext; [exact Hr3|]. intros r Hr0.
      destruct (bv_eqb r u) eqn:Hru.
      - apply bv_eqb_true_eq in Hru. subst r. rewrite !sr_get_upd_same by exact Hu0. rewrite Hmrg. rewrite (proj2 (Z.eqb_neq _ _) NZ). reflexivity.
      - apply bv_eqb_false_ne in Hru. rewrite !sr_get_upd_other by exact Hru. reflexivity. }
    unfold blt_ok in Hbo.
    destruct (sym_step segs (Branch BC_LT u t imm) ss3 scr_nil) as [ss4 scs4 scr4|] eqn:Hs4.
    - (* [comment removed for export] *)
      destruct scs4 as [|? ?]; [|discriminate Hbo]. apply Z.eqb_eq in Hbo.
      destruct (sym_step_branch_shape _ _ _ _ _ _ _ _ _ Hs4) as [npc ->]. cbn [s_pc sjump] in Hbo. subst npc.
      destruct (kx_step_sound segs F fc E base rom RNG ss3 regsX _ _ _ _ _ w3 [] Hf3 He3 Hd3 Hs4 eq_refl S3v S3v (Forall_nil _) (Forall_nil _) HrX HfuX HlfX HknX)
        as (regs3 & Hstep3 & Hr3 & Hfu3 & _).
      cbn [s_pc s_log s_regs sjump] in Hstep3, Hr3. rewrite ?S3p, ?S3l in Hstep3.
      eapply evtF_step; [exact Hstep3|]. exact (POST regs3 Hr3 Hfu3).
    - (* [comment removed for export] *)
      pose proof (sym_step_branch_scripted BC_LT u t imm ss3 true Hs4) as STEP4. rewrite Hgu, Hgt, S3p, Hok in STEP4.
      assert (SCS4 : scs_denot segs base E [SCBr true BC_LT e2 (EVar j)]).
      { constructor; [|constructor]. cbn [sc_denot branch_taken]. unfold bv_lts. rewrite He2, Hej. apply Z.ltb_lt. lia. }
      destruct (kx_step_sound segs F fc E base rom RNG ss3 regsX _ _ _ _ _ w3 [] Hf3 He3 Hd3 STEP4 eq_refl S3v S3v SCS4 (Forall_nil _) HrX HfuX HlfX HknX)
        as (regs3 & Hstep3 & Hr3 & Hfu3 & _).
      cbn [s_pc s_log s_regs sjump] in Hstep3, Hr3. rewrite ?S3p, ?S3l in Hstep3.
      eapply evtF_step; [exact Hstep3|]. exact (POST regs3 Hr3 Hfu3). }
  assert (SLOW : bv_signed b0 <> 0 -> forall regs1, regs_ok E sr regs1 -> rfull regs1 ->
            evtF segs RNG Q (MS regs1 F (Z_to_bv 64 slow) fc None (mem_denot E base (s_log ss)) rom)).
  { intros NZ regs1 Hr1 Hfu1.
    destruct (parse_slow_inv _ _ _ _ _ _ Hps) as (imm7 & Hia & H7 & Hcases).
    destruct (instr_at_inv _ _ Hia) as (w2 & Hf2 & He2 & Hd2).
    destruct (kx_step_sound segs F fc E base rom RNG (sjump ss slow) regs1 (OpImm ALU_AND u x' imm7)
                (sset (sjump ss slow) u (mkAluK fk ALU_AND ex (ELit (bv_signed imm7))) (slow + 4))
                [] scr_nil scr_nil w2 [] Hf2 He2 Hd2 eq_refl eq_refl Hc Hc (Forall_nil _) (Forall_nil _) Hr1 Hfu1 Hlf Hkn)
      as (regs2 & Hstep2 & Hr2 & Hfu2 & _).
    eapply evtF_step; [exact Hstep2|]. clear Hstep2. rewrite H7 in Hr2. fold e1 in Hr2.
    cbn [s_pc s_regs s_log s_know sjump sset] in Hr2 |- *. fold sr in Hr2. rewrite Hu0 in Hr2.
    destruct Hcases as [(-> & -> & ->) | (-> & -> & immc & Hiad & Hic)].
    - (* [comment removed for export] *)
      unfold sset, sjump in K, Hblt. cbn [s_pc s_regs s_log s_know s_next s_resv] in K, Hblt.
      fold sr in K. fold sr in Hblt. fold kn in K. fold kn in Hblt. fold fk in K. fold fk in Hblt. fold ex in K. fold ex in Hblt.
      fold e1 in K. fold e1 in Hblt. rewrite Hu0 in K, Hblt. rewrite sr_get_upd_same in K by exact Hu0.
      apply (BLT e1 (SSR (slow + 4) (sr_upd sr (ridx u) e1) (s_log ss) kn (s_next ss) (s_resv ss)) regs2);
        [reflexivity | reflexivity | reflexivity | exact Hc | reflexivity | exact Hblt | exact NZ | rewrite He1; lia | exact Hr2 | exact Hfu2 | exact K].
    - (* [comment removed for export] *)
      unfold sset, sjump in K, Hblt. cbn [s_pc s_regs s_log s_know s_next s_resv] in K, Hblt.
      fold sr in K. fold sr in Hblt. fold kn in K. fold kn in Hblt. fold fk in K. fold fk in Hblt. fold ex in K. fold ex in Hblt.
      fold e1 in K. fold e1 in Hblt. rewrite Hu0 in K, Hblt. rewrite !sr_get_upd_same in K, Hblt by exact Hu0.
      destruct (instr_at_inv _ _ Hiad) as (w2b & Hf2b & He2b & Hd2b).
      set (ss2 := SSR (slow + 4) (sr_upd sr (ridx u) e1) (s_log ss) kn (s_next ss) (s_resv ss)) in *.
      destruct (kx_step_sound segs F fc E base rom RNG ss2 regs2 (OpImm ALU_ADD u u immc)
                  (sset ss2 u (mkAluK fk ALU_ADD (sr_get (s_regs ss2) u) (ELit (bv_signed immc))) (slow + 4 + 4))
                  [] scr_nil scr_nil w2b [] Hf2b He2b Hd2b eq_refl eq_refl Hc Hc (Forall_nil _) (Forall_nil _) Hr2 Hfu2 Hlf Hkn)
        as (regs2b & Hstep2b & Hr2b & Hfu2b & _).
      eapply evtF_step; [exact Hstep2b|]. clear Hstep2b. rewrite Hic in Hr2b.
      cbn [s_pc s_regs s_log s_know sjump sset ss2] in Hr2b |- *. rewrite Hu0 in Hr2b. rewrite sr_get_upd_same in Hr2b by exact Hu0.
      set (e2 := mkAluK fk ALU_ADD e1 (ELit c)) in *.
      replace (slow + 4 + 4) with (slow + 8) by lia.
      rewrite ?sr_get_upd_same in K by exact Hu0. fold e2 in K.
      apply (BLT e2 (SSR (slow + 8) (sr_upd (sr_upd sr (ridx u) e1) (ridx u) e2) (s_log ss) kn (s_next ss) (s_resv ss)) regs2b);
        [ | reflexivity | reflexivity | exact Hc | reflexivity | exact Hblt | exact NZ | | exact Hr2b | exact Hfu2b | exact K].
      + assert (UU : forall n0 l (a1 b1 : expr), sr_upd (sr_upd l n0 a1) n0 b1 = sr_upd l n0 b1).
        { clear. induction n0 as [|n0 IH]; intros [|h tl] a1 b1; cbn; try reflexivity; rewrite IH; reflexivity. }
        apply UU.
      + unfold e2, fk. rewrite (mkAluK_denot segs E base _ _ _ _ (facts_of_ok segs E base _ Hkn)). fold fk. unfold alu64, alu.
        cbn [edenot].
        assert (Hu1 : bv_unsigned (edenot E e1) = xv mod 8).
        { rewrite <- He1. rewrite (zb_signed (edenot E e1)).
          pose proof (bv_unsigned_in_range _ (edenot E e1)) as R1. unfold bv_modulus in R1. change (2 ^ Z.of_N 64) with (2^64) in R1.
          rewrite (zb_signed (edenot E e1)) in He1.
          destruct (Z.ltb_spec (bv_unsigned (edenot E e1)) (2^63)); [reflexivity|].
          exfalso. Z.div_mod_to_equations. lia. }
        rewrite (zb_signed (_ + _)), bv_add_unsigned, Z_to_bv_unsigned, Hu1. unfold bv_wrap, bv_modulus.
        change (2 ^ Z.of_N 64) with 18446744073709551616. change (2^63) with 9223372036854775808.
        rewrite (Z.mod_small c) by lia. rewrite Z.mod_small by (Z.div_mod_to_equations; lia).
        destruct (Z.ltb_spec (xv mod 8 + c) 9223372036854775808); Z.div_mod_to_equations; lia. }
  (* [comment removed for export] *)
  assert (FAST : bv_signed b0 = 0 -> forall regs1, regs_ok E sr regs1 ->
            regs_ok E (sr_upd sr (ridx u) (merge_u (sr_get sr u) (sr_get (s_regs
              (if hasaddi
               then sset (sset (sjump ss slow) u e1 (slow + 4)) u
                      (mkAluK fk ALU_ADD (sr_get (s_regs (sset (sjump ss slow) u e1 (slow + 4))) u) (ELit c)) (slow + 8)
               else sset (sjump ss slow) u e1 (slow + 4))) u) j)) regs1).
  { intros Z0 regs1 Hr1. eapply regs_ok_ext; [exact Hr1|]. intros r Hr0.
    destruct (bv_eqb r u) eqn:Hru.
    - apply bv_eqb_true_eq in Hru. subst r. rewrite sr_get_upd_same by exact Hu0. rewrite Hmrg, Z0. reflexivity.
    - apply bv_eqb_false_ne in Hru. rewrite sr_get_upd_other by exact Hru. reflexivity. }
  destruct (chk_site_inv _ _ _ _ _ _ Hsite) as [(-> & -> & immB & -> & ->) | [(-> & immB & immj & -> & -> & Hjal & ->) | (-> & -> & immB & -> & ->)]].
  - (* [comment removed for export] *)
    pose proof (sym_step_branch_scripted BC_NE t 0 immB ss (negb (Z.eqb (bv_signed b0) 0)) Hstop) as STEP.
    fold sr in STEP. rewrite Ht, sr_get_x0 in STEP.
    assert (SCS : scs_denot segs base E [SCBr (negb (Z.eqb (bv_signed b0) 0)) BC_NE (EVar j) (ELit 0)]).
    { constructor; [|constructor]. cbn [sc_denot edenot branch_taken]. rewrite Hval, sbyte_zero. reflexivity. }
    destruct (kx_step_sound segs F fc E base rom RNG ss regs _ _ _ _ _ w [] Hf He Hd STEP eq_refl Hc Hc SCS (Forall_nil _) Hr Hfu Hlf Hkn)
      as (regs1 & Hstep1 & Hr1 & Hfu1 & _).
    eapply evtF_step; [exact Hstep1|]. clear Hstep1. cbn [s_pc s_regs s_log sjump] in Hr1 |- *. fold sr in Hr1.
    destruct (Z.eqb_spec (bv_signed b0) 0) as [Z0|NZ]; cbn [negb].
    + apply K; [exact (FAST Z0 regs1 Hr1) | exact Hfu1].
    + exact (SLOW NZ regs1 Hr1 Hfu1).
  - (* [comment removed for export] *)
    pose proof (sym_step_branch_scripted BC_EQ t 0 immB ss (Z.eqb (bv_signed b0) 0) Hstop) as STEP.
    fold sr in STEP. rewrite Ht, sr_get_x0 in STEP.
    assert (SCS : scs_denot segs base E [SCBr (Z.eqb (bv_signed b0) 0) BC_EQ (EVar j) (ELit 0)]).
    { constructor; [|constructor]. cbn [sc_denot edenot branch_taken]. rewrite Hval, sbyte_zero. reflexivity. }
    destruct (kx_step_sound segs F fc E base rom RNG ss regs _ _ _ _ _ w [] Hf He Hd STEP eq_refl Hc Hc SCS (Forall_nil _) Hr Hfu Hlf Hkn)
      as (regs1 & Hstep1 & Hr1 & Hfu1 & _).
    eapply evtF_step; [exact Hstep1|]. clear Hstep1. cbn [s_pc s_regs s_log sjump] in Hr1 |- *. fold sr in Hr1.
    destruct (Z.eqb_spec (bv_signed b0) 0) as [Z0|NZ].
    + apply K; [exact (FAST Z0 regs1 Hr1) | exact Hfu1].
    + (* [comment removed for export] *)
      destruct (instr_at_inv _ _ Hjal) as (wj & Hfj & Hej2 & Hdj).
      destruct (kx_step_sound segs F fc E base rom RNG (sjump ss (s_pc ss + 4)) regs1 (Jal 0 immj)
                  (sset (sjump ss (s_pc ss + 4)) 0 (ELit (s_pc ss + 4 + 4)) (j_target (s_pc ss + 4) immj))
                  [] scr_nil scr_nil wj [] Hfj Hej2 Hdj eq_refl eq_refl Hc Hc (Forall_nil _) (Forall_nil _) Hr1 Hfu1 Hlf Hkn)
        as (regsj & Hstepj & Hrj & Hfuj & _).
      eapply evtF_step; [exact Hstepj|]. clear Hstepj. cbn [s_pc s_regs s_log sjump sset] in Hrj |- *.
      exact (SLOW NZ regsj Hrj Hfuj).
  - (* [comment removed for export] *)
    pose proof (sym_step_branch_scripted BC_EQ t 0 immB ss (Z.eqb (bv_signed b0) 0) Hstop) as STEP.
    fold sr in STEP. rewrite Ht, sr_get_x0 in STEP.
    assert (SCS : scs_denot segs base E [SCBr (Z.eqb (bv_signed b0) 0) BC_EQ (EVar j) (ELit 0)]).
    { constructor; [|constructor]. cbn [sc_denot edenot branch_taken]. rewrite Hval, sbyte_zero. reflexivity. }
    destruct (kx_step_sound segs F fc E base rom RNG ss regs _ _ _ _ _ w [] Hf He Hd STEP eq_refl Hc Hc SCS (Forall_nil _) Hr Hfu Hlf Hkn)
      as (regs1 & Hstep1 & Hr1 & Hfu1 & _).
    eapply evtF_step; [exact Hstep1|]. clear Hstep1. cbn [s_pc s_regs s_log sjump] in Hr1 |- *. fold sr in Hr1.
    destruct (Z.eqb_spec (bv_signed b0) 0) as [Z0|NZ].
    + apply K; [exact (FAST Z0 regs1 Hr1) | exact Hfu1].
    + exact (SLOW NZ regs1 Hr1 Hfu1).
Qed.
Lemma asan_chkG_sound : forall ss acc i ss' ci w regs,
  fetch_word segs (Z_to_bv 64 (s_pc ss)) = Some w -> is_ecall w = false -> decode_any w = Some (i, 4) ->
  sym_step segs i ss scr_nil = SStop ->
  asan_chkG segs akn ss acc i = Some (ss', ci) ->
  s_resv ss = None ->
  scs_denot segs base E acc ->
  regs_ok E (s_regs ss) regs -> rfull regs -> log_flat E (s_log ss) -> know_ok segs E base (s_know ss) ->
  (forall regs', regs_ok E (s_regs ss') regs' -> rfull regs' ->
      evtF segs RNG Q (MS regs' F (Z_to_bv 64 (s_pc ss')) fc None (mem_denot E base (s_log ss)) rom)) ->
  evtF segs RNG Q (MS regs F (Z_to_bv 64 (s_pc ss)) fc None (mem_denot E base (s_log ss)) rom).
Proof.
  intros ss acc i ss' ci w regs Hf He Hd Hstop H Hc Hacc Hr Hfu Hlf Hkn K.
  unfold asan_chkG in H.
  destruct (chk_site segs (s_pc ss) i) as [[[[t neg] slow] ok]|] eqn:Hsite; [|discriminate H].
  destruct (sr_get (s_regs ss) t) as [|j| | | | | |] eqn:Ht; try discriminate H.
  destruct (find_rb j acc) as [[[a [|[|n]]] [|]]|] eqn:Hrb; try discriminate H.
  destruct (parse_slow segs slow) as [[[[[u x'] c] hasaddi] bltpc]|] eqn:Hps; [|discriminate H].
  destruct (instr_at segs bltpc) as [ib|] eqn:Hib; [|discriminate H]. destruct ib; try discriminate H.
  destruct c0; try discriminate H.
  lazymatch type of H with (if ?cnd then _ else _) = _ => destruct cnd eqn:Hcond; [|discriminate H] end.
  lazymatch type of H with (if ?cnd then _ else _) = _ => destruct cnd eqn:Hcond2; [|discriminate H] end.
  apply andb_prop in Hcond as [Hcond Hc7]. apply andb_prop in Hcond as [Hcond Hc0]. apply andb_prop in Hcond as [Hcond Ht0].
  apply andb_prop in Hcond as [Hcond Hut]. apply andb_prop in Hcond as [Hcond Hu0]. apply andb_prop in Hcond as [Hcond HJ].
  apply andb_prop in Hcond as [Hbu Hbt].
  (* [comment removed for export] *)
  unfold jal_to in HJ. destruct (instr_at segs (bltpc + 4)) as [ij|] eqn:HJi; [|discriminate HJ]. destruct ij; try discriminate HJ.
  apply andb_prop in HJ as [HJrd HJok]. apply bv_eqb_true_eq in HJrd. subst rd. apply Z.eqb_eq in HJok.
  apply andb_prop in Hcond2 as [Hcond2 Hblt]. apply andb_prop in Hcond2 as [Hsha Hcov].
  injection H as <- <-. cbn [s_pc s_regs s_log] in K.
  apply bv_eqb_true_eq in Hbu. apply bv_eqb_true_eq in Hbt. subst rs1 rs2.
  apply Z.leb_le in Hc0. apply Z.leb_le in Hc7.
  apply negb_true_iff in Hu0. apply negb_true_iff in Hut. apply negb_true_iff in Ht0.
  pose proof (bv_eqb_false_ne _ _ Hut) as Hne_ut. assert (Hne_tu : t <> u) by (intros X; apply Hne_ut; symmetry; exact X).
  set (kn := s_know ss) in *. set (fk := facts_of kn) in *. set (sr := s_regs ss) in *. set (ex := sr_get sr x') in *.
  set (e1 := mkAluK fk ALU_AND ex (ELit 7)) in *.
  (* [comment removed for export] *)
  pose proof (find_rb_In _ _ _ _ _ Hrb) as Hin.
  unfold scs_denot in Hacc. rewrite Forall_forall in Hacc. pose proof (Hacc _ Hin) as Hrd. cbn [sc_denot edenot] in Hrd.
  destruct Hrd as (bs & Hrdn & Hval).
  (* [comment removed for export] *)
  pose proof (shmatch_u kn ex a Hkn Hsha) as Hsh.
  set (xv := bv_unsigned (edenot E ex)) in *.
  (* [comment removed for export] *)
  destruct (unp_cover_sound kn ex (c + 1) Hkn Hcov ltac:(lia)) as (A & n & HinA & HA1 & HA2). fold xv in HA1, HA2.
  assert (HAok : aent_ok RNG E base (AUnp A n)) by (unfold aknow_ok in HAK; rewrite Forall_forall in HAK; exact (HAK _ HinA)).
  cbn [aent_ok] in HAok. destruct HAok as [HU HRNG].
  (* [comment removed for export] *)
  destruct (unpZ_byte base _ _ xv HU HA1 ltac:(lia)) as (b0 & Hb0 & Hgran).
  assert (Ea : adenot E a = Z_to_bv 64 (KXSHLO + xv / 8)).
  { apply bv_eq. rewrite Hsh, Z_to_bv_unsigned. symmetry. apply bv_wrap_small.
    unfold bv_modulus, KXSHLO. change (2 ^ Z.of_N 64) with 18446744073709551616.
    pose proof (bv_unsigned_in_range _ (edenot E ex)) as R. unfold bv_modulus in R. change (2 ^ Z.of_N 64) with 18446744073709551616 in R.
    subst xv. Z.div_mod_to_equations. lia. }
  rewrite Ea in Hrdn. cbn [AS.PropExec.rdn] in Hrdn. rewrite Hb0 in Hrdn. injection Hrdn as <-. rewrite sbyte_val in Hval. symmetry in Hval.
  (* [comment removed for export] *)
  assert (Hmrg : forall e2, edenot E (merge_u (sr_get sr u) e2 j) =
                 if Z.eqb (bv_signed b0) 0 then edenot E (sr_get sr u) else edenot E e2).
  { intros e2. unfold merge_u. cbn [edenot]. rewrite Hval. rewrite merge_word, sbyte_zero. reflexivity. }
  assert (Hej : bv_signed (edenot E (EVar j)) = bv_signed b0) by (cbn [edenot]; rewrite Hval; apply sbyte_signed).
  assert (He1 : bv_signed (edenot E e1) = xv mod 8).
  { unfold e1, fk. rewrite (mkAluK_denot segs E base _ _ _ _ (facts_of_ok segs E base _ Hkn)). unfold alu64, alu. cbn [edenot].
    rewrite (zb_signed (bv_and _ _)), bv_and_unsigned, Z_to_bv_unsigned. change (bv_wrap 64 7) with (Z.ones 3).
    rewrite Z.land_ones by lia. change (2^3) with 8. fold xv.
    destruct (Z.ltb_spec (xv mod 8) (2^63)); Z.div_mod_to_equations; lia. }
  (* [comment removed for export] *)
  assert (BLT : forall (e2 : expr) (ss3 : sym_state) (regsX : bvmap 5 word),
            s_regs ss3 = sr_upd sr (ridx u) e2 -> s_log ss3 = s_log ss -> s_know ss3 = kn -> s_resv ss3 = None -> s_pc ss3 = bltpc ->
            bge_ok segs (Branch BC_GE u t imm) ss3 (bltpc + 4) = true ->
            bv_signed b0 <> 0 -> bv_signed (edenot E e2) = xv mod 8 + c ->
            regs_ok E (s_regs ss3) regsX -> rfull regsX ->
            (forall regs', regs_ok E (sr_upd sr (ridx u) (merge_u (sr_get sr u) e2 j)) regs' -> rfull regs' ->
                evtF segs RNG Q (MS regs' F (Z_to_bv 64 ok) fc None (mem_denot E base (s_log ss)) rom)) ->
            evtF segs RNG Q (MS regsX F (Z_to_bv 64 bltpc) fc None (mem_denot E base (s_log ss)) rom)).
  { intros e2 ss3 regsX S3r S3l S3k S3v S3p Hbo NZ He2 HrX HfuX KX.
    destruct (unpZ_slow base _ _ xv c b0 HU HA1 ltac:(lia) ltac:(lia) Hb0 NZ) as [Hlt Hle7].
    destruct (instr_at_inv _ _ Hib) as (w3 & Hf3 & He3 & Hd3). rewrite <- S3p in Hf3.
    assert (HlfX : log_flat E (s_log ss3)) by (rewrite S3l; exact Hlf).
    assert (HknX : know_ok segs E base (s_know ss3)) by (rewrite S3k; exact Hkn).
    assert (Hgu : sr_get (s_regs ss3) u = e2) by (rewrite S3r; apply sr_get_upd_same; exact Hu0).
    assert (Hgt : sr_get (s_regs ss3) t = EVar j) by (rewrite S3r, sr_get_upd_other by exact Hne_tu; exact Ht).
    assert (POST : forall regs3, regs_ok E (s_regs ss3) regs3 -> rfull regs3 ->
                     evtF segs RNG Q (MS regs3 F (Z_to_bv 64 ok) fc None (mem_denot E base (s_log ss)) rom)).
    { intros regs3 Hr3 Hfu3. apply KX; [|exact Hfu3]. rewrite S3r in Hr3. eapply regs_ok_ext; [exact Hr3|]. intros r Hr0.
      destruct (bv_eqb r u) eqn:Hru.
      - apply bv_eqb_true_eq in Hru. subst r. rewrite !sr_get_upd_same by exact Hu0. rewrite Hmrg. rewrite (proj2 (Z.eqb_neq _ _) NZ). reflexivity.
      - apply bv_eqb_false_ne in Hru. rewrite !sr_get_upd_other by exact Hru. reflexivity. }
    (* [comment removed for export] *)
    destruct (instr_at_inv _ _ HJi) as (wj & Hfj & Hejj & Hdj).
    assert (JMP : forall regs3, regs_ok E (s_regs ss3) regs3 -> rfull regs3 ->
                    evtF segs RNG Q (MS regs3 F (Z_to_bv 64 (bltpc + 4)) fc None (mem_denot E base (s_log ss)) rom)).
    { intros regs3 Hr3 Hfu3.
      destruct (kx_step_sound segs F fc E base rom RNG (sjump ss3 (bltpc + 4)) regs3 (Jal 0 imm0)
                  (sset (sjump ss3 (bltpc + 4)) 0 (ELit (bltpc + 4 + 4)) (j_target (bltpc + 4) imm0))
                  [] scr_nil scr_nil wj [] Hfj Hejj Hdj eq_refl eq_refl S3v S3v (Forall_nil _) (Forall_nil _) Hr3 Hfu3 HlfX HknX)
        as (regsj & Hstepj & Hrj & Hfuj & _).
      cbn [s_pc s_regs s_log sjump sset] in Hstepj, Hrj. rewrite ?S3l in Hstepj. rewrite HJok in Hstepj.
      eapply evtF_step; [exact Hstepj|]. exact (POST regsj Hrj Hfuj). }
    unfold bge_ok in Hbo.
    destruct (sym_step segs (Branch BC_GE u t imm) ss3 scr_nil) as [ss4 scs4 scr4|] eqn:Hs4.
    - (* [comment removed for export] *)
      destruct scs4 as [|? ?]; [|discriminate Hbo]. apply Z.eqb_eq in Hbo.
      destruct (sym_step_branch_shape _ _ _ _ _ _ _ _ _ Hs4) as [npc ->]. cbn [s_pc sjump] in Hbo. subst npc.
      destruct (kx_step_sound segs F fc E base rom RNG ss3 regsX _ _ _ _ _ w3 [] Hf3 He3 Hd3 Hs4 eq_refl S3v S3v (Forall_nil _) (Forall_nil _) HrX HfuX HlfX HknX)
        as (regs3 & Hstep3 & Hr3 & Hfu3 & _).
      cbn [s_pc s_log s_regs sjump] in Hstep3, Hr3. rewrite ?S3p, ?S3l in Hstep3.
      eapply evtF_step; [exact Hstep3|]. exact (JMP regs3 Hr3 Hfu3).
    - (* [comment removed for export] *)
      pose proof (sym_step_branch_scripted BC_GE u t imm ss3 false Hs4) as STEP4. rewrite Hgu, Hgt, S3p in STEP4.
      assert (SCS4 : scs_denot segs base E [SCBr false BC_GE e2 (EVar j)]).
      { constructor; [|constructor]. cbn [sc_denot branch_taken]. unfold bv_lts. rewrite He2, Hej.
        rewrite (proj2 (Z.ltb_lt _ _)) by lia. reflexivity. }
      destruct (kx_step_sound segs F fc E base rom RNG ss3 regsX _ _ _ _ _ w3 [] Hf3 He3 Hd3 STEP4 eq_refl S3v S3v SCS4 (Forall_nil _) HrX HfuX HlfX HknX)
        as (regs3 & Hstep3 & Hr3 & Hfu3 & _).
      cbn [s_pc s_log s_regs sjump] in Hstep3, Hr3. rewrite ?S3p, ?S3l in Hstep3.
      eapply evtF_step; [exact Hstep3|]. exact (JMP regs3 Hr3 Hfu3). }
  assert (SLOW : bv_signed b0 <> 0 -> forall regs1, regs_ok E sr regs1 -> rfull regs1 ->
            evtF segs RNG Q (MS regs1 F (Z_to_bv 64 slow) fc None (mem_denot E base (s_log ss)) rom)).
  { intros NZ regs1 Hr1 Hfu1.
    destruct (parse_slow_inv _ _ _ _ _ _ Hps) as (imm7 & Hia & H7 & Hcases).
    destruct (instr_at_inv _ _ Hia) as (w2 & Hf2 & He2 & Hd2).
    destruct (kx_step_sound segs F fc E base rom RNG (sjump ss slow) regs1 (OpImm ALU_AND u x' imm7)
                (sset (sjump ss slow) u (mkAluK fk ALU_AND ex (ELit (bv_signed imm7))) (slow + 4))
                [] scr_nil scr_nil w2 [] Hf2 He2 Hd2 eq_refl eq_refl Hc Hc (Forall_nil _) (Forall_nil _) Hr1 Hfu1 Hlf Hkn)
      as (regs2 & Hstep2 & Hr2 & Hfu2 & _).
    eapply evtF_step; [exact Hstep2|]. clear Hstep2. rewrite H7 in Hr2. fold e1 in Hr2.
    cbn [s_pc s_regs s_log s_know sjump sset] in Hr2 |- *. fold sr in Hr2. rewrite Hu0 in Hr2.
    destruct Hcases as [(-> & -> & ->) | (-> & -> & immc & Hiad & Hic)].
    - (* [comment removed for export] *)
      unfold sset, sjump in K, Hblt. cbn [s_pc s_regs s_log s_know s_next s_resv] in K, Hblt.
      fold sr in K. fold sr in Hblt. fold kn in K. fold kn in Hblt. fold fk in K. fold fk in Hblt. fold ex in K. fold ex in Hblt.
      fold e1 in K. fold e1 in Hblt. rewrite Hu0 in K, Hblt. rewrite sr_get_upd_same in K by exact Hu0.
      apply (BLT e1 (SSR (slow + 4) (sr_upd sr (ridx u) e1) (s_log ss) kn (s_next ss) (s_resv ss)) regs2);
        [reflexivity | reflexivity | reflexivity | exact Hc | reflexivity | exact Hblt | exact NZ | rewrite He1; lia | exact Hr2 | exact Hfu2 | exact K].
    - (* [comment removed for export] *)
      unfold sset, sjump in K, Hblt. cbn [s_pc s_regs s_log s_know s_next s_resv] in K, Hblt.
      fold sr in K. fold sr in Hblt. fold kn in K. fold kn in Hblt. fold fk in K. fold fk in Hblt. fold ex in K. fold ex in Hblt.
      fold e1 in K. fold e1 in Hblt. rewrite Hu0 in K, Hblt. rewrite !sr_get_upd_same in K, Hblt by exact Hu0.
      destruct (instr_at_inv _ _ Hiad) as (w2b & Hf2b & He2b & Hd2b).
      set (ss2 := SSR (slow + 4) (sr_upd sr (ridx u) e1) (s_log ss) kn (s_next ss) (s_resv ss)) in *.
      destruct (kx_step_sound segs F fc E base rom RNG ss2 regs2 (OpImm ALU_ADD u u immc)
                  (sset ss2 u (mkAluK fk ALU_ADD (sr_get (s_regs ss2) u) (ELit (bv_signed immc))) (slow + 4 + 4))
                  [] scr_nil scr_nil w2b [] Hf2b He2b Hd2b eq_refl eq_refl Hc Hc (Forall_nil _) (Forall_nil _) Hr2 Hfu2 Hlf Hkn)
        as (regs2b & Hstep2b & Hr2b & Hfu2b & _).
      eapply evtF_step; [exact Hstep2b|]. clear Hstep2b. rewrite Hic in Hr2b.
      cbn [s_pc s_regs s_log s_know sjump sset ss2] in Hr2b |- *. rewrite Hu0 in Hr2b. rewrite sr_get_upd_same in Hr2b by exact Hu0.
      set (e2 := mkAluK fk ALU_ADD e1 (ELit c)) in *.
      replace (slow + 4 + 4) with (slow + 8) by lia.
      rewrite ?sr_get_upd_same in K by exact Hu0. fold e2 in K.
      apply (BLT e2 (SSR (slow + 8) (sr_upd (sr_upd sr (ridx u) e1) (ridx u) e2) (s_log ss) kn (s_next ss) (s_resv ss)) regs2b);
        [ | reflexivity | reflexivity | exact Hc | reflexivity | exact Hblt | exact NZ | | exact Hr2b | exact Hfu2b | exact K].
      + assert (UU : forall n0 l (a1 b1 : expr), sr_upd (sr_upd l n0 a1) n0 b1 = sr_upd l n0 b1).
        { clear. induction n0 as [|n0 IH]; intros [|h tl] a1 b1; cbn; try reflexivity; rewrite IH; reflexivity. }
        apply UU.
      + unfold e2, fk. rewrite (mkAluK_denot segs E base _ _ _ _ (facts_of_ok segs E base _ Hkn)). fold fk. unfold alu64, alu.
        cbn [edenot].
        assert (Hu1 : bv_unsigned (edenot E e1) = xv mod 8).
        { rewrite <- He1. rewrite (zb_signed (edenot E e1)).
          pose proof (bv_unsigned_in_range _ (edenot E e1)) as R1. unfold bv_modulus in R1. change (2 ^ Z.of_N 64) with (2^64) in R1.
          rewrite (zb_signed (edenot E e1)) in He1.
          destruct (Z.ltb_spec (bv_unsigned (edenot E e1)) (2^63)); [reflexivity|].
          exfalso. Z.div_mod_to_equations. lia. }
        rewrite (zb_signed (_ + _)), bv_add_unsigned, Z_to_bv_unsigned, Hu1. unfold bv_wrap, bv_modulus.
        change (2 ^ Z.of_N 64) with 18446744073709551616. change (2^63) with 9223372036854775808.
        rewrite (Z.mod_small c) by lia. rewrite Z.mod_small by (Z.div_mod_to_equations; lia).
        destruct (Z.ltb_spec (xv mod 8 + c) 9223372036854775808); Z.div_mod_to_equations; lia. }
  (* [comment removed for export] *)
  assert (FAST : bv_signed b0 = 0 -> forall regs1, regs_ok E sr regs1 ->
            regs_ok E (sr_upd sr (ridx u) (merge_u (sr_get sr u) (sr_get (s_regs
              (if hasaddi
               then sset (sset (sjump ss slow) u e1 (slow + 4)) u
                      (mkAluK fk ALU_ADD (sr_get (s_regs (sset (sjump ss slow) u e1 (slow + 4))) u) (ELit c)) (slow + 8)
               else sset (sjump ss slow) u e1 (slow + 4))) u) j)) regs1).
  { intros Z0 regs1 Hr1. eapply regs_ok_ext; [exact Hr1|]. intros r Hr0.
    destruct (bv_eqb r u) eqn:Hru.
    - apply bv_eqb_true_eq in Hru. subst r. rewrite sr_get_upd_same by exact Hu0. rewrite Hmrg, Z0. reflexivity.
    - apply bv_eqb_false_ne in Hru. rewrite sr_get_upd_other by exact Hru. reflexivity. }
  destruct (chk_site_inv _ _ _ _ _ _ Hsite) as [(-> & -> & immB & -> & ->) | [(-> & immB & immj & -> & -> & Hjal & ->) | (-> & -> & immB & -> & ->)]].
  - (* [comment removed for export] *)
    pose proof (sym_step_branch_scripted BC_NE t 0 immB ss (negb (Z.eqb (bv_signed b0) 0)) Hstop) as STEP.
    fold sr in STEP. rewrite Ht, sr_get_x0 in STEP.
    assert (SCS : scs_denot segs base E [SCBr (negb (Z.eqb (bv_signed b0) 0)) BC_NE (EVar j) (ELit 0)]).
    { constructor; [|constructor]. cbn [sc_denot edenot branch_taken]. rewrite Hval, sbyte_zero. reflexivity. }
    destruct (kx_step_sound segs F fc E base rom RNG ss regs _ _ _ _ _ w [] Hf He Hd STEP eq_refl Hc Hc SCS (Forall_nil _) Hr Hfu Hlf Hkn)
      as (regs1 & Hstep1 & Hr1 & Hfu1 & _).
    eapply evtF_step; [exact Hstep1|]. clear Hstep1. cbn [s_pc s_regs s_log sjump] in Hr1 |- *. fold sr in Hr1.
    destruct (Z.eqb_spec (bv_signed b0) 0) as [Z0|NZ]; cbn [negb].
    + apply K; [exact (FAST Z0 regs1 Hr1) | exact Hfu1].
    + exact (SLOW NZ regs1 Hr1 Hfu1).
  - (* [comment removed for export] *)
    pose proof (sym_step_branch_scripted BC_EQ t 0 immB ss (Z.eqb (bv_signed b0) 0) Hstop) as STEP.
    fold sr in STEP. rewrite Ht, sr_get_x0 in STEP.
    assert (SCS : scs_denot segs base E [SCBr (Z.eqb (bv_signed b0) 0) BC_EQ (EVar j) (ELit 0)]).
    { constructor; [|constructor]. cbn [sc_denot edenot branch_taken]. rewrite Hval, sbyte_zero. reflexivity. }
    destruct (kx_step_sound segs F fc E base rom RNG ss regs _ _ _ _ _ w [] Hf He Hd STEP eq_refl Hc Hc SCS (Forall_nil _) Hr Hfu Hlf Hkn)
      as (regs1 & Hstep1 & Hr1 & Hfu1 & _).
    eapply evtF_step; [exact Hstep1|]. clear Hstep1. cbn [s_pc s_regs s_log sjump] in Hr1 |- *. fold sr in Hr1.
    destruct (Z.eqb_spec (bv_signed b0) 0) as [Z0|NZ].
    + apply K; [exact (FAST Z0 regs1 Hr1) | exact Hfu1].
    + (* [comment removed for export] *)
      destruct (instr_at_inv _ _ Hjal) as (wj & Hfj & Hej2 & Hdj).
      destruct (kx_step_sound segs F fc E base rom RNG (sjump ss (s_pc ss + 4)) regs1 (Jal 0 immj)
                  (sset (sjump ss (s_pc ss + 4)) 0 (ELit (s_pc ss + 4 + 4)) (j_target (s_pc ss + 4) immj))
                  [] scr_nil scr_nil wj [] Hfj Hej2 Hdj eq_refl eq_refl Hc Hc (Forall_nil _) (Forall_nil _) Hr1 Hfu1 Hlf Hkn)
        as (regsj & Hstepj & Hrj & Hfuj & _).
      eapply evtF_step; [exact Hstepj|]. clear Hstepj. cbn [s_pc s_regs s_log sjump sset] in Hrj |- *.
      exact (SLOW NZ regsj Hrj Hfuj).
  - (* [comment removed for export] *)
    pose proof (sym_step_branch_scripted BC_EQ t 0 immB ss (Z.eqb (bv_signed b0) 0) Hstop) as STEP.
    fold sr in STEP. rewrite Ht, sr_get_x0 in STEP.
    assert (SCS : scs_denot segs base E [SCBr (Z.eqb (bv_signed b0) 0) BC_EQ (EVar j) (ELit 0)]).
    { constructor; [|constructor]. cbn [sc_denot edenot branch_taken]. rewrite Hval, sbyte_zero. reflexivity. }
    destruct (kx_step_sound segs F fc E base rom RNG ss regs _ _ _ _ _ w [] Hf He Hd STEP eq_refl Hc Hc SCS (Forall_nil _) Hr Hfu Hlf Hkn)
      as (regs1 & Hstep1 & Hr1 & Hfu1 & _).
    eapply evtF_step; [exact Hstep1|]. clear Hstep1. cbn [s_pc s_regs s_log sjump] in Hr1 |- *. fold sr in Hr1.
    destruct (Z.eqb_spec (bv_signed b0) 0) as [Z0|NZ].
    + apply K; [exact (FAST Z0 regs1 Hr1) | exact Hfu1].
    + exact (SLOW NZ regs1 Hr1 Hfu1).
Qed.
Lemma chk_siteZ_inv : forall p i t neg ok, chk_siteZ p i = Some (t, neg, ok) ->
  (neg = false /\ ok = p + 4 /\ exists imm, i = Branch BC_NE t 0 imm) \/
  (neg = true /\ exists imm, i = Branch BC_EQ t 0 imm /\ ok = br_target p imm).
Proof.
  intros p i t neg ok H. unfold chk_siteZ in H. destruct i; try discriminate H. destruct c; try discriminate H.
  - destruct (bv_eqb rs2 0) eqn:Hz; [|discriminate H]. injection H as <- <- <-. apply bv_eqb_true_eq in Hz. subst rs2.
    right. split; [reflexivity|]. exists imm. split; reflexivity.
  - destruct (bv_eqb rs2 0) eqn:Hz; [|discriminate H]. injection H as <- <- <-. apply bv_eqb_true_eq in Hz. subst rs2.
    left. split; [reflexivity|]. split; [reflexivity|]. exists imm. reflexivity.
Qed.

Lemma byte_zero_val : forall (b : byte) sx, bv_signed b = 0 -> Z_to_bv 64 (extz sx 1 (bytes_le_to_Z [b])) = Z_to_bv 64 0.
Proof.
  intros b sx Hs.
  assert (Hu : bv_unsigned b = 0).
  { pose proof (bv_signed_in_range _ b ltac:(discriminate)) as R. unfold bv_half_modulus, bv_modulus in R.
    change (2 ^ Z.of_N 8 / 2) with 128 in R.
    pose proof (bv_unsigned_in_range _ b) as Ru. unfold bv_modulus in Ru. change (2 ^ Z.of_N 8) with 256 in Ru.
    unfold bv_signed, bv_swrap in Hs. unfold bv_wrap, bv_half_modulus, bv_modulus in Hs.
    change (2 ^ Z.of_N 8) with 256 in Hs. change (256 / 2) with 128 in Hs. Z.div_mod_to_equations. lia. }
  unfold extz. cbn [bytes_le_to_Z]. change (0 ≪ 8) with 0. rewrite Z.lor_0_r, Hu. destruct sx; reflexivity.
Qed.

Lemma asan_chkZ_sound : forall ss acc i ss' ci w regs,
  fetch_word segs (Z_to_bv 64 (s_pc ss)) = Some w -> is_ecall w = false -> decode_any w = Some (i, 4) ->
  sym_step segs i ss scr_nil = SStop ->
  asan_chkZ segs akn ss acc i = Some (ss', ci) ->
  s_resv ss = None ->
  scs_denot segs base E acc ->
  regs_ok E (s_regs ss) regs -> rfull regs -> log_flat E (s_log ss) -> know_ok segs E base (s_know ss) ->
  (forall regs', regs_ok E (s_regs ss') regs' -> rfull regs' ->
      evtF segs RNG Q (MS regs' F (Z_to_bv 64 (s_pc ss')) fc None (mem_denot E base (s_log ss)) rom)) ->
  evtF segs RNG Q (MS regs F (Z_to_bv 64 (s_pc ss)) fc None (mem_denot E base (s_log ss)) rom).
Proof.
  intros ss acc i ss' ci w regs Hf He Hd Hstop H Hc Hacc Hr Hfu Hlf Hkn K.
  unfold asan_chkZ in H.
  destruct (chk_siteZ (s_pc ss) i) as [[[t neg] ok]|] eqn:Hsite; [|discriminate H].
  destruct (bv_eqb t 0) eqn:Ht0; [discriminate H|].
  destruct (sr_get (s_regs ss) t) as [|j| | | | | |] eqn:Ht; try discriminate H.
  destruct (find_rb j acc) as [[[a [|[|n]]] sx]|] eqn:Hrb; try discriminate H.
  lazymatch type of H with match ?fd with _ => _ end = _ => destruct fd as [ex|] eqn:Hfind; [|discriminate H] end.
  injection H as <- <-. cbn [s_pc s_regs s_log] in K.
  apply find_some in Hfind as [_ Hcond]. apply andb_prop in Hcond as [Hcond Hcov]. apply andb_prop in Hcond as [Hsha Hal].
  apply Z.leb_le in Hal.
  set (kn := s_know ss) in *. set (fk := facts_of kn) in *. set (sr := s_regs ss) in *.
  (* [comment removed for export] *)
  pose proof (find_rb_In _ _ _ _ _ Hrb) as Hin.
  unfold scs_denot in Hacc. rewrite Forall_forall in Hacc. pose proof (Hacc _ Hin) as Hrd. cbn [sc_denot edenot] in Hrd.
  destruct Hrd as (bs & Hrdn & Hval).
  (* [comment removed for export] *)
  pose proof (shmatch_u kn ex a Hkn Hsha) as Hsh.
  set (xv := bv_unsigned (edenot E ex)) in *.
  (* [comment removed for export] *)
  destruct (unp_cover_sound kn ex 8 Hkn Hcov ltac:(lia)) as (A & n & HinA & HA1 & HA2). fold xv in HA1, HA2.
  assert (HAok : aent_ok RNG E base (AUnp A n)) by (unfold aknow_ok in HAK; rewrite Forall_forall in HAK; exact (HAK _ HinA)).
  cbn [aent_ok] in HAok. destruct HAok as [HU HRNG].
  pose proof (ealign_sound segs E base kn ex Hkn) as [Hea1 Hea2]. fold xv in Hea2.
  assert (Hx8 : xv mod 8 = 0).
  { destruct Hea2 as [q Hq]. rewrite Hq. apply Z.mod_divide; [lia|]. exists (q * 2 ^ (ealign kn ex - 3)).
    replace (2 ^ ealign kn ex) with (2 ^ (ealign kn ex - 3) * 2 ^ 3) by (rewrite <- Z.pow_add_r by lia; f_equal; lia). change (2^3) with 8. lia. }
  (* [comment removed for export] *)
  destruct (unpZ_byte base _ _ xv HU HA1 ltac:(lia)) as (b0 & Hb0 & Hgran).
  assert (Hz : bv_signed b0 = 0).
  { destruct Hgran as [Hg|Hg]; [exact Hg|]. exfalso. Z.div_mod_to_equations. lia. }
  assert (Ea : adenot E a = Z_to_bv 64 (KXSHLO + xv / 8)).
  { apply bv_eq. rewrite Hsh, Z_to_bv_unsigned. symmetry. apply bv_wrap_small.
    unfold bv_modulus, KXSHLO. change (2 ^ Z.of_N 64) with 18446744073709551616.
    pose proof (bv_unsigned_in_range _ (edenot E ex)) as R. unfold bv_modulus in R. change (2 ^ Z.of_N 64) with 18446744073709551616 in R.
    subst xv. Z.div_mod_to_equations. lia. }
  rewrite Ea in Hrdn. cbn [AS.PropExec.rdn] in Hrdn. rewrite Hb0 in Hrdn. injection Hrdn as <-.
  rewrite (byte_zero_val b0 sx Hz) in Hval. symmetry in Hval.
  (* [comment removed for export] *)
  assert (POST : forall regs1, regs_ok E sr regs1 -> regs_ok E (sr_upd sr (ridx t) (ELit 0)) regs1).
  { intros regs1 Hr1. eapply regs_ok_ext; [exact Hr1|]. intros r Hr0. destruct (bv_eqb r t) eqn:Hrt.
    - apply bv_eqb_true_eq in Hrt. subst r. rewrite sr_get_upd_same by exact Ht0. rewrite Ht. cbn [edenot]. rewrite Hval. reflexivity.
    - apply bv_eqb_false_ne in Hrt. rewrite sr_get_upd_other by exact Hrt. reflexivity. }
  destruct (chk_siteZ_inv _ _ _ _ _ Hsite) as [(-> & -> & immB & ->) | (-> & immB & -> & ->)].
  - pose proof (sym_step_branch_scripted BC_NE t 0 immB ss false Hstop) as STEP. fold sr in STEP. rewrite Ht, sr_get_x0 in STEP.
    assert (SCS : scs_denot segs base E [SCBr false BC_NE (EVar j) (ELit 0)]).
    { constructor; [|constructor]. cbn [sc_denot edenot branch_taken]. rewrite Hval. reflexivity. }
    destruct (kx_step_sound segs F fc E base rom RNG ss regs _ _ _ _ _ w [] Hf He Hd STEP eq_refl Hc Hc SCS (Forall_nil _) Hr Hfu Hlf Hkn)
      as (regs1 & Hstep1 & Hr1 & Hfu1 & _).
    eapply evtF_step; [exact Hstep1|]. cbn [s_pc s_regs s_log sjump] in Hr1 |- *. exact (K regs1 (POST regs1 Hr1) Hfu1).
  - pose proof (sym_step_branch_scripted BC_EQ t 0 immB ss true Hstop) as STEP. fold sr in STEP. rewrite Ht, sr_get_x0 in STEP.
    assert (SCS : scs_denot segs base E [SCBr true BC_EQ (EVar j) (ELit 0)]).
    { constructor; [|constructor]. cbn [sc_denot edenot branch_taken]. rewrite Hval. reflexivity. }
    destruct (kx_step_sound segs F fc E base rom RNG ss regs _ _ _ _ _ w [] Hf He Hd STEP eq_refl Hc Hc SCS (Forall_nil _) Hr Hfu Hlf Hkn)
      as (regs1 & Hstep1 & Hr1 & Hfu1 & _).
    eapply evtF_step; [exact Hstep1|]. cbn [s_pc s_regs s_log sjump] in Hr1 |- *. exact (K regs1 (POST regs1 Hr1) Hfu1).
Qed.

Lemma asan_chk_sound : forall ss acc i ss' ci w regs,
  fetch_word segs (Z_to_bv 64 (s_pc ss)) = Some w -> is_ecall w = false -> decode_any w = Some (i, 4) ->
  sym_step segs i ss scr_nil = SStop ->
  asan_chk segs akn ss acc i = Some (ss', ci) ->
  s_resv ss = None ->
  scs_denot segs base E acc ->
  regs_ok E (s_regs ss) regs -> rfull regs -> log_flat E (s_log ss) -> know_ok segs E base (s_know ss) ->
  (forall regs', regs_ok E (s_regs ss') regs' -> rfull regs' ->
      evtF segs RNG Q (MS regs' F (Z_to_bv 64 (s_pc ss')) fc None (mem_denot E base (s_log ss)) rom)) ->
  evtF segs RNG Q (MS regs F (Z_to_bv 64 (s_pc ss)) fc None (mem_denot E base (s_log ss)) rom).
Proof.
  intros ss acc i ss' ci w regs Hf He Hd Hstop H. unfold asan_chk in H.
  destruct (asan_chkA segs akn ss acc i) as [[s1 c1]|] eqn:HA.
  - injection H as <- <-. exact (asan_chkA_sound ss acc i s1 c1 w regs Hf He Hd Hstop HA).
  - destruct (asan_chkG segs akn ss acc i) as [[s2 c2]|] eqn:HG.
    + injection H as <- <-. exact (asan_chkG_sound ss acc i s2 c2 w regs Hf He Hd Hstop HG).
    + exact (asan_chkZ_sound ss acc i ss' ci w regs Hf He Hd Hstop H).
Qed.

End ChkSound.
End SoundA.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section TreeSoundA.
Variable segs : list Segment.
Variable vmax : Z.
Variable akn : list aent.
Variables (F : bvmap 5 word) (fc : bv 32).
Variable E : env.
Variable base rom : word -> option byte.
Variable RNG : footprint.
Variable MI0 : Prop.
Variable Q : machine_state -> Prop.
Hypothesis HAK : aknow_ok RNG E base akn.

Fixpoint kt_oblA (t : ktreeA) : Prop :=
  match t with
  | KALeaf ss scs accs => PO segs E base RNG scs accs /\ PC segs F fc E base rom RNG MI0 Q ss
  | KAFork c a b scs accs t1 t2 =>
      PO segs E base RNG scs accs /\
      (branch_taken c (edenot E a) (edenot E b) = true -> kt_oblA t1) /\
      (branch_taken c (edenot E a) (edenot E b) = false -> kt_oblA t2)
  | KASplit x v scs accs t1 t2 =>
      PO segs E base RNG scs accs /\
      (branch_taken BC_EQ (edenot E x) (edenot E (ELit v)) = true -> kt_oblA t1) /\
      (branch_taken BC_EQ (edenot E x) (edenot E (ELit v)) = false -> kt_oblA t2)
  | KAChk ss ci t1 => kt_oblA t1
  end.

(* [comment removed for export] *)
Lemma kx_treeA_acc : forall fuel first stops scalls ss acc accs pacc,
  kt_oblA (kx_treeA segs vmax akn fuel first stops scalls ss acc accs pacc) -> PO segs E base RNG acc accs.
Proof.
  induction fuel as [|f IH]; intros first stops scalls ss acc accs pacc H; cbn [kx_treeA] in H.
  - exact (proj1 H).
  - destruct (negb first && existsb (Z.eqb (s_pc ss)) stops)%bool; [exact (proj1 H)|].
    destruct (fetch_word segs (Z_to_bv 64 (s_pc ss))) as [w|]; [|exact (proj1 H)].
    destruct (is_ecall w); [exact (proj1 H)|].
    destruct (decode_any w) as [[i sz]|]; [|exact (proj1 H)].
    destruct (negb (Z.eqb sz 4)); [exact (proj1 H)|].
    lazymatch type of H with kt_oblA (match ?mc with _ => _ end) => destruct mc as [[ss1 ci]|] end.
    { cbn [kt_oblA] in H. exact (IH _ _ _ _ _ _ _ H). }
    destruct (split_hint vmax i ss) as [[x v]|]; [exact (proj1 H)|].
    destruct (acc_sym (facts_of (s_know ss)) i ss) as [la|]; [|exact (proj1 H)].
    destruct (sym_step segs i ss scr_nil) as [ss' scs scr'|].
    + destruct (s_clean ss'); [|exact (proj1 H)].
      assert (X : PO segs E base RNG (sc_add scs acc) (la ++ accs)).
      { destruct (scalls && is_call i)%bool; [exact (proj1 H) | exact (IH _ _ _ _ _ _ _ H)]. }
      destruct X as [X1 X2]. split; [exact (proj2 (sc_add_denot segs base E scs acc X1)) | exact (proj2 (proj1 (Forall_app _ _ _) X2))].
    + destruct (sym_step segs i ss (SCR [true] [] [])) as [sst scst ?|]; [|exact (proj1 H)].
      destruct (sym_step segs i ss (SCR [false] [] [])) as [ssf scsf ?|]; [|exact (proj1 H)].
      destruct (sc_is_br true scst) as [[[c a] b]|]; [|exact (proj1 H)].
      destruct (sc_is_br false scsf) as [[[c' a'] b']|]; [|exact (proj1 H)].
      destruct (bc_eqb c c' && expr_eqb a a' && expr_eqb b b' && s_clean sst && s_clean ssf)%bool; [|exact (proj1 H)].
      cbn [kt_oblA] in H. destruct H as [[X1 X2] _]. split; [exact X1 | exact (proj2 (proj1 (Forall_app _ _ _) X2))].
Qed.

Lemma kx_treeA_sound : forall fuel first stops scalls ss acc accs pacc,
  s_resv ss = None ->
  kt_oblA (kx_treeA segs vmax akn fuel first stops scalls ss acc accs pacc) ->
  scs_denot segs base E pacc ->
  forall regs, regs_ok E (s_regs ss) regs -> rfull regs -> log_flat E (s_log ss) -> know_ok segs E base (s_know ss) ->
  (MI0 -> mem_inv segs (mem_denot E base (s_log ss))) ->
  evtF segs RNG Q (MS regs F (Z_to_bv 64 (s_pc ss)) fc None (mem_denot E base (s_log ss)) rom).
Proof.
  induction fuel as [|f IH]; intros first stops scalls ss acc accs pacc Hc H Hpa regs Hr Hfu Hlf Hkn Hmi; cbn [kx_treeA] in H.
  - destruct H as (_ & K). exact (K regs Hr Hfu Hlf Hmi).
  - assert (Hleaf : kt_oblA (KALeaf ss acc accs) ->
              evtF segs RNG Q (MS regs F (Z_to_bv 64 (s_pc ss)) fc None (mem_denot E base (s_log ss)) rom)).
    { intros (_ & K). exact (K regs Hr Hfu Hlf Hmi). }
    destruct (negb first && existsb (Z.eqb (s_pc ss)) stops)%bool; [exact (Hleaf H)|].
    destruct (fetch_word segs (Z_to_bv 64 (s_pc ss))) as [w|] eqn:Hf; [|exact (Hleaf H)].
    destruct (is_ecall w) eqn:He; [exact (Hleaf H)|].
    destruct (decode_any w) as [[i sz]|] eqn:Hd; [|exact (Hleaf H)].
    destruct (Z.eqb sz 4) eqn:Hsz; cbn [negb] in H; [|exact (Hleaf H)].
    apply Z.eqb_eq in Hsz. subst sz.
    (* [comment removed for export] *)
    lazymatch type of H with kt_oblA (match ?mc with _ => _ end) => destruct mc as [[ss1 ci]|] eqn:Hchk end.
    { destruct (sym_step segs i ss scr_nil) as [? ? ?|] eqn:Hstop; [discriminate Hchk|].
      cbn [kt_oblA] in H.
      pose proof (asan_chk_shape segs akn _ _ _ _ _ Hchk) as (Sl & Sk & Sn & Sv).
      refine (asan_chk_sound segs F fc E base rom RNG Q akn HAK ss pacc i ss1 ci w regs Hf He Hd Hstop Hchk Hc Hpa Hr Hfu Hlf Hkn _).
      intros regs' Hr' Hfu'. rewrite <- Sl.
      apply (IH false stops scalls ss1 acc accs pacc); [rewrite Sv; exact Hc | exact H | exact Hpa | exact Hr' | exact Hfu' | rewrite Sl; exact Hlf | rewrite Sk; exact Hkn | rewrite Sl; exact Hmi]. }
    destruct (split_hint vmax i ss) as [[x v]|] eqn:Hsp.
    { (* [comment removed for export] *)
      pose proof (split_hint_range vmax i ss x v Hsp) as Hv.
      cbn [kt_oblA] in H. destruct H as (_ & HT1 & HT2).
      destruct (branch_taken BC_EQ (edenot E x) (edenot E (ELit v))) eqn:C.
      - refine (IH _ _ _ (kt_enter ss 0 (split_know (s_know ss) true x v)) _ _ _ Hc (HT1 eq_refl) Hpa regs Hr Hfu Hlf _ Hmi).
        cbn [kt_enter s_know]. exact (kn_enter_ok segs E base _ _ Hkn (split_know_ok segs E base _ true x v Hkn Hv (split_eqb E x v true Hv C))).
      - refine (IH _ _ _ (kt_enter ss _ (split_know (s_know ss) false x v)) _ _ _ Hc (HT2 eq_refl) Hpa regs Hr Hfu Hlf _ Hmi).
        cbn [kt_enter s_know]. exact (kn_enter_ok segs E base _ _ Hkn (split_know_ok segs E base _ false x v Hkn Hv (split_eqb E x v false Hv C))). }
    destruct (acc_sym (facts_of (s_know ss)) i ss) as [la|] eqn:Ha; [|exact (Hleaf H)].
    destruct (sym_step segs i ss scr_nil) as [ss' scs scr'|] eqn:Hs.
    + destruct (s_clean ss') eqn:Hcl; [|exact (Hleaf H)]. apply s_clean_None in Hcl.
      assert (X : PO segs E base RNG (sc_add scs acc) (la ++ accs)).
      { destruct (scalls && is_call i)%bool; [exact (proj1 H) | exact (kx_treeA_acc _ _ _ _ _ _ _ _ H)]. }
      destruct X as [X1 X2].
      pose proof (proj1 (sc_add_denot segs base E scs acc X1)) as Hscs.
      pose proof (proj1 (proj1 (Forall_app _ _ _) X2)) as Hla.
      destruct (kx_step_sound segs F fc E base rom RNG ss regs i ss' scs scr_nil scr' w la Hf He Hd Hs Ha Hc Hcl Hscs Hla Hr Hfu Hlf Hkn)
        as (regs1 & Hstep & Hr1 & Hfu1 & Hlf1 & Hkn1 & Hmi1).
      eapply evtF_step; [exact Hstep|].
      destruct (scalls && is_call i)%bool.
      * destruct H as (_ & K). exact (K regs1 Hr1 Hfu1 Hlf1 (fun X => Hmi1 (Hmi X))).
      * exact (IH _ _ _ _ _ _ _ Hcl H (proj2 (Forall_app _ _ _) (conj Hscs Hpa)) regs1 Hr1 Hfu1 Hlf1 Hkn1 (fun X => Hmi1 (Hmi X))).
    + destruct (sym_step segs i ss (SCR [true] [] [])) as [sst scst scrt|] eqn:Hst; [|exact (Hleaf H)].
      destruct (sym_step segs i ss (SCR [false] [] [])) as [ssf scsf scrf|] eqn:Hsf; [|exact (Hleaf H)].
      destruct (sc_is_br true scst) as [[[c a] b]|] eqn:Bt; [|exact (Hleaf H)].
      destruct (sc_is_br false scsf) as [[[c' a'] b']|] eqn:Bf; [|exact (Hleaf H)].
      destruct (bc_eqb c c' && expr_eqb a a' && expr_eqb b b' && s_clean sst && s_clean ssf)%bool eqn:Hchk2; [|exact (Hleaf H)].
      repeat (apply andb_prop in Hchk2 as [Hchk2 ?]).
      apply bc_eqb_eq in Hchk2. subst c'.
      repeat match goal with X : expr_eqb _ _ = true |- _ => apply expr_eqb_eq in X end. subst a' b'.
      repeat match goal with X : s_clean _ = true |- _ => apply s_clean_None in X end.
      apply sc_is_br_some in Bt, Bf. subst scst scsf.
      cbn [kt_oblA] in H. destruct H as ([_ X2] & HT1 & HT2).
      pose proof (proj1 (proj1 (Forall_app _ _ _) X2)) as Hla.
      destruct (branch_taken c (edenot E a) (edenot E b)) eqn:C.
      * specialize (HT1 eq_refl).
        assert (Hscs : scs_denot segs base E [SCBr true c a b]) by (constructor; [exact C | constructor]).
        destruct (kx_step_sound segs F fc E base rom RNG ss regs i sst _ _ scrt w la Hf He Hd Hst Ha Hc ltac:(assumption) Hscs Hla Hr Hfu Hlf Hkn)
          as (regs1 & Hstep & Hr1 & Hfu1 & Hlf1 & Hkn1 & Hmi1).
        eapply evtF_step; [exact Hstep|].
        refine (IH _ _ _ (kt_enter sst 0 (br_know (s_know ss) true c a b)) _ _ _ _ HT1 (proj2 (Forall_app _ _ _) (conj Hscs Hpa)) regs1 Hr1 Hfu1 Hlf1 _ (fun X => Hmi1 (Hmi X))); [assumption|].
        cbn [kt_enter s_know]. exact (kn_enter_ok segs E base _ _ Hkn1 (br_know_ok segs E base (s_know ss) true c a b Hkn C)).
      * specialize (HT2 eq_refl).
        assert (Hscs : scs_denot segs base E [SCBr false c a b]) by (constructor; [exact C | constructor]).
        destruct (kx_step_sound segs F fc E base rom RNG ss regs i ssf _ _ scrf w la Hf He Hd Hsf Ha Hc ltac:(assumption) Hscs Hla Hr Hfu Hlf Hkn)
          as (regs1 & Hstep & Hr1 & Hfu1 & Hlf1 & Hkn1 & Hmi1).
        eapply evtF_step; [exact Hstep|].
        refine (IH _ _ _ (kt_enter ssf _ (br_know (s_know ss) false c a b)) _ _ _ _ HT2 (proj2 (Forall_app _ _ _) (conj Hscs Hpa)) regs1 Hr1 Hfu1 Hlf1 _ (fun X => Hmi1 (Hmi X))); [assumption|].
        cbn [kt_enter s_know]. exact (kn_enter_ok segs E base _ _ Hkn1 (br_know_ok segs E base (s_know ss) false c a b Hkn C)).
Qed.

End TreeSoundA.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Fixpoint kta_scs (t : ktreeA) : list sidecond :=
  match t with
  | KALeaf _ scs _ => scs
  | KAFork _ _ _ scs _ t1 t2 => scs ++ kta_scs t1 ++ kta_scs t2
  | KASplit _ _ scs _ t1 t2 => scs ++ kta_scs t1 ++ kta_scs t2
  | KAChk _ _ t1 => kta_scs t1
  end.

Fixpoint kta_leaves (t : ktreeA) : nat :=
  match t with
  | KALeaf _ _ _ => 1%nat
  | KAFork _ _ _ _ _ t1 t2 => (kta_leaves t1 + kta_leaves t2)%nat
  | KASplit _ _ _ _ t1 t2 => (kta_leaves t1 + kta_leaves t2)%nat
  | KAChk _ _ t1 => kta_leaves t1
  end.
Fixpoint kta_checks (t : ktreeA) : nat :=
  match t with
  | KALeaf _ _ _ => 0%nat
  | KAFork _ _ _ _ _ t1 t2 => (kta_checks t1 + kta_checks t2)%nat
  | KASplit _ _ _ _ t1 t2 => (kta_checks t1 + kta_checks t2)%nat
  | KAChk _ _ t1 => S (kta_checks t1)
  end.

(* [comment removed for export] *)
Definition sc_dis (dis : list chkinfo) (sc : sidecond) : bool :=
  match sc with
  | SCReadBase a 1%nat _ (EVar j) => existsb (fun ci => Nat.eqb (ci_j ci) j && saddr_eqb (ci_a ci) a) dis
  | _ => false
  end.
Definition acc_dis (dis : list chkinfo) (an : saddr * nat) : bool :=
  Nat.eqb (snd an) 1 && existsb (fun ci => saddr_eqb (ci_a ci) (fst an)) dis.

(* [comment removed for export] *)
Definition inband (kn : list kentry) (a : saddr) (n : expr) : bool :=
  xinside kn (a_base a) (a_off a) n (ELit 0) KXSHLO (ELit (KXSHHI - KXSHLO)).
Definition appwin (akn : list aent) (kn : list kentry) (a : saddr) (n : expr) : bool :=
  existsb (fun K => match K with
                    | AApp A N => xinside kn (a_base a) (a_off a) n (a_base A) (a_off A) N
                    | AUnp _ _ => false
                    | AShp _ _ => false
                    end) akn.
Definition sc_app (akn : list aent) (kn : list kentry) (sc : sidecond) : bool :=
  match sc with
  | SCDisj a1 n1 a2 n2 => (inband kn a1 n1 && appwin akn kn a2 n2) || (inband kn a2 n2 && appwin akn kn a1 n1)
  | _ => false
  end.

Definition sc_restA (akn : list aent) (kn : list kentry) (rs : list zreg) (dis : list chkinfo) (scs : list sidecond) : list sidecond :=
  List.filter (fun sc => negb (sc_auto kn rs sc || sc_dis dis sc || sc_app akn kn sc)) scs.
Definition acc_restA (kn : list kentry) (ws : list zreg) (dis : list chkinfo) (accs : list (saddr * nat)) : list (saddr * nat) :=
  List.filter (fun an => negb (acc_auto kn ws an || acc_dis dis an)) accs.
Definition node_chkA (akn : list aent) (kn : list kentry) (rs ws : list zreg) (dis : list chkinfo)
                     (scs rest : list sidecond) (accs arest : list (saddr * nat)) : bool :=
  forallb (fun sc => sc_auto kn rs sc || sc_dis dis sc || sc_app akn kn sc || sc_memx sc rest) scs &&
  forallb (fun an => acc_auto kn ws an || acc_dis dis an || acc_mem an arest) accs.

(* [comment removed for export] *)
Definition ci_chk (akn : list aent) (kn : list kentry) (ci : chkinfo) : bool :=
  shmatch akn (facts_of kn) (ci_x ci) (ci_a ci) && unp_cover akn kn (ci_x ci) (ci_c ci + 1)
  && Z.leb 0 (ci_c ci) && Z.leb (ci_c ci) 7.

Fixpoint kta_resid (akn : list aent) (kn : list kentry) (rs ws : list zreg) (dis : list chkinfo) (t : ktreeA) : vtree :=
  match t with
  | KALeaf ss scs accs => VLeaf (s_pc ss) (s_regs ss) (s_log ss) (sc_restA akn kn rs dis scs) (acc_restA kn ws dis accs)
  | KAFork c a b scs accs t1 t2 =>
      VFork c a b (sc_restA akn kn rs dis scs) (acc_restA kn ws dis accs)
            (kta_resid akn (kn_enter kn (br_know kn true c a b)) rs ws [] t1) (kta_resid akn (kn_enter kn (br_know kn false c a b)) rs ws [] t2)
  | KASplit x v scs accs t1 t2 =>
      VFork BC_EQ x (ELit v) (sc_restA akn kn rs dis scs) (acc_restA kn ws dis accs)
            (kta_resid akn (kn_enter kn (split_know kn true x v)) rs ws [] t1) (kta_resid akn (kn_enter kn (split_know kn false x v)) rs ws [] t2)
  | KAChk ss ci t1 => kta_resid akn kn rs ws (ci :: dis) t1
  end.

Fixpoint kta_chk (akn : list aent) (kn : list kentry) (rs ws : list zreg) (dis : list chkinfo) (t : ktreeA) (p : vtree) : bool :=
  match t, p with
  | KALeaf ss scs accs, VLeaf pc sr log rest arest =>
      Z.eqb (s_pc ss) pc && list_eqb expr_eqb (s_regs ss) sr && list_eqb sentry_eqb (s_log ss) log &&
      node_chkA akn kn rs ws dis scs rest accs arest
  | KAFork c a b scs accs t1 t2, VFork c' a' b' rest arest p1 p2 =>
      bc_eqb c c' && expr_eqb a a' && expr_eqb b b' &&
      node_chkA akn kn rs ws dis scs rest accs arest &&
      kta_chk akn (kn_enter kn (br_know kn true c a b)) rs ws [] t1 p1 && kta_chk akn (kn_enter kn (br_know kn false c a b)) rs ws [] t2 p2
  | KASplit x v scs accs t1 t2, VFork c' a' b' rest arest p1 p2 =>
      bc_eqb BC_EQ c' && expr_eqb x a' && expr_eqb (ELit v) b' && Z.leb 0 v && Z.ltb v (2^64) &&
      node_chkA akn kn rs ws dis scs rest accs arest &&
      kta_chk akn (kn_enter kn (split_know kn true x v)) rs ws [] t1 p1 && kta_chk akn (kn_enter kn (split_know kn false x v)) rs ws [] t2 p2
  | KAChk ss ci t1, _ => ci_chk akn kn ci && kta_chk akn kn rs ws (ci :: dis) t1 p
  | _, _ => false
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Inductive zak : Type :=
| ZAUnp (a n : zexp)      (* [comment removed for export] *)
| ZAApp (a n : zexp)      (* [comment removed for export] *)
| ZAShp (s x : zexp).     (* [comment removed for export] *)

Definition zak_aent (k : zak) : aent :=
  match k with ZAUnp a n => AUnp (zsa a) (zx n) | ZAApp a n => AApp (zsa a) (zx n) | ZAShp a n => AShp (zsa a) (zx n) end.
Definition zak_wf (nz : nat) (k : zak) : bool :=
  match k with ZAUnp a n | ZAApp a n | ZAShp a n => zwf nz a && zwf nz n end.

Section ZAK.
Variable segs : list Segment.
Variable m : word -> option byte.
Variable RNG : footprint.
Definition zak_prop (zs : list Z) (k : zak) : Prop :=
  match k with
  | ZAUnp a n => zspan_ok zs a n /\ unpZ m (zden zs a) (zden zs a + zden zs n) /\
                 (0 < zden zs n -> rng RNG (KXSHLO + zden zs a / 8) (shspanZ (zden zs a) (zden zs n)))
  | ZAApp a n => zspan_ok zs a n /\ zden zs a + zden zs n <= KXKEND /\ (zden zs a + zden zs n <= KXSHLO \/ KXSHHI <= zden zs a)
  | ZAShp a n => zspan_ok zs a n /\ zden zs a = KXSHLO + zden zs n / 8
  end.

Lemma zak_ent : forall zs E k, atoms_ok zs E -> zak_wf (length zs) k = true -> zak_prop zs k -> aent_ok RNG E m (zak_aent k).
Proof.
  intros zs E k HA HW HP. destruct k as [a n|a n|a n]; cbn [zak_wf zak_prop zak_aent aent_ok] in *;
    apply andb_prop in HW as [W1 W2]; destruct HP as ((S1 & S2 & S3) & HP).
  - rewrite !(estart_zx zs E a HA W1 S1), !(elen_zx zs E n HA W2 S2). exact HP.
  - unfold flat. rewrite !(estart_zx zs E a HA W1 S1), !(elen_zx zs E n HA W2 S2). unfold KXKEND in *. lia.
  - rewrite !(estart_zx zs E a HA W1 S1), !(elen_zx zs E n HA W2 S2). exact HP.
Qed.

Lemma zaks_ent : forall zs E aks, atoms_ok zs E -> forallb (zak_wf (length zs)) aks = true -> Forall (zak_prop zs) aks ->
  aknow_ok RNG E m (map zak_aent aks).
Proof.
  intros zs E aks HA HW HP. unfold aknow_ok. apply Forall_map. rewrite forallb_forall in HW. rewrite Forall_forall in HP |- *.
  intros k Hk. exact (zak_ent zs E k HA (HW k Hk) (HP k Hk)).
Qed.
End ZAK.

Section TreeGoA.
Variable segs : list Segment.
Variables (F : bvmap 5 word) (fc : bv 32).

Section WithEA.
Variable akn : list aent.
Variable m rom : word -> option byte.
Variable RNG : footprint.
Variable Q : machine_state -> Prop.
Variables (zs : list Z) (rs ws : list zreg) (reads : list rdspec).
Variable E : env.
Hypothesis HA : atoms_ok zs E.
Hypothesis HRD : reads_ok segs m (length zs) reads E.
Hypothesis HWR : forallb (zreg_wf (length zs)) rs = true.
Hypothesis HWW : forallb (zreg_wf (length zs)) ws = true.
Hypothesis HRS : Forall (zreg_prop segs m zs) rs.
Hypothesis HWS : Forall (zwin_prop RNG zs) ws.
Hypothesis HAK : aknow_ok RNG E m akn.

Definition DISOK (dis : list chkinfo) : Prop := Forall (fun ci => rd_ok segs m E (ci_a ci) 1 /\ accP E RNG (ci_a ci, 1%nat)) dis.

Lemma ci_chk_sound : forall kn ci, know_ok segs E m kn -> ci_chk akn kn ci = true ->
  rd_ok segs m E (ci_a ci) 1 /\ accP E RNG (ci_a ci, 1%nat).
Proof.
  intros kn ci HK H. unfold ci_chk in H. apply andb_prop in H as [H Hc7]. apply andb_prop in H as [H Hc0]. apply andb_prop in H as [Hsha Hcov].
  apply Z.leb_le in Hc0. apply Z.leb_le in Hc7.
  pose proof (shmatch_u segs E m RNG akn HAK kn (ci_x ci) (ci_a ci) HK Hsha) as Hsh.
  set (xv := bv_unsigned (edenot E (ci_x ci))) in *.
  destruct (unp_cover_sound segs E m akn kn (ci_x ci) (ci_c ci + 1) HK Hcov ltac:(lia)) as (A & n & HinA & HA1 & HA2). fold xv in HA1, HA2.
  assert (HAok : aent_ok RNG E m (AUnp A n)) by (unfold aknow_ok in HAK; rewrite Forall_forall in HAK; exact (HAK _ HinA)).
  cbn [aent_ok] in HAok. destruct HAok as [HU HRNG].
  destruct (unpZ_byte m _ _ xv HU HA1 ltac:(lia)) as (b0 & Hb0 & _).
  assert (Ea : adenot E (ci_a ci) = Z_to_bv 64 (KXSHLO + xv / 8)).
  { apply bv_eq. rewrite Hsh, Z_to_bv_unsigned. symmetry. apply bv_wrap_small.
    unfold bv_modulus, KXSHLO. change (2 ^ Z.of_N 64) with 18446744073709551616.
    pose proof (bv_unsigned_in_range _ (edenot E (ci_x ci))) as R. unfold bv_modulus in R. change (2 ^ Z.of_N 64) with 18446744073709551616 in R.
    subst xv. Z.div_mod_to_equations. lia. }
  split.
  - unfold rd_ok. rewrite Ea, (rdn_one segs m _ b0 Hb0). discriminate.
  - unfold accP. cbn [fst snd]. rewrite Hsh. specialize (HRNG ltac:(lia)). destruct HRNG as (R0 & R1 & R). apply R; [lia|].
    unfold shspanZ. cbn [Z.of_nat]. Z.div_mod_to_equations. lia.
Qed.

Lemma sc_app_sound : forall kn sc, know_ok segs E m kn -> sc_app akn kn sc = true -> sc_resid segs m E sc.
Proof.
  intros kn sc HK H. destruct sc as [| | a1 n1 a2 n2 | | | |]; try discriminate H. cbn [sc_app] in H. cbn [sc_resid sc_denot].
  assert (IB : forall a n, inband kn a n = true -> KXSHLO <= estart E a /\ estart E a + elenZ E n <= KXSHHI).
  { intros a n Hi. unfold inband in Hi. pose proof (xinside_sound segs E m kn _ _ _ _ _ _ HK Hi) as [X1 X2].
    unfold estart in X1, X2 |- *. cbn [a_base a_off edenot] in X1, X2. unfold elenZ in X2 |- *. cbn [edenot] in X2.
    rewrite !Z_to_bv_unsigned in X1. rewrite !Z_to_bv_unsigned in X2. change (bv_wrap 64 0) with 0 in X1, X2.
    rewrite (bv_wrap_small 64 (KXSHHI - KXSHLO)) in X2 by (unfold bv_modulus, KXSHHI, KXSHLO; change (2 ^ Z.of_N 64) with (2^64); lia).
    destruct a as [ab ao]. cbn [a_base a_off] in *. lia. }
  assert (AW : forall a n, appwin akn kn a n = true ->
            0 <= estart E a /\ estart E a + elenZ E n <= KXKEND /\ (estart E a + elenZ E n <= KXSHLO \/ KXSHHI <= estart E a)).
  { intros a n Hw. unfold appwin in Hw. apply existsb_exists in Hw as (K & Hin & HK').
    destruct K as [A N|A N|A N]; [discriminate HK'| |discriminate HK'].
    pose proof (xinside_sound segs E m kn _ _ _ _ _ _ HK HK') as [X1 X2].
    assert (HAok : aent_ok RNG E m (AApp A N)) by (unfold aknow_ok in HAK; rewrite Forall_forall in HAK; exact (HAK _ Hin)).
    cbn [aent_ok] in HAok. destruct HAok as ((F0 & F1 & F2 & F3) & B1 & B2).
    unfold estart in *. cbn [a_base a_off] in X1, X2. destruct a as [ab ao]; destruct A as [Ab Ao]. cbn [a_base a_off] in *. lia. }
  pose proof (bv_unsigned_in_range _ (edenot E n1)) as Rn1. pose proof (bv_unsigned_in_range _ (edenot E n2)) as Rn2.
  unfold bv_modulus in Rn1, Rn2. change (2 ^ Z.of_N 64) with (2^64) in Rn1, Rn2. fold (elenZ E n1) in Rn1. fold (elenZ E n2) in Rn2.
  unfold flat, KXSHLO, KXSHHI, KXKEND in *.
  apply orb_prop in H as [H|H]; apply andb_prop in H as [H1 H2]; destruct (IB _ _ H1) as [I1 I2]; destruct (AW _ _ H2) as (W0 & W1 & W2); lia.
Qed.

Lemma node_chkA_sound : forall kn dis scs rest accs arest, know_ok segs E m kn -> DISOK dis ->
  forallb (sc_rd_chk (length zs) reads) scs = true ->
  node_chkA akn kn rs ws dis scs rest accs arest = true -> PO2 segs m RNG E rest arest -> PO segs E m RNG scs accs.
Proof.
  intros kn dis scs rest accs arest HK HD Hrd Hc [H1 H2]. unfold node_chkA in Hc. apply andb_prop in Hc as [Hc1 Hc2].
  unfold DISOK in HD. rewrite Forall_forall in HD. split.
  - unfold scs_denot. rewrite Forall_forall. rewrite Forall_forall in H1. rewrite forallb_forall in Hrd, Hc1. intros sc Hin.
    apply (kx_readbase segs m _ reads E sc HRD (Hrd sc Hin)).
    specialize (Hc1 sc Hin). apply orb_prop in Hc1 as [Hc1|Hm]; [apply orb_prop in Hc1 as [Hc1|Happ]; [apply orb_prop in Hc1 as [Hau|Hdis]|]|].
    + exact (sc_auto_sound segs m zs E kn rs sc HA HK HWR HRS Hau).
    + destruct sc as [| | | | | a n sx e |]; try discriminate Hdis. cbn [sc_dis] in Hdis.
      destruct n as [|[|n]]; try discriminate Hdis. destruct e; try discriminate Hdis.
      apply existsb_exists in Hdis as (ci & Hci & Heq). apply andb_prop in Heq as [_ Heq]. apply saddr_eqb_eq in Heq. subst a.
      cbn [sc_resid]. exact (proj1 (HD ci Hci)).
    + exact (sc_app_sound kn sc HK Happ).
    + exact (H1 sc (sc_memx_In _ _ Hm)).
  - rewrite Forall_forall. rewrite Forall_forall in H2. rewrite forallb_forall in Hc2. intros an Hin.
    specialize (Hc2 an Hin). apply orb_prop in Hc2 as [Hc2|Hm]; [apply orb_prop in Hc2 as [Hau|Hdis]|].
    + exact (acc_auto_sound segs m RNG zs E kn ws an HA HK HWW HWS Hau).
    + unfold acc_dis in Hdis. apply andb_prop in Hdis as [Hn Hdis]. apply Nat.eqb_eq in Hn.
      apply existsb_exists in Hdis as (ci & Hci & Heq). apply saddr_eqb_eq in Heq.
      destruct an as [a n]. cbn [fst snd] in Hn, Heq. subst n a. exact (proj2 (HD ci Hci)).
    + exact (H2 an (acc_mem_In _ _ Hm)).
Qed.
Lemma kta_chk_sound : forall t r kn dis, know_ok segs E m kn -> DISOK dis ->
  forallb (sc_rd_chk (length zs) reads) (kta_scs t) = true ->
  kta_chk akn kn rs ws dis t r = true -> kt_obl2 E (PO2 segs m RNG E) (PC2 segs F fc m rom RNG Q E) r ->
  kt_oblA segs F fc E m rom RNG (mem_inv segs m) Q t.
Proof.
  induction t as [ss scs accs | c a b scs accs t1 IH1 t2 IH2 | x v scs accs t1 IH1 t2 IH2 | ss ci t1 IH1]; intros r kn dis HK HD Hrd Hc H.
  - destruct r as [pc sr log rest arest | c' a' b' rest arest r1 r2]; cbn [kta_chk kt_obl2] in *; try discriminate Hc.
    repeat (apply andb_prop in Hc as [Hc ?]).
    apply Z.eqb_eq in Hc.
    match goal with X : list_eqb expr_eqb _ _ = true |- _ => apply (list_eqb_eq expr_eqb expr_eqb_eq) in X; rename X into Hsr end.
    match goal with X : list_eqb sentry_eqb _ _ = true |- _ => apply (list_eqb_eq sentry_eqb sentry_eqb_eq) in X; rename X into Hlog end.
    destruct H as (H' & K). cbn [kt_oblA kta_scs] in *. split.
    + exact (node_chkA_sound kn dis scs rest accs arest HK HD Hrd ltac:(assumption) H').
    + intros regs' Hr Hfu Hlf Hmi. rewrite (regs_ok_full_eq E _ regs' Hr Hfu). rewrite Hc, Hsr, Hlog in *. exact (K Hlf Hmi).
  - destruct r as [pc sr log rest arest | c' a' b' rest arest r1 r2]; cbn [kta_chk kt_obl2] in *; try discriminate Hc.
    repeat (apply andb_prop in Hc as [Hc ?]).
    apply bc_eqb_eq in Hc. subst c'.
    repeat match goal with X : expr_eqb _ _ = true |- _ => apply expr_eqb_eq in X end. subst a' b'.
    cbn [kta_scs] in Hrd. rewrite !forallb_app in Hrd. apply andb_prop in Hrd as [Hrd0 Hrd]. apply andb_prop in Hrd as [Hrd1 Hrd2].
    destruct H as (H' & HT1 & HT2). cbn [kt_oblA]. split; [exact (node_chkA_sound kn dis scs rest accs arest HK HD Hrd0 ltac:(assumption) H')|].
    split; intro C.
    + apply (IH1 r1 (kn_enter kn (br_know kn true c a b)) []); [|constructor|assumption|assumption|exact (HT1 C)].
      exact (kn_enter_ok segs E m _ _ HK (br_know_ok segs E m kn true c a b HK C)).
    + apply (IH2 r2 (kn_enter kn (br_know kn false c a b)) []); [|constructor|assumption|assumption|exact (HT2 C)].
      exact (kn_enter_ok segs E m _ _ HK (br_know_ok segs E m kn false c a b HK C)).
  - destruct r as [pc sr log rest arest | c' a' b' rest arest r1 r2]; cbn [kta_chk kt_obl2] in *; try discriminate Hc.
    repeat (apply andb_prop in Hc as [Hc ?]).
    apply bc_eqb_eq in Hc. subst c'.
    repeat match goal with X : expr_eqb _ _ = true |- _ => apply expr_eqb_eq in X end. subst a' b'.
    assert (Hv : 0 <= v < 2^64) by (split; [apply Z.leb_le | apply Z.ltb_lt]; assumption).
    cbn [kta_scs] in Hrd. rewrite !forallb_app in Hrd. apply andb_prop in Hrd as [Hrd0 Hrd]. apply andb_prop in Hrd as [Hrd1 Hrd2].
    destruct H as (H' & HT1 & HT2). cbn [kt_oblA]. split; [exact (node_chkA_sound kn dis scs rest accs arest HK HD Hrd0 ltac:(assumption) H')|].
    split; intro C.
    + apply (IH1 r1 (kn_enter kn (split_know kn true x v)) []); [|constructor|assumption|assumption|exact (HT1 C)].
      exact (kn_enter_ok segs E m _ _ HK (split_know_ok segs E m kn true x v HK Hv (split_eqb E x v true Hv C))).
    + apply (IH2 r2 (kn_enter kn (split_know kn false x v)) []); [|constructor|assumption|assumption|exact (HT2 C)].
      exact (kn_enter_ok segs E m _ _ HK (split_know_ok segs E m kn false x v HK Hv (split_eqb E x v false Hv C))).
  - cbn [kta_chk] in Hc. apply andb_prop in Hc as [Hci Hc]. cbn [kt_oblA kta_scs] in *.
    apply (IH1 r kn (ci :: dis)); [exact HK | | exact Hrd | exact Hc | exact H].
    constructor; [exact (ci_chk_sound kn ci HK Hci) | exact HD].
Qed.
End WithEA.

(* [comment removed for export] *)
Definition kta_chk_all (zs : list Z) (rz : list zexp) (zks : list zk) (rk : list kentry) (aks : list zak) (rs ws : list zreg)
                       (reads : list rdspec) (t : ktreeA) (r : vtree) : bool :=
  let nz := length zs in
  forallb (zwf nz) rz && rds_chk nz 0 reads && forallb (sc_rd_chk nz reads) (kta_scs t) && forallb (rk_chk (map zk_kentry zks) (zk_tfs zks) nz reads) rk
  && forallb (zk_wf nz) zks && forallb (zreg_wf nz) rs && forallb (zreg_wf nz) ws && forallb (zak_wf nz) aks
  && kta_chk (map zak_aent aks) (map zk_kentry zks ++ rk) rs ws [] t r.

Theorem kx_treeA_evtF : forall RNG (Q : machine_state -> Prop) vmax fuel stops scalls zs rz xs zks rk aks pc m rom t r reads rs ws,
  kx_treeA segs vmax (map zak_aent aks) fuel true stops scalls (kt_init pc rz (map zk_kentry zks ++ rk) (length zs)) [] [] [] = t ->
  kta_chk_all zs rz zks rk aks rs ws reads t r = true ->
  Forall2 (fun e x => x = Z_to_bv 64 (zden zs e)) rz xs ->
  Forall (zk_prop segs m zs) zks ->
  Forall (zreg_prop segs m zs) rs ->
  Forall (zwin_prop RNG zs) ws ->
  Forall (zak_prop m RNG zs) aks ->
  (forall E, kx_env_ok segs m zs reads E -> know_ok segs E m (map zk_kentry zks ++ rk) ->
     kt_obl2 E (PO2 segs m RNG E) (PC2 segs F fc m rom RNG Q E) r) ->
  evtF segs RNG Q (MS (mkRl xs) F (Z_to_bv 64 pc) fc None m rom).
Proof.
  intros RNG Q vmax fuel stops scalls zs rz xs zks rk aks pc m rom t r reads rs ws Hex Hchk Hregs Hzk Hrs Hws Haks K.
  unfold kta_chk_all in Hchk. repeat (apply andb_prop in Hchk as [Hchk ?]).
  pose proof (kx_env_exists segs m zs reads ltac:(assumption)) as HE.
  set (E := kx_env (kx_vals segs m (map (Z_to_bv 64) zs) reads)) in *.
  assert (Hkn : know_ok segs E m (map zk_kentry zks ++ rk)).
  { assert (Hk0 : know_ok segs E m (map zk_kentry zks)) by (apply (zks_ent segs m zs E zks (proj1 HE)); assumption).
    assert (Htf : Forall (tf_ok segs m E) (zk_tfs zks)) by (apply (zk_tfs_ok segs m zs E zks (proj1 HE)); assumption).
    apply Forall_app. split; [exact Hk0|].
    apply Forall_forall. intros K0 HK0.
    match goal with X : forallb (rk_chk _ _ _ _) rk = true |- _ =>
      rewrite forallb_forall in X; exact (rk_chk_ok segs m _ _ _ reads E K0 (proj2 HE) Hk0 Htf (X K0 HK0)) end. }
  assert (HAK : aknow_ok RNG E m (map zak_aent aks)) by (apply (zaks_ent m RNG zs E aks (proj1 HE)); assumption).
  pose proof (kta_chk_sound (map zak_aent aks) m rom RNG Q zs rs ws reads E (proj1 HE) (proj2 HE) ltac:(assumption) ltac:(assumption) Hrs Hws HAK
                t r _ [] Hkn (Forall_nil _) ltac:(assumption) ltac:(assumption) (K E HE Hkn)) as Hobl.
  rewrite <- Hex in Hobl.
  exact (kx_treeA_sound segs vmax (map zak_aent aks) F fc E m rom RNG (mem_inv segs m) Q HAK fuel true stops scalls
           (kt_init pc rz (map zk_kentry zks ++ rk) (length zs)) [] [] [] eq_refl Hobl (Forall_nil _)
           (mkRl xs) (regs_ok_init zs E rz xs (proj1 HE) ltac:(assumption) Hregs) (rfull_mkRl xs) I Hkn (fun X => X)).
Qed.

Theorem kx_treeA_evt : forall (Q : machine_state -> Prop) vmax fuel stops scalls zs rz xs zks rk aks pc m rom t r reads rs,
  kx_treeA segs vmax (map zak_aent aks) fuel true stops scalls (kt_init pc rz (map zk_kentry zks ++ rk) (length zs)) [] [] [] = t ->
  kta_chk_all zs rz zks rk aks rs [] reads t r = true ->
  Forall2 (fun e x => x = Z_to_bv 64 (zden zs e)) rz xs ->
  Forall (zk_prop segs m zs) zks ->
  Forall (zreg_prop segs m zs) rs ->
  Forall (zak_prop m (fun _ _ => True) zs) aks ->
  (forall E, kx_env_ok segs m zs reads E -> know_ok segs E m (map zk_kentry zks ++ rk) ->
     kt_obl2 E (PO1 segs m E) (PC1 segs F fc m rom Q E) r) ->
  evt segs Q (MS (mkRl xs) F (Z_to_bv 64 pc) fc None m rom).
Proof.
  intros Q vmax fuel stops scalls zs rz xs zks rk aks pc m rom t r reads rs Hex Hchk Hregs Hzk Hrs Haks K.
  apply (evtF_evt segs (fun _ _ => True)).
  apply (kx_treeA_evtF (fun _ _ => True) Q vmax fuel stops scalls zs rz xs zks rk aks pc m rom t r reads rs [] Hex Hchk Hregs Hzk Hrs (Forall_nil _) Haks).
  intros E HE HK. apply kt_obl2_top. exact (K E HE HK).
Qed.

End TreeGoA.
