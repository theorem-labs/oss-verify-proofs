(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.AS Require Import PropExec CatExec AxSymExec3 AxSymExec3Sound MemSplit.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Seg Require Import SegLearn SegTmpl SegGhost.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Spec Require Import Prelim SjStage1 SjInvPath SjInv SjS2Inv SjS2Tab.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegP2 Require Import S2Ghost S2Lin S2Dig S2StrVC S2G2 S2WalkVC S2WalkLem S2WalkVCok.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegP2A Require Import S2WalkVCT.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2.
Open Scope Z_scope.

(* [comment removed for export] *)
Ltac lazy_eq :=
  repeat (first [ reflexivity
                | match goal with |- context [S2WalkVC.kimp ?sg ?k ?K] => destruct (S2WalkVC.kimp sg k K) end
                | match goal with |- context [leq ?a ?b] => destruct (leq a b) end
                | match goal with |- context [Z.leb ?a ?b] => destruct (Z.leb a b) end
                | match goal with |- context [caps_ok ?a ?b ?c] => destruct (caps_ok a b c) end ]; cbn [andb orb]).

Section Chk2.
  Variable segs : list Segment.
  Variable MF : Z.
  Variable TD : Z.
  Local Notation kimp := (kimp segs).

  (* [comment removed for export] *)
  Definition r1_read2 (kn : list kentry) (X NN L : expr) (s : sidecond) : list kentry * list ST.gatom :=
    match rrec 4 s with
    | Some (a, v) =>
        let KO := rel a X in let VX := x4 v in
        if kimp kn (KAlign KO 4) then if kimp kn (KRange KO 0 (KOMAX MF)) then if kimp kn (KRange NN 0 MF) then
        if kimp kn (KRange L 0 MF) then if kimp kn (KRange (esub2 (eaddl (emul 4 NN) 8) KO) 0 (KOMAX MF)) then
          let f1 := if kimp kn (KRange (esub2 (eaddl (emul 4 NN) 4) KO) 0 (KOMAX MF))
                    then [KRange VX 0 MF; KRange (esub2 L VX) 0 MF] else [] in
          let f2 := if kimp kn (KRange (esub2 (emul 4 NN) (eaddl KO 4)) 0 (KOMAX MF)) then [KRange (esub2 L VX) 1 MF] else [] in
          (KRange VX 0 (2 ^ 32 - 1) :: f1 ++ f2, [ST.GA 3 [KO; VX]])
        else ([], []) else ([], []) else ([], []) else ([], []) else ([], [])
    | None => ([], [])
    end.
  Lemma r1_read2_eq : forall kn X NN L s, r1_read2 kn X NN L s = r1_read segs MF kn X NN L s.
  Proof. intros. unfold r1_read2, r1_read. destruct (rrec 4 s) as [[a v]|]; [|reflexivity]. cbv zeta. lazy_eq. Qed.

  (* [comment removed for export] *)
  Definition r2_read2 (kn : list kentry) (src : list ST.gatom) (s : sidecond) : list kentry :=
    match rrec 4 s with
    | Some (a, v) =>
        flat_map (fun args => match args with
          | [OC; D; BW] =>
              let DO := rel a OC in
              if kimp kn (KAlign DO 8) then if kimp kn (KRange DO 0 8184) then if kimp kn (KRange (esub2 (emul 8 D) DO) 0 8184) then
              if kimp kn (KRange D 0 1023) then if kimp kn (KRange BW 0 (2 ^ 62)) then
                [KRange (x4 v) 0 (2 ^ 32 - 1); KRange (esub2 BW (emul 8 (x4 v))) 1 (2 ^ 62)] else [] else [] else [] else [] else []
          | _ => [] end) (atoms_of 5 src)
    | None => []
    end.
  Lemma r2_read2_eq : forall kn src s, r2_read2 kn src s = r2_read segs kn src s.
  Proof.
    intros. unfold r2_read2, r2_read. destruct (rrec 4 s) as [[a v]|]; [|reflexivity].
    apply flat_map_ext. intros [|OC [|D [|BW [|? ?]]]]; try reflexivity. cbv zeta. lazy_eq.
  Qed.

  (* [comment removed for export] *)
  Definition fill_facts2 (kn : list kentry) (s : sidecond) : list kentry :=
    match rrec 1 s with
    | Some (a, b) =>
        let A' := eaddl (a_base a) (a_off a) in
        flat_map (fun K => match fill_of K with
          | Some (FS, n, cb) =>
              if (if kimp kn (KRange (x1 b) (cb + 1) 255) then true else kimp kn (KRange (x1 b) 0 (cb - 1))) then
              if kimp kn (KRange A' 0 (2 ^ 62)) then if kimp kn (KRange FS 0 (2 ^ 62)) then
              if kimp kn (KRange (esub2 (eaddl FS n) A') 1 (2 ^ 62)) then [KRange (esub2 FS A') 1 (2 ^ 62)]
              else [] else [] else [] else []
          | None => [] end) kn
    | None => []
    end.
  Lemma fill_facts2_eq : forall kn s, fill_facts2 kn s = fill_facts segs kn s.
  Proof.
    intros. unfold fill_facts2, fill_facts. destruct (rrec 1 s) as [[a b]|]; [|reflexivity]. cbv zeta.
    apply flat_map_ext. intros K. destruct (fill_of K) as [[[FS n] cb]|]; [|reflexivity]. lazy_eq.
  Qed.

  (* [comment removed for export] *)
  Definition r3_read2 (kn : list kentry) (B L : expr) (s : sidecond) : list kentry :=
    match rrec 1 s with
    | Some (a, b) =>
        let XE := rel a B in
        if kimp kn (KRange XE 0 (MF + 63)) then if kimp kn (KRange (esub2 (eaddl L 63) XE) 0 (MF + 63)) then
        if kimp kn (KRange L 0 MF) then
        if (if kimp kn (KRange (x1 b) 1 255) then true else kimp kn (KRange (EVar b) 1 255)) then [KRange (esub2 L XE) 1 MF]
        else [] else [] else [] else []
    | None => []
    end.
  Lemma r3_read2_eq : forall kn B L s, r3_read2 kn B L s = r3_read segs MF kn B L s.
  Proof. intros. unfold r3_read2, r3_read. destruct (rrec 1 s) as [[a b]|]; [|reflexivity]. cbv zeta. lazy_eq. Qed.

  (* [comment removed for export] *)
  Definition r14_read2 (kn : list kentry) (src : list ST.gatom) (s : sidecond) : list kentry :=
    match rrec 1 s with
    | Some (a, v) =>
        flat_map (fun args => match args with
          | [IA; D] => let I := rel a IA in
              if kimp kn (KRange I 1 1023) then if kimp kn (KRange (esub2 D I) 0 1023) then if kimp kn (KRange D 0 1023) then
              if kimp kn (KRange IA 1 (2 ^ 62)) then [KRange (x1 v) 0 1; KRange (EVar v) 0 1] else [] else [] else [] else []
          | _ => [] end) (atoms_of 6 src)
    | None => []
    end.
  Lemma r14_read2_eq : forall kn src s, r14_read2 kn src s = r14_read segs kn src s.
  Proof.
    intros. unfold r14_read2, r14_read. destruct (rrec 1 s) as [[a v]|]; [|reflexivity].
    apply flat_map_ext. intros [|IA [|D [|? ?]]]; try reflexivity. cbv zeta. lazy_eq.
  Qed.

  (* [comment removed for export] *)
  Definition r4_tok2 (kn : list kentry) (NN L : expr) (args : list expr) : list kentry :=
    match args with
    | [K; VX] => if kimp kn (KRange (esub2 L VX) 1 MF) then if kimp kn (KRange (esub2 (eaddl (emul 4 NN) 4) K) 0 (KOMAX MF)) then
                 if kimp kn (KRange K 0 (KOMAX MF)) then if kimp kn (KRange NN 0 MF) then if kimp kn (KRange L 0 MF) then
                   [KRange (esub2 (emul 4 NN) (eaddl K 4)) 0 (KOMAX MF)] else [] else [] else [] else [] else []
    | _ => []
    end.
  Lemma r4_tok2_eq : forall kn NN L args, r4_tok2 kn NN L args = r4_tok segs MF kn NN L args.
  Proof. intros. unfold r4_tok2, r4_tok. destruct args as [|K [|VX [|? ?]]]; try reflexivity. lazy_eq. Qed.
  Definition r5_tok2 (kn : list kentry) (NN : expr) (args : list expr) : list ST.gatom :=
    match args with
    | [K; VX] => if kimp kn (KRange (esub2 (emul 4 NN) (eaddl K 4)) 0 (KOMAX MF)) then if kimp kn (KRange K 0 (KOMAX MF)) then
                 if kimp kn (KRange NN 0 MF) then [ST.GA 4 [eaddl K 4; eaddl VX 1]] else [] else [] else []
    | _ => []
    end.
  Lemma r5_tok2_eq : forall kn NN args, r5_tok2 kn NN args = r5_tok segs MF kn NN args.
  Proof. intros. unfold r5_tok2, r5_tok. destruct args as [|K [|VX [|? ?]]]; try reflexivity. lazy_eq. Qed.

  (* [comment removed for export] *)
  Definition derive2 (c : SG.vc) : list kentry * list ST.gatom :=
    let kn := SG.vc_kn c in let src := SG.vc_src c in let path := SG.vc_path c in
    let F6 := flat_map (fun s => srl_facts segs kn (e_val s)) (SG.vc_log c) in
    match find_atom 2 src, find_atom 1 src with
    | Some [X; NN], Some [B; L] =>
        let R1 := map (r1_read2 kn X NN L) path in
        let F1 := flat_map fst R1 in let A1 := flat_map snd R1 in
        let F2 := flat_map (r2_read2 kn src) path in
        let kn0 := flat_map (byte_facts segs kn) path ++ flat_map swar_facts path ++ kn in
        let F3 := flat_map (r3_read2 kn0 B L) path ++ flat_map (fill_facts2 kn0) path in
        let kn1 := F6 ++ F1 ++ F2 ++ F3 ++ flat_map (r14_read2 kn src) path ++ kn0 in
        let toks := atoms_of 3 src ++ map ST.g_args A1 in
        let F4 := flat_map (r4_tok2 kn1 NN L) toks in
        let kn2a := F4 ++ kn1 in
        let kn2 := flat_map (fun s => fst (r1_read2 kn2a X NN L s)) path ++ kn2a in
        let A5 := flat_map (r5_tok2 kn2 NN) toks in
        let SX := map (sexit segs MF kn2 path) (atoms_of 0 src) in
        let ges := atoms_of 4 src ++ map ST.g_args A5 ++ map ST.g_args (flat_map snd SX) in
        let F7 := flat_map (link_tok segs MF kn2 L ges (atoms_of 7 src)) toks in
        let F8 := str_facts segs MF TD kn2 path (SG.vc_log c) src toks (SG.vc_tgt c) in
        (F8 ++ flat_map fst SX ++ F7 ++ kn2, A1 ++ A5 ++ flat_map snd SX ++ flat_map (gnum1 segs MF kn2 path B L) (atoms_of 3 src))
    | _, _ => (F6 ++ kn, [])
    end.

  Lemma map_ext' : forall {T1 T2 : Type} (f g : T1 -> T2) l, (forall x, f x = g x) -> map f l = map g l.
  Proof. intros T1 T2 f g l H. induction l as [|x l IH]; cbn; [reflexivity | rewrite H, IH; reflexivity]. Qed.

  Lemma derive2_eq : forall c, derive2 c = derive segs MF TD c.
  Proof.
    intros c. unfold derive2, derive. cbv zeta.
    destruct (find_atom 2 (SG.vc_src c)) as [[|X [|NN [|? ?]]]|]; try reflexivity.
    destruct (find_atom 1 (SG.vc_src c)) as [[|B [|L [|? ?]]]|]; try reflexivity.
    rewrite (map_ext' (r1_read2 (SG.vc_kn c) X NN L) (r1_read segs MF (SG.vc_kn c) X NN L) _ (r1_read2_eq _ _ _ _)).
    rewrite (flat_map_ext _ _ (r2_read2_eq (SG.vc_kn c) (SG.vc_src c))).
    rewrite (flat_map_ext _ _ (r3_read2_eq _ B L)), (flat_map_ext _ _ (fill_facts2_eq _)), (flat_map_ext _ _ (r14_read2_eq _ _)).
    rewrite (flat_map_ext _ _ (r4_tok2_eq _ NN L)).
    rewrite (flat_map_ext (fun s => fst (r1_read2 _ X NN L s)) (fun s => fst (r1_read segs MF _ X NN L s))
               (fun s => f_equal fst (r1_read2_eq _ X NN L s))).
    rewrite (flat_map_ext _ _ (r5_tok2_eq _ NN)).
    reflexivity.
  Qed.

  (* [comment removed for export] *)
  Definition room_ok2 (kn : list kentry) (L : expr) (K : kentry) : bool :=
    match K with
    | KRange (EAlu ALU_SUB (EAlu ALU_SUB CS OL) (EAlu ALU_SUB L' VX)) lo hi =>
        if (leq L' L && Z.leb lo 7 && Z.leb (2 ^ 40) hi)%bool then if caps_ok kn L CS then
        if kimp kn (KRange L 0 MF) then if kimp kn (KRange CS 0 (2 ^ 40)) then if kimp kn (KRange (esub2 L VX) 0 MF) then
        if kimp kn (KRange VX 0 MF) then if kimp kn (KRange OL 0 BIGS) then kimp kn (KRange (esub2 (emul 5 VX) (emul 3 OL)) 5 (5 * MF))
        else false else false else false else false else false else false else false
    | _ => false
    end.
  Lemma room_ok2_eq : forall kn L K, room_ok2 kn L K = room_ok segs MF kn L K.
  Proof.
    intros kn L K. unfold room_ok2, room_ok.
    destruct K as [| | | | |e lo hi| | | |]; try reflexivity.
    destruct e as [| |o1 e1 e2| | | | |]; try reflexivity. destruct o1; try reflexivity.
    destruct e1 as [| |o2 CS OL| | | | |]; try reflexivity. destruct o2; try reflexivity.
    destruct e2 as [| |o3 L' VX| | | | |]; try reflexivity. destruct o3; try reflexivity. lazy_eq.
  Qed.

  Definition fact_ok2 (c : SG.vc) (kn2 : list kentry) (K : kentry) : bool :=
    if is_unk K then ST.kin K (SG.vc_kn c)
    else if is_pure2 K then
           (if kimp kn2 K then true
            else if (match find_atom 1 (SG.vc_src c) with Some [B; L] => room_ok2 kn2 L K | _ => false end) then true
            else gd_fact segs MF kn2 (SG.vc_src c) K)
         else false.

  Definition wvc_ok2 (c : SG.vc) : bool :=
    let '(kn2, A) := derive2 c in
    if forallb (fun g => match ST.g_id g with
                         | 0%nat => str_tgt_ok segs MF TD kn2 (SG.vc_path c) (SG.vc_log c) (SG.vc_src c) (atoms_of 3 (SG.vc_src c) ++ atoms_of 3 A) g
                         | 5%nat => goc_ok segs kn2 (SG.vc_log c) (SG.vc_src c) g
                         | 6%nat => gia_ok segs kn2 (SG.vc_log c) (SG.vc_src c) g
                         | 10%nat | 11%nat | 12%nat => gd_ok segs MF kn2 (SG.vc_path c) (SG.vc_src c) g
                         | _ => tgt_pure_ok segs kn2 (SG.vc_src c) A g
                         end) (SG.vc_tgt c)
    then forallb (fact_ok2 c kn2) (SG.vc_facts c) else false.

  Lemma forallb_ext' : forall {T : Type} (f g : T -> bool) l, (forall x, f x = g x) -> forallb f l = forallb g l.
  Proof. intros T f g l H. induction l as [|x l IH]; cbn; [reflexivity | rewrite H, IH; reflexivity]. Qed.

  Lemma wvc_ok2_eq : forall c, wvc_ok2 c = wvc_ok segs MF TD c.
  Proof.
    intros c. unfold wvc_ok2, wvc_ok. rewrite derive2_eq. destruct (derive segs MF TD c) as [kn2 A].
    destruct (forallb _ (SG.vc_tgt c)); [cbn [andb] | reflexivity].
    apply forallb_ext'. intros K. unfold fact_ok2. destruct (is_unk K); [reflexivity|].
    destruct (is_pure2 K); [cbn [andb] | reflexivity].
    destruct (kimp kn2 K); [reflexivity|]. cbn [orb].
    destruct (find_atom 1 (SG.vc_src c)) as [[|B [|L [|? ?]]]|]; try (cbn [orb]; reflexivity).
    rewrite room_ok2_eq. destruct (room_ok segs MF kn2 L K); reflexivity.
  Qed.

  (* [comment removed for export] *)
  Definition wvc_okL (c : SG.vc) : bool := wvc_ok2 (trimc c).
End Chk2.

Section Sound.
  Variable segs : list Segment.
  Variables data idxs : list Z.
  Variable MF : Z.
  Hypothesis MF_rng : 0 <= MF <= 2 ^ 30.
  Variable TD : Z.
  Hypothesis TD_rng : 0 <= TD /\ TD + 3544 < 2 ^ 64.
  Hypothesis D2V_IMG : forall m i, (forall x, TD <= x < TD + 3544 -> m (Z_to_bv 64 x) = None) -> 0 <= i < 886 ->
    rdn segs m (Z_to_bv 64 (TD + 4 * i)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 (d2v i))).

  Theorem wvc_ok2_sound : forall c, wvc_ok2 segs MF TD c = true -> SG.vc_holds segs (gp2 segs data idxs) c.
  Proof. intros c H. rewrite wvc_ok2_eq in H. exact (wvc_ok_sound segs data idxs MF MF_rng TD TD_rng D2V_IMG c H). Qed.

  Theorem wvc_okL_sound : forall c, wvc_okL segs MF TD c = true -> SG.vc_holds segs (gp2 segs data idxs) c.
  Proof.
    intros c H. unfold wvc_okL in H. rewrite wvc_ok2_eq in H.
    exact (wvc_okT_sound segs data idxs MF MF_rng TD TD_rng D2V_IMG c H).
  Qed.
End Sound.
