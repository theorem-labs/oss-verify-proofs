(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.AS Require Import PropExec AxSymExec3 AxSymExec3Sound.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Seg Require Import SegLearn SegTmpl SegGhost.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Spec Require Import Prelim SjStage1 SjInvPath SjInv.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegP2 Require Import S2Ghost S2G2 S2Lin S2StrVC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S.
Open Scope Z_scope.

Section Chk.
  Variable segs : list Segment.
  Variable MF : Z.            (* [comment removed for export] *)
  Variable TD : Z.            (* [comment removed for export] *)
  Definition KOMAX : Z := 4 * MF + 16.
  Definition BIGS : Z := 2 ^ 40.

  Definition kimp (kn : list kentry) (K : kentry) : bool := ST.kimplied segs kn K.

  Fixpoint find_atom (id : nat) (l : list ST.gatom) : option (list expr) :=
    match l with [] => None | g :: r => if Nat.eqb (ST.g_id g) id then Some (ST.g_args g) else find_atom id r end.
  Definition atoms_of (id : nat) (l : list ST.gatom) : list (list expr) :=
    map ST.g_args (List.filter (fun g => Nat.eqb (ST.g_id g) id) l).

  (* [comment removed for export] *)
  Definition rel (a : saddr) (X : expr) : expr := nsub (eaddl (a_base a) (a_off a)) X.

  (* [comment removed for export] *)
  Definition rrec (w : nat) (s : sidecond) : option (saddr * nat) :=
    match s with
    | SCReadBase a w' sx (EVar v) => if (Nat.eqb w w' && negb sx)%bool then Some (a, v) else None
    | _ => None
    end.

  (* [comment removed for export] *)
  Definition r1_read (kn : list kentry) (X NN L : expr) (s : sidecond) : list kentry * list ST.gatom :=
    match rrec 4 s with
    | Some (a, v) =>
        let KO := rel a X in let VX := x4 v in
        if (kimp kn (KAlign KO 4) && kimp kn (KRange KO 0 KOMAX) && kimp kn (KRange NN 0 MF) && kimp kn (KRange L 0 MF)
            && kimp kn (KRange (esub2 (eaddl (emul 4 NN) 8) KO) 0 KOMAX))%bool then
          let f1 := if kimp kn (KRange (esub2 (eaddl (emul 4 NN) 4) KO) 0 KOMAX)
                    then [KRange VX 0 MF; KRange (esub2 L VX) 0 MF] else [] in
          let f2 := if kimp kn (KRange (esub2 (emul 4 NN) (eaddl KO 4)) 0 KOMAX) then [KRange (esub2 L VX) 1 MF] else [] in
          (KRange VX 0 (2 ^ 32 - 1) :: f1 ++ f2, [ST.GA 3 [KO; VX]])
        else ([], [])
    | None => ([], [])
    end.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition caps_ok (kn : list kentry) (L CS : expr) : bool :=
    existsb (fun K => match K with
                      | KRange (EAlu ALU_SUB (EMd M_MUL (ELit k3) CS') (EMd M_MUL (ELit k5) L')) lo hi =>
                          (Z.eqb k3 3 && Z.eqb k5 5 && expr_eqb CS' CS && leq L' L && Z.leb 182 lo && Z.leb hi (2 ^ 40))%bool
                      | _ => false end) kn.
  Definition room_ok (kn : list kentry) (L : expr) (K : kentry) : bool :=
    match K with
    | KRange (EAlu ALU_SUB (EAlu ALU_SUB CS OL) (EAlu ALU_SUB L' VX)) lo hi =>
        (leq L' L && Z.leb lo 7 && Z.leb (2 ^ 40) hi && caps_ok kn L CS && kimp kn (KRange L 0 MF) && kimp kn (KRange CS 0 (2 ^ 40))
         && kimp kn (KRange (esub2 L VX) 0 MF) && kimp kn (KRange VX 0 MF) && kimp kn (KRange OL 0 BIGS)
         && kimp kn (KRange (esub2 (emul 5 VX) (emul 3 OL)) 5 (5 * MF)))%bool
    | _ => false
    end.

  Definition link_tok (kn : list kentry) (L : expr) (ges gsbs : list (list expr)) (tok : list expr) : list kentry :=
    match tok with
    | [K; VX] =>
        if kimp kn (KRange VX 0 MF) then
          flat_map (fun args => match args with
                    | [K'; E'] => if (leq K' K && kimp kn (KRange E' 0 BIGS))%bool then [KRange (esub2 VX E') 0 MF] else []
                    | _ => [] end) ges ++
          flat_map (fun args => match args with
                    | [K'; OL; ELit c] =>
                        if (leq K' K && Z.leb 0 c && Z.leb c 16 && kimp kn (KRange OL 0 BIGS))%bool
                        then KRange (esub2 (emul 5 VX) (emul 3 OL)) c (5 * MF) ::
                             (match OL with ELit ol => if (Z.leb 0 ol && Z.leb ol MF)%bool
                                                       then [KRange VX ((3 * ol + c + 4) / 5) MF] else [] | _ => [] end)
                        else []
                    | _ => [] end) gsbs
        else []
    | _ => []
    end.

  (* [comment removed for export] *)
  Definition r2_read (kn : list kentry) (src : list ST.gatom) (s : sidecond) : list kentry :=
    match rrec 4 s with
    | Some (a, v) =>
        flat_map (fun args => match args with
          | [OC; D; BW] =>
              let DO := rel a OC in
              if (kimp kn (KAlign DO 8) && kimp kn (KRange DO 0 8184) && kimp kn (KRange (esub2 (emul 8 D) DO) 0 8184)
                  && kimp kn (KRange D 0 1023) && kimp kn (KRange BW 0 (2 ^ 62)))%bool
              then [KRange (x4 v) 0 (2 ^ 32 - 1); KRange (esub2 BW (emul 8 (x4 v))) 1 (2 ^ 62)] else []
          | _ => [] end) (atoms_of 5 src)
    | None => []
    end.

  (* [comment removed for export] *)
  Definition dig_expr (b : nat) : expr := EAlu ALU_AND (EAlu ALU_ADD (x1 b) (ELit (-48))) (ELit 255).
  Definition msk_expr (b : nat) : expr := EAlu ALU_AND (x1 b) (ELit 255).
  Definition byte_facts (kn : list kentry) (s : sidecond) : list kentry :=
    match rrec 1 s with
    | Some (a, b) =>
        (if kimp kn (KRange (dig_expr b) 0 9) then [KRange (x1 b) 48 57] else []) ++
        flat_map (fun K => match K with
                           | KRange e lo hi => if (expr_eqb e (msk_expr b) && Z.leb 0 lo && Z.leb hi 255)%bool then [KRange (x1 b) lo hi] else []
                           | _ => [] end) kn
    | None => []
    end.

  (* [comment removed for export] *)
  Definition C06 : Z := 434041037028460038.
  Definition C0F : Z := 1085102592571150095.
  Definition CF0 : Z := 17361641481138401520.
  Definition C33 : Z := 3689348814741910323.
  Definition swar_v (T : expr) : option expr :=
    match T with
    | EAlu ALU_OR (EAlu ALU_AND (EAlu ALU_SRL (EAlu ALU_ADD v (ELit c1)) (ELit c4)) (ELit c2)) (EAlu ALU_AND v' (ELit c3)) =>
        if (Z.eqb c1 C06 && Z.eqb c4 4 && Z.eqb c2 C0F && Z.eqb c3 CF0 && expr_eqb v v')%bool then Some v else None
    | _ => None
    end.
  Definition is_lane (t : Z * expr) : bool :=
    match snd t with EExt false 0 1 (EVar _) => (Z.leb 0 (fst t) && Z.leb (fst t) (2 ^ 48))%bool | _ => false end.
  Definition top_lane (v : expr) : option nat :=
    let L := lin_of v in
    match List.filter (fun t => Z.eqb (fst t) (2 ^ 56)) (snd L) with
    | [(_, EExt false 0 1 (EVar b7))] =>
        let others := List.filter (fun t => negb (Z.eqb (fst t) (2 ^ 56))) (snd L) in
        if (Z.eqb (fst L) 0 && Nat.leb (length others) 7 && forallb is_lane others)%bool then Some b7 else None
    | _ => None
    end.
  Definition swar_facts (s : sidecond) : list kentry :=
    match s with
    | SCBr t c T (ELit k) =>
        if (Z.eqb k C33 && match t, c with true, BC_EQ => true | false, BC_NE => true | _, _ => false end)%bool then
          match swar_v T with
          | Some v => match top_lane v with Some b7 => [KRange (x1 b7) 42 255] | None => [] end
          | None => []
          end
        else []
    | _ => []
    end.

  (* [comment removed for export] *)
  Definition fill_of (K : kentry) : option (expr * Z * Z) :=
    match K with
    | KFill (SA FB FO) (ELit n) c => if (Z.leb 0 c && Z.ltb c 256 && Z.leb 1 n && Z.leb n 4096)%bool then Some (eaddl FB FO, n, c) else None
    | KZero (SA FB FO) (ELit n) => if (Z.leb 1 n && Z.leb n 4096)%bool then Some (eaddl FB FO, n, 0) else None
    | _ => None
    end.
  Definition fill_facts (kn : list kentry) (s : sidecond) : list kentry :=
    match rrec 1 s with
    | Some (a, b) =>
        let A' := eaddl (a_base a) (a_off a) in
        flat_map (fun K => match fill_of K with
          | Some (FS, n, cb) =>
              if ((kimp kn (KRange (x1 b) (cb + 1) 255) || kimp kn (KRange (x1 b) 0 (cb - 1)))
                  && kimp kn (KRange A' 0 (2 ^ 62)) && kimp kn (KRange FS 0 (2 ^ 62))
                  && kimp kn (KRange (esub2 (eaddl FS n) A') 1 (2 ^ 62)))%bool
              then [KRange (esub2 FS A') 1 (2 ^ 62)] else []
          | None => [] end) kn
    | None => []
    end.

  (* [comment removed for export] *)
  Definition r3_read (kn : list kentry) (B L : expr) (s : sidecond) : list kentry :=
    match rrec 1 s with
    | Some (a, b) =>
        let XE := rel a B in
        if (kimp kn (KRange XE 0 (MF + 63)) && kimp kn (KRange (esub2 (eaddl L 63) XE) 0 (MF + 63))
            && kimp kn (KRange L 0 MF)
            && (kimp kn (KRange (x1 b) 1 255) || kimp kn (KRange (EVar b) 1 255)))%bool
        then [KRange (esub2 L XE) 1 MF] else []
    | None => []
    end.

  (* [comment removed for export] *)
  Definition r4_tok (kn : list kentry) (NN L : expr) (args : list expr) : list kentry :=
    match args with
    | [K; VX] => if (kimp kn (KRange (esub2 L VX) 1 MF) && kimp kn (KRange (esub2 (eaddl (emul 4 NN) 4) K) 0 KOMAX)
                     && kimp kn (KRange K 0 KOMAX) && kimp kn (KRange NN 0 MF) && kimp kn (KRange L 0 MF))%bool
                 then [KRange (esub2 (emul 4 NN) (eaddl K 4)) 0 KOMAX] else []
    | _ => []
    end.
  Definition r5_tok (kn : list kentry) (NN : expr) (args : list expr) : list ST.gatom :=
    match args with
    | [K; VX] => if (kimp kn (KRange (esub2 (emul 4 NN) (eaddl K 4)) 0 KOMAX) && kimp kn (KRange K 0 KOMAX)
                     && kimp kn (KRange NN 0 MF))%bool
                 then [ST.GA 4 [eaddl K 4; eaddl VX 1]] else []
    | _ => []
    end.

  (* [comment removed for export] *)
  Fixpoint srl_facts (kn : list kentry) (e : expr) : list kentry :=
    match e with
    | EAlu ALU_SRL a (ELit s) =>
        (if (Z.leb 0 s && Z.ltb s 64)%bool then
           KRange (esub2 a (emul (2 ^ s) e)) 0 (2 ^ s - 1) ::
           (if kimp kn (KRange a 0 (2 ^ 34)) then [KRange e 0 (Z.shiftr (2 ^ 34) s)] else [])
         else []) ++ srl_facts kn a
    | EAlu _ a b | EAluw _ a b | EMd _ a b | EMdw _ a b => srl_facts kn a ++ srl_facts kn b
    | EExt _ _ _ a => srl_facts kn a
    | _ => []
    end.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition byte34 (kn : list kentry) (path : list sidecond) (B X : expr) : bool :=
    existsb (fun s => match rrec 1 s with
                      | Some (a, b) => (leq (rel a B) X && (kimp kn (KRange (x1 b) 34 34) || kimp kn (KRange (EVar b) 34 34)))%bool
                      | None => false
                      end) path.

  (* [comment removed for export] *)
  Definition koff (P' P : expr) : option Z := match lin_of (nsub P' P) with (k, []) => Some k | _ => None end.

  (* [comment removed for export] *)
  Definition sstart_ok (kn : list kentry) (path : list sidecond) (lg : list sentry) (X NN B L : expr) (toks : list (list expr))
      (B' L' P' KO' : expr) : bool :=
    (leq B B' && leq L L' && kimp kn (KRange L 0 MF) && kimp kn (KRange NN 0 MF) && kimp kn (KRange KO' 0 KOMAX)
     && kimp kn (KRange (esub2 (emul 4 NN) (eaddl KO' 4)) 0 KOMAX) && SG.log_apart kn lg [(B', 0, L')] &&
     existsb (fun args => match args with
                          | [K; V] => (leq K KO' && leq P' (eaddl V 1) && byte34 kn path B V)%bool
                          | _ => false end) toks)%bool.

  (* [comment removed for export] *)
  Definition sarm_ok (kn : list kentry) (path : list sidecond) (lg : list sentry) (src : list ST.gatom) (B' L' P' KO' : expr) : bool :=
    existsb (fun args => match args with
      | [B; L; P; KO] =>
          match koff P' P with
          | Some k => (leq B B' && leq L L' && leq KO KO' && Z.leb 1 k && Z.leb k 12 && kimp kn (KRange L 0 MF)
                       && has_kimg kn TD (TD + 3544) && arm_ok TD B P k path && SG.log_apart kn lg [(B', 0, L')])%bool
          | None => false
          end
      | _ => false end) (atoms_of 0 src).

  Definition str_tgt_ok (kn : list kentry) (path : list sidecond) (lg : list sentry) (src : list ST.gatom) (toks : list (list expr))
      (g : ST.gatom) : bool :=
    match ST.g_id g, ST.g_args g, find_atom 2 src, find_atom 1 src with
    | 0%nat, [B'; L'; P'; KO'], Some [X; NN], Some [B; L] =>
        (sstart_ok kn path lg X NN B L toks B' L' P' KO' || sarm_ok kn path lg src B' L' P' KO')%bool
    | _, _, _, _ => false
    end.

  (* [comment removed for export] *)
  Definition str_facts (kn : list kentry) (path : list sidecond) (lg : list sentry) (src : list ST.gatom) (toks : list (list expr))
      (tgt : list ST.gatom) : list kentry :=
    flat_map (fun g => match ST.g_args g with
                       | [B'; L'; P'; KO'] => if str_tgt_ok kn path lg src toks g then [KRange (esub2 L' P') 1 MF] else []
                       | _ => [] end) tgt.

  (* [comment removed for export] *)
  Definition sexit (kn : list kentry) (path : list sidecond) (args : list expr) : list kentry * list ST.gatom :=
    match args with
    | [B; L; P; KO] => if (byte34 kn path B P && kimp kn (KRange L 0 MF))%bool
                       then ([KRange (esub2 L P) 1 MF], [ST.GA 4 [eaddl KO 4; eaddl P 1]]) else ([], [])
    | _ => ([], [])
    end.

  (* [comment removed for export] *)
  Definition byte_in (kn : list kentry) (path : list sidecond) (B X : expr) (lo hi : Z) : bool :=
    existsb (fun s => match rrec 1 s with
                      | Some (a, b) => (leq (rel a B) X && (kimp (KRange (x1 b) 0 255 :: kn) (KRange (x1 b) lo hi)
                                                           || kimp kn (KRange (EVar b) lo hi)))%bool
                      | None => false
                      end) path.
  (* [comment removed for export] *)
  Definition out_fact (b : nat) (K : kentry) : bool :=
    match K with
    | KRange (EAlu ALU_ADD (EExt false 0 1 (EVar b')) (ELit z)) lo _ => (Nat.eqb b' b && Z.leb (-45) z && Z.leb z 0 && Z.leb 58 (lo - z))%bool
    | _ => false
    end.
  Definition byte_out (kn : list kentry) (path : list sidecond) (B X : expr) : bool :=
    existsb (fun s => match rrec 1 s with
                      | Some (a, b) => (leq (rel a B) X && existsb (out_fact b) kn)%bool
                      | None => false
                      end) path.
  Definition gnum1 (kn : list kentry) (path : list sidecond) (B L : expr) (args : list expr) : list ST.gatom :=
    match args with
    | [K; V] =>
        if (leq K (ELit 0) && kimp kn (KRange (esub2 L V) 1 MF) && kimp kn (KRange V 0 MF) && kimp kn (KRange L 0 MF))%bool then
          (if (byte_in kn path B V 45 45 || byte_in kn path B V 48 57)%bool then [ST.GA 9 []] else []) ++
          (if (byte_in kn path B V 0 44 || byte_in kn path B V 46 47 || byte_in kn path B V 58 255 || byte_out kn path B V)%bool
           then [ST.GA 8 []] else [])
        else []
    | _ => []
    end.

  (* [comment removed for export] *)
  Definition r14_read (kn : list kentry) (src : list ST.gatom) (s : sidecond) : list kentry :=
    match rrec 1 s with
    | Some (a, v) =>
        flat_map (fun args => match args with
          | [IA; D] => let I := rel a IA in
              if (kimp kn (KRange I 1 1023) && kimp kn (KRange (esub2 D I) 0 1023) && kimp kn (KRange D 0 1023)
                  && kimp kn (KRange IA 1 (2 ^ 62)))%bool
              then [KRange (x1 v) 0 1; KRange (EVar v) 0 1] else []
          | _ => [] end) (atoms_of 6 src)
    | None => []
    end.

  (* [comment removed for export] *)
  Definition derive (c : SG.vc) : list kentry * list ST.gatom :=
    let kn := SG.vc_kn c in let src := SG.vc_src c in let path := SG.vc_path c in
    let F6 := flat_map (fun s => srl_facts kn (e_val s)) (SG.vc_log c) in
    match find_atom 2 src, find_atom 1 src with
    | Some [X; NN], Some [B; L] =>
        let R1 := map (r1_read kn X NN L) path in
        let F1 := flat_map fst R1 in let A1 := flat_map snd R1 in
        let F2 := flat_map (r2_read kn src) path in
        let kn0 := flat_map (byte_facts kn) path ++ flat_map swar_facts path ++ kn in
        let F3 := flat_map (r3_read kn0 B L) path ++ flat_map (fill_facts kn0) path in
        let kn1 := F6 ++ F1 ++ F2 ++ F3 ++ flat_map (r14_read kn src) path ++ kn0 in
        let toks := atoms_of 3 src ++ map ST.g_args A1 in
        let F4 := flat_map (r4_tok kn1 NN L) toks in
        let kn2a := F4 ++ kn1 in
        (* [comment removed for export] *)
        let kn2 := flat_map (fun s => fst (r1_read kn2a X NN L s)) path ++ kn2a in
        let A5 := flat_map (r5_tok kn2 NN) toks in
        let SX := map (sexit kn2 path) (atoms_of 0 src) in
        let ges := atoms_of 4 src ++ map ST.g_args A5 ++ map ST.g_args (flat_map snd SX) in
        let F7 := flat_map (link_tok kn2 L ges (atoms_of 7 src)) toks in
        let F8 := str_facts kn2 path (SG.vc_log c) src toks (SG.vc_tgt c) in
        (F8 ++ flat_map fst SX ++ F7 ++ kn2, A1 ++ A5 ++ flat_map snd SX ++ flat_map (gnum1 kn2 path B L) (atoms_of 3 src))
    | _, _ => (F6 ++ kn, [])
    end.

  (* [comment removed for export] *)
  Definition ge_src (src : list ST.gatom) (A : list ST.gatom) : list (list expr) :=
    atoms_of 4 src ++ atoms_of 4 A ++ atoms_of 3 src ++ atoms_of 3 A.

  Definition tgt_pure_ok (kn : list kentry) (src A : list ST.gatom) (g : ST.gatom) : bool :=
    match ST.g_id g, ST.g_args g with
    | 3%nat, [K; V] => existsb (fun args => match args with [K'; V'] => (leq K K' && leq V V')%bool | _ => false end) (atoms_of 3 A)
    | 4%nat, [K; E] =>
        existsb (fun args => match args with
                 | [K'; E'] => (leq K K' && kimp kn (KRange E 0 BIGS) && kimp kn (KRange E' 0 BIGS) && kimp kn (KRange (esub2 E' E) 0 BIGS))%bool
                 | _ => false end) (ge_src src A)
    | 7%nat, [K; OL; ELit cc] =>
        (Z.leb 0 cc && Z.leb cc 16 && kimp kn (KRange OL 0 BIGS) &&
         (existsb (fun args => match args with
                   | [K'; E'] => (leq K K' && kimp kn (KRange E' 0 BIGS)
                                  && kimp kn (KRange (esub2 (emul 5 E') (eaddl (emul 3 OL) cc)) 0 BIGS))%bool
                   | _ => false end) (ge_src src A) ||
          existsb (fun args => match args with
                   | [K'; OL'; ELit cc'] => (leq K K' && Z.leb 0 cc' && Z.leb cc' 16 && kimp kn (KRange OL' 0 BIGS)
                                            && kimp kn (KRange (esub2 (eaddl (emul 3 OL') cc') (eaddl (emul 3 OL) cc)) 0 BIGS))%bool
                   | _ => false end) (atoms_of 7 src)))%bool
    | 8%nat, [] => existsb (fun g => match ST.g_id g, ST.g_args g with 8%nat, [] => true | _, _ => false end) A
    | 9%nat, [] => existsb (fun g => match ST.g_id g, ST.g_args g with 9%nat, [] => true | _, _ => false end) A
    | _, _ => false
    end.

  (* [comment removed for export] *)
  Definition same_addr (kn : list kentry) (a b : expr) : bool := (leq a b || SL.dtrue (decide_branch kn BC_EQ a b))%bool.
  Fixpoint newest (kn : list kentry) (a : expr) (lg : list sentry) : option (sentry * list sentry) :=
    match lg with
    | [] => None
    | s :: r => if (Nat.eqb (e_width s) 4 && same_addr kn (eaddl (a_base (e_addr s)) (a_off (e_addr s))) a)%bool then Some (s, [])
                else match newest kn a r with Some (s', pre) => Some (s', s :: pre) | None => None end
    end.
  (* [comment removed for export] *)
  Definition cell_ok (kn : list kentry) (lg : list sentry) (OC' D' BW' a : expr) : bool :=
    match newest kn a lg with
    | Some (s, pre) =>
        (kimp kn (KRange (e_val s) 0 (2 ^ 32 - 1)) && kimp kn (KRange (esub2 BW' (emul 8 (e_val s))) 1 (2 ^ 62))
         && SG.log_apart kn pre [(a, 0, ELit 4)])%bool
    | None => false
    end.

  Definition goc_ok (kn : list kentry) (lg : list sentry) (src : list ST.gatom) (g : ST.gatom) : bool :=
    match ST.g_id g, ST.g_args g with
    | 5%nat, [OC'; D'; BW'] =>
        (kimp kn (KRange OC' 1 (2 ^ 62)) && kimp kn (KRange D' 0 1023) && kimp kn (KRange BW' 0 (2 ^ 62)) &&
         ((* [comment removed for export] *)
          (leq D' (ELit 0) && cell_ok kn lg OC' D' BW' OC') ||
          existsb (fun args => match args with
          | [OC; D; BW] =>
              (leq OC OC' && kimp kn (KRange D 0 1023) && kimp kn (KRange BW 0 (2 ^ 62)) && kimp kn (KRange (esub2 BW' BW) 0 (2 ^ 62)) &&
               ((* [comment removed for export] *)
                (kimp kn (KRange (esub2 D D') 0 1023) && SG.log_apart kn lg [(OC', 0, eaddl (emul 8 D') 4)]) ||
                (* [comment removed for export] *)
                (leq D' (eaddl D 1) && SG.log_apart kn lg [(OC', 0, eaddl (emul 8 D) 4)] &&
                 cell_ok kn lg OC' D' BW' (EAlu ALU_ADD OC' (emul 8 D')))))%bool
          | _ => false end) (atoms_of 5 src)))%bool
    | _, _ => false
    end.

  (* [comment removed for export] *)
  Fixpoint newest1 (kn : list kentry) (a : expr) (lg : list sentry) : option (sentry * list sentry) :=
    match lg with
    | [] => None
    | s :: r => if (Nat.eqb (e_width s) 1 && same_addr kn (eaddl (a_base (e_addr s)) (a_off (e_addr s))) a)%bool then Some (s, [])
                else match newest1 kn a r with Some (s', pre) => Some (s', s :: pre) | None => None end
    end.

  (* [comment removed for export] *)
  Definition gia_ok (kn : list kentry) (lg : list sentry) (src : list ST.gatom) (g : ST.gatom) : bool :=
    match ST.g_id g, ST.g_args g with
    | 6%nat, [IA'; D'] =>
        (kimp kn (KRange D' 0 1023) && kimp kn (KRange IA' 1 (2 ^ 62)) &&
         (leq D' (ELit 0) ||
          existsb (fun args => match args with
            | [IA; D] =>
                (leq IA IA' && kimp kn (KRange D 0 1023) &&
                 ((kimp kn (KRange (esub2 D D') 0 1023) && SG.log_apart kn lg [(IA', 1, D')]) ||
                  (leq D' (eaddl D 1) && SG.log_apart kn lg [(IA', 1, D)] &&
                   match newest1 kn (EAlu ALU_ADD IA' D') lg with
                   | Some (s, pre) => (kimp kn (KRange (e_val s) 0 1) && SG.log_apart kn pre [(EAlu ALU_ADD IA' D', 0, ELit 1)])%bool
                   | None => false
                   end)))%bool
            | _ => false end) (atoms_of 6 src)))%bool
    | _, _ => false
    end.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition digv_at (kn : list kentry) (path : list sidecond) (B X D : expr) : bool :=
    existsb (fun s => match rrec 1 s with
                      | Some (a, v) => (leq (rel a B) X && leq D (EAlu ALU_ADD (x1 v) (ELit (-48))) && kimp kn (KRange (x1 v) 48 57))%bool
                      | None => false
                      end) path.
  (* [comment removed for export] *)
  Definition nodig_at (kn : list kentry) (path : list sidecond) (B X : expr) : bool :=
    existsb (fun s => match rrec 1 s with
                      | Some (a, v) => (leq (rel a B) X && kimp kn (KRange (dig_expr v) 10 (2 ^ 64 - 1)))%bool
                      | None => false
                      end) path.
  (* [comment removed for export] *)
  Definition zero_at (kn : list kentry) (path : list sidecond) (B X : expr) : bool :=
    existsb (fun s => match rrec 1 s with
                      | Some (a, v) => (leq (rel a B) X && (kimp kn (KRange (x1 v) 48 48) || kimp kn (KRange (EVar v) 48 48)))%bool
                      | None => false
                      end) path.
  (* [comment removed for export] *)
  Definition acc_step (X X' D : expr) : bool :=
    (leq (nsub X' (emul 10 X)) D || leq (nsub X' (emul 10 X)) (EAlu ALU_AND D (ELit 255)))%bool.
  Definition gdb_step (src : list ST.gatom) (P X X' : expr) : bool :=
    existsb (fun g => match g with [P2; D] => (leq P2 P && acc_step X X' D)%bool | _ => false end) (atoms_of 11 src).
  (* [comment removed for export] *)
  Definition gdv_ok (kn : list kentry) (src : list ST.gatom) (L : expr) (args : list expr) : bool :=
    match args with
    | [S0'; P'; X'] =>
        ((leq P' S0' && leq X' (ELit 0) && kimp kn (KRange S0' 0 MF) && kimp kn (KRange (esub2 L S0') 0 MF)) ||
         existsb (fun a => match a with
                  | [S0; P; X] => (leq S0' S0 && ((leq P' P && leq X' X) || (leq P' (eaddl P 1) && gdb_step src P X X')))%bool
                  | _ => false end) (atoms_of 10 src))%bool
    | _ => false
    end.
  (* [comment removed for export] *)
  Definition gdb_ok (kn : list kentry) (path : list sidecond) (src : list ST.gatom) (B L : expr) (args : list expr) : bool :=
    match args with
    | [P'; D'] =>
        ((kimp kn (KRange P' 0 MF) && kimp kn (KRange (esub2 (eaddl L 63) P') 0 (MF + 64)) && digv_at kn path B P' D') ||
         existsb (fun a => match a with [P; D] => (leq P' P && leq D' D)%bool | _ => false end) (atoms_of 11 src))%bool
    | _ => false
    end.
  (* [comment removed for export] *)
  Definition gdz_adv (kn : list kentry) (path : list sidecond) (B S2 S2' : expr) : bool :=
    (leq S2' S2 || (leq S2' (eaddl S2 1) && zero_at kn path B S2))%bool.
  Definition gdz_ok (kn : list kentry) (path : list sidecond) (src : list ST.gatom) (B : expr) (args : list expr) : bool :=
    match args with
    | [S0'; S2'; P'; X'] =>
        (existsb (fun a => match a with
                  | [S0; S2; P; X] => (leq S0' S0 && leq P' P && leq X' X && gdz_adv kn path B S2 S2')%bool
                  | _ => false end) (atoms_of 12 src) ||
         existsb (fun a => match a with
                  | [S0; P; X] => (leq S0' S0 && gdz_adv kn path B S0 S2' &&
                                  ((leq P' P && leq X' X && nodig_at kn path B P) ||
                                   (leq P' (eaddl P 1) && nodig_at kn path B P' && gdb_step src P X X')))%bool
                  | _ => false end) (atoms_of 10 src))%bool
    | _ => false
    end.
  Definition gd_ok (kn : list kentry) (path : list sidecond) (src : list ST.gatom) (g : ST.gatom) : bool :=
    match find_atom 1 src with
    | Some [B; L] =>
        match ST.g_id g with
        | 10%nat => gdv_ok kn src L (ST.g_args g)
        | 11%nat => gdb_ok kn path src B L (ST.g_args g)
        | 12%nat => gdz_ok kn path src B (ST.g_args g)
        | _ => false
        end
    | _ => false
    end.
  (* [comment removed for export] *)
  Definition le18 (kn : list kentry) (L A P : expr) : bool :=
    (kimp kn (KRange (esub2 P A) 0 18) ||
     (kimp kn (KRange (esub2 (eaddl A 18) P) 0 (2 ^ 62)) && kimp kn (KRange L 0 MF)))%bool.
  Definition E18 : Z := 999999999999999999.
  Definition gd_fact (kn : list kentry) (src : list ST.gatom) (K : kentry) : bool :=
    match find_atom 1 src with Some [_; L] =>
    match K with
    | KRange X' lo hi =>
        (Z.eqb lo 0 && Z.eqb hi E18 &&
         (existsb (fun a => match a with
                   | [S0; S2; P; X] => (leq X' X && le18 kn L S2 P)%bool
                   | _ => false end) (atoms_of 12 src) ||
          existsb (fun a => match a with
                   | [S0; P; X] => ((leq X' X && le18 kn L S0 P) ||
                                   (gdb_step src P X X' && le18 kn L S0 (eaddl P 1)))%bool
                   | _ => false end) (atoms_of 10 src)))%bool
    | _ => false
    end
    | _ => false
    end.

  Definition is_unk (K : kentry) : bool := match K with KUnk _ _ => true | _ => false end.
  Definition is_pure2 (K : kentry) : bool := match K with KRange _ _ _ | KAlign _ _ | KDisj _ _ _ _ => true | _ => false end.

  Definition wvc_ok (c : SG.vc) : bool :=
    let '(kn2, A) := derive c in
    (forallb (fun g => match ST.g_id g with
                       | 0%nat => str_tgt_ok kn2 (SG.vc_path c) (SG.vc_log c) (SG.vc_src c) (atoms_of 3 (SG.vc_src c) ++ atoms_of 3 A) g
                       | 5%nat => goc_ok kn2 (SG.vc_log c) (SG.vc_src c) g
                       | 6%nat => gia_ok kn2 (SG.vc_log c) (SG.vc_src c) g
                       | 10%nat | 11%nat | 12%nat => gd_ok kn2 (SG.vc_path c) (SG.vc_src c) g
                       | _ => tgt_pure_ok kn2 (SG.vc_src c) A g
                       end) (SG.vc_tgt c) &&
     forallb (fun K => if is_unk K then ST.kin K (SG.vc_kn c)
                       else (is_pure2 K && (kimp kn2 K || match find_atom 1 (SG.vc_src c) with
                                                         | Some [B; L] => room_ok kn2 L K | _ => false end
                                            || gd_fact kn2 (SG.vc_src c) K))%bool)
             (SG.vc_facts c))%bool.
End Chk.
