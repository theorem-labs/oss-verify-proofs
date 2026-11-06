(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import HeapCeil.
From OSSVerify.Proofs.boost_beast.http_request.lib.Lib Require Import Tac Image ZBridge SysStep SFModel CellsX Arr TacX.
From OSSVerify.Proofs.boost_beast.http_request.lib.Bo Require Import BSegs AsShadow AsConst AsIface AsIface6 AsStack0 AXRep AXRep2 AXPRep.
From OSSVerify.Proofs.boost_beast.http_request.lib.Ub Require Import XUbsan.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)

Fixpoint lzeqb (a b : list Z) : bool :=
  match a, b with
  | [], [] => true
  | x :: a', y :: b' => (x =? y) && lzeqb a' b'
  | _, _ => false
  end.

Lemma lzeqb_eq : forall a b, lzeqb a b = true <-> a = b.
Proof.
  induction a as [|x a IH]; intros [|y b]; cbn; split; intros H; try discriminate; try reflexivity.
  - apply andb_prop in H. destruct H as [H1 H2]. apply Z.eqb_eq in H1. apply IH in H2. subst. reflexivity.
  - injection H as -> ->. rewrite Z.eqb_refl. cbn. apply IH. reflexivity.
Qed.
Lemma lzeqb_neq : forall a b, lzeqb a b = false <-> a <> b.
Proof.
  intros a b. destruct (lzeqb a b) eqn:E; split; intros H; try discriminate.
  - apply lzeqb_eq in E. contradiction.
  - intros C. apply lzeqb_eq in C. rewrite C in E. discriminate.
  - reflexivity.
Qed.
Lemma lzeqb_length : forall a b, length a <> length b -> lzeqb a b = false.
Proof. intros a b H. apply lzeqb_neq. intros ->. apply H. reflexivity. Qed.

(* [comment removed for export] *)
Definition L_CL : list Z := [67; 76].                                       Definition A_CL : Z := 0x26b80.
Definition L_IND : list Z := [73; 78; 68].                                  Definition A_IND : Z := 0x26ba0.
Definition L_ECKOUT : list Z := [69; 67; 75; 79; 85; 84].                   Definition A_ECKOUT : Z := 0x26bc0.
Definition L_NNECT : list Z := [78; 78; 69; 67; 84].                        Definition A_NNECT : Z := 0x26be0.
Definition L_PY : list Z := [80; 89].                                       Definition A_PY : Z := 0x26c00.
Definition L_ELETE : list Z := [69; 76; 69; 84; 69].                        Definition A_ELETE : Z := 0x26c20.
Definition L_ET : list Z := [69; 84].                                       Definition A_ET : Z := 0x26c40.
Definition L_EAD : list Z := [69; 65; 68].                                  Definition A_EAD : Z := 0x26c60.
Definition L_INK : list Z := [73; 78; 75].                                  Definition A_INK : Z := 0x26c80.
Definition L_OCK : list Z := [79; 67; 75].                                  Definition A_OCK : Z := 0x26ca0.
Definition L_SEARCH : list Z := [83; 69; 65; 82; 67; 72].                   Definition A_SEARCH : Z := 0x26cc0.
Definition L_RGE : list Z := [82; 71; 69].                                  Definition A_RGE : Z := 0x26ce0.
Definition L_ACTIVITY : list Z := [65; 67; 84; 73; 86; 73; 84; 89].         Definition A_ACTIVITY : Z := 0x26d00.
Definition L_ALENDAR : list Z := [65; 76; 69; 78; 68; 65; 82].              Definition A_ALENDAR : Z := 0x26d20.
Definition L_OL : list Z := [79; 76].                                       Definition A_OL : Z := 0x26d40.
Definition L_VE : list Z := [86; 69].                                       Definition A_VE : Z := 0x26d60.
Definition L_OTIFY : list Z := [79; 84; 73; 70; 89].                        Definition A_OTIFY : Z := 0x26d80.
Definition L_PTIONS : list Z := [80; 84; 73; 79; 78; 83].                   Definition A_PTIONS : Z := 0x26da0.
Definition L_TCH : list Z := [84; 67; 72].                                  Definition A_TCH : Z := 0x26dc0.
Definition L_ST : list Z := [83; 84].                                       Definition A_ST : Z := 0x26de0.
Definition L_OPFIND : list Z := [79; 80; 70; 73; 78; 68].                   Definition A_OPFIND : Z := 0x26e00.
Definition L_OPPATCH : list Z := [79; 80; 80; 65; 84; 67; 72].              Definition A_OPPATCH : Z := 0x26e20.
Definition L_BIND : list Z := [66; 73; 78; 68].                             Definition A_BIND : Z := 0x26e40.
Definition L_PORT : list Z := [80; 79; 82; 84].                             Definition A_PORT : Z := 0x26e60.
Definition L_EARCH : list Z := [69; 65; 82; 67; 72].                        Definition A_EARCH : Z := 0x26e80.
Definition L_UBSCRIBE : list Z := [85; 66; 83; 67; 82; 73; 66; 69].         Definition A_UBSCRIBE : Z := 0x26ea0.
Definition L_RACE : list Z := [82; 65; 67; 69].                             Definition A_RACE : Z := 0x26ec0.
Definition L_LINK : list Z := [76; 73; 78; 75].                             Definition A_LINK : Z := 0x26ee0.
Definition L_LOCK : list Z := [76; 79; 67; 75].                             Definition A_LOCK : Z := 0x26f00.
Definition L_SUBSCRIBE : list Z := [83; 85; 66; 83; 67; 82; 73; 66; 69].    Definition A_SUBSCRIBE : Z := 0x26f20.
(* [comment removed for export] *)
Definition L_T : list Z := [84].

(* [comment removed for export] *)
Definition VLITS : list (Z * list Z) :=
  [(A_CL, L_CL);
   (A_IND, L_IND);
   (A_ECKOUT, L_ECKOUT);
   (A_NNECT, L_NNECT);
   (A_PY, L_PY);
   (A_ELETE, L_ELETE);
   (A_ET, L_ET);
   (A_EAD, L_EAD);
   (A_INK, L_INK);
   (A_OCK, L_OCK);
   (A_SEARCH, L_SEARCH);
   (A_RGE, L_RGE);
   (A_ACTIVITY, L_ACTIVITY);
   (A_ALENDAR, L_ALENDAR);
   (A_OL, L_OL);
   (A_VE, L_VE);
   (A_OTIFY, L_OTIFY);
   (A_PTIONS, L_PTIONS);
   (A_TCH, L_TCH);
   (A_ST, L_ST);
   (A_OPFIND, L_OPFIND);
   (A_OPPATCH, L_OPPATCH);
   (A_BIND, L_BIND);
   (A_PORT, L_PORT);
   (A_EARCH, L_EARCH);
   (A_UBSCRIBE, L_UBSCRIBE);
   (A_RACE, L_RACE);
   (A_LINK, L_LINK);
   (A_LOCK, L_LOCK);
   (A_SUBSCRIBE, L_SUBSCRIBE)].

(* [comment removed for export] *)
Definition verb_of (l : list Z) : Z :=
  match l with
  | [] => 0
  | c :: r =>
    if c =? 65 then (if lzeqb r L_CL then 20 else 0)
    else if c =? 66 then (if lzeqb r L_IND then 17 else 0)
    else if c =? 67 then
      match r with
      | [] => 0
      | c2 :: r2 =>
        if c2 =? 72 then (if lzeqb r2 L_ECKOUT then 23 else 0)
        else if c2 =? 79 then (if lzeqb r2 L_NNECT then 6 else if lzeqb r2 L_PY then 9 else 0)
        else 0
      end
    else if c =? 68 then (if lzeqb r L_ELETE then 1 else 0)
    else if c =? 71 then (if lzeqb r L_ET then 2 else 0)
    else if c =? 72 then (if lzeqb r L_EAD then 3 else 0)
    else if c =? 76 then (if lzeqb r L_INK then 32 else if lzeqb r L_OCK then 10 else 0)
    else if c =? 77 then
      match r with
      | [] => 0
      | c2 :: r2 =>
        if c2 =? 45 then (if lzeqb r2 L_SEARCH then 25 else 0)
        else if c2 =? 69 then (if lzeqb r2 L_RGE then 24 else 0)
        else if c2 =? 75 then
          (if lzeqb r2 L_ACTIVITY then 22 else
           match r2 with
           | [] => 0
           | c3 :: r3 => if c3 =? 67 then (if lzeqb r3 L_ALENDAR then 31 else if lzeqb r3 L_OL then 11 else 0) else 0
           end)
        else if c2 =? 79 then (if lzeqb r2 L_VE then 12 else 0)
        else 0
      end
    else if c =? 78 then (if lzeqb r L_OTIFY then 26 else 0)
    else if c =? 79 then (if lzeqb r L_PTIONS then 7 else 0)
    else if c =? 80 then
      match r with
      | [] => 0
      | c2 :: r2 =>
        if c2 =? 65 then (if lzeqb r2 L_TCH then 29 else 0)
        else if c2 =? 79 then (if lzeqb r2 L_ST then 4 else 0)
        else if c2 =? 82 then (if lzeqb r2 L_OPFIND then 13 else if lzeqb r2 L_OPPATCH then 14 else 0)
        else if c2 =? 85 then (if lzeqb r2 L_RGE then 30 else if lzeqb r2 L_T then 5 else 0)
        else 0
      end
    else if c =? 82 then
      match r with
      | [] => 0
      | c2 :: r2 => if c2 =? 69 then (if lzeqb r2 L_BIND then 18 else if lzeqb r2 L_PORT then 21 else 0) else 0
      end
    else if c =? 83 then (if lzeqb r L_EARCH then 15 else if lzeqb r L_UBSCRIBE then 27 else 0)
    else if c =? 84 then (if lzeqb r L_RACE then 8 else 0)
    else if c =? 85 then
      match r with
      | [] => 0
      | c2 :: r2 => if c2 =? 78 then
                      (if lzeqb r2 L_BIND then 19 else if lzeqb r2 L_LINK then 33
                       else if lzeqb r2 L_LOCK then 16 else if lzeqb r2 L_SUBSCRIBE then 28 else 0)
                    else 0
      end
    else 0
  end.

Ltac range_ifs := repeat (lazymatch goal with |- 0 <= (if ?b then _ else _) <= 33 => destruct b | _ => fail end); try lia.
Lemma verb_of_range : forall l, 0 <= verb_of l <= 33.
Proof.
  intros [|c r]; cbn [verb_of]; [lia|].
  repeat (lazymatch goal with
          | |- 0 <= (if ?b then _ else _) <= 33 => destruct b
          | |- 0 <= match ?r with _ => _ end <= 33 => destruct r
          | _ => fail end); lia.
Qed.

(* [comment removed for export] *)
Definition VERB_NAMES : list (list Z * Z) :=
  [([68;69;76;69;84;69], 1); ([71;69;84], 2); ([72;69;65;68], 3); ([80;79;83;84], 4); ([80;85;84], 5);
   ([67;79;78;78;69;67;84], 6); ([79;80;84;73;79;78;83], 7); ([84;82;65;67;69], 8); ([67;79;80;89], 9);
   ([76;79;67;75], 10); ([77;75;67;79;76], 11); ([77;79;86;69], 12); ([80;82;79;80;70;73;78;68], 13);
   ([80;82;79;80;80;65;84;67;72], 14); ([83;69;65;82;67;72], 15); ([85;78;76;79;67;75], 16); ([66;73;78;68], 17);
   ([82;69;66;73;78;68], 18); ([85;78;66;73;78;68], 19); ([65;67;76], 20); ([82;69;80;79;82;84], 21);
   ([77;75;65;67;84;73;86;73;84;89], 22); ([67;72;69;67;75;79;85;84], 23); ([77;69;82;71;69], 24);
   ([77;45;83;69;65;82;67;72], 25); ([78;79;84;73;70;89], 26); ([83;85;66;83;67;82;73;66;69], 27);
   ([85;78;83;85;66;83;67;82;73;66;69], 28); ([80;65;84;67;72], 29); ([80;85;82;71;69], 30);
   ([77;75;67;65;76;69;78;68;65;82], 31); ([76;73;78;75], 32); ([85;78;76;73;78;75], 33)].
Lemma verb_of_names : forallb (fun p => verb_of (fst p) =? snd p) VERB_NAMES = true.
Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Lemma verb_of_A : forall r, verb_of (65 :: r) = (if lzeqb r L_CL then 20 else 0). Proof. reflexivity. Qed.
Lemma verb_of_B : forall r, verb_of (66 :: r) = (if lzeqb r L_IND then 17 else 0). Proof. reflexivity. Qed.
Lemma verb_of_C : forall r, verb_of (67 :: r) =
  match r with [] => 0 | c2 :: r2 =>
    if c2 =? 72 then (if lzeqb r2 L_ECKOUT then 23 else 0)
    else if c2 =? 79 then (if lzeqb r2 L_NNECT then 6 else if lzeqb r2 L_PY then 9 else 0) else 0 end.
Proof. reflexivity. Qed.
Lemma verb_of_D : forall r, verb_of (68 :: r) = (if lzeqb r L_ELETE then 1 else 0). Proof. reflexivity. Qed.
Lemma verb_of_G : forall r, verb_of (71 :: r) = (if lzeqb r L_ET then 2 else 0). Proof. reflexivity. Qed.
Lemma verb_of_H : forall r, verb_of (72 :: r) = (if lzeqb r L_EAD then 3 else 0). Proof. reflexivity. Qed.
Lemma verb_of_L : forall r, verb_of (76 :: r) = (if lzeqb r L_INK then 32 else if lzeqb r L_OCK then 10 else 0).
Proof. reflexivity. Qed.
Lemma verb_of_M : forall r, verb_of (77 :: r) =
  match r with [] => 0 | c2 :: r2 =>
    if c2 =? 45 then (if lzeqb r2 L_SEARCH then 25 else 0)
    else if c2 =? 69 then (if lzeqb r2 L_RGE then 24 else 0)
    else if c2 =? 75 then
      (if lzeqb r2 L_ACTIVITY then 22 else
       match r2 with [] => 0
       | c3 :: r3 => if c3 =? 67 then (if lzeqb r3 L_ALENDAR then 31 else if lzeqb r3 L_OL then 11 else 0) else 0 end)
    else if c2 =? 79 then (if lzeqb r2 L_VE then 12 else 0) else 0 end.
Proof. reflexivity. Qed.
Lemma verb_of_N : forall r, verb_of (78 :: r) = (if lzeqb r L_OTIFY then 26 else 0). Proof. reflexivity. Qed.
Lemma verb_of_O : forall r, verb_of (79 :: r) = (if lzeqb r L_PTIONS then 7 else 0). Proof. reflexivity. Qed.
Lemma verb_of_P : forall r, verb_of (80 :: r) =
  match r with [] => 0 | c2 :: r2 =>
    if c2 =? 65 then (if lzeqb r2 L_TCH then 29 else 0)
    else if c2 =? 79 then (if lzeqb r2 L_ST then 4 else 0)
    else if c2 =? 82 then (if lzeqb r2 L_OPFIND then 13 else if lzeqb r2 L_OPPATCH then 14 else 0)
    else if c2 =? 85 then (if lzeqb r2 L_RGE then 30 else if lzeqb r2 L_T then 5 else 0) else 0 end.
Proof. reflexivity. Qed.
Lemma verb_of_R : forall r, verb_of (82 :: r) =
  match r with [] => 0 | c2 :: r2 =>
    if c2 =? 69 then (if lzeqb r2 L_BIND then 18 else if lzeqb r2 L_PORT then 21 else 0) else 0 end.
Proof. reflexivity. Qed.
Lemma verb_of_S : forall r, verb_of (83 :: r) = (if lzeqb r L_EARCH then 15 else if lzeqb r L_UBSCRIBE then 27 else 0).
Proof. reflexivity. Qed.
Lemma verb_of_T : forall r, verb_of (84 :: r) = (if lzeqb r L_RACE then 8 else 0). Proof. reflexivity. Qed.
Lemma verb_of_U : forall r, verb_of (85 :: r) =
  match r with [] => 0 | c2 :: r2 =>
    if c2 =? 78 then (if lzeqb r2 L_BIND then 19 else if lzeqb r2 L_LINK then 33
                      else if lzeqb r2 L_LOCK then 16 else if lzeqb r2 L_SUBSCRIBE then 28 else 0) else 0 end.
Proof. reflexivity. Qed.
(* [comment removed for export] *)
Lemma verb_of_other : forall c r, (c < 65 \/ 85 < c \/ In c [69; 70; 73; 74; 75; 81]) -> verb_of (c :: r) = 0.
Proof.
  intros c r H. cbn [verb_of].
  repeat (lazymatch goal with
          | |- (if c =? ?k then _ else _) = 0 =>
              let E := fresh "E" in destruct (Z.eqb_spec c k) as [E|E]; [exfalso; subst c; cbn in H; lia|]
          | _ => fail end).
  reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Section HCW.
  Context {HCEIL : HeapCeil}.

Definition ASTRING_TO_VERB_STACK : Z := 48 + ABCMP_STACK.   (* [comment removed for export] *)

Definition verb_post_v (v : Z) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (P : Z) (bs : list byte) (lo shi : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz v) a1 a2 a3 a4 a5 a6 a7
                  s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch [(lo, bv_unsigned sp)]%Z m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo (bv_unsigned sp)
    /\ bytes_at bsegs m' P bs
    /\ ACONST m' /\ stack0 m' lo shi                                                     (* [comment removed for export] *)
    /\ accessible m' P (Z.of_nat (length bs)) /\ shvis m' P (P + Z.of_nat (length bs)).

Definition string_to_verb_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (P : Z) (bs : list byte) (lo shi : Z) (m : mem) : machine_state -> Prop :=
  verb_post_v (verb_of (zbytes bs)) ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc P bs lo shi m.

Definition string_to_verb_stmt : Prop :=
  forall (P : Z) (bs : list byte) (lo shi : Z)
    ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem),
  bytes_at bsegs m P bs -> P + Z.of_nat (length bs) < 2^64 ->
  stk bsegs m lo (bv_unsigned sp) -> lo + ASTRING_TO_VERB_STACK <= bv_unsigned sp -> aceil <= lo ->   (* [comment removed for export] *)
  (bv_unsigned sp <= P \/ P + Z.of_nat (length bs) <= lo) ->
  mem_inv bsegs m ->
  (* [comment removed for export] *)
  bv_unsigned sp mod 16 = 0 ->
  ACONST m -> stack0 m lo shi -> bv_unsigned sp <= shi ->
  accessible m P (Z.of_nat (length bs)) -> shvis m P (P + Z.of_nat (length bs)) -> in_app_mem P (P + Z.of_nat (length bs)) ->
  0 < P ->                                  (* [comment removed for export] *)
  evt bsegs (string_to_verb_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc P bs lo shi m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz P) (wz (Z.of_nat (length bs))) a2 a3 a4 a5 a6 a7
              s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 P_A_STRING_TO_VERB) fc None m (seg_rom bsegs)).

End HCW.
