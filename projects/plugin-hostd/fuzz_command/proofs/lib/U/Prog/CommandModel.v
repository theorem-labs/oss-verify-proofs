From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Import PropExec MState Mem Exec Frame.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U Require Import Img0.
Import ListNotations.
Open Scope Z_scope.

Definition NUL : byte := Z_to_bv 8 0.
Definition str (l : list Z) : list byte := map (Z_to_bv 8) l.

Definition cstr_at (m : word -> option byte) (p : Z) (s : list byte) : Prop :=
  bytes_at rsegs m p (s ++ [NUL]) /\ ~ In NUL s.

Definition IMG_END : Z := 0x54f98.

Definition GOT_GREC : Z := 0x22cf8.
Definition G_REC : Z := 0x34028.
Definition GOT_GQUIT : Z := 0x22d10.
Definition GOT_GUARD : Z := 0x22d40.
Definition GUARD : Z := 0x54730.
Definition G_QUIT : Z := 0x343e8.

Definition REC_NCALLS : Z := 8.
Definition REC_CALLS : Z := 16.
Definition REC_CALL_SIZE : Z := 56.
Definition REC_ANSWER : Z := 912.
Definition REC_NREPLIES : Z := 920.
Definition REC_REPLY : Z := 928.
Definition REC_REPLY_SIZE : Z := 936.
Definition REC_STATE : Z := 944.
Definition REC_HOST : Z := 952.

Definition CALL_FN : Z := 0.
Definition CALL_NARGS : Z := 4.
Definition CALL_ARGS : Z := 8.

Definition WORDS_TEXT : Z := 0.
Definition WORDS_COPY : Z := 8.
Definition WORDS_W : Z := 16.
Definition WORDS_N : Z := 24.

Definition S_DASH : list byte := str [45].
Definition S_OWN : list byte := str [111; 119; 110].
Definition S_DEFAULT : list byte := str [100; 101; 102; 97; 117; 108; 116].
Definition S_POOL : list byte := str [112; 111; 111; 108; 58].
Definition S_VERDICT : list byte := str [118; 101; 114; 100; 105; 99; 116; 61].
Definition S_QUIT : list byte := str [113; 117; 105; 116].

Definition has_prefix (s k : list byte) : Prop := firstn (length k) s = k.

Definition bytes_eqb (a b : list byte) : bool :=
  if list_eq_dec Z.eq_dec (map bv_unsigned a) (map bv_unsigned b) then true else false.
Definition prefixb (s k : list byte) : bool := bytes_eqb (firstn (length k) s) k.

Definition LIT_DASH : Z := 0x108b0.
Definition LIT_OWN : Z := 0x10678.
Definition LIT_DEFAULT : Z := 0x107c3.
Definition LIT_POOL : Z := 0x10a13.
Definition LIT_VERDICT : Z := 0x107cb.
Definition LIT_SPTAB : Z := 0x1064c.
Definition LIT_QUIT : Z := 0x109ef.

Definition outside_stack (lo S a n : Z) : Prop := disjoint_from [(lo, S)] a n.

Definition word_slot (m : word -> option byte) (lo S : Z) (A : Z) (p : word) (s : list byte) : Prop :=
  bytes_at rsegs m A (le8 p) /\ outside_stack lo S A 8 /\
  cstr_at m (bv_unsigned p) s /\ outside_stack lo S (bv_unsigned p) (Z.of_nat (length s) + 1).

Definition void_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (m : word -> option byte) (ms' : machine_state) : Prop :=
  exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
    ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                  s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
             F (ret_pc ra) fc None m' (seg_rom rsegs) /\
    munch [(lo, bv_unsigned sp)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\
    stk rsegs m' lo (bv_unsigned sp).

Definition bz (b : byte) : Z := bv_unsigned b.

Fixpoint skip_sp (s : list byte) : list byte :=
  match s with
  | b :: s' => if bz b =? 32 then skip_sp s' else s
  | [] => []
  end.

Fixpoint item_scan (d : Z) (s : list byte) : list byte * list byte :=
  match s with
  | [] => ([], [])
  | b :: s' =>
      if (d =? 0) && (bz b =? 32) then ([], s)
      else
        let d' := if (bz b =? 60) || (bz b =? 91) then d + 1
                  else if ((bz b =? 62) || (bz b =? 93)) && (0 <? d) then d - 1 else d in
        let (it, rest) := item_scan d' s' in (b :: it, rest)
  end.

Fixpoint items_f (fuel : nat) (s : list byte) : list (list byte) :=
  match fuel with
  | O => []
  | S f =>
      match skip_sp s with
      | [] => []
      | s1 => let (it, rest) := item_scan 0 s1 in it :: items_f f rest
      end
  end.

Definition shape_items (s : list byte) : list (list byte) := items_f (length s) s.

Fixpoint word_len (r : list byte) : nat :=
  match r with
  | b :: r' => if bz b =? 32 then O else S (word_len r')
  | [] => O
  end.

Definition has_lt (it : list byte) : bool := existsb (fun b => bz b =? 60) it.

Fixpoint reply_matches_items (its : list (list byte)) (r : list byte) : bool :=
  match its with
  | [] => match r with [] => true | _ => false end
  | it :: its' =>
      let w := word_len r in
      if Nat.eqb w 0 then false
      else if negb (has_lt it) && negb (bytes_eqb it (firstn w r)) then false
      else match skipn w r with
           | [] => reply_matches_items its' []
           | _ :: [] => false
           | _ :: r'' => reply_matches_items its' r''
           end
  end.

Definition reply_matches (shape reply : list byte) : bool :=
  reply_matches_items (shape_items shape) reply.
