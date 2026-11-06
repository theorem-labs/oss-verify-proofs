From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Import PropExec MState Mem Exec Frame Image.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U Require Import Img0.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import CommandModel check_reply_c strcspn_c.
Import ListNotations.
Open Scope Z_scope.

Definition CHECK_ARITY : Z := 0x14614.
Definition CHECK_ARITY_K : Z := 240.
Definition G_PARSED : Z := 0x226c0.
Definition UNB : Z := 2147483647.
Definition REC_BROADCAST : Z := 5.

Definition parsed_rows : list (Z * Z * Z) :=
  [(0x1045b, 0x106c8, 0);
   (0x1060b, 0x1045f, 0);
   (0x103c1, 0x10687, 0);
   (0x10781, 0x107da, 0);
   (0x10792, 0x10896, 0);
   (0x10692, 0x1069d, 0);
   (0x1059a, 0x1098a, 0);
   (0x10705, 0x10300, 0);
   (0x109a1, 0x10460, 0);
   (0x1072e, 0x106bc, 0);
   (0x104ed, 0x10298, 0);
   (0x1064f, 0x1086c, 0);
   (0x1067c, 0x10687, 0);
   (0x104e2, 0x10617, 0);
   (0x104fc, 0x1093e, 0);
   (0x1041e, 0x1065a, 0);
   (0x10375, 0x1086c, 0);
   (0x109a9, 0x1086c, 0);
   (0x10821, 0x1066c, 1);
   (0x10962, 0x105fd, 1);
   (0x109f4, 0x10589, 1);
   (0x109ef, 0x109ef, 1)].

Definition g_parsed_bytes : list byte :=
  concat (map (fun r => match r with (na, sy, fm) =>
    le8 (Z_to_bv 64 na) ++ le8 (Z_to_bv 64 sy) ++ le4 (Z_to_bv 64 fm) ++ [NUL; NUL; NUL; NUL] end) parsed_rows).

Fixpoint has_dots (l : list byte) : bool :=
  match l with
  | [] => false
  | a :: l' =>
      match l' with
      | b :: c :: _ => (bz a =? 46) && (bz b =? 46) && (bz c =? 46)
      | _ => false
      end || has_dots l'
  end.

Definition bracketed (it : list byte) : bool :=
  match it with
  | [] => false
  | a :: _ => (bz a =? 91) && (bz (last it a) =? 93)
  end.

Definition bump (mx : Z) : Z := if mx =? UNB then mx else mx + 1.

Fixpoint arity_items (its : list (list byte)) (mn mx : Z) : Z * Z :=
  match its with
  | [] => (mn, mx)
  | it :: rest =>
      if bytes_eqb it (str [124]) then
        match rest with
        | [] => (mn, mx)
        | _ :: rest' => arity_items rest' mn mx
        end
      else if bracketed it then
        (if has_dots it then arity_items rest mn UNB else arity_items rest mn (bump mx))
      else arity_items rest (mn + 1) (bump mx)
  end.

Fixpoint format_arity_items (its : list (list byte)) (mn mx : Z) : Z * Z :=
  match its with
  | [] => (mn, mx)
  | it :: rest =>
      if bytes_eqb it (str [46; 46; 46]) then format_arity_items rest mn UNB
      else format_arity_items rest (mn + 1) (bump mx)
  end.

Definition row_arity (sy : list byte) (fm : Z) : Z * Z :=
  if fm =? 0 then arity_items (shape_items sy) 0 0
  else match shape_items sy with [] => (0, 0) | _ :: its => format_arity_items its 0 0 end.

Fixpoint row_find (v : list byte) (rows : list (Z * Z * Z)) : option (Z * Z) :=
  match rows with
  | [] => None
  | (na, sy, fm) :: rows' => if bytes_eqb (img_str na) v then Some (row_arity (img_str sy) fm) else row_find v rows'
  end.

Definition verb_prefix (v f : list byte) : bool :=
  Nat.eqb (cspn_len (str [32; 9]) v) (length f) && prefixb v f.

Definition passed_on_m (v : list byte) : bool :=
  bytes_eqb v (img_str 0x1067c) || bytes_eqb v (img_str 0x104e2) ||
  verb_prefix v (str [99; 111; 110; 110; 101; 99; 116]) ||
  verb_prefix v (str [100; 105; 115; 99; 111; 110; 110; 101; 99; 116]).

Definition arity_ok (t : Z) (v : list byte) (q nc fn0 : Z) : Prop :=
  t = 0 \/ (q = 0 /\ nc = 0) \/ (0 < nc /\ fn0 = REC_BROADCAST /\ passed_on_m v = true) \/
  match row_find v parsed_rows with
  | None => True
  | Some (mn, mx) => mn <= Z.min t 64 - 1 <= mx
  end.

Definition check_arity_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z)
         (t q nc fn0 : Z) (ww p0 : word) (v : list byte) (can : word),
    mem_inv rsegs m ->
    stk rsegs m lo (bv_unsigned sp) -> lo + CHECK_ARITY_K <= bv_unsigned sp -> IMG_END <= lo ->
    bytes_at rsegs m GOT_GUARD (le8 (Z_to_bv 64 GUARD)) -> bytes_at rsegs m GUARD (le8 can) ->
    bytes_at rsegs m G_PARSED g_parsed_bytes ->
    bytes_at rsegs m GOT_GREC (le8 (Z_to_bv 64 G_REC)) ->
    0 <= nc <= 16 -> bytes_at rsegs m (G_REC + REC_NCALLS) (le4 (Z_to_bv 64 nc)) ->
    (0 < nc -> 0 <= fn0 < 26 /\ bytes_at rsegs m (G_REC + REC_CALLS + CALL_FN) (le4 (Z_to_bv 64 fn0))) ->
    bytes_at rsegs m GOT_GQUIT (le8 (Z_to_bv 64 G_QUIT)) ->
    0 <= q < 2^32 -> bytes_at rsegs m G_QUIT (le4 (Z_to_bv 64 q)) ->
    0 <= t <= 4096 ->
    bv_unsigned a0 mod 8 = 0 ->
    bytes_at rsegs m (bv_unsigned a0 + WORDS_N) (le4 (Z_to_bv 64 t)) ->
    outside_stack lo (bv_unsigned sp) (bv_unsigned a0 + WORDS_N) 4 ->
    bytes_at rsegs m (bv_unsigned a0 + WORDS_W) (le8 ww) ->
    outside_stack lo (bv_unsigned sp) (bv_unsigned a0 + WORDS_W) 8 ->
    (0 < t -> word_slot m lo (bv_unsigned sp) (bv_unsigned ww) p0 v) ->
    (0 < t -> bv_unsigned ww <> 0 /\ bv_unsigned ww mod 8 = 0) ->
    arity_ok t v q nc fn0 ->
    evt rsegs (void_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 CHECK_ARITY) fc None m (seg_rom rsegs)).

Example arity_table :
  map (fun r => match r with (na, sy, fm) => row_arity (img_str sy) fm end) parsed_rows =
  [(2, 4); (0, 0); (1, 1); (0, 1); (1, 1); (2, 2); (2, 2); (3, 3); (3, 4); (1, 1); (2, 2); (1, 1); (1, 1); (2, 2);
   (2, UNB); (1, 1); (1, 1); (1, 1); (1, 1); (2, 2); (2, 2); (0, 0)].
Proof. vm_compute. reflexivity. Qed.
