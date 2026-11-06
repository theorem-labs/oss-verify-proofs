(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cjson/cjson_read_fuzzer/lib/P/F_vsnprintf.v, with its module paths and module names changed; 710 of its 816 lines of code are new or changed and 1295 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_boxreg/lib/CJ/RL/GX/Printf_text.v, with its module paths and module names changed; 57 of its 133 lines of code are new or changed and 740 lines of the source are left out. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib Require MemNorm.
Import ListNotations.
Open Scope Z_scope.

Inductive pf_piece : Type := PLit (b : Z) | Pd | Pc | Px04 | Px02 | Pllu | Ps | Pps.
Inductive pf_arg : Type := AInt (v : Z) | AU64 (u : Z) | APtr (s : list Z).

Fixpoint pf_parse (f : list Z) : option (list pf_piece) :=
  match f with
  | [] => Some []
  | b :: r =>
    if b =? 37 then
      match r with
      | c :: r1 =>
        if c =? 100 then option_map (cons Pd) (pf_parse r1)
        else if c =? 99 then option_map (cons Pc) (pf_parse r1)
        else if c =? 115 then option_map (cons Ps) (pf_parse r1)
        else if c =? 48 then
          match r1 with
          | c2 :: c3 :: r3 =>
              if (c2 =? 52) && (c3 =? 120) then option_map (cons Px04) (pf_parse r3)
              else if (c2 =? 50) && (c3 =? 120) then option_map (cons Px02) (pf_parse r3)
              else None
          | _ => None
          end
        else if c =? 108 then
          match r1 with
          | c2 :: c3 :: r3 => if (c2 =? 108) && (c3 =? 117) then option_map (cons Pllu) (pf_parse r3) else None
          | _ => None
          end
        else if c =? 46 then
          match r1 with
          | c2 :: c3 :: r3 => if (c2 =? 42) && (c3 =? 115) then option_map (cons Pps) (pf_parse r3) else None
          | _ => None
          end
        else None
      | [] => None
      end
    else if (0 <? b) && (b <? 256) then option_map (cons (PLit b)) (pf_parse r)
    else None
  end.

Fixpoint pf_digits (fuel : nat) (x : Z) (acc : list Z) : list Z :=
  match fuel with
  | O => acc
  | S f => if x <? 10 then (48 + x) :: acc else pf_digits f (x / 10) ((48 + x mod 10) :: acc)
  end.

Definition pf_dec (v : Z) : list Z := if v <? 0 then 45 :: pf_digits 11 (- v) [] else pf_digits 11 v [].

Definition pf_hexd (d : Z) : Z := if d <? 10 then 48 + d else 87 + d.

Fixpoint pf_hexs (fuel : nat) (x : Z) (acc : list Z) : list Z :=
  match fuel with
  | O => acc
  | S f => if x <? 16 then pf_hexd x :: acc else pf_hexs f (x / 16) (pf_hexd (x mod 16) :: acc)
  end.

Definition pf_hex4 (v : Z) : list Z :=
  let h := pf_hexs 8 (v mod 2^32) [] in repeat 48 (4 - length h) ++ h.

Definition pf_hex2 (v : Z) : list Z :=
  let h := pf_hexs 8 (v mod 2^32) [] in repeat 48 (2 - length h) ++ h.

Definition pf_udec (u : Z) : list Z := pf_digits 20 u [].

Fixpoint pf_text (ps : list pf_piece) (args : list pf_arg) : option (list Z) :=
  match ps with
  | [] => match args with [] => Some [] | _ :: _ => None end
  | PLit b :: ps' => option_map (cons b) (pf_text ps' args)
  | Pd :: ps' => match args with AInt v :: a' => option_map (app (pf_dec v)) (pf_text ps' a') | _ => None end
  | Pc :: ps' => match args with AInt v :: a' => option_map (cons (v mod 256)) (pf_text ps' a') | _ => None end
  | Px04 :: ps' => match args with AInt v :: a' => option_map (app (pf_hex4 v)) (pf_text ps' a') | _ => None end
  | Px02 :: ps' => match args with AInt v :: a' => option_map (app (pf_hex2 v)) (pf_text ps' a') | _ => None end
  | Pllu :: ps' => match args with AU64 u :: a' => option_map (app (pf_udec u)) (pf_text ps' a') | _ => None end
  | Ps :: ps' => match args with APtr s :: a' => option_map (app s) (pf_text ps' a') | _ => None end
  | Pps :: ps' =>
      match args with
      | AInt k :: APtr s :: a' =>
          if (0 <=? k) && (k <=? Z.of_nat (length s)) then option_map (app (firstn (Z.to_nat k) s)) (pf_text ps' a')
          else None
      | _ => None
      end
  end.

Definition pf_bytes (l : list Z) : list byte := map (Z_to_bv 8) l.

Definition pf_img_free (D n : Z) : Prop :=
  forall i, 0 <= i < n -> forall s, In s (segments_reserved rsegs) ->
    ~ (bv_unsigned (fst s) <= D + i < bv_unsigned (fst s) + bv_unsigned (snd s)).

Definition pf_arg_ok (m : word -> option byte) (S lo D n : Z) (r : word) (a : pf_arg) : Prop :=
  match a with
  | AInt v => (-2^31 <= v < 2^31) /\ bv_unsigned r mod 2^32 = v mod 2^32
  | AU64 u => bv_unsigned r = u
  | APtr s =>
      Forall (fun c => 0 < c < 256) s /\
      exists slack : list byte,
        bytes_at rsegs m (bv_unsigned r) (pf_bytes (s ++ [0]) ++ slack)
        /\ (- (bv_unsigned r + Z.of_nat (length s) + 1)) mod 8 <= Z.of_nat (length slack)
        /\ 0 < bv_unsigned r
        /\ (bv_unsigned r + Z.of_nat (length s) + 1 + Z.of_nat (length slack) <= lo \/ S <= bv_unsigned r)
        /\ (bv_unsigned r + Z.of_nat (length s) + 1 + Z.of_nat (length slack) <= D \/ D + n <= bv_unsigned r)
  end.

Fixpoint pf_args_ok (m : word -> option byte) (S lo D n : Z) (rs : list word) (args : list pf_arg) : Prop :=
  match args, rs with
  | [], _ => True
  | a :: args', r :: rs' => pf_arg_ok m S lo D n r a /\ pf_args_ok m S lo D n rs' args'
  | _ :: _, [] => False
  end.

Definition printf_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word)
    (lo D r : Z) (Tw : list Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (Ft : bvmap 5 word) (fc' : bv 32)
                    (m' : word -> option byte),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7
                  s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             Ft (ret_pc ra) fc' None m' (seg_rom rsegs)
    /\ munch [(lo, bv_unsigned sp); (D, D + Z.of_nat (length Tw) + 1)] m m'
    /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ MemNorm.task_mem rsegs m'
    /\ frm0 fc'
    /\ (forall k : reg, bv_unsigned k <> 10 -> reg_get Ft k = reg_get F k)
    /\ stk rsegs m' lo (bv_unsigned sp)
    /\ bytes_at rsegs m' D (pf_bytes (Tw ++ [0])).

Example pf_ex_resp : pf_parse [114; 101; 115; 112; 32; 37; 100] = Some [PLit 114; PLit 101; PLit 115; PLit 112; PLit 32; Pd]
  /\ pf_text [PLit 114; PLit 101; PLit 115; PLit 112; PLit 32; Pd] [AInt (-2147483648)]
     = Some [114; 101; 115; 112; 32; 45; 50; 49; 52; 55; 52; 56; 51; 54; 52; 56].
Proof. split; reflexivity. Qed.
Example pf_ex_esc : pf_parse [92; 37; 99] = Some [PLit 92; Pc] /\ pf_text [PLit 92; Pc] [AInt 34] = Some [92; 34]
  /\ pf_parse [92; 117; 37; 48; 52; 120] = Some [PLit 92; PLit 117; Px04]
  /\ pf_text [PLit 92; PLit 117; Px04] [AInt 31] = Some [92; 117; 48; 48; 49; 102]
  /\ pf_text [Px04] [AInt 0] = Some [48; 48; 48; 48].
Proof. repeat split; reflexivity. Qed.
Example pf_ex_prec : pf_parse [60; 37; 46; 42; 115; 62; 37; 115] = Some [PLit 60; Pps; PLit 62; Ps]
  /\ pf_text [PLit 60; Pps; PLit 62; Ps] [AInt 2; APtr [97; 98; 99]; APtr [120]] = Some [60; 97; 98; 62; 120]
  /\ pf_text [Pd] [AInt 0] = Some [48] /\ pf_text [Pd] [AInt 2147483647] = Some [50; 49; 52; 55; 52; 56; 51; 54; 52; 55].
Proof. repeat split; reflexivity. Qed.
Example pf_ex_disco : pf_parse [37; 48; 50; 120; 58; 37; 108; 108; 117] = Some [Px02; PLit 58; Pllu]
  /\ pf_text [Px02; PLit 58; Pllu] [AInt 10; AU64 18446744073709551615]
     = Some ([48; 97; 58] ++ [49; 56; 52; 52; 54; 55; 52; 52; 48; 55; 51; 55; 48; 57; 53; 53; 49; 54; 49; 53])
  /\ pf_text [Px02] [AInt 255] = Some [102; 102] /\ pf_text [Pllu] [AU64 0] = Some [48].
Proof. repeat split; reflexivity. Qed.
