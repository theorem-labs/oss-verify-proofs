(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Bool String Ascii Lia.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import Prelim.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import StrerrorTable.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition str (s : string) : list Z :=
  map (fun a => Z.of_N (N_of_ascii a)) (list_ascii_of_string s).

Lemma str_app : forall a b, str (a ++ b) = (str a ++ str b)%list.
Proof.
  intros a b. unfold str. rewrite <- map_app. f_equal.
  induction a as [|c a IH]; cbn; [reflexivity|]. now rewrite IH.
Qed.

(* [comment removed for export] *)
Fixpoint udigits_aux (fuel : nat) (base : Z) (n : Z) (acc : list Z) : list Z :=
  match fuel with
  | O => acc
  | S fuel' => if n <=? 0 then acc
               else udigits_aux fuel' base (n / base)
                      ((if n mod base <? 10 then 48 + n mod base else 87 + n mod base) :: acc)
  end.
(* [comment removed for export] *)

Definition udigits (base n : Z) : list Z := udigits_aux 64%nat base n [].
Definition dec_udigits (n : Z) : list Z := udigits 10 n.
Definition hex_udigits (n : Z) : list Z := udigits 16 n.

(* [comment removed for export] *)
Definition render_unsigned (n : Z) : list Z := if n =? 0 then [48] else dec_udigits n.
Definition render_signed (v : Z) : list Z :=
  if v <? 0 then 45 :: dec_udigits (- v) else render_unsigned v.
Definition render_hex (n : Z) : list Z := if n =? 0 then [48] else hex_udigits n.

(* [comment removed for export] *)
Inductive conv : Type :=
| Cd      (* [comment removed for export] *)
| Cu      (* [comment removed for export] *)
| Cx      (* [comment removed for export] *)
| C08x    (* [comment removed for export] *)
| Cs      (* [comment removed for export] *)
| Czu     (* [comment removed for export] *)
| Clu     (* [comment removed for export] *)
| Cld.    (* [comment removed for export] *)

Inductive fitem : Type :=
| FLit (s : list Z)     (* [comment removed for export] *)
| FConv (c : conv)
| FBad (s : list Z).    (* [comment removed for export] *)

Inductive farg : Type := AInt (v : Z) | AStr (s : list Z).

(* [comment removed for export] *)
Fixpoint take_lit (s : list Z) : list Z * list Z :=
  match s with
  | [] => ([], [])
  | c :: s' => if c =? 37 then ([], s) else let (l, r) := take_lit s' in (c :: l, r)
  end.

Definition parse_conv (s : list Z) : option (conv * list Z) :=
  match s with
  | 100 :: r => Some (Cd, r)          (* [comment removed for export] *)
  | 105 :: r => Some (Cd, r)          (* [comment removed for export] *)
  | 117 :: r => Some (Cu, r)          (* [comment removed for export] *)
  | 120 :: r => Some (Cx, r)          (* [comment removed for export] *)
  | 115 :: r => Some (Cs, r)          (* [comment removed for export] *)
  | 122 :: 117 :: r => Some (Czu, r)  (* [comment removed for export] *)
  | 108 :: 117 :: r => Some (Clu, r)  (* [comment removed for export] *)
  | 108 :: 100 :: r => Some (Cld, r)  (* [comment removed for export] *)
  | 48 :: 56 :: 120 :: r => Some (C08x, r)  (* [comment removed for export] *)
  | _ => None
  end.

Fixpoint parse_fmt_aux (fuel : nat) (s : list Z) : list fitem :=
  match fuel with
  | O => match s with [] => [] | _ => [FBad s] end
  | S fuel' =>
      match s with
      | [] => []
      | 37 :: r =>
          match parse_conv r with
          | Some (c, r') => FConv c :: parse_fmt_aux fuel' r'
          | None => [FBad s]
          end
      | _ => let (l, r) := take_lit s in FLit l :: parse_fmt_aux fuel' r
      end
  end.
Definition parse_fmt (s : list Z) : list fitem := parse_fmt_aux (List.length s) s.
Definition fmt (s : string) : list fitem := parse_fmt (str s).

(* [comment removed for export] *)
Definition zeros (n : Z) : list Z := zrepeat 48 n.

Definition int_pieces (neg : bool) (digits : list Z) : list (list Z) :=
  (* [comment removed for export] *)
  (if neg then [45] else []) ::
  (match digits with [] => [ [48]; [] ] | _ => [ digits ] end).

Definition conv_pieces (c : conv) (a : farg) : list (list Z) :=
  match c, a with
  | Cd, AInt v => let v := s32 v in int_pieces (v <? 0) (dec_udigits (Z.abs v))
  | Cld, AInt v => let v := s64 v in int_pieces (v <? 0) (dec_udigits (Z.abs v))
  | Cu, AInt v => int_pieces false (dec_udigits (u32 v))
  | Cx, AInt v => int_pieces false (hex_udigits (u32 v))
  | Czu, AInt v => int_pieces false (dec_udigits (u64 v))
  | Clu, AInt v => int_pieces false (dec_udigits (u64 v))
  | C08x, AInt v =>
      let d := hex_udigits (u32 v) in
      let nd := zlength d + (if u32 v =? 0 then 1 else 0) in   (* [comment removed for export] *)
      [] :: (if nd <? 8 then [zeros (8 - nd)] else [])
         ++ (match d with [] => [ [48]; [] ] | _ => [ d ] end)
  | Cs, AStr s => [ []; s ]
  (* [comment removed for export] *)
  | Cs, AInt _ => [ []; [] ]
  | _, AStr s => [ []; s ]
  end.

(* [comment removed for export] *)
Fixpoint fmt_pieces (items : list fitem) (args : list farg) : list (list Z) :=
  match items with
  | [] => []
  | FLit l :: items' => l :: fmt_pieces items' args
  | FConv c :: items' =>
      let a := hd (AInt 0) args in
      [] :: conv_pieces c a ++ fmt_pieces items' (tl args)
  | FBad s :: _ => [ s ]
  end.

(* [comment removed for export] *)
Definition fmt_output (items : list fitem) (args : list farg) : list Z :=
  List.concat (fmt_pieces items args).

(* [comment removed for export] *)
Definition sprintf (f : string) (args : list farg) : list Z := fmt_output (fmt f) args.
Definition pieces (f : string) (args : list farg) : list (list Z) := fmt_pieces (fmt f) args.

(* [comment removed for export] *)
Definition snprintf_out (n : Z) (items : list fitem) (args : list farg) : list Z :=
  firstn (Z.to_nat (n - 1)) (fmt_output items args).
Definition snprintf_ret (items : list fitem) (args : list farg) : Z :=
  zlength (fmt_output items args).
Definition snprintf (n : Z) (f : string) (args : list farg) : list Z :=
  snprintf_out n (fmt f) args.

(* [comment removed for export] *)
Fixpoint table_lookup (t : list (Z * string)) (e : Z) : option string :=
  match t with
  | [] => None
  | (k, s) :: t' => if k =? e then Some s else table_lookup t' e
  end.

(* [comment removed for export] *)
Definition strerror (e : Z) : list Z :=
  let e' := if (0 <=? e) && (e <? STRERROR_N) then e else 0 in
  str (match table_lookup strerror_table e' with Some s => s | None => strerror_default end).

(* [comment removed for export] *)
Definition strerror_r (e : Z) (buflen : Z) : Z * list Z :=
  let msg := strerror e in
  if zlength msg <? buflen then (0, msg)
  else (34, if 0 <? buflen then firstn (Z.to_nat (buflen - 1)) msg else []).

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition pieces_emit_d (rc : Z) : list (list Z) := pieces "%d
" [AInt rc].
(* [comment removed for export] *)
Definition pieces_failed_remove (e : Z) : list (list Z) := pieces "failed remove, errno=%d
" [AInt e].
Definition pieces_failed_open (e : Z) : list (list Z) := pieces "failed open, errno=%d
" [AInt e].
(* [comment removed for export] *)
Definition pieces_couldnt_open (errbuf : list Z) : list (list Z) := pieces "Couldn't open pcap file %s
" [AStr errbuf].
(* [comment removed for export] *)
Definition pieces_packet_length (caplen len : Z) : list (list Z) := pieces "packet length=%d/%d
" [AInt caplen; AInt len].
(* [comment removed for export] *)
Definition pieces_number_of_packets (n : Z) : list (list Z) := pieces "number of packets=%d
" [AInt n].

(* [comment removed for export] *)
Definition pieces_usage (argv0 : list Z) : list (list Z) := pieces "usage: %s INPUT
" [AStr argv0].
Definition pieces_cannot_open (path : list Z) : list (list Z) := pieces "cli: cannot open %s
" [AStr path].
Definition pieces_read_error (path : list Z) : list (list Z) := pieces "cli: read error on %s
" [AStr path].
Definition pieces_oom : list (list Z) := pieces "cli: out of memory
" [].
Definition pieces_too_big : list (list Z) := pieces "cli: input >= %u bytes, refused
" [AInt 67108864].
Definition pieces_short_hdr : list (list Z) := pieces "cli: input shorter than header
" [].
Definition pieces_cfg_overrun : list (list Z) := pieces "cli: config_len overruns input
" [].

(* [comment removed for export] *)
Local Open Scope string_scope.
Example pieces_emit_0 : pieces_emit_d 0 = [ []%list; []%list; [48]; []%list; [10] ]%list.
Proof. vm_compute. reflexivity. Qed.
Example pieces_emit_neg : pieces_emit_d (-5) = [ []%list; [45]; [53]; [10] ]%list.
Proof. vm_compute. reflexivity. Qed.
Example pieces_packet_length_ex :
  pieces_packet_length 12 0 = [ str "packet length="; []%list; []%list; str "12"; str "/"; []%list; []%list; str "0"; []%list; [10] ]%list.
Proof. vm_compute. reflexivity. Qed.
Example pieces_usage_ex : pieces_usage (str "prog") = [ str "usage: "; []%list; []%list; str "prog"; str " INPUT" ++ [10] ]%list.
Proof. vm_compute. reflexivity. Qed.
Example pieces_08x_0 : pieces "0x%08x" [AInt 0] = [ str "0x"; []%list; []%list; str "0000000"; str "0"; []%list ]%list.
Proof. vm_compute. reflexivity. Qed.
Example pieces_08x_ff : pieces "0x%08x" [AInt 255] = [ str "0x"; []%list; []%list; str "000000"; str "ff" ]%list.
Proof. vm_compute. reflexivity. Qed.
Example pieces_d_big : List.concat (pieces "%d" [AInt 4294967295]) = str "-1".
Proof. vm_compute. reflexivity. Qed.
Example snprintf_trunc : snprintf 8 "abc%udef" [AInt 12345] = str "abc1234".
Proof. vm_compute. reflexivity. Qed.
Example strerror_2 : strerror 2 = str "No such file or directory".
Proof. vm_compute. reflexivity. Qed.
Example strerror_12 : strerror 12 = str "Out of memory".
Proof. vm_compute. reflexivity. Qed.
Example strerror_neg : strerror (-1) = str "No error information".
Proof. vm_compute. reflexivity. Qed.
Example strerror_41 : strerror 41 = str "No error information".   (* [comment removed for export] *)
Proof. vm_compute. reflexivity. Qed.
Example strerror_200 : strerror 200 = str "No error information".
Proof. vm_compute. reflexivity. Qed.
