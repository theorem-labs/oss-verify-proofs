(* The two boolean checkers over the allocator record's lists (lib/B/YF0m.v, the B twin of lib/A/AF0m.v) that a
   contract may state about an image range: `cmd_addr_b a n` (every byte of [a, a + n) has a shadow byte that the
   record pins and that admits the byte) and `cmd_hull_b a n` (every byte of the 8-byte shadow words that the checks
   of [a, a + n) read is pinned). A shadow byte is pinned when it lies in one of the record's zero-shadow ranges
   (value 0) or in one of its absolute constant cells. The record holds at every AR state, so these facts hold at
   every AR state; the lemmas that turn them into range_addressable and shadow_hull_vis are the B twins of
   lib/A/Prog/CmdRecFacts.v's cmd_addressable_chk, cmd_hull_vis_chk and cmd_aread_ok_chk. Definitions only. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v YG0f.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require Import YF0m.
Import ListNotations.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.
(* [f] holds at every integer of [lo, lo + k) *)
Fixpoint crf_zallf (f : Z -> bool) (lo : Z) (k : nat) : bool :=
match k with O => true | S k' => f lo && crf_zallf f (lo + 1) k' end.
Definition crf_some {A : Type} (o : option A) : bool := match o with Some _ => true | None => false end.
(* the byte at [a] of an absolute constant cell, if [a] is inside it *)
Definition crf_cell_byte (c : acell) (a : Z) : option Z :=
match c with
| ACell (ANum s) w (AV (ANum v)) =>
  if (s <=? a) && (a <? s + Z.of_nat w) then Some (le_byte v w (Z.to_nat (a - s))) else None
| _ => None
end.
Fixpoint crf_cells_byte (l : list acell) (a : Z) : option Z :=
match l with
| [] => None
| c :: t => match crf_cell_byte c a with Some v => Some v | None => crf_cells_byte t a end
end.
(* [s] is a shadow byte of one of the zero-shadow ranges [l] *)
Definition crf_zsh_hit (l : list (Z * Z)) (s : Z) : bool :=
existsb (fun r => (shadow_of_addr SHADOW_OFF (fst r) <=? s) && (s <? shadow_of_addr SHADOW_OFF (fst r) + snd r / 8)) l.
(* the record's absolute constant cells: Tfib_const ly without its layout-relative part *)
Definition cmd_cabs : list acell := Tfib_const_abs ++ Tfib_const_shadow.
(* the byte AR pins at [a]: a shadow byte of a zero-shadow range is 0, a byte of an absolute constant cell has the
   cell's value *)
Definition cmd_byte (a : Z) : option Z :=
if crf_zsh_hit Tfib_zero_shadow a then Some 0 else crf_cells_byte cmd_cabs a.
Definition crf_saddr_okb (x s : Z) : bool := (s =? 0) || ((x mod 8 <? s) && (s <? 8)).
Definition cmd_addr_b (a n : Z) : bool :=
crf_zallf (fun x => match cmd_byte (shadow_of_addr SHADOW_OFF x) with Some s => crf_saddr_okb x s | None => false end)
a (Z.to_nat n).
Definition cmd_hull_b (a n : Z) : bool :=
crf_zallf (fun s => crf_some (cmd_byte s)) (shadow_addr a / 8 * 8)
(Z.to_nat (shadow_addr (a + n - 1) / 8 * 8 + 8 - shadow_addr a / 8 * 8)).
