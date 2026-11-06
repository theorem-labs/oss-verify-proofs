From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib Require Import Img0 Contract.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import RelayFrame RelayModel HarnessRep ListRep.
Import ListNotations.
Local Open Scope Z_scope.

Definition G_GONE : Z := 0x30fc8.

Definition nulbytes (n : nat) : list byte := repeat (Z_to_bv 8 0) n.

Definition texts (l : hlist) : list (list Z) := map (fun r => bzs (snd r)) (hl_recs l).

Definition set_held (h : hsrc) (l : hlist) : hsrc :=
  HS (hs_fd h) (hs_open h) (hs_closed h) (hs_eintr h) (hs_pending h) (hs_off h) (hs_partial h) (hs_pjunk h)
     (hs_npartial h) (hs_overlong h) (hs_pad h) (hs_expected h) l.

Definition set_exp_held (h : hsrc) (e l : hlist) : hsrc :=
  HS (hs_fd h) (hs_open h) (hs_closed h) (hs_eintr h) (hs_pending h) (hs_off h) (hs_partial h) (hs_pjunk h)
     (hs_npartial h) (hs_overlong h) (hs_pad h) e l.

Definition is_begin (l : list Z) : bool :=
  match gesture l with
  | Some (GBegin, _) => true
  | _ => false
  end.

Definition count_begin (ls : list (list Z)) : nat := length (filter is_begin ls).

Definition bstream (l : hlist) : list byte := concat (map (fun r => snd r ++ [Z_to_bv 8 0]) (hl_recs l)).

Definition prefixb (P x : list byte) : bool :=
  Nat.leb (length P) (length x) && list_eqb (bzs (firstn (length P) x)) (bzs P).

Definition want_of (P : list byte) (rs : list (Z * list byte)) : nat := length (filter (fun r => prefixb P (snd r)) rs).

Definition END4 : list byte := [Z_to_bv 8 32; Z_to_bv 8 101; Z_to_bv 8 110; Z_to_bv 8 100].

Fixpoint split_nul (d : list byte) : option (list byte * list byte) :=
  match d with
  | [] => None
  | b :: d' =>
      if bv_unsigned b =? 0 then Some ([], d')
      else match split_nul d' with
           | Some (l, r) => Some (b :: l, r)
           | None => None
           end
  end.

Fixpoint find_text (y : list byte) (rs : list (Z * list byte)) : option nat :=
  match rs with
  | [] => None
  | r :: rs' => if list_eqb (bzs (snd r)) (bzs y) then Some O else option_map S (find_text y rs')
  end.

Definition drop_nth (i : nat) (rs : list (Z * list byte)) : list (Z * list byte) := firstn i rs ++ skipn (S i) rs.

Fixpoint ends_run (P : list byte) (rs : list (Z * list byte)) (d : list byte) (w : nat)
    : option (list (Z * list byte) * list (Z * list byte) * Z) :=
  match w with
  | O => Some (rs, [], 0)
  | S w' =>
      match split_nul d with
      | None => None
      | Some (l, d') =>
          let n := length l in
          if Nat.leb 4 n && list_eqb (bzs (skipn (n - 4) l)) (bzs END4) && prefixb P l then
            match find_text (firstn (n - 4) l) rs with
            | None => None
            | Some i =>
                match ends_run P (drop_nth i rs) d' w' with
                | None => None
                | Some (rs', ds, c) => Some (rs', nth i rs (0, []) :: ds, Z.of_nat n + 1 + c)
                end
            end
          else None
      end
  end.

Fixpoint first_zero (os : list Z) : option nat :=
  match os with
  | [] => None
  | o :: os' => if o =? 0 then Some O else option_map S (first_zero os')
  end.
