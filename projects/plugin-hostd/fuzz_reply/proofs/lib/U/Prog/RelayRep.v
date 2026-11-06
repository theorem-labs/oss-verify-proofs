From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YO0i YO0f YO0d YO05 YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U Require Import Img0 Contract.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import gesture_end_c RelayFrame gestures_end_b_c.
Import ListNotations.
Local Open Scope Z_scope.

Record rentry := RE {
  re_fd : Z; re_eof : Z; re_skip : Z; re_pad1 : list byte;
  re_buf : Z; re_used : Z; re_cap : Z; re_hp : Z; re_kh : Z; re_pad2 : list byte;
  re_keys : list (Z * list byte * list byte); re_U : list byte; re_junk : list byte }.

Definition re_nheld (e : rentry) : Z := Z.of_nat (length (re_keys e)).

Definition entry_bytes (e : rentry) : list byte :=
  le4 (Z_to_bv 64 (re_fd e)) ++ le4 (Z_to_bv 64 (re_eof e)) ++ le4 (Z_to_bv 64 (re_skip e)) ++ re_pad1 e ++
  le8 (Z_to_bv 64 (re_buf e)) ++ le8 (Z_to_bv 64 (re_used e)) ++ le8 (Z_to_bv 64 (re_cap e)) ++
  le8 (Z_to_bv 64 (re_hp e)) ++ le4 (Z_to_bv 64 (re_nheld e)) ++ re_pad2 e.

Definition entry_cleared (e : rentry) : rentry :=
  RE (re_fd e) (re_eof e) (re_skip e) (re_pad1 e) (re_buf e) (re_used e) (re_cap e) 0 0 (re_pad2 e)
     [] (re_U e) (re_junk e).

Definition entry_blocks (e : rentry) : list Z :=
  (if re_cap e =? 0 then [] else [re_buf e]) ++ (if re_hp e =? 0 then [] else [re_hp e]) ++ map key_addr (re_keys e).

Definition entries_total (es : list rentry) : Z := fold_right (fun e acc => keys_total (re_keys e) + acc) 0 es.

Definition entries_out (es : list rentry) : list byte := concat (map (fun e => keys_out (re_keys e)) es).

Section RR.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable Bm : malloc_syms.
Variable API : AllocAPI Bm.
Let segs := ms_segs Bm.
Let MR := aa_MR API.

Definition entry_ok (L : layout) (A : astate) (mem : word -> option byte) (e : rentry) : Prop :=
  (re_eof e = 0 \/ re_eof e = 1) /\ (re_skip e = 0 \/ re_skip e = 1) /\
  length (re_pad1 e) = 4%nat /\ length (re_pad2 e) = 4%nat /\
  0 <= re_fd e < 2 ^ 31 /\
  (re_cap e = 0 \/ re_cap e = 8192 \/ re_cap e = 16384) /\
  Z.of_nat (length (re_U e)) = re_used e /\ re_used e <= 6000 /\ ~ In (Z_to_bv 8 0) (re_U e) /\
  ((re_cap e = 0 /\ re_buf e = 0 /\ re_used e = 0) \/
   (0 < re_cap e /\ In (re_buf e, re_cap e) (blocks L A) /\ fresh_block Bm (re_buf e) (re_cap e) /\
    Z.of_nat (length (re_junk e)) = re_cap e - re_used e /\
    rw_cells segs mem (re_buf e) [CB (Z.to_nat (re_cap e)) (re_U e ++ re_junk e)])) /\
  re_nheld e < 2 ^ 26 /\
  ((re_hp e = 0 /\ re_keys e = []) \/
   (In (re_hp e, re_kh e) (blocks L A) /\ fresh_block Bm (re_hp e) (re_kh e) /\ 8 * re_nheld e <= re_kh e /\ 8 <= re_kh e /\
    bytes_at segs mem (re_hp e) (key_ptrs (re_keys e)))) /\
  NoDup (map key_addr (re_keys e)) /\
  NoDup (map key_text (re_keys e)) /\
  Forall (fun k =>
    In (key_addr k, Z.of_nat (length (key_text k)) + 1) (blocks L A) /\
    fresh_block Bm (key_addr k) (Z.of_nat (length (key_text k)) + 1) /\
    bytes_at segs mem (key_addr k) (key_text k ++ Z_to_bv 8 0 :: key_slack k) /\
    ~ In (Z_to_bv 8 0) (key_text k) /\ 14 <= Z.of_nat (length (key_text k)) <= 6000 /\
    (- (key_addr k + Z.of_nat (length (key_text k)) + 1)) mod 8 <= Z.of_nat (length (key_slack k))) (re_keys e).

Definition entries_disjoint (OUT : Z) (es : list rentry) : Prop :=
  NoDup (concat (map entry_blocks es)) /\ ~ In OUT (concat (map entry_blocks es)).

Definition table_at (mem : word -> option byte) (G : Z) (es : list rentry) (tail : list byte) : Prop :=
  Z.of_nat (length tail) = 896 - 56 * Z.of_nat (length es) /\
  rw_cells segs mem G [CB 896%nat (concat (map entry_bytes es) ++ tail)].

End RR.
