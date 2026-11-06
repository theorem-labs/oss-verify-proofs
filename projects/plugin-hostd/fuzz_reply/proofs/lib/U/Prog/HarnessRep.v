From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YO0i YO0f YO0d YO05 YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U Require Import Img0 Contract.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import RelayFrame RelayModel.
Import ListNotations.
Local Open Scope Z_scope.

Definition G_S : Z := 0x31920.
Definition SRC_SIZE : Z := 96.
Definition SOURCES_MAX : Z := 4.

Definition bz (b : byte) : Z := bv_unsigned b.
Definition bzs (l : list byte) : list Z := map bz l.

Definition text_rec (r : Z * list byte) : list byte := le8 (Z_to_bv 64 (fst r)) ++ le8 (Z_to_bv 64 (Z.of_nat (length (snd r)))).

Record hlist := HL { hl_v : Z; hl_cap : Z; hl_recs : list (Z * list byte); hl_junk : list byte }.

Definition hl_n (l : hlist) : Z := Z.of_nat (length (hl_recs l)).

Record hsrc := HS {
  hs_fd : Z; hs_open : Z; hs_closed : Z; hs_eintr : Z;
  hs_pending : hlist; hs_off : Z;
  hs_partial : Z; hs_pjunk : list byte; hs_npartial : Z; hs_overlong : Z; hs_pad : list byte;
  hs_expected : hlist; hs_held : hlist }.

Definition hs_W (h : hsrc) : list byte := firstn (Z.to_nat (hs_npartial h)) (hs_pjunk h).

Definition hs_state (h : hsrc) : lstate := LS (bzs (hs_W h)) (hs_overlong h =? 1).

Definition pending_stream (h : hsrc) : list byte :=
  match hl_recs (hs_pending h) with
  | [] => []
  | r :: rs => skipn (Z.to_nat (hs_off h)) (snd r) ++ concat (map snd rs)
  end.

Definition list_blocks (l : hlist) : list Z := (if hl_cap l =? 0 then [] else [hl_v l]) ++ map fst (hl_recs l).

Definition hs_blocks (h : hsrc) : list Z :=
  list_blocks (hs_pending h) ++ [hs_partial h] ++ list_blocks (hs_expected h) ++ list_blocks (hs_held h).

Section HR.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable Bm : malloc_syms.
Variable API : AllocAPI Bm.
Let segs := ms_segs Bm.
Let MR := aa_MR API.

Definition list_at (L : layout) (A : astate) (mem : word -> option byte) (LA : Z) (l : hlist) (lines : bool) : Prop :=
  rw_cells segs mem LA [C8 (Z_to_bv 64 (hl_v l)); C4 (Z_to_bv 64 (hl_n l)); C4 (Z_to_bv 64 (hl_cap l))] /\
  hl_n l <= hl_cap l < 2 ^ 30 /\
  ((hl_cap l = 0 /\ hl_v l = 0) \/
   (0 < hl_cap l /\ In (hl_v l, 16 * hl_cap l) (blocks L A) /\ fresh_block Bm (hl_v l) (16 * hl_cap l) /\
    Z.of_nat (length (hl_junk l)) = 16 * (hl_cap l - hl_n l) /\
    rw_cells segs mem (hl_v l) [CB (Z.to_nat (16 * hl_cap l)) (concat (map text_rec (hl_recs l)) ++ hl_junk l)])) /\
  NoDup (map fst (hl_recs l)) /\ ~ In (hl_v l) (map fst (hl_recs l)) /\
  Forall (fun r =>
    In (fst r, Z.of_nat (length (snd r)) + 1) (blocks L A) /\ fresh_block Bm (fst r) (Z.of_nat (length (snd r)) + 1) /\
    rw_cells segs mem (fst r) [CB (length (snd r) + 1) (snd r ++ [Z_to_bv 8 0])] /\
    (lines = true -> ~ In (Z_to_bv 8 0) (snd r) /\ Z.of_nat (length (snd r)) <= 6000) /\
    (lines = false -> (1 <= length (snd r))%nat)) (hl_recs l).

Definition src_at (L : layout) (A : astate) (mem : word -> option byte) (HA : Z) (h : hsrc) : Prop :=
  rw_cells segs mem HA [C4 (Z_to_bv 64 (hs_fd h)); C4 (Z_to_bv 64 (hs_open h));
                        C4 (Z_to_bv 64 (hs_closed h)); C4 (Z_to_bv 64 (hs_eintr h))] /\
  (hs_closed h = 0 \/ hs_closed h = 1) /\ (hs_eintr h = 0 \/ hs_eintr h = 1) /\
  hs_open h = 1 /\ 0 <= hs_fd h < 2 ^ 31 /\
  list_at L A mem (HA + 16) (hs_pending h) false /\
  rw_cells segs mem (HA + 32) [C8 (Z_to_bv 64 (hs_off h)); C8 (Z_to_bv 64 (hs_partial h));
                               C8 (Z_to_bv 64 (hs_npartial h)); C4 (Z_to_bv 64 (hs_overlong h))] /\
  ((hl_recs (hs_pending h) = [] /\ hs_off h = 0) \/
   (exists r rs, hl_recs (hs_pending h) = r :: rs /\ 0 <= hs_off h < Z.of_nat (length (snd r)))) /\
  0 <= hs_npartial h <= 6000 /\ (hs_overlong h = 0 \/ hs_overlong h = 1) /\
  In (hs_partial h, 6000) (blocks L A) /\ fresh_block Bm (hs_partial h) 6000 /\
  Z.of_nat (length (hs_pjunk h)) = 6000 /\
  rw_cells segs mem (hs_partial h) [CB (Z.to_nat 6000) (hs_pjunk h)] /\
  ~ In (Z_to_bv 8 0) (hs_W h) /\
  list_at L A mem (HA + 64) (hs_expected h) true /\
  list_at L A mem (HA + 80) (hs_held h) true /\
  NoDup (hs_blocks h).

End HR.
