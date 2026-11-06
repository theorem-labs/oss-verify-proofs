From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.U.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.U Require Import Contract.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.U Require Import FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Lib Require PropExec Mem Cells Exec Step Frame.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.U Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.U.Prog Require Import HeadampModel GrantModel GrantSweepModel.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.U.Prog Require Import SlotNeeds_c LLVMFuzzerTestOneInput_c.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.U.Prog Require NextModel UbsanHalts.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.U.Prog Require reac_headamp_tx_set_c reac_headamp_tx_arm_scene_c
  reac_headamp_tx_set_resweep_c.
Import ListNotations.
Local Open Scope Z_scope.

Definition PC_ENTRY : Z := 0x1313c.
Definition PC_MALLOC_T : Z := 0x13270.
Definition PC_MALLOC_T_RET : Z := 0x13274.
Definition PC_SET0 : Z := 0x132b0.
Definition PC_SET : Z := 0x132f0.
Definition PC_UNSET0 : Z := 0x134a4.
Definition PC_UNSET : Z := 0x134bc.
Definition PC_ADMIT : Z := 0x13538.
Definition PC_RAW_NOK : Z := 0x135b8.
Definition PC_MALLOC_SW1 : Z := 0x13604.
Definition PC_MALLOC_SW1_RET : Z := 0x13608.
Definition PC_FREE_SW1 : Z := 0x13930.
Definition PC_FREE_SW1_RET : Z := 0x13934.
Definition PC_MALLOC_SW2 : Z := 0x1396c.
Definition PC_MALLOC_SW2_RET : Z := 0x13970.
Definition PC_FREE_SW2 : Z := 0x139f4.
Definition PC_FREE_SW2_RET : Z := 0x139f8.
Definition PC_SCHED : Z := 0x13b94.
Definition PC_FREE_T : Z := 0x13ccc.
Definition PC_FREE_T_RET : Z := 0x13cd0.
Definition PC_RET0 : Z := 0x1317c.
Definition MALLOC_PC : Z := 0x164d4.
Definition FREE_PC : Z := 0x16394.

Definition rg (ms : machine_state) (r : Z) : word := PropExec.getr (ms_regs ms) (Z_to_bv 5 r).
Definition w64 (z : Z) : word := Z_to_bv 64 z.
Definition SREGS : list Z := [8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27].
Definition sregs (ms : machine_state) : list word := map (rg ms) SREGS.

Definition pbz (pl : list byte) (i : nat) : Z := bv_unsigned (nth i pl (Z_to_bv 8 0)).
Definition rd8 (pl : list byte) (pos : nat) : Z * nat :=
  if (pos <? length pl)%nat then (pbz pl pos, S pos) else (0, pos).
Definition rd16 (pl : list byte) (pos : nat) : Z * nat :=
  let '(lo, p1) := rd8 pl pos in let '(hi, p2) := rd8 pl p1 in (lo + 256 * hi, p2).
Definition rd32 (pl : list byte) (pos : nat) : Z * nat :=
  let '(lo, p1) := rd16 pl pos in let '(hi, p2) := rd16 pl p1 in (lo + 65536 * hi, p2).
Definition sext16 (u : Z) : Z := if u <? 32768 then u else u - 65536.

Record hdr := mkhdr { h_u16 : Z; h_in : Z; h_rows : Z; h_pos : nat }.
Definition h_base (h : hdr) : Z := sext16 (h_u16 h).
Definition h_hi (h : hdr) : Z := h_u16 h / 256 * 256.
Definition header (pl : list byte) : hdr :=
  let '(u, p1) := rd16 pl 0 in let '(i, p2) := rd8 pl p1 in let '(r, p3) := rd8 pl p2 in mkhdr u i r p3.

Fixpoint cells (pl : list byte) (pos : nat) (k : nat) : list (Z * Z * Z) * nat :=
  match k with
  | O => ([], pos)
  | S k' =>
      let '(c, p1) := rd8 pl pos in let '(q, p2) := rd8 pl p1 in let '(v, p3) := rd8 pl p2 in
      let '(rest, pe) := cells pl p3 k' in ((c, q, v) :: rest, pe)
  end.

Definition nset (pl : list byte) : Z := fst (rd8 pl (h_pos (header pl))).
Definition pos_cells (pl : list byte) : nat := snd (rd8 pl (h_pos (header pl))).
Definition cells_upto (pl : list byte) (i : nat) : list (Z * Z * Z) * nat := cells pl (pos_cells pl) i.
Definition pos_end (pl : list byte) : nat := snd (cells_upto pl (Z.to_nat (nset pl))).

Definition raw_rd (pl : list byte) : Z * Z * nat :=
  let '(rb, p1) := rd8 pl (pos_end pl) in let '(rw, p2) := rd8 pl p1 in (rb, rw, p2).
Definition pos_raw (pl : list byte) : nat := snd (raw_rd pl).
Definition sched_rd (pl : list byte) : Z * Z * Z * Z * nat :=
  let '(sb, p1) := rd8 pl (pos_raw pl) in let '(sw, p2) := rd8 pl p1 in
  let '(per, p3) := rd32 pl p2 in let '(fr, p4) := rd16 pl p3 in (sb, sw, per, fr mod 4097, p4).

Definition Z144 : list byte := repeat (Z_to_bv 8 0) 144.
Definition T0 : list byte := repeat (Z_to_bv 8 0) 460.
Definition ws_put (ws : list byte) (c q v : Z) : list byte :=
  Mem.upd_bytes ws (Z.to_nat (3 * c + q)) [Z_to_bv 8 v].
Definition tstate : Type := (list byte * list byte * list byte)%type.
Definition set_step (s : tstate) (x : Z * Z * Z) : tstate :=
  let '(T, ws, st) := s in
  let '(c, q, v) := x in
  if (c <? 48) && legalb q v
  then (reac_headamp_tx_set_c.set_T T c q v, ws_put ws c q 1, ws_put st c q v)
  else s.
Definition after_sets (cs : list (Z * Z * Z)) : tstate := fold_left set_step cs (T0, Z144, Z144).
Definition tables_at (pl : list byte) (i : nat) : tstate := after_sets (fst (cells_upto pl i)).
Definition tables_end (pl : list byte) : tstate := tables_at pl (Z.to_nat (nset pl)).
Definition T_end (pl : list byte) : list byte := fst (fst (tables_end pl)).
Definition ws_end (pl : list byte) : list byte := snd (fst (tables_end pl)).
Definition st_end (pl : list byte) : list byte := snd (tables_end pl).

Definition Hrel (T ws st : list byte) : Prop :=
  forall c q, 0 <= c < 48 -> 0 <= q < 3 ->
    tb ws (3 * c + q) = tb T (144 + 3 * c + q) /\ tb st (3 * c + q) = tb T (3 * c + q).

Definition ok (pl : list byte) : bool := fits (h_base (header pl)) (h_in (header pl)).

Definition T_sched0 (pl : list byte) : list byte :=
  let '(sb, sw, per, _, _) := sched_rd pl in
  reac_headamp_tx_set_resweep_c.set_resweep_T
    (if (sw =? 0) || (48 <=? sb) then T_end pl else reac_headamp_tx_arm_scene_c.arm_T (T_end pl) sb sw)
    (Z_to_bv 64 per).
Definition frames (pl : list byte) : Z := let '(_, _, _, f, _) := sched_rd pl in f.
Definition us_step (ws us : list byte) (r : Z) (e : Z * Z * Z) : list byte :=
  let '(c, q, _) := e in
  if (r =? 1) && (c <? 48) && (q <? 3) && (tb ws (3 * c + q) =? 0)
  then ws_put us c q (tb us (3 * c + q) + 1) else us.
Fixpoint sched (T : list byte) (t : Z) (ws us : list byte) (k : nat) : list byte * list byte :=
  match k with
  | O => (T, us)
  | S k' => let '(r, e, T') := NextModel.next_model T t in sched T' t ws (us_step ws us r e) k'
  end.
Definition sched_at (pl : list byte) (t : Z) (i : nat) : list byte * list byte :=
  sched (T_sched0 pl) t (ws_end pl) Z144 i.

Record slot_ctx := mkctx {
  x_S : Z; x_ra : word; x_gp : word; x_tp : word; x_sv : list word;
  x_p : Z; x_pl : list byte; x_F : bvmap 5 word; x_fc : bv 32 }.
Definition x_n (x : slot_ctx) : Z := Z.of_nat (length (x_pl x)).
Definition SPL (x : slot_ctx) : Z := x_S x - LLVM_FRAME.
Definition hd (x : slot_ctx) : hdr := header (x_pl x).

Definition common (x : slot_ctx) (pc : Z) (ms : machine_state) : Prop :=
  ms_pc_val ms = w64 pc /\ ms_fregs ms = x_F x /\ ms_fcsr ms = x_fc x /\ ms_resv ms = None /\
  ms_svc_pending ms = None /\ ms_rom ms = seg_rom rsegs /\
  rg ms 3 = x_gp x /\ rg ms 4 = x_tp x /\
  Step.rw_cells rsegs (ms_mem ms) (x_p x) [Cells.CB (length (x_pl x)) (x_pl x)] /\
  Frame.stk rsegs (ms_mem ms) (x_S x - LLVM_STACK) (x_S x) /\ Mem.mem_inv rsegs (ms_mem ms) /\
  0 < x_p x /\ x_p x + x_n x < 2 ^ 63 /\ (x_p x + x_n x <= x_S x - LLVM_STACK \/ x_S x <= x_p x) /\
  Mem.bytes_at rsegs (ms_mem ms) CTRL_HEADAMP_ROW CTRL_HEADAMP_BYTES /\
  CTRL_HEADAMP_ROW + 24 <= x_S x - LLVM_STACK /\
  (x_p x + x_n x <= CTRL_HEADAMP_ROW \/ CTRL_HEADAMP_ROW + 24 <= x_p x).

Definition body (x : slot_ctx) (pc : Z) (ms : machine_state) : Prop :=
  common x pc ms /\ rg ms 2 = w64 (SPL x) /\
  Step.rw_cells rsegs (ms_mem ms) (x_S x - 104) (map Cells.C8 (rev (x_sv x) ++ [x_ra x])) /\
  x_S x mod 16 = 0 /\ length (x_sv x) = 12%nat /\ x_S x < 2 ^ 63.

Definition slots (x : slot_ctx) (ms : machine_state) : Prop :=
  Step.rw_cells rsegs (ms_mem ms) (SPL x + 8)
    [Cells.C8 (w64 (h_rows (hd x))); Cells.C8 (w64 (h_hi (hd x)));
     Cells.C8 (w64 (h_base (hd x))); Cells.C8 (w64 (h_in (hd x)))].

Definition cslot (x : slot_ctx) (pos : nat) (ms : machine_state) : Prop :=
  Step.rw_cells rsegs (ms_mem ms) (SPL x + 48) [Cells.C8 (w64 (x_p x + Z.of_nat pos))].

Definition wnot (a : Z) : Z := 18446744073709551615 - a.

Definition nots (x : slot_ctx) (ms : machine_state) : Prop :=
  Step.rw_cells rsegs (ms_mem ms) (SPL x + 40) [Cells.C8 (w64 (wnot (SPL x + 216)))] /\
  Step.rw_cells rsegs (ms_mem ms) (SPL x + 48) [Cells.C8 (w64 (wnot (SPL x + 360)))].

Definition cur (x : slot_ctx) (pos : nat) (ms : machine_state) : Prop :=
  rg ms 27 = w64 (x_p x + Z.of_nat pos) /\ rg ms 25 = w64 (x_n x - Z.of_nat pos).

Definition cur5 (x : slot_ctx) (pos : nat) (ms : machine_state) : Prop :=
  rg ms 21 = w64 (x_p x + Z.of_nat pos) /\ rg ms 25 = w64 (x_n x - Z.of_nat pos).

Definition blk (x : slot_ctx) (t n : Z) : Prop :=
  0 < t /\ t + n < 2 ^ 63 /\ (t + n <= x_S x - LLVM_STACK \/ x_S x <= t) /\
  (t + n <= x_p x \/ x_p x + x_n x <= t) /\ (t + n <= CTRL_HEADAMP_ROW \/ CTRL_HEADAMP_ROW + 24 <= t).

Definition table (x : slot_ctx) (t : Z) (T : list byte) (ms : machine_state) : Prop :=
  blk x t 460 /\ t mod 16 = 0 /\ length T = 460%nat /\
  Step.rw_cells rsegs (ms_mem ms) t [Cells.CB 460 T].

Definition arrays (x : slot_ctx) (ws st : list byte) (ms : machine_state) : Prop :=
  length ws = 144%nat /\ length st = 144%nat /\
  Step.rw_cells rsegs (ms_mem ms) (SPL x + 360) [Cells.CB 144 ws] /\
  Step.rw_cells rsegs (ms_mem ms) (SPL x + 216) [Cells.CB 144 st].

Definition kept (x : slot_ctx) (W : list (Z * Z)) (ms ms' : machine_state) : Prop :=
  Frame.munch ((x_S x - LLVM_STACK, x_S x) :: W) (ms_mem ms) (ms_mem ms') /\
  Frame.wmono rsegs (ms_mem ms) (ms_mem ms').

Definition At_entry (x : slot_ctx) (ms : machine_state) : Prop :=
  common x PC_ENTRY ms /\ x_S x mod 16 = 0 /\ length (x_sv x) = 12%nat /\ x_S x < 2 ^ 63 /\
  rg ms 2 = w64 (x_S x) /\ rg ms 1 = x_ra x /\ sregs ms = x_sv x /\
  rg ms 10 = w64 (x_p x) /\ rg ms 11 = w64 (x_n x) /\ 0 < x_p x /\ x_p x + x_n x < 2 ^ 63 /\
  (x_p x + x_n x <= x_S x - LLVM_STACK \/ x_S x <= x_p x).

Definition At_ret0 (x : slot_ctx) (ms : machine_state) : Prop := body x PC_RET0 ms \/ body x PC_FREE_T_RET ms.

Definition At_mallocT (x : slot_ctx) (ms : machine_state) : Prop :=
  body x PC_MALLOC_T ms /\ x_n x < 2 ^ 26 /\ rg ms 10 = w64 460 /\ cur x (h_pos (hd x)) ms /\
  rg ms 9 = w64 (h_base (hd x)) /\ rg ms 19 = w64 (h_in (hd x)) /\ rg ms 18 = w64 (h_rows (hd x)) /\
  rg ms 20 = w64 (h_hi (hd x)).

Definition At_mallocT_ret (x : slot_ctx) (t : Z) (ms : machine_state) : Prop :=
  body x PC_MALLOC_T_RET ms /\ x_n x < 2 ^ 26 /\ rg ms 10 = w64 t /\ cur x (h_pos (hd x)) ms /\
  rg ms 9 = w64 (h_base (hd x)) /\ rg ms 19 = w64 (h_in (hd x)) /\ rg ms 18 = w64 (h_rows (hd x)) /\
  rg ms 20 = w64 (h_hi (hd x)) /\
  blk x t 460 /\ t mod 16 = 0 /\ exists junk, Step.rw_cells rsegs (ms_mem ms) t [Cells.CB 460 junk].

Definition At_set0 (x : slot_ctx) (t : Z) (ms : machine_state) : Prop :=
  body x PC_SET0 ms /\ x_n x < 2 ^ 26 /\ rg ms 8 = w64 t /\ cur x (h_pos (hd x)) ms /\
  slots x ms /\ table x t T0 ms /\ arrays x Z144 Z144 ms.

Definition At_set (x : slot_ctx) (t : Z) (i : nat) (ms : machine_state) : Prop :=
  body x PC_SET ms /\ x_n x < 2 ^ 26 /\ (Z.of_nat i < nset (x_pl x)) /\
  rg ms 8 = w64 t /\ cur x (snd (cells_upto (x_pl x) i)) ms /\
  rg ms 18 = w64 (nset (x_pl x) - Z.of_nat i) /\ rg ms 9 = w64 2 /\ rg ms 26 = w64 1 /\
  slots x ms /\ nots x ms /\
  let '(T, ws, st) := tables_at (x_pl x) i in table x t T ms /\ arrays x ws st ms /\ Hrel T ws st /\ I1 T.

Definition At_unset0 (x : slot_ctx) (t : Z) (ms : machine_state) : Prop :=
  body x PC_UNSET0 ms /\ x_n x < 2 ^ 26 /\ rg ms 8 = w64 t /\ cur x (pos_end (x_pl x)) ms /\
  slots x ms /\
  table x t (T_end (x_pl x)) ms /\ arrays x (ws_end (x_pl x)) (st_end (x_pl x)) ms /\
  Hrel (T_end (x_pl x)) (ws_end (x_pl x)) (st_end (x_pl x)) /\ I1 (T_end (x_pl x)).

Definition At_unset (x : slot_ctx) (t : Z) (c : Z) (ms : machine_state) : Prop :=
  body x PC_UNSET ms /\ x_n x < 2 ^ 26 /\ 0 <= c < 48 /\ rg ms 8 = w64 t /\
  rg ms 25 = w64 (x_n x - Z.of_nat (pos_end (x_pl x))) /\
  rg ms 9 = w64 c /\ rg ms 18 = w64 2 /\ rg ms 23 = w64 48 /\ rg ms 24 = w64 3 /\
  rg ms 27 = w64 (SPL x + 360 + 3 * c) /\ slots x ms /\ cslot x (pos_end (x_pl x)) ms /\
  table x t (T_end (x_pl x)) ms /\ arrays x (ws_end (x_pl x)) (st_end (x_pl x)) ms /\
  Hrel (T_end (x_pl x)) (ws_end (x_pl x)) (st_end (x_pl x)) /\ I1 (T_end (x_pl x)).

Definition At_admit (x : slot_ctx) (t : Z) (ms : machine_state) : Prop :=
  body x PC_ADMIT ms /\ x_n x < 2 ^ 26 /\ rg ms 8 = w64 t /\
  rg ms 25 = w64 (x_n x - Z.of_nat (pos_end (x_pl x))) /\ slots x ms /\ cslot x (pos_end (x_pl x)) ms /\
  table x t (T_end (x_pl x)) ms /\ arrays x (ws_end (x_pl x)) (st_end (x_pl x)) ms /\
  Hrel (T_end (x_pl x)) (ws_end (x_pl x)) (st_end (x_pl x)) /\ I1 (T_end (x_pl x)).

Definition at_after_admit (x : slot_ctx) (t : Z) (pc : Z) (ms : machine_state) : Prop :=
  body x pc ms /\ x_n x < 2 ^ 26 /\ rg ms 8 = w64 t /\
  rg ms 25 = w64 (x_n x - Z.of_nat (pos_end (x_pl x))) /\ slots x ms /\ cslot x (pos_end (x_pl x)) ms /\
  table x t (T_end (x_pl x)) ms /\ arrays x (ws_end (x_pl x)) (st_end (x_pl x)) ms /\
  Hrel (T_end (x_pl x)) (ws_end (x_pl x)) (st_end (x_pl x)) /\ I1 (T_end (x_pl x)).

Definition sw1_size (x : slot_ctx) : Z := Z.max (h_rows (hd x)) 1 * 34.

Definition At_mallocSW1 (x : slot_ctx) (t : Z) (ms : machine_state) : Prop :=
  at_after_admit x t PC_MALLOC_SW1 ms /\ ok (x_pl x) = true /\ rg ms 10 = w64 (sw1_size x) /\
  cur5 x (pos_end (x_pl x)) ms /\ rg ms 18 = w64 (h_rows (hd x)) /\ rg ms 19 = w64 (h_in (hd x)) /\
  Step.rw_cells rsegs (ms_mem ms) (SPL x + 214) [Cells.CB 2 [Z_to_bv 8 (h_base (hd x)); Z_to_bv 8 (h_in (hd x))]].

Definition At_mallocSW1_ret (x : slot_ctx) (t s : Z) (ms : machine_state) : Prop :=
  at_after_admit x t PC_MALLOC_SW1_RET ms /\ ok (x_pl x) = true /\ rg ms 10 = w64 s /\
  cur5 x (pos_end (x_pl x)) ms /\ rg ms 18 = w64 (h_rows (hd x)) /\ rg ms 19 = w64 (h_in (hd x)) /\
  Step.rw_cells rsegs (ms_mem ms) (SPL x + 214) [Cells.CB 2 [Z_to_bv 8 (h_base (hd x)); Z_to_bv 8 (h_in (hd x))]] /\
  blk x s (sw1_size x) /\ (s + sw1_size x <= t \/ t + 460 <= s) /\
  exists junk, Step.rw_cells rsegs (ms_mem ms) s [Cells.CB (Z.to_nat (sw1_size x)) junk].

Definition At_freeSW1 (x : slot_ctx) (t s : Z) (ms : machine_state) : Prop :=
  at_after_admit x t PC_FREE_SW1 ms /\ ok (x_pl x) = true /\ rg ms 10 = w64 s /\ rg ms 9 = w64 s /\
  blk x s (sw1_size x).

Definition At_raw (x : slot_ctx) (t : Z) (pc : Z) (ms : machine_state) : Prop :=
  at_after_admit x t pc ms /\
  (pc = PC_RAW_NOK /\ ok (x_pl x) = false /\ cur5 x (pos_end (x_pl x)) ms \/ pc = PC_FREE_SW1_RET /\ ok (x_pl x) = true).

Definition At_mallocSW2 (x : slot_ctx) (t : Z) (ms : machine_state) : Prop :=
  body x PC_MALLOC_SW2 ms /\ x_n x < 2 ^ 26 /\ rg ms 8 = w64 t /\ cur5 x (pos_raw (x_pl x)) ms /\
  rg ms 10 = w64 4352 /\
  (let '(rb, rw, _) := raw_rd (x_pl x) in
   Step.rw_cells rsegs (ms_mem ms) (SPL x + 66) [Cells.CB 2 [Z_to_bv 8 rb; Z_to_bv 8 rw]]) /\
  table x t (T_end (x_pl x)) ms /\ arrays x (ws_end (x_pl x)) (st_end (x_pl x)) ms /\
  Hrel (T_end (x_pl x)) (ws_end (x_pl x)) (st_end (x_pl x)) /\ I1 (T_end (x_pl x)).

Definition At_mallocSW2_ret (x : slot_ctx) (t s : Z) (ms : machine_state) : Prop :=
  body x PC_MALLOC_SW2_RET ms /\ x_n x < 2 ^ 26 /\ rg ms 8 = w64 t /\ cur5 x (pos_raw (x_pl x)) ms /\
  rg ms 10 = w64 s /\
  (let '(rb, rw, _) := raw_rd (x_pl x) in
   Step.rw_cells rsegs (ms_mem ms) (SPL x + 66) [Cells.CB 2 [Z_to_bv 8 rb; Z_to_bv 8 rw]]) /\
  table x t (T_end (x_pl x)) ms /\ arrays x (ws_end (x_pl x)) (st_end (x_pl x)) ms /\
  Hrel (T_end (x_pl x)) (ws_end (x_pl x)) (st_end (x_pl x)) /\ I1 (T_end (x_pl x)) /\
  blk x s 4352 /\ (s + 4352 <= t \/ t + 460 <= s) /\
  exists junk, Step.rw_cells rsegs (ms_mem ms) s [Cells.CB 4352 junk].

Definition At_freeSW2 (x : slot_ctx) (t s : Z) (ms : machine_state) : Prop :=
  body x PC_FREE_SW2 ms /\ x_n x < 2 ^ 26 /\ rg ms 8 = w64 t /\ rg ms 10 = w64 s /\ rg ms 9 = w64 s /\
  cur5 x (pos_raw (x_pl x)) ms /\
  table x t (T_end (x_pl x)) ms /\ arrays x (ws_end (x_pl x)) (st_end (x_pl x)) ms /\
  Hrel (T_end (x_pl x)) (ws_end (x_pl x)) (st_end (x_pl x)) /\ I1 (T_end (x_pl x)) /\ blk x s 4352.

Definition At_freeSW2_ret (x : slot_ctx) (t : Z) (ms : machine_state) : Prop :=
  body x PC_FREE_SW2_RET ms /\ x_n x < 2 ^ 26 /\ rg ms 8 = w64 t /\ cur5 x (pos_raw (x_pl x)) ms /\
  table x t (T_end (x_pl x)) ms /\ arrays x (ws_end (x_pl x)) (st_end (x_pl x)) ms /\
  Hrel (T_end (x_pl x)) (ws_end (x_pl x)) (st_end (x_pl x)) /\ I1 (T_end (x_pl x)).

Definition sched_flag (pl : list byte) : Z :=
  let '(sb, sw, _, _, _) := sched_rd pl in if negb (sw =? 0) && (sb <? 48) then 1 else 0.

Definition At_sched (x : slot_ctx) (t : Z) (i : nat) (ms : machine_state) : Prop :=
  body x PC_SCHED ms /\ x_n x < 2 ^ 26 /\ Z.of_nat i < frames (x_pl x) /\ rg ms 8 = w64 t /\
  rg ms 22 = w64 (Z.of_nat i - frames (x_pl x)) /\ rg ms 23 = w64 (-1) /\ rg ms 24 = w64 2 /\
  rg ms 25 = w64 1 /\ rg ms 26 = w64 47 /\ rg ms 27 = w64 3 /\ rg ms 19 = w64 (wnot (SPL x + 360)) /\
  rg ms 21 = w64 (sched_flag (x_pl x)) /\
  Step.rw_cells rsegs (ms_mem ms) (SPL x + 48) [Cells.C8 (w64 (wnot (SPL x + 66)))] /\
  (let '(sb, sw, _, _, _) := sched_rd (x_pl x) in rg ms 9 = w64 sb /\ rg ms 18 = w64 (sb + sw)) /\
  (let '(T, us) := sched_at (x_pl x) t i in
   table x t T ms /\ I1 T /\ length us = 144%nat /\ Step.rw_cells rsegs (ms_mem ms) (SPL x + 66) [Cells.CB 144 us]) /\
  arrays x (ws_end (x_pl x)) (st_end (x_pl x)) ms /\
  Hrel (T_end (x_pl x)) (ws_end (x_pl x)) (st_end (x_pl x)).

Definition At_freeT (x : slot_ctx) (t : Z) (ms : machine_state) : Prop :=
  body x 0x13cc8 ms /\ x_n x < 2 ^ 26 /\ rg ms 8 = w64 t /\ blk x t 460 /\ t mod 16 = 0.

Definition seg_head : Prop := forall x ms, At_entry x ms ->
  Exec.evt rsegs (fun ms' => kept x [] ms ms' /\
    ((2 ^ 26 <= x_n x /\ At_ret0 x ms') \/ (x_n x < 2 ^ 26 /\ At_mallocT x ms'))) ms.

Definition seg_init : Prop := forall x t ms, At_mallocT_ret x t ms ->
  Exec.evt rsegs (fun ms' => kept x [(t, t + 460)] ms ms' /\ At_set0 x t ms') ms.

Definition seg_nset : Prop := forall x t ms, At_set0 x t ms ->
  Exec.evt rsegs (fun ms' => kept x [] ms ms' /\
    ((nset (x_pl x) = 0 /\ At_unset0 x t ms') \/ (0 < nset (x_pl x) /\ At_set x t 0 ms'))) ms.

Definition seg_set_turn : Prop := forall x t i ms, At_set x t i ms ->
  Exec.evt rsegs (fun ms' => kept x [(t, t + 460)] ms ms' /\
    ((Z.of_nat (S i) < nset (x_pl x) /\ At_set x t (S i) ms') \/
     (Z.of_nat (S i) = nset (x_pl x) /\ At_unset0 x t ms'))) ms.

Definition seg_unset_enter : Prop := forall x t ms, At_unset0 x t ms ->
  Exec.evt rsegs (fun ms' => kept x [] ms ms' /\ At_unset x t 0 ms') ms.

Definition seg_unset_turn : Prop := forall x t c ms, At_unset x t c ms ->
  Exec.evt rsegs (fun ms' => kept x [] ms ms' /\
    ((c + 1 < 48 /\ At_unset x t (c + 1) ms') \/ (c + 1 = 48 /\ At_admit x t ms'))) ms.

Definition seg_admit : Prop := forall x t ms, At_admit x t ms ->
  Exec.evt rsegs (fun ms' => kept x [] ms ms' /\
    ((ok (x_pl x) = true /\ At_mallocSW1 x t ms') \/ (ok (x_pl x) = false /\ At_raw x t PC_RAW_NOK ms'))) ms.

Definition seg_sweep : Prop := forall x t s ms, At_mallocSW1_ret x t s ms ->
  Exec.evt rsegs (fun ms' => kept x [(s, s + sw1_size x)] ms ms' /\ At_freeSW1 x t s ms') ms.

Definition seg_raw : Prop := forall x t pc ms, At_raw x t pc ms ->
  Exec.evt rsegs (fun ms' => kept x [] ms ms' /\ At_mallocSW2 x t ms') ms.

Definition seg_rawsweep : Prop := forall x t s ms, At_mallocSW2_ret x t s ms ->
  Exec.evt rsegs (fun ms' => kept x [(s, s + 4352)] ms ms' /\ At_freeSW2 x t s ms') ms.

Definition seg_sched_setup : Prop := forall x t ms, At_freeSW2_ret x t ms ->
  Exec.evt rsegs (fun ms' => kept x [(t, t + 460)] ms ms' /\
    ((frames (x_pl x) = 0 /\ At_freeT x t ms') \/ (0 < frames (x_pl x) /\ At_sched x t 0 ms'))) ms.

Definition seg_sched_turn : Prop := forall x t i ms, At_sched x t i ms ->
  Exec.evt rsegs (fun ms' => kept x [(t, t + 460)] ms ms' /\
    ((Z.of_nat (S i) < frames (x_pl x) /\ At_sched x t (S i) ms') \/
     (Z.of_nat (S i) = frames (x_pl x) /\ At_freeT x t ms'))) ms.

Definition seg_epilogue : Prop := forall x ms, At_ret0 x ms ->
  Exec.evt rsegs (fun ms' => ms_mem ms' = ms_mem ms /\ ms_pc_val ms' = MState.ret_pc (x_ra x) /\
    ms_fregs ms' = x_F x /\ ms_fcsr ms' = x_fc x /\ ms_resv ms' = None /\ ms_svc_pending ms' = None /\
    rg ms' 1 = x_ra x /\ rg ms' 2 = w64 (x_S x) /\ rg ms' 3 = x_gp x /\ rg ms' 4 = x_tp x /\
    sregs ms' = x_sv x /\ rg ms' 10 = w64 0 /\ ms_rom ms' = seg_rom rsegs) ms.

Definition phase_unset_once : Prop := forall pl t i c q,
  0 <= c < 48 -> 0 <= q < 3 -> tb (ws_end pl) (3 * c + q) = 0 ->
  tb (snd (sched_at pl t i)) (3 * c + q) <= 1.

Section SR.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {LS : lib_shape}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Context {SH : sink_head} {SK : sink_syms}.

Definition alloc_state (L : layout) (A : astate) (mem : word -> option byte) (md : Model) (b : sbound) : Prop :=
  aa_MR API L A mem md /\ WF A /\ bounded A /\ st_init_done A = true /\ res_ok_slots A b.

Definition unit_binding : Prop :=
  ms_segs B = rsegs /\ ms_malloc B = MALLOC_PC /\ ms_free B = FREE_PC.

Definition norm_at (P : machine_state -> Prop) (s : machine_state) : Prop :=
  exists s0, P s0 /\ MemNorm.ms_rel rsegs s s0.

Definition payload_blk (x : slot_ctx) (L : layout) (A : astate) : Prop :=
  (x_n x = 0 /\ in_img B (x_p x)) \/ (0 < x_n x /\ exists q, In (q, x_n x) (user_blocks A) /\ ptr_addr L q = x_p x).

Definition live_blk (L : layout) (A : astate) (t n : Z) : Prop :=
  exists q, In (q, n) (user_blocks A) /\ ptr_addr L q = t.

Definition errno_wr (mem : word -> option byte) : Prop :=
  forall a, errno_addr B <= a < errno_addr B + 4 -> writable_at (ms_segs B) mem a.

Definition glue_pre (x : slot_ctx) (Pre : machine_state -> Prop) (s : machine_state) (md : Model) (L : layout)
    (A : astate) (b : sbound) : Prop :=
  frame_allocator B API /\ unit_binding /\ x_tp x = w64 (ms_tp B) /\
  norm_at Pre s /\ MemNorm.ro_agree (ms_segs B) (ms_mem s) /\
  ms_fregs s = fp_regs /\ ms_fcsr s = fp_csr /\ alloc_state L A (ms_mem s) md b /\
  errno_wr (ms_mem s) /\ payload_blk x L A /\
  errno_addr B + 4 <= alloc_ceiling /\
  (forall i, 0 <= i < 24 -> ~ static_owned B (CTRL_HEADAMP_ROW + i) /\
     ~ (ms_ctx B <= CTRL_HEADAMP_ROW + i < ms_ctx B + CTX_SIZE) /\
     ~ (errno_addr B <= CTRL_HEADAMP_ROW + i < errno_addr B + 4)).

Definition glue_post (x : slot_ctx) (Post : machine_state -> Prop) (Live : layout -> astate -> Prop)
    (s' : machine_state) (md' : Model) (L' : layout) (A' : astate) (b' : sbound) : Prop :=
  norm_at Post s' /\ MemNorm.ro_agree (ms_segs B) (ms_mem s') /\
  ms_fregs s' = fp_regs /\ ms_fcsr s' = fp_csr /\ alloc_state L' A' (ms_mem s') md' b' /\
  errno_wr (ms_mem s') /\ payload_blk x L' A' /\ Live L' A'.

Definition malloc_glue (x : slot_ctx) (Pre : machine_state -> Prop) (Live : layout -> astate -> Prop) (n : Z)
    (Post : Z -> machine_state -> Prop) : Prop :=
  forall s md L A b, glue_pre x Pre s md L A b -> Live L A -> room_slots b n ->
  SR (ms_segs B) (mkCfg s md) (fun c' =>
    exists s' md' L' A' r,
      c' = mkCfg s' md' /\ glue_post x (Post r) Live s' md' L' A' (sb_malloc b n) /\ live_blk L' A' r n /\
      call_post_k B (aa_MR API) ALLOC_STACK L A (ms_regs s) (ms_mem s) md (fun _ => False) L' A' (ms_regs s')
        (ms_mem s') md' /\
      fresh_block B r n /\ r mod 16 = 0 /\
      (exists b1 b2, blocks L' A' = b1 ++ (r, n) :: b2 /\ blocks L A = b1 ++ b2) /\
      blocks_kept B L A (ms_mem s) (ms_mem s') (fun _ => False) /\ guard_kept B (ms_mem s) (ms_mem s') /\
      (forall q k, In (q, k) (user_blocks A) -> In (q, k) (user_blocks A'))).

Definition free_glue (x : slot_ctx) (Pre : machine_state -> Prop) (Live : layout -> astate -> Prop) (s0 n : Z)
    (Post : machine_state -> Prop) : Prop :=
  forall s md L A b q, glue_pre x Pre s md L A b -> Live L A -> In (q, n) (user_blocks A) -> ptr_addr L q = s0 ->
  SR (ms_segs B) (mkCfg s md) (fun c' =>
    exists s' md' L' A',
      c' = mkCfg s' md' /\ glue_post x Post Live s' md' L' A' (sb_free b n) /\
      call_post B (aa_MR API) L A (ms_regs s) (ms_mem s) md (fun a => s0 <= a < s0 + n) L' A' (ms_regs s')
        (ms_mem s') md' /\
      (exists b1 b2, blocks L A = b1 ++ (s0, n) :: b2 /\ blocks L' A' = b1 ++ b2) /\
      blocks_kept B L A (ms_mem s) (ms_mem s') (fun a => a = s0) /\ guard_kept B (ms_mem s) (ms_mem s') /\
      (forall q' k, In (q', k) (user_blocks A) -> q' <> q -> In (q', k) (user_blocks A'))).

Definition no_live (L : layout) (A : astate) : Prop := True.

Definition seg_mallocT : Prop := forall x, alloc_ceiling + LLVM_STACK <= x_S x ->
  malloc_glue x (At_mallocT x) no_live 460 (fun t => At_mallocT_ret x t).
Definition seg_mallocSW1 : Prop := forall x t, alloc_ceiling + LLVM_STACK <= x_S x ->
  malloc_glue x (At_mallocSW1 x t) (fun L A => live_blk L A t 460) (sw1_size x) (fun s => At_mallocSW1_ret x t s).
Definition seg_mallocSW2 : Prop := forall x t, alloc_ceiling + LLVM_STACK <= x_S x ->
  malloc_glue x (At_mallocSW2 x t) (fun L A => live_blk L A t 460) 4352 (fun s => At_mallocSW2_ret x t s).
Definition seg_freeSW1 : Prop := forall x t s, alloc_ceiling + LLVM_STACK <= x_S x ->
  free_glue x (At_freeSW1 x t s) (fun L A => live_blk L A t 460) s (sw1_size x) (At_raw x t PC_FREE_SW1_RET).
Definition seg_freeSW2 : Prop := forall x t s, alloc_ceiling + LLVM_STACK <= x_S x ->
  free_glue x (At_freeSW2 x t s) (fun L A => live_blk L A t 460) s 4352 (At_freeSW2_ret x t).
Definition seg_freeT : Prop := forall x t, alloc_ceiling + LLVM_STACK <= x_S x ->
  free_glue x (At_freeT x t) no_live t 460 (At_ret0 x).

End SR.

Definition plan_closes : Prop :=
  seg_head -> seg_init -> seg_nset -> seg_set_turn -> seg_unset_enter -> seg_unset_turn -> seg_admit ->
  seg_sweep -> seg_raw -> seg_rawsweep -> seg_sched_setup -> seg_sched_turn -> seg_epilogue -> phase_unset_once ->
  UbsanHalts.grant_slot_ubsan.
