(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import Tac Image ZBridge SysStep SFModel SFW1_lemmas InitMem Arr Frame.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import Images.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Common Require Import ShapeAlgCfg.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.R Require Import PortShim.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.R Require Import RMallocRep RMallocTree RMalloc_iface RYajlRep RYajl_iface RY_lib RY_rz RY_kit2
     RY_lex_kit RY_lex_main.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Agent Require Import MallocBlocks.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import RawAlloc Prelim YajlBase YajlBuf YajlLeaf YajlLex YajlParser YajlFactsLex YajlFactsBuf.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.R Require Export RY_lex_top1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Open Scope yprog_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)

From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Section P.
Variables (sp gp tp : word) (F : bvmap 5 word) (fc : bv 32) (lo T : Z) (txt : list Z) (H L LB OBP OLP : Z).

(* [comment removed for export] *)
Lemma lex_prologue : forall (ra t0 t1 t2 s0 s1 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 obw olw : word)
    (m : mem) (e off : Z),
  stk rsegs m lo (bv_unsigned sp) -> mem_inv rsegs m ->
  rw_cells rsegs m (H + 32) [C4 (wz off)] -> rw_cells rsegs m OBP [C8 obw] -> rw_cells rsegs m OLP [C4 olw] ->
  rw_cells rsegs m L (lxcells e LB (H + 72)) -> rw_cells rsegs m LB (buf_cells ybuf_zero 0 (H + 72)) ->
  lexenv (bv_unsigned sp) lo T (zlength txt) H L LB ->
  bv_unsigned sp <= OLP -> OLP + 4 <= OBP -> OBP + 8 <= 2^64 ->
  0 <= off <= zlength txt ->
  evt rsegs (fun ms' => exists (a1' : word) (junk : list byte) (m1 : mem),
      ms' = MS (mkR ra (wz (bv_unsigned sp - 128)) gp tp t0 t1 t2 (wz 10) s1 (wz off) a1' (wz (zlength txt)) (wz (H + 32)) (wz OBP) (wz OLP) a6 a7
                    (wz L) (wz T) (wz (H + 32)) (wz (zlength txt)) (wz off) (wz 90) (wz 49) (wz 42) (wz 47) (wz RY_JT_LEX) t3 t4 t5 t6)
               F (wz 0x13f50) fc None m1 (seg_rom rsegs)
      /\ munch [(lo, bv_unsigned sp); (H + 32, H + 36); (L, L + 48); (LB + 8, LB + 12); (OLP, OLP + 4); (OBP, OBP + 8)] m m1
      /\ wmono rsegs m m1 /\ mem_inv rsegs m1 /\ stk rsegs m1 lo (bv_unsigned sp - 128)
      /\ rw_cells rsegs m1 (bv_unsigned sp - 128) (lex_frame OBP OLP junk ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11)
      /\ rw_cells rsegs m1 (H + 32) [C4 (wz off)] /\ rw_cells rsegs m1 OBP [C8 (wz 0)] /\ rw_cells rsegs m1 OLP [C4 (wz 0)]
      /\ rw_cells rsegs m1 L (lxcells e LB (H + 72)) /\ rw_cells rsegs m1 LB (buf_cells ybuf_zero 0 (H + 72)))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz L) (wz T) (wz (zlength txt)) (wz (H + 32)) (wz OBP) (wz OLP) a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz RY_LEX_LEX) fc None m (seg_rom rsegs)).
Proof.
  intros until off. intros STK MI OFF OB OL LC BC ENV SPL OLB OBB OFFB.
  destruct ENV. unfold lxcells, buf_cells, RY_LEX_LEX, RY_JT_LEX in *. unfold wz. unfold alloc_ceiling in *.
  cbn [buf_state_code yb_state yb_len yb_used ybuf_zero] in BC. unfold wz in OFF, OB, OL, LC, BC.
  pose proof (rw_cells_bound _ _ _ _ OB) as OBR. cbn [cells_size csize Nat.add] in OBR.
  (* [comment removed for export] *)
  pose proof (munch_refl [(lo, bv_unsigned sp); (OLP, OLP + 4); (OBP, OBP + 8)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MUf.
  pose proof (wmono_refl rsegs m) as WMf.
  pose proof OFF as OFF1. pose proof OFF as OFF2.
  yhide OFF. yhide OFF1. yhide OFF2. yhide OB. yhide OL. yhide LC. yhide BC.
  clear le_Tsep.
  zstep. carve_frame 128%nat STK.
  do 13 zstep.
  yreveal OFF1 MUf WMf.
  zstep. zstep. rewrite ysx32_small by lia. clear OFF1.
  yreveal OB MUf WMf. yreveal OL MUf WMf. clear MUf WMf.
  zstep. zstep. lit_store.
  yreveal OFF2 MU WM.
  zstep. rewrite ysx32_small by lia. clear OFF2. zstep. zstep. lit_store.
  zstep. if_cases KA; zify_cond KA. 2:{ kill KA. } clear KA.
  do 10 zstep.
  yreveal OFF MU WM. yreveal LC MU WM. yreveal BC MU WM.
  apply evt_done. eexists _, _, _. split; [reflexivity|].
  split.
  { eapply munch_weaken; [| exact MU]. intros x Hx. cbn [outside] in Hx |- *.
    destruct Hx as (X1 & X2 & X3 & X4 & X5 & X6 & _). exact (conj X1 (conj X5 (conj X6 I))). }
  unfold lex_frame. repeat match goal with |- _ /\ _ => split end; first [assumption| eassumption].
Qed.
End P.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma tok_eqb_eof_false : forall tok, tok <> TK_eof -> tok_eqb tok TK_eof = false.
Proof. intros [] H; try reflexivity. congruence. Qed.
Lemma tok_eqb_error : forall tok, tok_eqb tok TK_error = true -> tok = TK_error.
Proof. intros [] H; try discriminate H. reflexivity. Qed.

(* [comment removed for export] *)
Lemma lexW_facts : forall SP lo H L LB OLP OBP B (LB0 : list block) hid lid bid,
  alloc_ceiling <= lo -> SP <= OLP -> OLP + 4 <= OBP -> OBP + 8 <= B -> lo <= SP ->
  In (hid, H, 104) LB0 -> In (lid, L, 48) LB0 -> In (bid, LB, 32) LB0 ->
  rblock_range H 104 -> rblock_range L 48 -> rblock_range LB 32 ->
  let W := [(lo, SP); (H + 32, H + 36); (L, L + 48); (LB + 8, LB + 12); (OLP, OLP + 4); (OBP, OBP + 8)] in
  Forall (rclient_write_ok LB0) W
  /\ Forall (fun iv : Z * Z => snd iv <= B /\ (snd iv <= RAUXV_CELL \/ RAUXV_CELL + 8 <= fst iv)) W
  /\ Forall (fun iv : Z * Z => snd iv <= RY_CALLBACKS \/ RY_CALLBACKS + 152 <= fst iv) W.
Proof.
  intros SP lo H L LB OLP OBP B LB0 hid lid bid CE S1 S2 S3 S4 I1 I2 I3 R1 R2 R3.
  unfold rblock_range, alloc_ceiling, RAUXV_CELL, RY_CALLBACKS in *. cbv zeta.
  split; [| split]; repeat (apply Forall_cons; [cbn [fst snd]|]); try apply Forall_nil; try lia.
  - left. cbn. unfold alloc_ceiling. lia.
  - right; right. exists (hid, H, 104). split; [exact I1| cbn; lia].
  - right; right. exists (lid, L, 48). split; [exact I2| cbn; lia].
  - right; right. exists (bid, LB, 32). split; [exact I3| cbn; lia].
  - left. cbn. unfold alloc_ceiling. lia.
  - left. cbn. unfold alloc_ceiling. lia.
Qed.

(* [comment removed for export] *)
Lemma lexenv_intro : forall (SP lo T len H L LB : Z) (REST : list block) hid lid bid,
  alloc_ceiling <= lo -> lo <= SP - 8432 -> SP < 2^64 ->
  rblock_range H 104 -> rblock_range L 48 -> rblock_range LB 32 ->
  bsep (hid, H, 104) (lid, L, 48) -> bsep (hid, H, 104) (bid, LB, 32) -> bsep (lid, L, 48) (bid, LB, 32) ->
  0 <= len < 2^26 -> 0 < T -> T + len < 2^62 ->
  ((exists bt, In bt REST /\ blk_addr bt <= T /\ T + len <= blk_addr bt + blk_size bt) \/ len = 0) ->
  all_range REST -> sep_from (hid, H, 104) REST -> sep_from (lid, L, 48) REST -> sep_from (bid, LB, 32) REST ->
  lexenv SP lo T len H L LB.
Proof.
  intros SP lo T len H L LB REST hid lid bid CE LO SPU RH RL RLB S1 S2 S3 LEN TP TL TXR RR SH SL SB.
  unfold rblock_range, bsep in *. cbn [blk_addr blk_size fst snd] in *.
  constructor;
    [exact CE| exact LO| exact SPU| clear - RH; lia| clear - RL; lia| clear - RLB; lia| clear - S1; lia| clear - S2; lia| clear - S3; lia
    | exact LEN| clear - TP TL; lia|].
  intros Hl. destruct TXR as [(bt & IN & B1 & B2)|Z0]; [| lia].
  pose proof (all_range_In _ _ RR IN) as X. unfold rblock_range in X.
  pose proof (sep_from_In _ _ _ SH IN) as Y1. pose proof (sep_from_In _ _ _ SL IN) as Y2. pose proof (sep_from_In _ _ _ SB IN) as Y3.
  unfold bsep in Y1, Y2, Y3. cbn [blk_addr blk_size fst snd] in Y1, Y2, Y3.
  clear S1 S2 S3 SH SL SB RR RH RL RLB.
  split; [clear Y1 Y2 Y3; lia|]. split; [clear Y2 Y3; lia|]. split; [clear Y1 Y3; lia|]. clear Y1 Y2; lia.
Qed.

(* [comment removed for export] *)
Lemma lexW_client_outside : forall (SP lo H L LB OLP OBP : Z) (REST : list block) hid lid bid a,
  alloc_ceiling <= lo -> lo <= SP -> SP <= OLP -> OLP + 4 <= OBP ->
  rblock_range H 104 -> rblock_range L 48 -> rblock_range LB 32 ->
  all_range REST -> sep_from (hid, H, 104) REST -> sep_from (lid, L, 48) REST -> sep_from (bid, LB, 32) REST ->
  0 <= a < 2^64 -> rclient_addr REST SP a -> ~ yin_ivs [(OLP, OLP + 4); (OBP, OBP + 8)] a ->
  outside [(lo, SP); (H + 32, H + 36); (L, L + 48); (LB + 8, LB + 12); (OLP, OLP + 4); (OBP, OBP + 8)] a.
Proof.
  intros SP lo H L LB OLP OBP REST hid lid bid a CE LO S1 S2 RH RL RLB RR SH SL SB Ha Hc Hx.
  unfold rblock_range in RH, RL, RLB. cbn [outside yin_ivs fst snd] in Hx |- *. unfold alloc_ceiling in *.
  destruct Hc as [Hc|[Hc|(b & Hb & Hr)]].
  - lia.
  - destruct Hc as [Hc _]. lia.
  - pose proof (all_range_In _ _ RR Hb) as Hbr. unfold rblock_range, alloc_ceiling in Hbr.
    pose proof (sep_from_In _ _ _ SH Hb) as Y1. pose proof (sep_from_In _ _ _ SL Hb) as Y2. pose proof (sep_from_In _ _ _ SB Hb) as Y3.
    unfold bsep in Y1, Y2, Y3. cbn [blk_addr blk_size fst snd] in Y1, Y2, Y3.
    clear SH SL SB RR.
    repeat split; first [clear Y1 Y2 Y3; lia| clear Y2 Y3; lia| clear Y1 Y3; lia| clear Y1 Y2; lia].
Qed.

Lemma lexL_client_outside : forall (SP lo L : Z) (REST : list block) lid a,
  alloc_ceiling <= lo -> lo <= SP -> rblock_range L 48 -> sep_from (lid, L, 48) REST ->
  0 <= a < 2^64 -> rclient_addr REST SP a -> outside [(L, L + 48)] a.
Proof.
  intros SP lo L REST lid a CE LO RL SL Ha Hc.
  unfold rblock_range in RL. cbn [outside]. unfold alloc_ceiling in *. split; [| exact I].
  destruct Hc as [Hc|[Hc|(b & Hb & Hr)]].
  - lia.
  - destruct Hc as [Hc _]. lia.
  - pose proof (sep_from_In _ _ _ SL Hb) as Y2. unfold bsep in Y2. cbn [blk_addr blk_size fst snd] in Y2. lia.
Qed.

(* [comment removed for export] *)
Lemma hand_split : forall m h mh pew pad,
  rw_cells rsegs m (mh_addr mh) (hand_cells ryc h mh pew pad) <->
  (rw_cells rsegs m (mh_addr mh) [C8 (wz (yc_callbacks ryc)); C8 (wz (mh_ctx mh)); C8 (wz (mh_lexer mh)); C8 pew]
   /\ rw_cells rsegs m (mh_addr mh + 32) [C4 (wz (h_bytesConsumed h))]
   /\ rw_cells rsegs m (mh_addr mh + 36) [C4 pad; C8 (wz (mb_addr (mh_decbuf mh))); C8 (wz (mh_stack mh)); C4 (wz (h_stack_size h)); C4 (wz (h_used h)); C8 (wz (mh_addr mh + 72))]
   /\ rw_cells rsegs m (mh_addr mh + 72) (alloc_cells ryc)).
Proof.
  intros m h mh pew pad. unfold hand_cells, hand_head_cells.
  change ([C8 (wz (yc_callbacks ryc)); C8 (wz (mh_ctx mh)); C8 (wz (mh_lexer mh)); C8 pew; C4 (wz (h_bytesConsumed h)); C4 pad;
           C8 (wz (mb_addr (mh_decbuf mh))); C8 (wz (mh_stack mh)); C4 (wz (h_stack_size h)); C4 (wz (h_used h)); C8 (wz (mh_addr mh + 72))] ++ alloc_cells ryc)
    with ((([C8 (wz (yc_callbacks ryc)); C8 (wz (mh_ctx mh)); C8 (wz (mh_lexer mh)); C8 pew] ++ [C4 (wz (h_bytesConsumed h))])
           ++ [C4 pad; C8 (wz (mb_addr (mh_decbuf mh))); C8 (wz (mh_stack mh)); C4 (wz (h_stack_size h)); C4 (wz (h_used h)); C8 (wz (mh_addr mh + 72))])
          ++ alloc_cells ryc).
  rewrite !ycells_app. cbn [cells_size csize Nat.add length app].
  replace (mh_addr mh + 32 + 4) with (mh_addr mh + 36) by lia. replace (mh_addr mh + 36 + 36) with (mh_addr mh + 72) by lia.
  tauto.
Qed.

End RC__1.
