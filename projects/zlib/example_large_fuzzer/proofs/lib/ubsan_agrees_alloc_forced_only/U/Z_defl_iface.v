(* reloc-zl14c *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Tac Image Arr.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.P Require Import Z_kit.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.U Require Import Z_dview Z_drep Z_trees_iface.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZIface DeflateState DeflateLz DeflateBlk FillWinModel SendModel RefFlushBlk13 RefDeflSlow2 RefDeflSlow3 RefDeflSlow6 RefDeflFast6 RefDeflSafeFB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).
Definition Z_FILL_WINDOW : Z := 0x16a08.
Definition Z_DEFLATE_SLOW : Z := 0x1a07c.
Definition Z_READ_BUF : Z := 0x197e4.
Definition Z_FILLWIN_STACK : Z := 272.
Definition Z_SLOW_STACK : Z := 128 + 512.
Definition din_tie (inp : list Z) (d : deflate_state) : Prop :=
  cs_input (ds_strm d) = arr_of_list inp /\ Forall (fun b => 0 <= b < 256) inp.
Definition fill_window_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (L : dlay) (d : deflate_state) (inp : list Z) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ munch [(lo, bv_unsigned sp); (dl_S L, dl_S L + 112); (dl_As L, dl_As L + DS_SIZE); (dl_Aw L, dl_Aw L + DS_WIN);
              (dl_Ap L, dl_Ap L + 2 * DS_NPREV); (dl_Ah L, dl_Ah L + 2 * DS_NHEAD)] m m'
    /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ stk usegs m' lo (bv_unsigned sp)
    /\ DREP m' L (fill_window d) /\ din m' L inp.
Definition fill_window_stmt : Prop :=
  forall (L : dlay) (d : deflate_state) (inp : list Z) (nout lo : Z)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem),
  DREP m L d -> din m L inp -> din_tie inp d -> mem_inv usegs m ->
  stk usegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - Z_FILLWIN_STACK -> bv_unsigned sp mod 16 = 0 ->
  dlay_below L lo (bv_unsigned sp) -> dio_sep L (zlength inp) nout lo ->
  fw_wf 32768 32768 d -> ds_insert d = 0 -> ds_wrap d <> 2 -> cs_avail_in (ds_strm d) <= 1 ->
  - 2 ^ 62 <= ds_block_start d < 2 ^ 62 ->
  a0 = wz (dl_As L) ->
  evt usegs (fill_window_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L d inp lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz Z_FILL_WINDOW) fc None m (seg_rom usegs)).
Fixpoint sbs_ok (fuel : nat) (s : deflate_state) (flush : Z) : Prop :=
  match fuel with
  | O => True
  | S f => (- 2 ^ 62 <= ds_block_start s < 2 ^ 62)
           /\ match snd (st_sbody s flush) with
              | LCont => sbs_ok f (fst (st_sbody s flush)) flush
              | _ => True
              end
  end.
Lemma sbs_ok_S : forall f s flush,
  sbs_ok (S f) s flush = ((- 2 ^ 62 <= ds_block_start s < 2 ^ 62) /\ match snd (st_sbody s flush) with LCont => sbs_ok f (fst (st_sbody s flush)) flush | _ => True end).
Proof. reflexivity. Qed.
Definition sdec_fe (X4 : deflate_state) : Prop :=
  (dist_cond X4 = true -> snd (st_sdist X4) = true -> fb_entry (fst (st_sdist X4)) 0)
  /\ (dist_cond X4 = false -> ds_match_available X4 <> 0 -> (ds_sym_next X4 + 3 =? ds_sym_end X4) = true -> fb_entry (slit1 X4) 0).
Definition shash_fe (s1 : deflate_state) : Prop :=
  sdec_fe (st_lm (prev_st (fst (st_hash s1))) (snd (st_hash s1))).
Definition strip_fe (s : deflate_state) (flush : Z) : Prop :=
  snd (st_fill s flush) = None -> shash_fe (fst (st_fill s flush)).
Fixpoint sloop_fe (fuel : nat) (s : deflate_state) (flush : Z) : Prop :=
  match fuel with
  | O => True
  | S f => strip_fe s flush
           /\ match snd (st_sbody s flush) with
              | LCont => sloop_fe f (fst (st_sbody s flush)) flush
              | _ => True
              end
  end.
Lemma sloop_fe_S : forall f s flush,
  sloop_fe (S f) s flush = (strip_fe s flush /\ match snd (st_sbody s flush) with LCont => sloop_fe f (fst (st_sbody s flush)) flush | _ => True end).
Proof. reflexivity. Qed.
Definition stail_fe (s1 : deflate_state) : Prop :=
  forall last, 0 <= last <= 1 -> fb_entry (tail_st (if negb (ds_match_available s1 =? 0) then break1_st s1 else s1)) last.
Definition tail_fe (flush : Z) (f : nat) (X : deflate_state) : Prop :=
  match snd (deflate_slow_loop f X flush) with Some _ => True | None => stail_fe (fst (deflate_slow_loop f X flush)) end.
Lemma tail_fe_S : forall flush f X,
  tail_fe flush (S f) X = match snd (st_sbody X flush) with
                          | LCont => tail_fe flush f (fst (st_sbody X flush))
                          | LBreak => stail_fe (fst (st_sbody X flush))
                          | LRet bs => True
                          end.
Proof. intros flush f X. unfold tail_fe. rewrite sloop_step'. destruct (snd (st_sbody X flush)); reflexivity. Qed.
Definition slow_fe (d : deflate_state) (flush : Z) : Prop := sloop_fe (lz_fuel d) d flush /\ tail_fe flush (lz_fuel d) d.
Lemma shash_fe_hi : forall s1, shash_fe s1 -> 3 <= ds_lookahead s1 -> sdec_fe (st_lm (hash_st s1) (hash_hh s1)).
Proof. intros s1 H Hl. unfold shash_fe in H. destruct (hash_hi_eq s1 Hl) as [E1 E2]. rewrite E1, E2 in H. exact H. Qed.
Lemma shash_fe_lo : forall s1, shash_fe s1 -> ds_lookahead s1 < 3 -> sdec_fe (st_lm (prev_st s1) 0).
Proof. intros s1 H Hl. unfold shash_fe in H. destruct (hash_lo_eq s1 Hl) as [E1 E2]. rewrite E1, E2 in H. exact H. Qed.
Definition tr_flush_block_stmtE : Prop :=
  forall (L : dlay) (s : deflate_state) (buf : option Z) (len last lo : Z)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem),
  DREP m L s -> mem_inv usegs m -> relro_clean m ->
  stk usegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - Z_TRFB_STACK -> bv_unsigned sp mod 16 = 0 ->
  dlay_below L lo (bv_unsigned sp) ->
  BINV DS_PEND s -> fb_safe s buf len last -> fb_entry s last -> fb_buf_ok buf len -> 0 <= len < 2^64 -> 0 <= last <= 1 ->
  a0 = wz (dl_As L) -> a1 = wz (match buf with Some off => dl_Aw L + off | None => 0 end) -> a2 = wz len -> a3 = wz last ->
  evt usegs (tr_flush_block_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L s buf len last lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz Z_TR_FLUSH_BLOCK) fc None m (seg_rom usegs)).
Definition bs_code (b : block_state) : Z :=
  match b with need_more => 0 | block_done => 1 | finish_started => 2 | finish_done => 3 end.
Definition deflate_slow_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (L : dlay) (d : deflate_state) (flush : Z) (inp : list Z) (rest0 : list byte) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz (bs_code (snd (deflate_slow d flush)))) a1 a2 a3 a4 a5 a6 a7
                  s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ munch [(lo, bv_unsigned sp); (dl_S L, dl_S L + 112); (dl_As L, dl_As L + DS_SIZE); (dl_Aw L, dl_Aw L + DS_WIN);
              (dl_Ap L, dl_Ap L + 2 * DS_NPREV); (dl_Ah L, dl_Ah L + 2 * DS_NHEAD); (dl_Ab L, dl_Ab L + DS_PEND);
              (dl_NO L, dl_NO L + Z.of_nat (length rest0))] m m'
    /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ stk usegs m' lo (bv_unsigned sp)
    /\ DREP m' L (fst (deflate_slow d flush)) /\ din m' L inp /\ dout m' L rest0 (ds_strm (fst (deflate_slow d flush))).
Definition deflate_slow_stmt : Prop :=
  forall (L : dlay) (d : deflate_state) (flush : Z) (inp : list Z) (rest0 : list byte) (lo : Z)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem),
  DREP m L d -> din m L inp -> din_tie inp d -> dout m L rest0 (ds_strm d) -> mem_inv usegs m -> relro_clean m ->
  stk usegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - Z_SLOW_STACK -> bv_unsigned sp mod 16 = 0 ->
  dlay_below L lo (bv_unsigned sp) -> dio_sep L (zlength inp) (Z.of_nat (length rest0)) lo ->
  slow_safe d flush -> (flush = Z_NO_FLUSH \/ flush = Z_FINISH) ->
  ds_w_size d = 32768 -> ds_hash_size d = 32768 -> ds_lit_bufsize d = 16384 -> ds_insert d = 0 -> ds_wrap d <> 2 ->
  ds_wrap d <> 0 -> - 2 <= ds_wrap d <= 2 ->
  cs_avail_in (ds_strm d) <= 1 -> 0 <= cs_avail_out (ds_strm d) < 2^31 ->
  (length (cs_out_rev (ds_strm (fst (deflate_slow d flush)))) <= length rest0)%nat ->
  sbs_ok (lz_fuel d) d flush -> slow_fe d flush ->
  a0 = wz (dl_As L) -> a1 = wz flush ->
  evt usegs (deflate_slow_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L d flush inp rest0 lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz Z_DEFLATE_SLOW) fc None m (seg_rom usegs)).
Definition Z_DEFLATE_PC : Z := 0x1723c.
Definition Z_DEFLATE_IN_STACK : Z := 80 + Z_SLOW_STACK.
Definition deflate_in_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (L : dlay) (dF : deflate_state) (rc : Z) (inp : list Z) (rest0 : list byte) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz (rc mod 2^64)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ munch [(lo, bv_unsigned sp); (dl_S L, dl_S L + 112); (dl_As L, dl_As L + DS_SIZE); (dl_Aw L, dl_Aw L + DS_WIN);
              (dl_Ap L, dl_Ap L + 2 * DS_NPREV); (dl_Ah L, dl_Ah L + 2 * DS_NHEAD); (dl_Ab L, dl_Ab L + DS_PEND);
              (dl_NO L, dl_NO L + Z.of_nat (length rest0))] m m'
    /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ stk usegs m' lo (bv_unsigned sp)
    /\ DREP m' L dF /\ din m' L inp /\ dout m' L rest0 (ds_strm dF).
