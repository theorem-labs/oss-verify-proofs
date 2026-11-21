(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: relocated for the zlib 1.4 build, ported to the model, comments removed. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.E1 Require Import SymEx2Expr SymEx2 SymEx2Tac MemRel SymAux RomRead.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel Require Import Prog ZIface InflateState InflateFast InflateArms Inflate InflateInv.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.D6S Require Import Segs6.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6S Require Import ISLayout IS6 InflMem InflRod6.
Import ListNotations.
Local Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.PropExec.FPState}.


Definition pc6_inflate : Z := 0x1cf48.
Definition pc6_disp : Z := 0x1d0b4.
Definition pc6_leave : Z := 0x1eab8.
Definition pc6_ret : Z := 0x1ec44.
Definition pc6_mem : Z := 0x1ebe8.
Definition pc6_need_dict : Z := 0x1eccc.
Definition INF_FRAME : Z := 224.
Definition INF_SCRATCH : Z := 192.

Definition saved_slots : list (Z * Z) :=
  [(1, 216); (8, 208); (9, 200); (18, 192); (19, 184); (20, 176); (21, 168); (22, 160); (23, 152);
   (24, 144); (25, 136); (26, 128); (27, 120)].

Definition msg6_addr (m : Z) : Z :=
  if m =? MSG_NULL then 0
  else if m =? MSG_incorrect_header_check then 0x104f8
  else if m =? MSG_unknown_compression_method then 0x105ab
  else if m =? MSG_invalid_window_size then 0x10490
  else if m =? MSG_unknown_header_flags_set then 0x103cf
  else if m =? MSG_header_crc_mismatch then 0x10606
  else if m =? MSG_invalid_block_type then 0x10472
  else if m =? MSG_invalid_stored_block_lengths then 0x10316
  else if m =? MSG_too_many_length_or_distance_symbols then 0x10419
  else if m =? MSG_invalid_code_lengths_set then 0x1064c
  else if m =? MSG_invalid_bit_length_repeat then 0x102ba
  else if m =? MSG_invalid_code_missing_end_of_block then 0x1050f
  else if m =? MSG_invalid_literal_lengths_set then 0x10382
  else if m =? MSG_invalid_distances_set then 0x10578
  else if m =? MSG_invalid_literal_length_code then 0x104dc
  else if m =? MSG_invalid_distance_code then 0x10351
  else if m =? MSG_invalid_distance_too_far_back then 0x102d4
  else if m =? MSG_incorrect_data_check then 0x105c6
  else if m =? MSG_incorrect_length_check then 0x104a4
  else 0.


Definition IMG6_TOP : Z := 0x5c000.
Definition offimg (a n : Z) : Prop := a + n <= 0x10000 \/ IMG6_TOP <= a.


Record icv : Type := ICV {
  cv_sp : Z; cv_R0 : bvmap 5 word; cv_ZP : Z; cv_S : Z; cv_I0 : Z; cv_P0 : Z; cv_WB : Z;
  cv_NI : Z; cv_NO : Z; cv_WN : Z; cv_flush : Z; cv_TOT0 : Z; cv_fa : Z; cv_ff : Z; cv_opq : Z }.

Section Ctx.
  Variable v : icv.
  Local Abbreviation sp := (cv_sp v). Local Abbreviation R0 := (cv_R0 v). Local Abbreviation ZP := (cv_ZP v).
  Local Abbreviation S := (cv_S v). Local Abbreviation I0 := (cv_I0 v). Local Abbreviation P0 := (cv_P0 v).
  Local Abbreviation WB := (cv_WB v). Local Abbreviation NI := (cv_NI v). Local Abbreviation NO := (cv_NO v).
  Local Abbreviation WN := (cv_WN v). Local Abbreviation flush := (cv_flush v). Local Abbreviation TOT0 := (cv_TOT0 v).
  Local Abbreviation FA := (cv_fa v). Local Abbreviation FF := (cv_ff v). Local Abbreviation OPQ := (cv_opq v).

  Record ictx : Prop := ICTX {
    ic_ret : ret_ok (getr R0 1);
    ic_sp : IMG6_TOP + INF_FRAME + INF_SCRATCH <= sp /\ sp < 2 ^ 63 /\ sp mod 16 = 0;
    ic_ZP : 0 < ZP /\ ZP + 112 < 2 ^ 63 /\ ZP mod 8 = 0;
    ic_S : 0 < S /\ S + 7176 < 2 ^ 63 /\ S mod 16 = 0;
    ic_I0 : 0 < I0 /\ I0 + NI < 2 ^ 63 /\ 0 <= NI < 2 ^ 31;
    ic_P0 : 0 < P0 /\ P0 + NO < 2 ^ 63 /\ 0 <= NO < 2 ^ 31;
    ic_WB : 0 <= WB /\ WB + WN < 2 ^ 63 /\ (WN = 0 /\ WB = 0 \/ WN = 32768 /\ 0 < WB /\ WB mod 16 = 0);
    ic_flush : 0 <= flush <= 4;
    ic_TOT0 : 0 <= TOT0 < 2 ^ 64;
    ic_hooks : 0 <= FA < 2 ^ 64 /\ 0 <= FF < 2 ^ 64 /\ 0 <= OPQ < 2 ^ 64;
    ic_nofast : True;
    ic_o_Z : offimg ZP 112;
    ic_o_S : offimg S 7176;
    ic_o_I : 0 < NI -> offimg I0 NI;
    ic_o_P : 0 < NO -> offimg P0 NO;
    ic_o_W : offimg WB WN;
    ic_d_fZ : sep (sp - INF_FRAME - INF_SCRATCH) (INF_FRAME + INF_SCRATCH) ZP 112;
    ic_d_fS : sep (sp - INF_FRAME - INF_SCRATCH) (INF_FRAME + INF_SCRATCH) S 7176;
    ic_d_fI : 0 < NI -> sep (sp - INF_FRAME - INF_SCRATCH) (INF_FRAME + INF_SCRATCH) I0 NI;
    ic_d_fP : 0 < NO -> sep (sp - INF_FRAME - INF_SCRATCH) (INF_FRAME + INF_SCRATCH) P0 NO;
    ic_d_fW : sep (sp - INF_FRAME - INF_SCRATCH) (INF_FRAME + INF_SCRATCH) WB WN;
    ic_d_ZS : sep ZP 112 S 7176;
    ic_d_ZI : sep ZP 112 I0 NI;
    ic_d_ZO : sep ZP 112 P0 NO;
    ic_d_ZW : sep ZP 112 WB WN;
    ic_d_SI : 0 < NI -> sep S 7176 I0 NI;
    ic_d_SP : 0 < NO -> sep S 7176 P0 NO;
    ic_d_SW : sep S 7176 WB WN;
    ic_d_IP : sep I0 NI P0 NO;
    ic_d_IW : 0 < NI -> sep I0 NI WB WN;
    ic_d_PW : 0 < NO -> sep P0 NO WB WN;
    ic_sp47 : sp <= 2 ^ 47;
    ic_Sbelow : S + 7176 <= sp - INF_FRAME - INF_SCRATCH
  }.


  Definition izs6 (M : word -> option byte) (c : icall) : Prop :=
    cell s6_segs M (ZP + 0) 8 (I0 + ic_next_in c) /\ cell s6_segs M (ZP + 8) 4 (ic_avail_in c)
    /\ cell s6_segs M (ZP + 16) 8 (ic_total_in c)
    /\ cell s6_segs M (ZP + 24) 8 (P0 + ic_next_out c) /\ cell s6_segs M (ZP + 32) 4 (ic_avail_out c)
    /\ cell s6_segs M (ZP + 40) 8 (ic_total_out c)
    /\ cell s6_segs M (ZP + 48) 8 (msg6_addr (ic_msg c))
    /\ cell s6_segs M (ZP + 56) 8 S
    /\ cell s6_segs M (ZP + 64) 8 FA /\ cell s6_segs M (ZP + 72) 8 FF /\ cell s6_segs M (ZP + 80) 8 OPQ
    /\ cell s6_segs M (ZP + 96) 8 (ic_adler c).

  Definition iframe6 (M : word -> option byte) : Prop :=
    (forall r o, In (r, o) saved_slots -> cell s6_segs M (sp - INF_FRAME + o) 8 (bv_unsigned (getr R0 (Z_to_bv 5 r))))
    /\ cell s6_segs M (sp - INF_FRAME + 104) 8 flush
    /\ cell s6_segs M (sp - INF_FRAME + 96) 8 ZP
    /\ cell s6_segs M (sp - INF_FRAME + 88) 8 (-16180)
    /\ cell s6_segs M (sp - INF_FRAME + 72) 8 16209
    /\ cell s6_segs M (sp - INF_FRAME + 56) 8 NI
    /\ cell s6_segs M (sp - INF_FRAME + 48) 8 (S + 7160)
    /\ cell s6_segs M (sp - INF_FRAME + 40) 8 (flush - 5)
    /\ cell s6_segs M (sp - INF_FRAME + 32) 8 (S + 160)
    /\ cell s6_segs M (sp - INF_FRAME + 24) 8 (S + 808)
    /\ cell s6_segs M (sp - INF_FRAME + 16) 8 (S + 1384)
    /\ cell s6_segs M (sp - INF_FRAME + 8) 8 (S + 136)
    /\ cell s6_segs M (sp - INF_FRAME + 0) 8 (S + 140).

  Record LMEM (w : iw) (M : word -> option byte) : Prop := LM {
    lm_rod : rod6_clear M;
    lm_sc : is6_scalars M S (ISP ZP WB) (w_s w);
    lm_lens : cells s6_segs M (S + 168) 2 2 320 (arr_get (is_lens (w_s w)));
    lm_work : cells s6_segs M (S + 808) 2 2 288 (arr_get (is_work (w_s w)));
    lm_codes : cells s6_segs M (S + 1384) 4 4 1444 (arr_get (is_codes (w_s w)));
    lm_win : WN <> 0 -> cells s6_segs M WB 1 1 WN (arr_get (is_window (w_s w)));
    lm_in : cells s6_segs M I0 1 1 NI (arr_get (ic_input (w_c w)));
    lm_out : cells s6_segs M P0 1 1 (ir_put (w_r w)) (arr_get (ic_outbuf (w_c w)));
    lm_zs : izs6 M (w_c w);
    lm_fr : iframe6 M;
    lm_outc : cell s6_segs M (sp - INF_FRAME + 80) 8 (ir_out (w_r w));
    lm_map_f : mapped M (sp - INF_FRAME - INF_SCRATCH) (INF_FRAME + INF_SCRATCH);
    lm_map_Z : mapped M ZP 112;
    lm_map_S : mapped M S 7176;
    lm_map_P : mapped M P0 NO;
    lm_map_W : WN <> 0 -> mapped M WB WN }.

  Definition live_mode (m : Z) : Prop := ~ (FLAGS <= m <= HCRC) /\ m <> SYNC.

  Definition LX (w : iw) : Prop :=
    let s := w_s w in let c := w_c w in let r := w_r w in
    (is_wrap s = 5 \/ is_wrap s = 1) /\ is_wbits s = 15 /\ live_mode (is_mode s)
    /\ (is_flags s = 0 \/ (is_flags s = -1 /\ (is_mode s = HEAD \/ is_mode s = BAD) /\ ir_out r = ir_left r))
    /\ ir_in r = NI /\ - 2 ^ 31 <= ir_ret r < 2 ^ 31
    /\ - 1 <= ic_msg c <= 27
    /\ is_havedict s = 0.

  Definition LFIX (R : bvmap 5 word) : Prop :=
    getr R 2 = zw (sp - INF_FRAME) /\ getr R 8 = zw S /\ getr R 10 = zw ZP /\ getr R 11 = zw flush
    /\ getr R 22 = zw (S + 168) /\ getr R 31 = zw (-16180) /\ getr R 29 = zw 30 /\ getr R 25 = zw A6_JTAB
    /\ getr R 20 = zw 16209
    /\ getr R 3 = getr R0 3 /\ getr R 4 = getr R0 4.
  Definition LVARS (w : iw) (R : bvmap 5 word) : Prop :=
    let r := w_r w in
    getr R 18 = zw (ir_have r) /\ getr R 19 = zw (P0 + ir_put r) /\ getr R 1 = zw (ir_left r)
    /\ getr R 23 = zw (ir_hold r) /\ getr R 24 = zw (ir_bits r)
    /\ getr R 27 = zw (I0 + ir_next r).

  Definition LREG_arm (w : iw) (R : bvmap 5 word) : Prop :=
    LFIX R /\ LVARS w R /\ (is_mode (w_s w) = BAD -> getr R 9 = zw (-3)).

  Definition LREG_leave (w : iw) (R : bvmap 5 word) : Prop :=
    getr R 2 = zw (sp - INF_FRAME) /\ getr R 8 = zw S /\ getr R 10 = zw ZP /\ getr R 11 = zw flush
    /\ getr R 3 = getr R0 3 /\ getr R 4 = getr R0 4
    /\ LVARS w R /\ getr R 9 = zw (ir_ret (w_r w)).

  Definition LREG_ret (rc : Z) (R : bvmap 5 word) : Prop :=
    getr R 2 = zw (sp - INF_FRAME) /\ getr R 21 = zw rc /\ getr R 3 = getr R0 3 /\ getr R 4 = getr R0 4.

  Definition same_blocks (s s' : inflate_state) : Prop :=
    is_self_blk s' = is_self_blk s /\ is_window_blk s' = is_window_blk s /\ is_wbits s' = is_wbits s.

  Definition MFRAME (put0 put1 : Z) (M M' : word -> option byte) : Prop :=
    put0 <= put1
    /\ (forall x : word, M x <> None -> M' x <> None)
    /\ (forall x : word,
          ~ (sp - INF_FRAME - INF_SCRATCH <= bv_unsigned x < sp) -> ~ (S <= bv_unsigned x < S + 7176) ->
          ~ (ZP <= bv_unsigned x < ZP + 112) -> ~ (P0 + put0 <= bv_unsigned x < P0 + put1) ->
          M' x = M x).


  Inductive bkind : Type :=
    | BK_ARM (m : Z)
    | BK_LEAVE
    | BK_RET (rc : Z).

  Definition RETC (w : iw) (M : word -> option byte) : Prop := cell s6_segs M (sp - INF_FRAME + 64) 8 (ir_ret (w_r w)).

  Definition ENTRY (w : iw) (R : bvmap 5 word) (M : word -> option byte) : Prop :=
    LMEM w M /\ RETC w M /\ LX w /\ LREG_arm w R.

  Definition loop_post (w0 : iw) (stop : istop) (w' : iw) (R' : bvmap 5 word) (M' : word -> option byte) : Prop :=
    LMEM w' M' /\ LX w' /\ same_blocks (w_s w0) (w_s w')
    /\ match stop with
       | SLeave => LREG_leave w' R'
       | SRet rc => LREG_ret rc R' /\ rc <> Z_OK /\ - 2 ^ 31 <= rc < 2 ^ 31
       end.
  Definition stop_pc (stop : istop) : Z := match stop with SLeave => pc6_leave | SRet _ => pc6_ret end.

  Definition arm_post (w : iw) (M : word -> option byte) (res : ares unit)
             (R' : bvmap 5 word) (M' : word -> option byte) (pc' : Z) : Prop :=
    match res with
    | ARun _ w' => pc' = arm6_pc (is_mode (w_s w')) /\ ENTRY w' R' M'
                   /\ same_blocks (w_s w) (w_s w') /\ MFRAME (ir_put (w_r w)) (ir_put (w_r w')) M M'
    | ALeave w' => pc' = pc6_leave /\ loop_post w SLeave w' R' M' /\ MFRAME (ir_put (w_r w)) (ir_put (w_r w')) M M'
    | ARet rc w' => pc' = pc6_ret /\ loop_post w (SRet rc) w' R' M' /\ MFRAME (ir_put (w_r w)) (ir_put (w_r w')) M M'
    end.
End Ctx.


Section Stmts.
  Definition arm_stmt (m : Z) : Prop :=
    forall (v : icv) (w : iw) (R : bvmap 5 word) (M : word -> option byte),
      ictx v ->
      is_mode (w_s w) = m ->
      ENTRY v w R M ->
      pinv (cv_NI v) (cv_NO v) (cv_WN v) (cv_TOT0 v) w ->
      exists R' M' pc',
        msteps s6_segs (mkst R (Z_to_bv 64 (arm6_pc m)) M s6_rom) (mkst R' (Z_to_bv 64 pc') M' s6_rom)
        /\ arm_post v w M (dispatch ivar_ref (cv_flush v) w) R' M' pc'.

  Definition loop_stmt : Prop :=
    forall (v : icv) (w : iw) (R : bvmap 5 word) (M : word -> option byte),
      ictx v ->
      ENTRY v w R M ->
      pinv (cv_NI v) (cv_NO v) (cv_WN v) (cv_TOT0 v) w ->
      let '(stop, w') := inf_loop ivar_ref (cv_flush v) w in
      exists R' M',
        msteps s6_segs (mkst R (Z_to_bv 64 (arm6_pc (is_mode (w_s w)))) M s6_rom) (mkst R' (Z_to_bv 64 (stop_pc stop)) M' s6_rom)
        /\ loop_post v w stop w' R' M'
        /\ MFRAME v (ir_put (w_r w)) (ir_put (w_r w')) M M'.
End Stmts.

Lemma wrap15_eqb0 : forall w, w = 5 \/ w = 1 -> (w =? 0) = false.
Proof. intros w [-> | ->]; reflexivity. Qed.
Lemma wrap15_ne0 : forall w, w = 5 \/ w = 1 -> w <> 0.
Proof. intros w [-> | ->]; discriminate. Qed.
Lemma wrap15_and2 : forall w, w = 5 \/ w = 1 -> (Z.land w 2 =? 0) = true.
Proof. intros w [-> | ->]; reflexivity. Qed.
Lemma wrap15_and1 : forall w, w = 5 \/ w = 1 -> (Z.land w 1 =? 0) = false.
Proof. intros w [-> | ->]; reflexivity. Qed.
Lemma wrap15_range : forall w, w = 5 \/ w = 1 -> 0 <= w < 8.
Proof. intros w [-> | ->]; lia. Qed.
End FXG.
