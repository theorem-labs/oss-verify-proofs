(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QXup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXup. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q5Rg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q5Rg. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Lib.GwApply.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QCcH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCcH. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q0Ek.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q0Ek. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qsw7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qsw7. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QJjn.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJjn. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QRUw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRUw. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q8tj.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q8tj.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QSL3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QSL3.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q9Mh.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q9Mh.Mq3.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QAyu.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QAyu.Mq3.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QXOI.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXOI.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QheR.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QheR.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QnCn.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QnCn.
Import ListNotations. Unset Keyed Unification. Local Ltac Qfw3.Mq3.model_reg_tac n X mexpr ::= Qfw3.Mq3.mkr__model_reg_tac_1 n X mexpr.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q0Hd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q0Hd.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib Require Import CodeAt StepGen StepGenX StepGenX2 GwCallee GwApply GwApply2 GwApplyJ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac step_core segs R F pc fc rv m ro ::= sg_step_core; gwj_pc_norm; gwj_align_norm. Local Ltac mkr__step_core_0 segs R F pc fc rv m ro := sg_step_core; gwj_pc_norm; gwj_align_norm.
Local Ltac zstep ::= sg_zstep; gwj_pc_norm; gwj_align_norm. Local Ltac mkr__zstep_1 := sg_zstep; gwj_pc_norm; gwj_align_norm.
Local Ltac post_call segs m ::= g_post_call segs m. Local Ltac mkr__post_call_2 segs m := g_post_call segs m.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QxiR Q7mx.

Section G.
Variables (segs : list Segment) (base : Z).
Variables (w_12 w_13 : Z).
Variables (hi_12 : bv 20).
Variables (lo_13 : bv 12).
Variables (G_10760 : Z).
Context {RC__ : Q6q3.RunConsts}.
Variables (e_malloc e_free e_calloc e_realloc e_malloc2 e_free2 gTP gGOTG gGUARD gAUXV gLIBC : Z) (gVOL gCS : Z -> Prop) (gHEXGOT gHEXPTR gHEXCHARS gIMG_LO gIMG_HI : Z).
Hypothesis gH1 : forall a, gCS a -> (gIMG_LO <= a < gIMG_HI)%Z.
Hypothesis gH2 : gl_range_ok gIMG_LO gIMG_HI.
Hypothesis gH3 : forall a, (gTP - 164 <= a < gTP - 160)%Z -> (gIMG_LO <= a < gIMG_HI)%Z.
Hypothesis gH4 : forall a, (gTP - 164 <= a < gTP - 160)%Z -> ~ gCS a.
Hypothesis gH5 : forall c a, In c [(gHEXGOT, le8 (Z_to_bv 64 gHEXPTR)); (gHEXPTR, le8 (Z_to_bv 64 gHEXCHARS))] -> (fst c <= a < fst c + Z.of_nat (length (snd c)))%Z ->
~ gCS a /\ ~ (gTP - 164 <= a < gTP - 160)%Z /\ (gIMG_LO <= a < gIMG_HI)%Z.
Hypothesis LAY_gIMG_LO : (gIMG_LO = 65536)%Z.
Hypothesis LAY_TPLO : gw_le gIMG_LO (gTP - 164).
Hypothesis LAY_TPHI : gw_le (gTP - 160) gIMG_HI.
Hypothesis AL_gTP : gw_al gTP 4.
Hypothesis RNG_gTP : gw_br gTP 8.

#[using="LAY_gIMG_LO LAY_TPLO LAY_TPHI"] Lemma gLAYF0 : ((gIMG_LO <= gTP - 164 /\ gTP - 160 <= gIMG_HI) /\ gIMG_LO = 65536)%Z.
Proof. clear - LAY_gIMG_LO LAY_TPLO LAY_TPHI gTP gIMG_LO gIMG_HI. pose proof LAY_TPLO as X1; pose proof LAY_TPHI as X2; unfold gw_le in X1, X2. split; [split; [exact X1 | exact X2] | exact LAY_gIMG_LO]. Qed.
Variables (e_fn_obj_to_json_string e_fn_arr_to_json_string e_fn_bool_to_json_string e_fn_dbl_to_json_string e_fn_int_to_json_string e_fn_str_to_json_string e_fn_ud_to_json_string e_fn_free_userdata e_fn_lh_entry_free e_fn_lh_char_hash e_fn_lh_char_equal e_fn_arr_entry_free : Z).
Hypothesis CODE : code_at segs base (QxiR.ulhprobe_code w_12 w_13).
Hypothesis BASE4 : gw_b4 base.
Hypothesis BASER : gw_br base 484.
Hypothesis D_12 : decode_any (Z_to_bv 32 w_12) = Some (Auipc 17 hi_12, 4%Z).
Hypothesis E_12 : is_ecall (Z_to_bv 32 w_12) = false.
Hypothesis D_13 : decode_any (Z_to_bv 32 w_13) = Some (FLoad FMT_D 15 17 lo_13, 4%Z).
Hypothesis E_13 : is_ecall (Z_to_bv 32 w_13) = false.
Hypothesis ANCH_13 : gw_anch (Z.shiftl (bv_signed hi_12) 12 + (base + 48) + bv_signed lo_13)%Z G_10760.
Hypothesis RNG_G_10760 : gw_br G_10760 8.
Hypothesis ROM_G_10760 : ro_bytes segs G_10760 [Z_to_bv 8 31; Z_to_bv 8 133; Z_to_bv 8 235; Z_to_bv 8 81; Z_to_bv 8 184; Z_to_bv 8 30; Z_to_bv 8 229; Z_to_bv 8 63].

Hypothesis ent_addr_mod8 : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty2 (@QXOI.gw_all) (@QXOI.ent_addr_mod8) (base + 484)%Z)) in let T := eval cbv beta delta [QXOI.u_lh_entry_free_entry QXOI.u_lh_table_free_entry] in T in let T := gw_fold_pcs T base (484)%Z [0; 48; 80]%Z in exact T).
Arguments ent_addr_mod8 _%_Z_scope _%_nat_scope.

Let U4L : heap_layout :=
{| hl_segs := segs;
hl_malloc := e_malloc; hl_free := e_free; hl_calloc := e_calloc; hl_realloc := e_realloc; hl_malloc2 := e_malloc2; hl_free2 := e_free2;
hl_tp := gTP;
hl_got_guard := gGOTG; hl_guard := gGUARD; hl_auxv := gAUXV; hl_libc := gLIBC; hl_volatile := gVOL;
hl_stack := 8256;
hl_client_static := gCS;
hl_scratch := fun a => (gTP - 164 <= a < gTP - 160)%Z;
hl_consts := [(gHEXGOT, le8 (Z_to_bv 64 gHEXPTR)); (gHEXPTR, le8 (Z_to_bv 64 gHEXCHARS))];
hl_img_lo := gIMG_LO; hl_img_hi := gIMG_HI;
hl_static_in_img := gH1; hl_img_range := gH2; hl_scratch_in_img := gH3; hl_scratch_not_static := gH4; hl_consts_ok := gH5 |}.
Let U4F : fnaddrs := {| fn_obj_to_json_string := e_fn_obj_to_json_string; fn_arr_to_json_string := e_fn_arr_to_json_string; fn_bool_to_json_string := e_fn_bool_to_json_string; fn_dbl_to_json_string := e_fn_dbl_to_json_string; fn_int_to_json_string := e_fn_int_to_json_string; fn_str_to_json_string := e_fn_str_to_json_string; fn_ud_to_json_string := e_fn_ud_to_json_string; fn_free_userdata := e_fn_free_userdata; fn_lh_entry_free := e_fn_lh_entry_free; fn_lh_char_hash := e_fn_lh_char_hash; fn_lh_char_equal := e_fn_lh_char_equal; fn_arr_entry_free := e_fn_arr_entry_free |}.
#[using="w_12 w_13 hi_12 lo_13 G_10760 RC__ e_malloc e_free e_calloc e_realloc e_malloc2 e_free2 gTP gGOTG gGUARD gAUXV gLIBC gVOL gCS gHEXGOT gHEXPTR gHEXCHARS gIMG_LO gIMG_HI gH1 gH2 gH3 gH4 gH5 LAY_gIMG_LO LAY_TPLO LAY_TPHI AL_gTP RNG_gTP e_fn_obj_to_json_string e_fn_arr_to_json_string e_fn_bool_to_json_string e_fn_dbl_to_json_string e_fn_int_to_json_string e_fn_str_to_json_string e_fn_ud_to_json_string e_fn_free_userdata e_fn_lh_entry_free e_fn_lh_char_hash e_fn_lh_char_equal e_fn_arr_entry_free CODE BASE4 BASER D_12 E_12 D_13 E_13 ANCH_13 RNG_G_10760 ROM_G_10760 ent_addr_mod8 U4F"] Lemma gw_all : True. Proof. exact I. Qed.

Definition hdr_cells := ltac:(let t := constr:(ltac:(gw_ctx2 (@Q7mx.hdr_cells))) in let t := eval cbv beta delta [Q7mx.hdr_cells] in t in exact t).

Definition u_ins_frame (sp rac s0c s1c s2c s3c s4c : word) (m : word -> option byte) : Prop :=
  rw_cells segs m (bv_unsigned sp + -48) [C8 s4c; C8 s3c; C8 s2c; C8 s1c; C8 s0c; C8 rac].

Section UStore.
Variables (sp gp tp : word) (s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (t tbl size k v opts : Z) (es : list lent) (svs : list slotv) (ffn : Z).
Variables (rac s0c s1c s2c s3c s4c : word).

Definition u_store_block_stmt : Prop :=
  forall (g : Z) (sg : slotv) (cnt hd tl : Z) (ixl : nat) (sl : slotv)
    (x1 x8 x9 x18 x19 x20 x29 x30 x31 : word) (m : word -> option byte) (lo : Z),
  0 <= g < size -> In size lf_sizes -> Z.of_nat (length svs) = size -> nth_error svs (Z.to_nat g) = Some sg ->
  0 <= cnt < size -> 0 <= k < 2^64 -> 0 <= v < 2^64 -> 0 <= ffn < 2^64 -> opts = 0 ->
  (hd = 0 /\ tl = 0) \/ (hd <> 0 /\ tl = ent_addr tbl ixl /\ nth_error svs ixl = Some sl /\ ixl <> Z.to_nat g /\ 0 <= hd < 2^64) ->
  0 < t -> t mod 16 = 0 -> t + 56 <= lo -> 0 < tbl -> tbl mod 16 = 0 -> tbl + 40 * size <= lo ->
  (t + 56 <= tbl \/ tbl + 40 * size <= t) ->
  lo <= bv_unsigned sp - 48 ->
  mem_inv segs m ->
  rw_cells segs m t (hdr_cells tbl ffn size cnt hd tl) ->
  lh_slots segs m tbl svs ->
  u_ins_frame sp rac s0c s1c s2c s3c s4c m -> stk segs m lo (bv_unsigned sp + -48) ->
  evt segs (fun ms' => exists (x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29' x30' x31' : word) m',
      ms' = MS (mkR rac sp gp tp x5 x6 x7 s0c s1c (Z_to_bv 64 0)
                 x11 x12 x13 x14 x15 x16 x17
                 s2c s3c s4c s5 s6 s7 s8 s9 s10 s11 x28 x29' x30' x31')
           F (ret_pc rac) fc None m' (seg_rom segs)
      /\ munch [(t, t + 56); (tbl, tbl + 40 * size)] m m' /\ wmono segs m m' /\ mem_inv segs m'
      /\ rw_cells segs m' t (hdr_cells tbl ffn size (cnt + 1) (if hd =? 0 then ent_addr tbl (Z.to_nat g) else hd) (ent_addr tbl (Z.to_nat g)))
      /\ lh_slots segs m' tbl (Q7mx.ins_svs svs (Z.to_nat g) sg k v hd tl ixl sl tbl)
      /\ stk segs m' lo (bv_unsigned sp))
    (MS (QxiR.u_ins_regs sp gp tp s5 s6 s7 s8 s9 s10 s11 t tbl size k v opts x1 (Z_to_bv 64 0) x8 x9 g (Z_to_bv 64 (tbl + g * 40)) x18 x19 x20 (Z_to_bv 64 (sv_k sg)) x29 x30 x31)
        F (Z_to_bv 64 (base + 0x15c)) fc None m (seg_rom segs)).

Definition u_ins_tail_post (cnt lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists (g : nat) (sg : slotv) (ixl : nat) (sl : slotv)
      (x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) m',
    (g < length svs)%nat /\ nth_error svs g = Some sg /\ is_free sg /\ ~ In g (map le_ix es) /\
    (es <> [] -> exists jl el, nth_error es jl = Some el /\ (S jl = length es)%nat /\ ixl = le_ix el /\ nth_error svs ixl = Some sl) /\
    ms' = MS (mkR rac sp gp tp x5 x6 x7 s0c s1c (Z_to_bv 64 0)
               x11 x12 x13 x14 x15 x16 x17
               s2c s3c s4c s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
         F (ret_pc rac) fc None m' (seg_rom segs)
    /\ munch [(t, t + 56); (tbl, tbl + 40 * size)] m m' /\ wmono segs m m' /\ mem_inv segs m'
    /\ rw_cells segs m' t (hdr_cells tbl ffn size (cnt + 1) (match es with [] => ent_addr tbl g | _ => hd_of tbl es end) (ent_addr tbl g))
    /\ lh_slots segs m' tbl (Q7mx.ins_svs svs g sg k v (hd_of tbl es) (tl_of tbl es) ixl sl tbl)
    /\ stk segs m' lo (bv_unsigned sp).

Definition u_ins_tail_stmt : Prop :=
  forall (h cnt lo : Z) (x1 x5 x6 x7 x8 x9 x15 x17 x18 x19 x20 x28 x29 x30 x31 : word) (m : word -> option byte),
  0 <= h < 2^64 -> In size lf_sizes -> Z.of_nat (length svs) = size -> cnt = Z.of_nat (length es) -> cnt < size ->
  lh_link tbl es svs -> lh_keys segs m es -> 0 <= k < 2^64 -> 0 <= v < 2^64 -> 0 <= ffn < 2^64 -> opts = 0 ->
  0 < t -> t mod 16 = 0 -> t + 56 <= lo -> 0 < tbl -> tbl mod 16 = 0 -> tbl + 40 * size <= lo ->
  (t + 56 <= tbl \/ tbl + 40 * size <= t) ->
  lo <= bv_unsigned sp - 48 ->
  mem_inv segs m ->
  rw_cells segs m t (hdr_cells tbl ffn size cnt (hd_of tbl es) (tl_of tbl es)) ->
  lh_slots segs m tbl svs ->
  u_ins_frame sp rac s0c s1c s2c s3c s4c m -> stk segs m lo (bv_unsigned sp + -48) ->
  evt segs (u_ins_tail_post cnt lo m)
    (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp x5 x6 x7 x8 x9
          (Z_to_bv 64 t) (Z_to_bv 64 k) (Z_to_bv 64 v) (Z_to_bv 64 h) (Z_to_bv 64 opts) x15 (Z_to_bv 64 size) x17
          x18 x19 x20 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
        F (Z_to_bv 64 (base + 0xb8)) fc None m (seg_rom segs)).

End UStore.

End G.
