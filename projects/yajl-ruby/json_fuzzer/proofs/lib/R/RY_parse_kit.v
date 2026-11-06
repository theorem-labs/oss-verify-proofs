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
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import Tac Image ZBridge SysStep SFModel SFW1_lemmas InitMem Arr NodesCfg.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import Images.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Common Require Import ShapeAlgCfg.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.R Require Import PortShim.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.R Require Import RMallocRep RMallocTree RMalloc_iface RYajlRep RYajl_iface RY_lib RY_rz RY_kit2.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Agent Require Import MallocBlocks.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import RawAlloc Prelim YajlBase YajlBuf YajlLex YajlDecode YajlParser YajlLeaf YajlFactsBuf YajlFactsLex YajlFactsParse YajlFactsLoop.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)

From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Lemma state_code_range : forall s, 0 <= state_code s < 12.
Proof. intros []; cbn; lia. Qed.

Lemma tok_code_range : forall t, 0 <= tok_code t < 15.
Proof. intros []; cbn; lia. Qed.

(* [comment removed for export] *)
Definition state_target (s : ystate) : Z :=
  match s with
  | ST_start | ST_map_need_val | ST_array_start | ST_array_need_val => 0x15494
  | ST_parse_complete => 0x16124
  | ST_parse_error | ST_lexical_error => 0x15da4
  | ST_map_start | ST_map_need_key => 0x154fc
  | ST_map_sep => 0x15600
  | ST_map_got_val => 0x15558
  | ST_array_got_val => 0x155ac
  end.

(* [comment removed for export] *)
Lemma stack_top_byte : forall s rest junk,
  nth_error (zbytes (stack_bytes (s :: rest)) ++ junk) (Z.to_nat (zlength rest)) = Some (Z_to_bv 8 (state_code s)).
Proof.
  intros s rest junk. rewrite stack_bytes_cons, zbytes_app. cbn [zbytes map].
  rewrite <- app_assoc. cbn [app]. rewrite nth_error_app2 by (rewrite zbytes_length, stack_bytes_length; unfold zlength; lia).
  rewrite zbytes_length, stack_bytes_length. unfold zlength. rewrite Nat2Z.id, Nat.sub_diag. reflexivity.
Qed.

Section S.
Variable HK : RawAlloc.PState -> list block -> (word -> option byte) -> Model -> Prop.
Hypothesis HKS : HK_silent_stmt HK.
Hypothesis HKP : HK_perm_stmt HK.
Hypothesis HKF : HK_frame_stmt HK.
Hypothesis HKB : HK_blocks_stmt HK.
Notation buf_rep := (buf_rep rsegs).
Notation buf_struct := (buf_struct rsegs).
Notation buf_data := (buf_data rsegs).
Notation lexer_rep := (lexer_rep rsegs).
Notation hand_rep := (hand_rep rsegs ryc).
Notation hand_struct := (hand_struct rsegs ryc).
Notation bs_rep := (bs_rep rsegs).
Notation ctx_rep := (ctx_rep rsegs).
Notation text_at := (text_at rsegs).
Notation RYST := (RYST HK).
Notation yparse_head_inv := (yparse_head_inv HK).
Notation yparse_exit_cont := (yparse_exit_cont HK).

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma head_dispatch : forall (ra sp gp tp : word) (s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (H T len : Z)
    (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 s5v s6v s8v : word)
    (h : yhandle) (SB : Z) (s : ystate) (rest : list ystate) (junk : list byte) (pew pad : word) (mh : mhand),
  h_stack h = s :: rest ->
  mh_addr mh = H -> mh_stack mh = SB ->
  rw_cells rsegs m H (hand_cells ryc h mh pew pad) ->
  rw_cells rsegs m SB [CB (Z.to_nat (h_used h)) (zbytes (stack_bytes (h_stack h))); CB (Z.to_nat (h_stack_size h - h_used h)) junk] ->
  0 <= h_stack_size h < 2^31 -> h_used h <= h_stack_size h ->
  mem_inv rsegs m ->
  evt rsegs (fun ms' => ms' = MS (mkR ra sp gp tp t0 t1 t2 (wz H) (wz (H + 48)) (wz (state_target s)) (wz SB) a2 a3 a4 a5 a6 a7
                                   (wz len) (wz T) (wz (H + 32)) (wz 0) s6v (wz 11) s8v (wz RY_JT_TOKVAL) (wz 13) (wz RY_JT_STATE) t3 t4 t5 t6)
                              F (wz (state_target s)) fc None m (seg_rom rsegs))
    (yparse_head_state ra sp gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m H T len (h_used h) t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 s5v s6v s8v).
Proof.
  intros until mh. intros HST EH ESB HC SC SZ US MI.
  unfold yparse_head_state, RY_PARSE_HEAD, RY_JT_TOKVAL, RY_JT_STATE, wz.
  assert (USED : h_used h = zlength rest + 1) by (unfold h_used; rewrite HST; unfold zlength; cbn [length]; lia).
  assert (U0 : 0 <= zlength rest) by (unfold zlength; lia).
  pose proof (rw_cells_bound _ _ _ _ SC) as SCB. cbn [cells_size csize Nat.add] in SCB.
  pose proof (rw_cells_bound _ _ _ _ HC) as HCB. rewrite hand_cells_size in HCB.
  unfold hand_cells, hand_head_cells, alloc_cells in HC. cbn [yc_callbacks yc_malloc_w yc_realloc_w yc_free_w ryc app] in HC.
  rewrite EH, ESB in HC. unfold wz in HC.
  destruct (u8arr_of_CB2 _ _ _ _ _ _ _ SC) as (ARR & L1 & L2).
  pose proof (u8arr_read rsegs m SB _ (h_used h - 1) (Z_to_bv 8 (state_code s)) _ ARR
                ltac:(rewrite HST; replace (Z.to_nat (h_used h - 1)) with (Z.to_nat (zlength rest)) by lia; apply stack_top_byte) ltac:(lia) eq_refl) as RK.
  pose proof (state_code_range s) as CR.
  (* [comment removed for export] *)
  zstep. zstep. zstep. zstep. rewrite (land_M32_small (h_used h + -1)) by lia. zstep.
  replace (SB + (h_used h + -1)) with (SB + (h_used h - 1)) by lia. change (wa (SB + (h_used h - 1))) with (Z_to_bv 64 (SB + (h_used h - 1))) in RK.
  step. clear RK. change (Z_to_bv 8 (state_code s)) with (b8 (state_code s)). rewrite (zxb_b8 (state_code s)) by lia. unfold wz.
  (* [comment removed for export] *)
  step. if_cases K; zify_cond K. { exfalso. revert K. rewrite ?unsigned_lit by lia. lia. }
  (* [comment removed for export] *)
  destruct s; cbn [state_code state_target]; (step; step; step; step; step; step; apply evt_done; reflexivity).
Qed.



(* [comment removed for export] *)
(* [comment removed for export] *)
Record penv := mkPE {
  p_ra : word; p_sp : word; p_gp : word; p_tp : word;
  p_s0 : word; p_s1 : word; p_s2 : word; p_s3 : word; p_s4 : word; p_s5 : word;
  p_s6 : word; p_s7 : word; p_s8 : word; p_s9 : word; p_s10 : word; p_s11 : word;
  p_F : bvmap 5 word; p_fc : bv 32;
  p_T : Z; p_txt : list Z; p_lo : Z; p_B : Z; p_K : TSet;
  p_m0 : mem; p_REST : list block; p_mh : mhand; p_h : yhandle; p_cx : yctx }.

Definition pSP (E : penv) : Z := bv_unsigned (p_sp E).          (* [comment removed for export] *)
Definition pCX (E : penv) : Z := mh_ctx (p_mh E).
Definition pH (E : penv) : Z := mh_addr (p_mh E).
Definition pLEN (E : penv) : Z := zlength (p_txt E).

(* [comment removed for export] *)
Definition pstate (E : penv) (pc : Z) (m : mem) (rav t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 s5v s6v s8v s10v : word) : machine_state :=
  MS (mkR rav (p_sp E) (p_gp E) (p_tp E) t0 t1 t2 (wz (pH E)) (wz (pH E + 48)) a0 a1 a2 a3 a4 a5 a6 a7
          (wz (pLEN E)) (wz (p_T E)) (wz (pH E + 32)) s5v s6v (wz 11) s8v (wz RY_JT_TOKVAL) s10v (wz RY_JT_STATE) t3 t4 t5 t6)
     (p_F E) (wz pc) (p_fc E) None m (seg_rom rsegs).

(* [comment removed for export] *)
Definition yhead_invX (ra sp tp : word) (s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e : word) (F : bvmap 5 word)
    (m : mem) (mo : Model) (s : PState) (REST : list block) (h : yhandle) (mh : mhand) (cx : yctx)
    (T : Z) (txt : list Z) (lo B : Z) : Prop :=
  yparse_head_inv ra sp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e (reg_get F 8%bv) m mo s REST h mh cx T txt lo B
  /\ h_stack_blk h <> None.

(* [comment removed for export] *)
Definition pok (E : penv) : Prop :=
  p_K E [] /\ loop_pre (pLEN E) (p_h E) (p_cx E) /\ 0 < h_used (p_h E) /\ h_stack_blk (p_h E) <> None
  /\ pLEN E < 2^26
  /\ ((exists bt, In bt (p_REST E) /\ blk_addr bt <= p_T E /\ p_T E + pLEN E <= blk_addr bt + blk_size bt) \/ pLEN E = 0)
  /\ pSP E + 144 <= pCX E /\ pCX E + 8 <= p_B E
  /\ (Z.max 0x7fff80000000 (Z.min 0x800000000000 rc_sp) - 8388608) <= p_lo E /\ p_lo E <= pSP E + 144 - 8656 /\ p_tp E = wz RATP /\ p_B E + 144 <= 2^64
  /\ yroom (p_REST E) 8.
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition pmem (E : penv) (m : mem) (mo : Model) (s : PState) (LK : list block) (h : yhandle) (mh : mhand) (cx : yctx) (obw olw : word) : Prop :=
  RYST s (yblocks mh h ++ LK ++ p_REST E) m mo
  /\ hand_rep m h mh /\ mh_same (p_mh E) mh /\ ctx_rep m (pCX E) cx /\ text_at m (p_T E) (p_txt E)
  /\ (exists padw, yparse_frame m (p_sp E) (p_ra E) (p_s0 E) (p_s1 E) (p_s2 E) (p_s3 E) (p_s4 E) (p_s5 E) (p_s6 E) (p_s7 E)
                                 (p_s8 E) (p_s9 E) (p_s10 E) (p_s11 E) (reg_get (p_F E) 8%bv) padw obw olw)
  /\ rauxv_ok m (p_B E) /\ stk rsegs m (p_lo E) (pSP E)
  /\ (exists errv : word, rw_cells rsegs m (errno_addr (p_tp E)) [C4 errv]) /\ mem_inv rsegs m
  /\ ry_pres (p_REST E) (pSP E + 144) [(pCX E, pCX E + 8)] (p_m0 E) m
  /\ h_stack_blk h <> None
  /\ LK = [].               (* [comment removed for export] *)

(* [comment removed for export] *)
Definition again_cont (E : penv) : Prop :=
  forall (rav t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 s5v s6v s8v : word) (m' : mem) (mo' : Model) (s' : PState)
         (h' : yhandle) (cx' : yctx) (mh' : mhand) (LK : list block),
    yleaf (yparse_step jf_callbacks (p_txt E) (pLEN E) (p_h E) (p_cx E)) (SR_again h' cx') ->
    mh_same (p_mh E) mh' -> ry_pres (p_REST E) (pSP E + 144) [(pCX E, pCX E + 8)] (p_m0 E) m' -> LK = [] ->
    yhead_invX (p_ra E) (p_sp E) (p_tp E) (p_s0 E) (p_s1 E) (p_s2 E) (p_s3 E) (p_s4 E) (p_s5 E) (p_s6 E) (p_s7 E)
               (p_s8 E) (p_s9 E) (p_s10 E) (p_s11 E) (p_F E) m' mo' s' (LK ++ p_REST E) h' mh' cx' (p_T E) (p_txt E) (p_lo E) (p_B E) ->
    realizes_cfg acfg rsegs (mkCfg (yparse_head_state rav (p_sp E) (p_gp E) (p_tp E) (p_s0 E) (p_s1 E) (p_s2 E) (p_s3 E) (p_s4 E) (p_s5 E)
                             (p_s6 E) (p_s7 E) (p_s8 E) (p_s9 E) (p_s10 E) (p_s11 E) (p_F E) (p_fc E) m'
                             (pH E) (p_T E) (pLEN E) (h_used h') t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 s5v s6v s8v) mo') (p_K E).

Definition exit_cont (E : penv) : Prop :=
  yparse_exit_cont (p_K E) (p_ra E) (p_sp E) (p_gp E) (p_tp E) (p_s0 E) (p_s1 E) (p_s2 E) (p_s3 E) (p_s4 E) (p_s5 E)
                   (p_s6 E) (p_s7 E) (p_s8 E) (p_s9 E) (p_s10 E) (p_s11 E) (p_F E) (p_fc E) (p_m0 E) (p_REST E) (p_mh E)
                   (p_T E) (p_txt E) (p_lo E) (p_B E)
     (fun r => let '(st, h', cx') := r in yleaf (yparse_step jf_callbacks (p_txt E) (pLEN E) (p_h E) (p_cx E)) (SR_done st h' cx')).

End S.

(* [comment removed for export] *)
Lemma buf_blocks_len : forall mb b, Z.of_nat (length (buf_blocks mb b)) <= 2.
Proof. intros mb b. unfold buf_blocks. destruct (yb_data b); cbn; lia. Qed.
Lemma bs_blocks_len : forall sid SB h, Z.of_nat (length (bs_blocks sid SB h)) <= 1.
Proof. intros. unfold bs_blocks. destruct (h_stack_blk h); cbn; lia. Qed.
Lemma lexer_blocks_len : forall lid L mbl lx, Z.of_nat (length (lexer_blocks lid L mbl lx)) <= 3.
Proof. intros. unfold lexer_blocks. cbn [length]. pose proof (buf_blocks_len mbl (lx_buf lx)). lia. Qed.
Lemma yblocks_len : forall mh h, Z.of_nat (length (yblocks mh h)) <= 7.
Proof.
  intros. unfold yblocks. cbn [length]. rewrite !length_app.
  pose proof (lexer_blocks_len (mh_lid mh) (mh_lexer mh) (mh_lexbuf mh) (h_lexer h)).
  pose proof (buf_blocks_len (mh_decbuf mh) (h_decbuf h)). pose proof (bs_blocks_len (mh_sid mh) (mh_stack mh) h). lia.
Qed.
End RC__1.

(* [comment removed for export] *)
Ltac yroom_solve :=
  repeat match goal with H : ?l = @nil block |- _ => first [subst l | rewrite H in *; clear H] end;
  unfold yroom in *; cbn [length app] in * |-; cbn [length app];
  rewrite ?length_app in * |-; rewrite ?length_app; cbn [length app] in * |-; cbn [length app]; fold block in *;
  repeat match goal with
  | |- context [length (buf_blocks ?a ?b)] => pose proof (buf_blocks_len a b); set (length (buf_blocks a b)) in *
  | |- context [length (bs_blocks ?a ?b ?c)] => pose proof (bs_blocks_len a b c); set (length (bs_blocks a b c)) in *
  | |- context [length (lexer_blocks ?a ?b ?c ?d)] => pose proof (lexer_blocks_len a b c d); set (length (lexer_blocks a b c d)) in *
  | |- context [length (yblocks ?a ?b)] => pose proof (yblocks_len a b); set (length (yblocks a b)) in *
  end;
  rewrite ?NHELDc_val in *; lia.

