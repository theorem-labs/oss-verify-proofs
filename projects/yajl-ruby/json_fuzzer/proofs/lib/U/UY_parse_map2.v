(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import Tac Image ZBridge SysStep SFModel SFW1_lemmas InitMem Arr FP NodesCfg.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import Images.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Common Require Import ShapeAlgCfg.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.R Require Import PortShim.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.U Require Import UMallocRep UMallocTree UMalloc_iface.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.R Require Import RYajlRep.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.U Require Import UYajl_iface.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.R Require Import RY_lib.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.U Require Import UY_rz UY_kit2 UY_parse_kit UY_parse_kitJ UY_parse_kitD UY_parse_map.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Agent Require Import MallocBlocks.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import RawAlloc Prelim YajlBase YajlBuf YajlLex YajlDecode YajlParser YajlLeaf YajlFactsBuf YajlFactsLex YajlFactsDecode YajlFactsParse YajlFactsLoop.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Open Scope yprog_scope.

From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Section S.
Variable HK : RawAlloc.PState -> list block -> (word -> option byte) -> Model -> Prop.
Hypothesis HKS : HK_silent_stmt HK.
Hypothesis HKP : HK_perm_stmt HK.
Hypothesis HKF : HK_frame_stmt HK.
Hypothesis HKB : HK_blocks_stmt HK.
Notation buf_rep := (buf_rep usegs).
Notation buf_struct := (buf_struct usegs).
Notation buf_data := (buf_data usegs).
Notation lexer_rep := (lexer_rep usegs).
Notation hand_rep := (hand_rep usegs ryc).
Notation hand_struct := (hand_struct usegs ryc).
Notation bs_rep := (bs_rep usegs).
Notation ctx_rep := (ctx_rep usegs).
Notation text_at := (text_at usegs).
Notation RYST := (RYST HK).
Notation yparse_head_inv := (yparse_head_inv HK).
Notation yparse_exit_cont := (yparse_exit_cont HK).
Notation pmem := (pmem HK).
Notation again_cont := (again_cont HK).
Notation exit_cont := (exit_cont HK).
Notation yhead_invX := (yhead_invX HK).

Hypothesis YLX : ylex_lex_stmt HK.
Ltac if_lit :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      let v := eval vm_compute in c in change c with v; cbv iota
  end.
Hypothesis YCEM : ycb_end_map_stmt.
Hypothesis YCMK : ycb_map_key_stmt.
Hypothesis YSD : ystring_decode_stmt HK.
Hypothesis YBC : ybuf_clear_stmt.
Hypothesis YBE : ybuf_err_stmt.
Hypothesis YBD : ybuf_data_stmt.
Hypothesis YBL : ybuf_len_stmt.
Hypothesis YBS : ybs_set_stmt.

Lemma pass_map : forall E m mo s h mh cx obw olw st rest
    (rav t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 s5v s6v s8v : word),
  pok E -> pmem E m mo s [] h mh cx obw olw -> h = p_h E -> cx = p_cx E ->
  h_stack h = st :: rest -> map_state st = true ->
  again_cont E -> exit_cont E ->
  realizes_cfg acfg usegs (mkCfg (yparse_head_state rav (p_sp E) (p_gp E) (p_tp E) (p_s0 E) (p_s1 E) (p_s2 E) (p_s3 E) (p_s4 E) (p_s5 E)
                           (p_s6 E) (p_s7 E) (p_s8 E) (p_s9 E) (p_s10 E) (p_s11 E) (p_F E) (p_fc E) m
                           (pH E) (p_T E) (pLEN E) (h_used h) t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 s5v s6v s8v) mo) (p_K E).
Proof.
  intros until s8v. intros OK PM EH ECX HST MS AG EX.
  eapply pass_lex; [exact HKS| exact HKP| exact HKB| exact YLX| exact OK| exact PM| exact EH| exact ECX| exact HST| apply map_state_lex; exact MS|].
  intros until LK'. intros YL LPOST HINV PM1. rewrite (map_state_target _ MS).
  pose proof (pmem_ranges _ HKB _ _ _ _ _ _ _ _ _ _ OK PM1) as (_ & _ & _ & _ & _ & _ & _ & B3).
  assert (HST1 : h_stack (h_set_lex_off h lx' off') = st :: rest) by exact HST.
  pose proof HINV as (_ & OFFB & DBI & DBOK & (FROK & _ & _ & _ & EOL & EAL) & _).
  assert (OL : 0 < cx_objectLevel cx).
  { rewrite EOL, HST. pose proof (count_map_nonneg rest). destruct st; cbn in MS |- *; try discriminate; lia. }
  subst h cx.
  pose proof (step_map (p_txt E) (pLEN E) (p_h E) (p_cx E) st rest lx' tok off' ob n) as SL.
  (* [comment removed for export] *)
  pose proof PM1 as (RY1 & HR1 & _ & _ & _ & _ & _ & _ & _ & MI1 & _). apply RYST_split in RY1. destruct RY1 as [HK1 _].
  pose proof (tok_code_range tok) as TR.
  unfold pstate. cbn [Z.add Pos.add]. unfold wz.
  rz_seg HKS HK1.
  (* [comment removed for export] *)
  assert (GENS : (tok = TK_string \/ tok = TK_string_esc) ->
            exists i0, ob = OB_text i0 /\ 0 <= i0 /\ 0 <= n /\ i0 + n <= pLEN E /\ sbody_ix (p_txt E) i0 (i0 + n)).
  { intros HT. destruct HT as [-> | ->]; cbn -[zslice znth] in LPOST;
      destruct LPOST as (OF1 & _ & _ & _ & _ & i1 & EOB & Hi & Hn & Hin & _ & _ & _ & _ & SB); exists i1; (split; [exact EOB|]);
      (split; [clear -Hi OFFB; lia| split; [exact Hn| split; [clear -Hin OF1; lia| exact SB]]]). }
  destruct tok; cbn [tok_code] in *.
  all: zstep; zstep; zstep; if_lit.
  (* [comment removed for export] *)
  all: try (zstep; zstep; zstep; zstep; zstep; zstep; zstep; zstep).
  all: apply evt_done.
  (* [comment removed for export] *)
  all: first
    [ eapply (map_default HK); first [exact HKS|exact HKP|exact HKF|exact HKB|exact YLX|exact YCEM|exact YCMK|exact YSD|exact YBC|exact YBE|exact YBD|exact YBL|exact YBS|exact OK|exact PM1|exact HST1|exact MS|exact AG|exact EX|exact OL|idtac]
    | change (Z_to_bv 64 2) with (wz (status_code YS_insufficient_data)); eapply (J_exit HK); first [exact HKS|exact HKP|exact HKF|exact HKB|exact YLX|exact YCEM|exact YCMK|exact YSD|exact YBC|exact YBE|exact YBD|exact YBL|exact YBS|exact OK|exact PM1|exact HST1|exact MS|exact AG|exact EX|exact OL|idtac]
    | eapply (map_error HK); first [exact HKS|exact HKP|exact HKF|exact HKB|exact YLX|exact YCEM|exact YCMK|exact YSD|exact YBC|exact YBE|exact YBD|exact YBL|exact YBS|exact OK|exact PM1|exact HST1|exact MS|exact AG|exact EX|exact OL|idtac]
    | eapply (map_rbracket HK); first [exact HKS|exact HKP|exact HKF|exact HKB|exact YLX|exact YCEM|exact YCMK|exact YSD|exact YBC|exact YBE|exact YBD|exact YBL|exact YBS|exact OK|exact PM1|exact HST1|exact MS|exact AG|exact EX|exact OL|idtac]
    | eapply (map_key_tail HK); first [exact HKS|exact HKP|exact HKF|exact HKB|exact YLX|exact YCEM|exact YCMK|exact YSD|exact YBC|exact YBE|exact YBD|exact YBL|exact YBS|exact OK|exact PM1|exact HST1|exact MS|exact AG|exact EX|exact OL|idtac]
    | destruct (GENS (or_intror eq_refl)) as (i0 & -> & I0 & N0 & IN & SBX);
      eapply (map_string_esc HK); first [exact HKS|exact HKP|exact HKF|exact HKB|exact YLX|exact YCEM|exact YCMK|exact YSD|exact YBC|exact YBE|exact YBD|exact YBL|exact YBS|exact OK|exact PM1|exact HST1|exact MS|exact AG|exact EX|exact OL|idtac]
    | idtac "NOARM" ].
  all: try (cbn [outref_addr]; reflexivity).
  all: try exact I0. all: try exact N0. all: try exact IN. all: try exact SBX. all: try exact DBI. all: try exact DBOK.
  (* [comment removed for export] *)
  all: try (intros ->; try (split; [exact OL|])).
  all: try (intros db' YLD HOK). 
  all: lazymatch goal with |- yleaf _ _ => apply (SL _ HST MS YL); cbv beta iota zeta; cbn [h_bytesConsumed h_set_lex_off h_decbuf out_bytes h_stack] | |- _ => idtac end.
  all: try (unfold yparse_error; rewrite (ybs_set_eq _ _ _ _ HST1) by (cbn [h_stack_size h_set_lex_off]; exact (proj2 B3)); cbn [ybind]; apply yl_ret).
  all: try (rewrite (ybs_set_eq _ _ _ _ HST1) by (cbn [h_stack_size h_set_lex_off]; exact (proj2 B3)); cbn [ybind]; apply yl_ret).
  all: try apply yl_ret.
  (* [comment removed for export] *)
  1,2: rewrite (ybs_current_eq _ _ _ HST1); cbn [ybind state_eqb state_code Z.eqb].
  1:{ cbn [cb_end_map jf_callbacks]. unfold yassert. destruct (Z.ltb_spec 0 (cx_objectLevel (p_cx E))); [| lia]. cbn [ybind].
      rewrite (ybs_pop_eq _ _ _ HST1). cbn [ybind]. apply yl_ret. }
  1:{ unfold yparse_error. rewrite (ybs_set_eq _ _ _ _ HST1) by (cbn [h_stack_size h_set_lex_off]; exact (proj2 B3)). cbn [ybind]. apply yl_ret. }
  (* [comment removed for export] *)
  1:{ cbn [cb_map_key jf_callbacks]. unfold yassert. destruct (Z.ltb_spec 0 (cx_objectLevel (p_cx E))); [| lia]. cbn [ybind].
      rewrite (ybs_set_eq _ _ _ _ HST1) by (cbn [h_stack_size h_set_lex_off]; exact (proj2 B3)). cbn [ybind]. apply yl_ret. }
  (* [comment removed for export] *)
  all: unfold ydecode_tok; cbn [h_decbuf h_set_lex_off];
       (eapply yleaf_bind; [eapply yleaf_bind; [apply ybuf_clear_leaf; exact DBOK|]; cbv beta; eapply yleaf_bind; [exact YLD|]; apply yl_ret|]);
       cbv beta; cbn [h_decbuf h_set_decbuf]; unfold ybuf_err, buf_state_ok, ybuf_data_chk, ybuf_len_chk.
  1:{ rewrite HOK. cbn [negb ybind cb_map_key jf_callbacks]. unfold yassert. destruct (Z.ltb_spec 0 (cx_objectLevel (p_cx E))); [| lia]. cbn [ybind].
      rewrite (ybs_set_eq _ st rest) by (first [exact HST| cbn [h_stack_size h_set_decbuf h_set_lex_off]; unfold h_used; cbn [h_stack h_set_decbuf h_set_lex_off]; unfold h_used in B3; exact (proj2 B3)]).
      cbn [ybind]. apply yl_ret. }
  1:{ destruct (yb_state db'); [congruence| |]; cbn [negb ybind]; unfold ybuf_chk_fail;
      (rewrite (ybs_set_eq _ st rest) by (first [exact HST| cbn [h_stack_size h_set_decbuf h_set_lex_off]; unfold h_used; cbn [h_stack h_set_decbuf h_set_lex_off]; unfold h_used in B3; exact (proj2 B3)]));
      cbn [ybind]; apply yl_ret. }
Qed.

End S.
End RC__1.
