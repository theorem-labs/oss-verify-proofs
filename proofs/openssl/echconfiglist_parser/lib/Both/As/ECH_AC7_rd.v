(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Arr Bytes ZBridge SysStep Exec CellsX TacX Frame.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow AsConst AsIface AsIfaceX AsCXXHeap AsCall AsCallX ECH_AImg ECH_Xpres ECH_ARep ECH_ALib ECH_Iface
  ECH_AStmt_C1 ECH_AStmt_C6 ECH_AStmt_C7 ECH_AKit ECH_AsKit ECH_AC7_kit.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import N6_tac.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import Prelim.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import StoreDj InNth.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_n8 segs m a bs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section S.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Local Ltac kill K := exfalso; revert K; rewrite ?unsigned_lit, ?signed_lit by lia; lia.

  (* [comment removed for export] *)
  Lemma amemctrl_body : forall (cmd : Z), (cmd = BIO_CTRL_EOF \/ cmd = BIO_CTRL_PUSH) ->
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (LB : list block) (a larg parg lo : Z) (R : membio),
      a0 = Z_to_bv 64 a -> a1 = Z_to_bv 64 cmd -> a2 = Z_to_bv 64 larg -> a3 = Z_to_bv 64 parg ->
      0 <= larg < 2^63 -> 0 <= parg < 2^64 ->
      MEMBIO H LB m a R -> MEMBIO_below a R lo -> MEMBIO_shad m a R -> ACONST m ->
      stk asegs m lo (bv_unsigned sp) -> aceil <= lo -> lo <= bv_unsigned sp - 64 -> mem_inv asegs m -> bv_unsigned ra mod 2 = 0 ->
      evt asegs (memctrl_post H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc LB (mem_ctrl_rv R cmd) a R lo m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 P_mem_ctrl) fc None m (seg_rom asegs)).
  Proof.
    intros cmd CMD. intros until R. intros A0 A1 A2 A3 LR PR MB BL SH AC ST CEIL LO MI RAE. subst a0 a1 a2 a3.
    unfold P_mem_ctrl, mem_ctrl_rv, mb_avail in *. acb.
    membio_open m a R MB BL SH AC.
    pose proof (aword_range sp) as SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    carve_frame 64%nat ST.
    do 9 step.                                                    (* [comment removed for export] *)
    membio_reacc MU.
    (* [comment removed for export] *)
    unfold id in ACCa, ACCbb, ACCbm, ACCrp. repeat step. ub_dead. repeat step. ubal_by AAL. if_lit. repeat step. zsimp. ck8_check ACCa (a + 64).
    (* [comment removed for export] *)
    repeat zstep. ck8_load ACCa (a + 48). step. step. if_false_by (ck1_bnez_false 0 eq_refl).
    (* [comment removed for export] *)
    repeat zstep. ub_dead. repeat zstep. ubal_by BBAL. if_lit.
    repeat zstep. rewrite zx32_lit by lia. rewrite ?(unsigned_lit (mb_flags R)) by lia. rewrite RDO. if_lit.
    (* [comment removed for export] *)
    repeat zstep. ck8_check ACCbb (mb_bb R).
    repeat zstep. ck8_check ACCbb (mb_bb R + 8).
    repeat zstep. ub_dead. repeat zstep. ubal_by BMAL. if_lit.
    repeat zstep. ck8_check ACCbm (mb_bm R + 8).
    repeat zstep. ub_dead. repeat zstep. ubal_by RPAL. if_lit.
    repeat zstep. ck8_check ACCrp (mb_rp R + 8). repeat zstep. ck8_check ACCbm (mb_bm R). repeat zstep.
    destruct CMD as [-> | ->].
    - (* [comment removed for export] *)
      if_lit. repeat zstep. if_lit. repeat zstep.
      change (2 =? 2) with true. cbv iota.
      (* [comment removed for export] *)
      ck8_check ACCa (a + 56).
      (* [comment removed for export] *)
      assert (FIN : forall a0v a6v : word,
        evt asegs (memctrl_post H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc LB (if mb_len R - mb_pos R =? 0 then 1 else 0) a R lo m)
          (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp
                   (Z_to_bv 64 (Z.shiftr (a + 48) 3 + 2147450880)) (Z_to_bv 64 (Z.shiftr (mb_bm R + 8) 3 + 2147450880)) (Z_to_bv 64 (mb_len R - mb_pos R)) sp
                   (Z_to_bv 64 larg) a0v (Z_to_bv 64 0)
                   (Z_to_bv 64 (mb_bm R)) (Z_to_bv 64 (mb_rp R)) (Z_to_bv 64 (mb_bm R + 8)) (Z_to_bv 64 (mb_rp R + 8)) a6v (Z_to_bv 64 512)
                   (Z_to_bv 64 (mb_bb R)) (Z_to_bv 64 parg) (Z_to_bv 64 a) (Z_to_bv 64 (Z.b2z (mb_len R - mb_pos R <? 1))) (Z_to_bv 64 2147450880) s7 s8 s9 s10 s11
                   (Z_to_bv 64 (Z.shiftr (mb_bm R) 3 + 2147450880)) (Z_to_bv 64 (mb_buf R + mb_pos R)) (Z_to_bv 64 113) t6)
              F (Z_to_bv 64 0x417f0c) fc None m1 (seg_rom asegs))).
      { intros a0v a6v. zstep.
        replace (Z.b2z (mb_len R - mb_pos R <? 1)) with (if mb_len R - mb_pos R =? 0 then 1 else 0)
          by (unfold Z.b2z; destruct (Z.ltb_spec (mb_len R - mb_pos R) 1); destruct (Z.eqb_spec (mb_len R - mb_pos R) 0); lia).
        do 10 step.
        release_frame FR ST (bv_unsigned sp). unfold memctrl_post. finish.
        all: try (eapply ACONST_stack_frame7; [exact AC| exact MU| exact WM| exact CEIL]). all: try membio_tac. }
      cbv delta [mkR] in FIN.
      zstep. step. if_cases K2; zify_cond K2.
      + do 2 zstep. apply FIN.
      + zstep. zstep. rewrite NUMR. rewrite sx32_lit by lia. if_lit. do 2 zstep. apply FIN.
    - (* [comment removed for export] *)
      if_lit. repeat zstep. if_lit.
      change (6 =? 2) with false. cbv iota.
      repeat zstep.
      release_frame FR ST (bv_unsigned sp). unfold memctrl_post. finish.
      all: try (eapply ACONST_stack_frame7; [exact AC| exact MU| exact WM| exact CEIL]). all: try membio_tac.
  Qed.

  Lemma amemctrl_spec : memctrl_stmt H.
  Proof.
    unfold memctrl_stmt, memctrl_stmt_at, MEMCTRL_STACK, FR_mem_ctrl. intros until R. intros A0 A1 A2 A3 CMD LR PR MB BL SEP NM SH AC ST CEIL LO MI RAE.
    eapply amemctrl_body; eassumption.
  Qed.

  (* [comment removed for export] *)
  Lemma abioctrl_mem_spec : bioctrl_mem_stmt H.
  Proof.
    unfold bioctrl_mem_stmt, memctrl_stmt_at, BIOCTRL_STACK, MEMCTRL_STACK, FR_BIO_ctrl, FR_mem_ctrl.
    intros until R. intros A0 A1 A2 A3 CMD LR PR MB BL SEP NM SH AC ST CEIL LO MI RAE. specialize (NM eq_refl). subst a0 a1 a2 a3.
    unfold P_BIO_ctrl in *. acb.
    pose proof BL as BL0. pose proof SH as SH0.
    membio_open m a R MB BL SH AC.
    assert (CMDR : 0 <= cmd < 7) by (unfold BIO_CTRL_EOF, BIO_CTRL_PUSH in CMD; lia).
    pose proof (aword_range sp) as SPR. pose proof (aword_range ra) as RAR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    (* [comment removed for export] *)
    pose proof NM as MT. unfold METH_mem, O_METH_BREAD, wz in MT. unfold A_mem_buf_method in MT.
    assert (IN : In (A_mem_buf_method, 112, 112) aglobals) by (unfold A_mem_buf_method; in_nth).
    pose proof (ACONST_global_addressable m _ 112 112 AC IN ltac:(lia)) as ADmt.
    assert (ACCmt : id (accessible m A_mem_buf_method 112)).
    { unfold id. eapply addressable_accessible; [exact ADmt| lia| lia| unfold A_mem_buf_method, AAPP_HI; lia]. }
    unfold A_mem_buf_method in ACCmt, ADmt. unfold A_mem_buf_method in BC. norm_addr MT.
    carve_frame 96%nat ST.
    do 12 step.                                                        (* [comment removed for export] *)
    step.                                                              (* [comment removed for export] *)
    pose proof ACCa as ACCa0. hide ACCa0.
    membio_reacc MU. unfold id in ACCa, ACCbb, ACCbm, ACCrp, ACCmt.
    (* [comment removed for export] *)
    step. if_cases K0; zify_cond K0; [kill K0|]. clear K0.
    step. step. ubal_by AAL. step. if_lit. step. step.
    (* [comment removed for export] *)
    do 4 step. zsimp. ck8_check ACCa (a + 8).
    (* [comment removed for export] *)
    st1. step. if_false. step.
    (* [comment removed for export] *)
    step. step. if_lit. zstep. zstep. zstep. ck8_check_lit ACCmt (0x5ae5a0 + 64).
    (* [comment removed for export] *)
    st1. step. if_false.
    (* [comment removed for export] *)
    repeat zstep. ck8_check ACCa (a + 16).
    (* [comment removed for export] *)
    step. step. st1. step. if_lit.
    (* [comment removed for export] *)
    repeat zstep. ck8_check ACCa (a + 24). st1. step. if_lit.
    (* [comment removed for export] *)
    ck8_check ACCa (a + 8). st1. step. if_lit. step. step. if_lit. repeat zstep. ck8_check_lit ACCmt (0x5ae5a0 + 64). st1.
    (* [comment removed for export] *)
    step. step. step. step. unfold P_mem_ctrl. step.
    eapply evt_cut.
    { eapply (amemctrl_body cmd CMD) with (lo := lo) (R := R) (LB := LB);
        [reflexivity| reflexivity| reflexivity| reflexivity| exact LR| exact PR| membio_tac| exact BL0
        | eapply (MEMBIO_shad_across_stack H LB m); [exact MB| exact SH0| exact MU| exact WM| exact CEIL]
        | eapply ACONST_stack_frame7; [exact AC| exact MU| exact WM| exact CEIL]
        | rewrite unsigned_lit by lia; exact ST| exact CEIL| rewrite unsigned_lit by lia; lia| assumption| rewrite unsigned_lit by lia; reflexivity]. }
    unfold memctrl_post. 
    lazymatch goal with |- forall s', _ -> evt _ _ _ => idtac end.
    alandx MU WM. clear ACCa ACCbb ACCbm ACCrp ACCmt.
    unhide ACCa0. unfold id in ACCa0. pose proof (accessible_across_stack _ _ _ _ _ _ ACCa0 MU CEIL) as ACCa.
    (* [comment removed for export] *)
    ck8_check ACCa (a + 16). step. st1. step. if_lit.
    (* [comment removed for export] *)
    repeat zstep. ck8_check ACCa (a + 24). st1. step. if_lit.
    (* [comment removed for export] *)
    step. do 11 st1. step. step.
    release_frame FR ST (bv_unsigned sp). finish.
  Qed.

  (* [comment removed for export] *)
  Lemma abioeof_mem_spec : bioeof_mem_stmt H.
  Proof.
    unfold bioeof_mem_stmt. intros until R. intros A0 MB BL SEP NM SH AC ST CEIL LO MI RAE. subst a0.
    unfold P_BIO_eof, BIOEOF_STACK, BIOCTRL_STACK, MEMCTRL_STACK, FR_BIO_eof, FR_BIO_ctrl, FR_mem_ctrl in *. acb.
    pose proof BL as BL0. pose proof SH as SH0.
    membio_open m a R MB BL SH AC.
    pose proof (aword_range sp) as SPR. pose proof (aword_range ra) as RAR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    pose proof NM as MT. unfold METH_mem, O_METH_BREAD, A_mem_buf_method, wz in MT. norm_addr MT.
    carve_frame 16%nat ST.
    do 4 step.                                                         (* [comment removed for export] *)
    membio_reacc MU. unfold id in ACCa. clear ACCbb ACCbm ACCrp.
    (* [comment removed for export] *)
    step. ub_dead. step. ubal_by AAL. step. if_lit. step. step. step. zstep. zstep. zstep. ck8_check ACCa (a + 48).
    (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
      assert (BCx : rw_cells asegs mc a (bio_cells (membio_bio R)))
        by (unfold bio_cells, membio_bio, wz; cbn [bio_method bio_init bio_shutdown bio_flags bio_retry bio_numf bio_ptr bio_next bio_prev bio_refs bio_nread bio_nwrite]; exact BC) end.
    pose proof (bio_flags_byte _ _ _ BCx) as RD. cbn [bio_flags membio_bio] in RD. clear BCx. st1. clear RD.
    zstep. rewrite wz_unsigned by lia. rewrite land_mod256_128, AEOF by lia. step. if_false.
    (* [comment removed for export] *)
    step. step. step. unfold P_BIO_ctrl. step.
    pose proof abioctrl_mem_spec as BCS. unfold bioctrl_mem_stmt, memctrl_stmt_at, BIOCTRL_STACK, MEMCTRL_STACK, FR_BIO_ctrl, FR_mem_ctrl, P_BIO_ctrl in BCS.
    eapply evt_cut.
    { eapply BCS with (lo := lo) (R := R) (LB := LB) (cmd := BIO_CTRL_EOF); clear BCS;
        [reflexivity| reflexivity| reflexivity| reflexivity| left; reflexivity| lia| lia| membio_tac| exact BL0| exact SEP| intros _; unfold METH_mem, O_METH_BREAD, A_mem_buf_method; exact MT
        | eapply (MEMBIO_shad_across_stack H LB m); [exact MB| exact SH0| exact MU| exact WM| exact CEIL]
        | eapply ACONST_stack_frame7; [exact AC| exact MU| exact WM| exact CEIL]
        | rewrite unsigned_lit by lia; exact ST| exact CEIL| rewrite unsigned_lit by lia; lia| assumption| rewrite unsigned_lit by lia; reflexivity]. }
    clear BCS. unfold memctrl_post. alandx MU WM.
    assert (RV : 0 <= mem_ctrl_rv R BIO_CTRL_EOF <= 1) by (unfold mem_ctrl_rv; destruct (BIO_CTRL_EOF =? BIO_CTRL_EOF); [destruct (mb_avail R =? 0)|]; lia).
    (* [comment removed for export] *)
    step. zstep. rewrite swrap32_small by lia. st1. st1. step. step.
    release_frame FR ST (bv_unsigned sp). finish.
  Qed.
End S.
