(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.skcms.iccprofile_info.images Require Import Asan.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require Import PropExec CatExec CatSim SeqExec StoreOk SymExec Hoare Frame PropExecFP.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require Import LibDefs.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.AsLib Require Import AsSymExec AsSymExecSound AsSymRun AsSymDrive AsSymCall AsFuzzContract AsLibShadow AsLibDefs AsRtSpec AsLibTagsLib AsLibPlace.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.AsLib Require Import AsSymDriveLZ.
Unset Lia Cache. Unset Nia Cache.   (* [comment removed for export] *)
From Stdlib Require Import Zify.
(* [comment removed for export] *)
Local Ltac el_t1 := (intros; Zify.zify_pre_hook; zify_elim_let; zify_op; zify_iter_specs; Zify.zify_post_hook); xlia zchecker.
(* [comment removed for export] *)
Local Ltac el_dm_pose x k := let v := eval vm_compute in k in lazymatch v with Zpos _ =>   (* [comment removed for export] *)
  lazymatch goal with _ : (x = k * (x / k) + x mod k)%Z |- _ => fail | _ =>
    pose proof (Z.div_mod x k ltac:(vm_compute; discriminate)); pose proof (Z.mod_pos_bound x k ltac:(vm_compute; reflexivity)) end end.
Local Ltac el_dm := repeat match goal with
  | |- context [ (?x / ?k)%Z ] => el_dm_pose x k
  | |- context [ (?x mod ?k)%Z ] => el_dm_pose x k
  | H : ?T |- _ => lazymatch T with (_ <= _)%Z => idtac | (_ < _)%Z => idtac | @eq Z _ _ => idtac | _ /\ _ => idtac | _ \/ _ => idtac end;
      match T with context [ (?x / ?k)%Z ] => el_dm_pose x k | context [ (?x mod ?k)%Z ] => el_dm_pose x k end
  end.
Local Ltac el_lia_core3 := first [ el_t1 | Zify.zify; xlia zchecker ].   (* [comment removed for export] *)
Local Ltac el_lia_core := first [ el_t1 | ((progress el_dm); el_t1) ].
Local Ltac el_goal_has_var := match goal with |- ?G => match G with context [?x] => is_var x end end.
Local Ltac Lia.lia ::= tryif el_goal_has_var then el_lia_core else first [ solve [clear; el_lia_core] | el_lia_core ].
Import ListNotations.
Open Scope bv_scope.
Import ASX. Import ASXS.
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac ev_simpl E ::=
  lazymatch goal with |- ?G =>
    let G1 := match tt with | _ => eval unfold E in G | _ => G end in
    let G2 := eval lazy [ev eb vals_ev blobs_ev nth app junk_vals fjunk_vals] in G1 in
    change G2
  end.
Local Ltac ev_simpl_in E H ::= try unfold E in H; lazy [ev eb vals_ev blobs_ev nth app junk_vals fjunk_vals] in H.
(* [comment removed for export] *)
#[local] Ltac AsSymDrive.run_fp_with_h HR HF HK fuel stops scr chints keep extra ::= run_fp_with_h_lz HR HF HK fuel stops scr chints keep extra.
#[local] Ltac AsSymDrive.branch_case_with HR HF HK Hc ::= branch_case_with_lz HR HF HK Hc.


#[local] Abbreviation SEGS := Asan.M.loaded_segments.
#[local] Abbreviation TP := 0x5d9b70%Z.

Section Malloc.
  Variable ceil : Z.
  Variables (FPI : FPState) (regs : bvmap 5 word) (mem rom : word -> option byte).
  Variables (ret sp h ctx thr t48 t56 dtls v24 mid : word) (fs : Z).

  Hypothesis Hra : getr regs 1 = ret.
  Hypothesis Hret : ret_ok ret.
  Hypothesis Hsp : getr regs 2 = sp.
  Hypothesis Htp : getr regs 4 = Z_to_bv 64 TP.
  (* [comment removed for export] *)
  Hypothesis C_14d8d0 : rdn SEGS mem (Z_to_bv 64 0xa0888) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x98a10)).
  Hypothesis C_154d20 : rdn SEGS mem (Z_to_bv 64 0xa7898) 1 = Some (word_to_le_bytes 1 (Z_to_bv 64 1)).
  Hypothesis C_14c198 : rdn SEGS mem (Z_to_bv 64 0x9f7d0) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 1)).
  Hypothesis C_14c1a0 : rdn SEGS mem (Z_to_bv 64 0x9f7d8) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0xfffffffffffff800)).
  Hypothesis C_677080 : rdn SEGS mem (Z_to_bv 64 0x5d9b68) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x5d9b90)).
  Hypothesis C_6770d8 : rdn SEGS mem (Z_to_bv 64 0x5d9b98) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x5da370)).
  Hypothesis C_1538a8 : rdn SEGS mem (Z_to_bv 64 0xa6420) 1 = Some (word_to_le_bytes 1 (Z_to_bv 64 1)).
  Hypothesis C_1538ac : rdn SEGS mem (Z_to_bv 64 0xa6424) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 0)).
  Hypothesis C_677030 : rdn SEGS mem (Z_to_bv 64 0x5d9b18) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x5faf18)).
  Hypothesis C_678088 : rdn SEGS mem (Z_to_bv 64 0x5faf18) 8 = Some (word_to_le_bytes 8 ctx).
  Hypothesis C_ctx152 : rdn SEGS mem (Z_to_bv 64 (bv_unsigned ctx + 152)) 8 = Some (word_to_le_bytes 8 thr).
  Hypothesis C_thr48  : rdn SEGS mem (Z_to_bv 64 (bv_unsigned thr + 48)) 8 = Some (word_to_le_bytes 8 t48).
  Hypothesis C_thr56  : rdn SEGS mem (Z_to_bv 64 (bv_unsigned thr + 56)) 8 = Some (word_to_le_bytes 8 t56).
  Hypothesis C_14b2f8 : rdn SEGS mem (Z_to_bv 64 0x9eae0) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x1386e8)).
  Hypothesis C_1e5bf1 : rdn SEGS mem (Z_to_bv 64 0x138771) 1 = Some (word_to_le_bytes 1 (Z_to_bv 64 1)).
  Hypothesis C_14b358 : rdn SEGS mem (Z_to_bv 64 0x9eb40) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x136658)).
  Hypothesis C_1e3ad8 : rdn SEGS mem (Z_to_bv 64 0x136658) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 0)).
  Hypothesis C_14c1e8 : rdn SEGS mem (Z_to_bv 64 0x9f7e0) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x8)).
  Hypothesis C_6770b0 : rdn SEGS mem (Z_to_bv 64 0x5d9b78) 8 = Some (word_to_le_bytes 8 dtls).
  Hypothesis C_dtls24 : rdn SEGS mem (Z_to_bv 64 (bv_unsigned dtls + 24)) 8 = Some (word_to_le_bytes 8 v24).
  Hypothesis C_677088 : rdn SEGS mem (Z_to_bv 64 0x5d9b70) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 fs)).
  Hypothesis C_14b308 : rdn SEGS mem (Z_to_bv 64 0x9eaf0) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0xa6bb8)).
  Hypothesis C_154040 : rdn SEGS mem (Z_to_bv 64 0xa6bb8) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 SB)).
  Hypothesis C_14b310 : rdn SEGS mem (Z_to_bv 64 0x9eaf8) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0xa78a8)).
  Hypothesis C_154d30 : rdn SEGS mem (Z_to_bv 64 0xa78a8) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
  Hypothesis C_14b318 : rdn SEGS mem (Z_to_bv 64 0x9eb00) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0xa78b0)).
  Hypothesis C_154d38 : rdn SEGS mem (Z_to_bv 64 0xa78b0) 8 = Some (word_to_le_bytes 8 mid).
  Hypothesis C_14b320 : rdn SEGS mem (Z_to_bv 64 0x9eb08) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0xa78a0)).
  Hypothesis C_154d28 : rdn SEGS mem (Z_to_bv 64 0xa78a0) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x7fffffffffff)).
  (* [comment removed for export] *)
  Hypothesis R_ctx : (appm (bv_unsigned ctx + 152) 8 /\ (4096 <= bv_unsigned ctx + 152)%Z) /\ (bv_unsigned ctx + 160 <= ceil)%Z.
  Hypothesis R_thr : (4096 <= bv_unsigned thr + 48)%Z /\ (bv_unsigned thr + 64 <= ceil)%Z.
  Hypothesis R_dtls : (appm (bv_unsigned dtls + 24) 8 /\ (4096 <= bv_unsigned dtls + 24)%Z) /\ (bv_unsigned dtls + 32 <= ceil)%Z.
  Hypothesis R_v24 : (bv_unsigned v24 <> 0)%Z.
  (* [comment removed for export] *)
  Hypothesis F_96 : rdn SEGS mem (Z_to_bv 64 (fs + 96)) 1 = Some (word_to_le_bytes 1 (Z_to_bv 64 0)).
  Hypothesis F_88 : rdn SEGS mem (Z_to_bv 64 (fs + 88)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 20)).
  Hypothesis R_fs : (appm (fs) FS_SIZE /\ (0 < fs)%Z) /\ (fs + FS_SIZE <= ceil)%Z /\ (fs mod 4096 = 0)%Z.
  (* [comment removed for export] *)
  Hypothesis R_sp : ((AS_STKLO <= ceil)%Z /\ (ceil + 208 <= bv_unsigned sp)%Z) /\ (bv_unsigned sp <= 2 ^ 47)%Z.
  Hypothesis W_sp : RiscvSemantics.store_ok SEGS mem (Z_to_bv 64 (bv_unsigned sp - 208)) 208 = true.

  Section Class5.
    Let pos : Z := (bv_unsigned h mod 512)%Z.
    Let F : Z := (fs + 0x509000 + 2048 * pos)%Z.
    Let fa : Z := (fs + 0x8c00 + pos)%Z.
    Hypothesis H_hint : rdn SEGS mem (Z_to_bv 64 (fs + 40)) 8 = Some (word_to_le_bytes 8 h).
    Hypothesis H_flag : mem (Z_to_bv 64 fa) = Some (Z_to_bv 8 0).
    Hypothesis W_hint : RiscvSemantics.store_ok SEGS mem (Z_to_bv 64 (fs + 40)) 8 = true.
    Hypothesis W_flag : RiscvSemantics.store_ok SEGS mem (Z_to_bv 64 fa) 1 = true.
    Hypothesis W_frame : RiscvSemantics.store_ok SEGS mem (Z_to_bv 64 F) 2048 = true.
    Hypothesis W_shad : RiscvSemantics.store_ok SEGS mem (Z_to_bv 64 (SB + F / 8)) 256 = true.

    Let E : env := Env (vals_ev (junk_vals regs ++ fjunk_vals (fp_regs (FPState:=FPI))
                                 ++ [Z_to_bv 64 fs; h; ctx; thr; t48; t56; dtls; v24; Z_to_bv 64 pos; mid])) (blobs_ev []).
    (* [comment removed for export] *)

    Definition lit8 (a v : Z) : kentry := KWord (SA (ELit 0) a) 8 (ELit v).
    Definition kn0v1 : list kentry :=
      [lit8 0xa0888 0x98a10; KWord (SA (ELit 0) 0xa7898) 1 (ELit 1); lit8 0x9f7d0 1; lit8 0x9f7d8 0xfffffffffffff800;
       lit8 0x5d9b68 0x5d9b90; lit8 0x5d9b98 0x5da370; KWord (SA (ELit 0) 0xa6420) 1 (ELit 1); KWord (SA (ELit 0) 0xa6424) 4 (ELit 0);
       lit8 0x5d9b18 0x5faf18; KWord (SA (ELit 0) 0x5faf18) 8 (EVar 66); KWord (SA (EVar 66) 152) 8 (EVar 67);
       KWord (SA (EVar 67) 48) 8 (EVar 68); KWord (SA (EVar 67) 56) 8 (EVar 69);
       lit8 0x9eae0 0x1386e8; KWord (SA (ELit 0) 0x138771) 1 (ELit 1); lit8 0x9eb40 0x136658; KWord (SA (ELit 0) 0x136658) 4 (ELit 0);
       lit8 0x9f7e0 0x8; KWord (SA (ELit 0) 0x5d9b78) 8 (EVar 70); KWord (SA (EVar 70) 24) 8 (EVar 71);
       KWord (SA (ELit 0) 0x5d9b70) 8 (EVar 64);
       lit8 0x9eaf0 0xa6bb8; lit8 0xa6bb8 SB; lit8 0x9eaf8 0xa78a8; lit8 0xa78a8 0; lit8 0x9eb00 0xa78b0;
       KWord (SA (ELit 0) 0xa78b0) 8 (EVar 73); lit8 0x9eb08 0xa78a0; lit8 0xa78a0 0x7fffffffffff;
       KRange (EVar 66) (4096 - 152) (2 ^ 47 - 160); KRange (EVar 67) (4096 - 48) (2 ^ 47 - 64);
       KRange (EVar 70) (4096 - 24) (2 ^ 47 - 32); KRange (EVar 71) 1 (2 ^ 64 - 1);
       KWord (SA (EVar 64) 96) 1 (ELit 0); KWord (SA (EVar 64) 88) 8 (ELit 20); KWord (SA (EVar 64) 40) 8 (EVar 65);
       KRange (EVar 64) 1 (2 ^ 47 - FS_SIZE); KAlign (EVar 64) 4096; KWr (SA (EVar 64) 40) 8;
       KRange (EVar 72) 0 511;
       KWord (SA (EAlu ALU_ADD (EVar 64) (EVar 72)) 0x8c00) 1 (ELit 0);
       KWr (SA (EAlu ALU_ADD (EVar 64) (EVar 72)) 0x8c00) 1;
       KWr (SA (EAlu ALU_ADD (EVar 64) (EMd M_MUL (ELit 2048) (EVar 72))) 0x509000) 2048;
       KWr (SA (EAlu ALU_ADD (EMd M_MUL (ELit 256) (EVar 72)) (EAlu ALU_SRL (EVar 64) (ELit 3))) (SB + 0xa1200)) 256;
       KDisj (SA (EVar 64) 0) 0x9000 (SA (EAlu ALU_ADD (EVar 64) (EMd M_MUL (ELit 2048) (EVar 72))) 0x509000) 2048;
       KDisj (SA (EVar 64) 0) 0x1000 (SA (EAlu ALU_ADD (EVar 64) (EVar 72)) 0x8c00) 1;
       KRange (EVar 2) (AS_STKLO + 208) (2 ^ 47); KWr (SA (EVar 2) (-208)) 208;
       KDisj (SA (EAlu ALU_ADD (EVar 64) (EVar 72)) 0x8c00) 1 (SA (EVar 2) (-208)) 208;
       KDisj (SA (EAlu ALU_ADD (EVar 64) (EMd M_MUL (ELit 2048) (EVar 72))) 0x509000) 2048 (SA (EVar 2) (-208)) 208].

    Ltac klit := eapply (kword_intro SEGS E mem (ELit 0) (Z_to_bv 64 0));
      [ reflexivity | cbn [edenot]; ev_simpl E; reflexivity | lia | lia
      | rewrite u_lit0; lia | rewrite u_lit0; lia | rewrite u_lit0, Z.add_0_l; eassumption ].
    Ltac kvar base off w v x C := eapply (kword_intro SEGS E mem base _ off w v x);
      [ cbn [edenot]; ev_simpl E; reflexivity | cbn [edenot]; ev_simpl E; reflexivity | lia | lia | lia | lia | exact C ].

    Lemma pos_range : (0 <= pos <= 511)%Z.
    Proof using rom h mid fs. subst pos. pose proof (Z.mod_pos_bound (bv_unsigned h) 512 ltac:(lia)). lia. Qed.

    Lemma Ufs : bv_unsigned (Z_to_bv 64 fs) = fs.
    Proof using ceil rom sp h mid fs R_fs R_sp. apply u_small. unfold FS_SIZE in R_fs. lia. Qed.
    Lemma Upos : bv_unsigned (Z_to_bv 64 pos) = pos.
    Proof using rom h mid fs. apply u_small. pose proof pos_range. lia. Qed.

    Lemma fs8 : (fs = 8 * (fs / 8))%Z.
    Proof using ceil rom h mid fs R_fs.
      destruct R_fs as (_ & _ & R3). pose proof (Z.div_mod fs 4096 ltac:(lia)) as D1. rewrite R3, Z.add_0_r in D1.
      set (q := (fs / 4096)%Z) in D1. rewrite D1.
      replace (4096 * q)%Z with ((512 * q) * 8)%Z by lia. rewrite Z.div_mul by lia. lia.
    Qed.

    (* [comment removed for export] *)
    Lemma den_flagbase : edenot E (EAlu ALU_ADD (EVar 64) (EVar 72)) = Z_to_bv 64 (fs + pos).
    Proof using ceil FPI regs rom sp h ctx thr t48 t56 dtls v24 mid fs R_fs R_sp. cbn [edenot]. ev_simpl E. rewrite alu_add. unfold v_add. rewrite Ufs, Upos. reflexivity. Qed.
    Lemma den_framebase' : alu64 ALU_ADD (Z_to_bv 64 fs) (mul_div M_MUL (Z_to_bv 64 2048) (Z_to_bv 64 pos)) = Z_to_bv 64 (fs + 2048 * pos).
    Proof using ceil rom sp h mid fs R_fs R_sp.
      rewrite alu_add, m_mul. unfold v_add, v_mul. rewrite Ufs, Upos, (u_small 2048) by lia.
      pose proof pos_range. rewrite u_small by lia. reflexivity.
    Qed.
    Lemma den_framebase : edenot E (EAlu ALU_ADD (EVar 64) (EMd M_MUL (ELit 2048) (EVar 72))) = Z_to_bv 64 (fs + 2048 * pos).
    Proof using ceil FPI regs rom sp h ctx thr t48 t56 dtls v24 mid fs R_fs R_sp. cbn [edenot]. ev_simpl E. apply den_framebase'. Qed.
    Lemma den_flagbase' : alu64 ALU_ADD (Z_to_bv 64 fs) (Z_to_bv 64 pos) = Z_to_bv 64 (fs + pos).
    Proof using ceil rom sp h mid fs R_fs R_sp. rewrite alu_add. unfold v_add. rewrite Ufs, Upos. reflexivity. Qed.
    Lemma den_shbase : edenot E (EAlu ALU_ADD (EMd M_MUL (ELit 256) (EVar 72)) (EAlu ALU_SRL (EVar 64) (ELit 3))) = Z_to_bv 64 (256 * pos + fs / 8).
    Proof using ceil FPI regs rom sp h ctx thr t48 t56 dtls v24 mid fs R_fs R_sp.
      cbn [edenot]. ev_simpl E. rewrite alu_add, m_mul. unfold v_add, v_mul. rewrite u_srl3, Ufs, Upos, (u_small 256) by lia.
      pose proof pos_range. rewrite u_small by lia. reflexivity.
    Qed.

    Lemma kn0v1_ok : know_ok SEGS E mem kn0v1.
    Proof using ceil FPI regs mem rom sp h ctx thr t48 t56 dtls v24 mid fs Hsp C_14d8d0 C_154d20 C_14c198 C_14c1a0 C_677080 C_6770d8 C_1538a8 C_1538ac C_677030 C_678088 C_ctx152 C_thr48 C_thr56 C_14b2f8 C_1e5bf1 C_14b358 C_1e3ad8 C_14c1e8 C_6770b0 C_dtls24 C_677088 C_14b308 C_154040 C_14b310 C_154d30 C_14b318 C_154d38 C_14b320 C_154d28 R_ctx R_thr R_dtls R_v24 F_96 F_88 R_fs R_sp W_sp H_hint H_flag W_hint W_flag W_frame W_shad.
      unfold kn0v1, lit8, know_ok. pose proof (u64_range h). pose proof (u64_range sp). pose proof (u64_range ctx).
      pose proof (u64_range thr). pose proof (u64_range dtls). pose proof (u64_range v24). pose proof pos_range as Hpos.
      pose proof Ufs as Ufs. pose proof Upos as Upos.
      pose proof den_flagbase as Dfl. pose proof den_framebase as Dfr. pose proof den_shbase as Dsh.
      assert (HF_def : F = (fs + 5279744 + 2048 * pos)%Z) by reflexivity.
      assert (Hfa_def : fa = (fs + 35840 + pos)%Z) by reflexivity.
      clearbody F fa pos.
      unfold FS_SIZE in *. destruct R_fs as (Rfs1 & Rfs2 & Rfs3).
      assert (Hfs8 : (0 <= fs / 8 < 2 ^ 44)%Z) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
      pose proof fs8 as Hfs8e.
      repeat lazymatch goal with |- Forall _ (_ :: _) => constructor | |- Forall _ [] => constructor end.
      all: lazymatch goal with |- Forall _ _ => fail | _ => idtac end.
      all: try klit.
      - kvar (EVar 66) 152%Z 8%nat (EVar 67) thr C_ctx152.
      - kvar (EVar 67) 48%Z 8%nat (EVar 68) t48 C_thr48.
      - kvar (EVar 67) 56%Z 8%nat (EVar 69) t56 C_thr56.
      - kvar (EVar 70) 24%Z 8%nat (EVar 71) v24 C_dtls24.
      - apply krange_intro. cbn [edenot]; ev_simpl E. lia.
      - apply krange_intro. cbn [edenot]; ev_simpl E. lia.
      - apply krange_intro. cbn [edenot]; ev_simpl E. lia.
      - apply krange_intro. cbn [edenot]; ev_simpl E. lia.
      - eapply (kword_intro SEGS E mem (EVar 64) (Z_to_bv 64 fs) 96 1 (ELit 0) (Z_to_bv 64 0));
          [ cbn [edenot]; ev_simpl E; reflexivity | reflexivity | lia | lia | rewrite Ufs; lia | rewrite Ufs; lia | rewrite Ufs; exact F_96 ].
      - eapply (kword_intro SEGS E mem (EVar 64) (Z_to_bv 64 fs) 88 8 (ELit 20) (Z_to_bv 64 20));
          [ cbn [edenot]; ev_simpl E; reflexivity | reflexivity | lia | lia | rewrite Ufs; lia | rewrite Ufs; lia | rewrite Ufs; exact F_88 ].
      - eapply (kword_intro SEGS E mem (EVar 64) (Z_to_bv 64 fs) 40 8 (EVar 65) h);
          [ cbn [edenot]; ev_simpl E; reflexivity | reflexivity | lia | lia | rewrite Ufs; lia | rewrite Ufs; lia | rewrite Ufs; exact H_hint ].
      - apply krange_intro. cbn [edenot]; ev_simpl E. rewrite Ufs. lia.
      - apply kalign_intro; [lia|]. cbn [edenot]; ev_simpl E. rewrite Ufs. lia.
      - apply (kwr_intro SEGS E mem (EVar 64) (Z_to_bv 64 fs) 40 8); [cbn [edenot]; ev_simpl E; reflexivity | rewrite Ufs; lia | lia | rewrite Ufs; lia | rewrite Ufs; exact W_hint].
      - apply krange_intro. cbn [edenot]; ev_simpl E. rewrite Upos. lia.
      - eapply (kword_intro SEGS E mem _ (Z_to_bv 64 (fs + pos)) 0x8c00 1 (ELit 0) (Z_to_bv 64 0) Dfl); try reflexivity; try lia;
          rewrite ?(u_small (fs + pos)) by lia; try lia.
        replace (fs + pos + 35840)%Z with fa by lia. apply rdn_pointwise; [reflexivity | rewrite u_small by lia; lia |].
        intros jj Hjj. destruct jj; [|lia]. cbn [nth Z.of_nat]. rewrite u_small by lia. rewrite Z.add_0_r.
        exact H_flag.
      - apply (kwr_intro SEGS E mem _ (Z_to_bv 64 (fs + pos)) 0x8c00 1 Dfl); rewrite ?(u_small (fs + pos)) by lia; try lia.
        replace (fs + pos + 35840)%Z with fa by lia. exact W_flag.
      - apply (kwr_intro SEGS E mem _ (Z_to_bv 64 (fs + 2048 * pos)) 0x509000 2048 Dfr); rewrite ?(u_small (fs + 2048 * pos)) by lia; try lia.
        replace (fs + 2048 * pos + 5279744)%Z with F by lia. exact W_frame.
      - apply (kwr_intro SEGS E mem _ (Z_to_bv 64 (256 * pos + fs / 8)) (SB + 0xa1200) 256 Dsh); unfold SB; rewrite ?(u_small (256 * pos + fs / 8)) by lia; try lia.
        replace (256 * pos + fs / 8 + (2147450880 + 659968))%Z with (SB + F / 8)%Z; [exact W_shad|].
        rewrite HF_def. unfold SB. replace (fs + 5279744 + 2048 * pos)%Z with ((fs / 8 + 659968 + 256 * pos) * 8)%Z by lia.
        rewrite Z.div_mul by lia. lia.
      - cbn [kentry_ok]. unfold estart. cbn [a_base a_off]. rewrite Dfr. cbn [edenot]. ev_simpl E. rewrite Ufs, u_small by lia. lia.
      - cbn [kentry_ok]. unfold estart. cbn [a_base a_off]. rewrite Dfl. cbn [edenot]. ev_simpl E. rewrite Ufs, u_small by lia. lia.
      - apply krange_intro. cbn [edenot]; ev_simpl E. rewrite Hsp. lia.
      - apply (kwr_intro SEGS E mem (EVar 2) sp (-208) 208); [cbn [edenot]; ev_simpl E; exact Hsp | lia | lia | lia | ].
        replace (bv_unsigned sp + -208)%Z with (bv_unsigned sp - 208)%Z by lia. exact W_sp.
      - cbn [kentry_ok]. unfold estart. cbn [a_base a_off]. rewrite Dfl. cbn [edenot]. ev_simpl E. rewrite Hsp, u_small by lia. lia.
      - cbn [kentry_ok]. unfold estart. cbn [a_base a_off]. rewrite Dfr. cbn [edenot]. ev_simpl E. rewrite Hsp, u_small by lia. lia.
    Qed.

    Definition kn0 : list kentry := kn0v1 ++
      [KDisj (SA (EVar 64) 0) FS_SIZE ZSH ZSHL; KDisj (SA (EVar 64) 0) FS_SIZE ZIMG ZIMGL;
       KDisj (SA (EVar 64) 0) FS_SIZE (SA (EVar 2) (-208)) 208;
       KDisj (SA (EVar 66) 152) 8 (SA (EVar 2) (-208)) 208; KDisj (SA (EVar 67) 48) 16 (SA (EVar 2) (-208)) 208;
       KDisj (SA (EVar 70) 24) 8 (SA (EVar 2) (-208)) 208].
    Lemma kn0_ok : know_ok SEGS E mem kn0.
    Proof using ceil FPI regs mem rom sp h ctx thr t48 t56 dtls v24 mid fs Hsp C_14d8d0 C_154d20 C_14c198 C_14c1a0 C_677080 C_6770d8 C_1538a8 C_1538ac C_677030 C_678088 C_ctx152 C_thr48 C_thr56 C_14b2f8 C_1e5bf1 C_14b358 C_1e3ad8 C_14c1e8 C_6770b0 C_dtls24 C_677088 C_14b308 C_154040 C_14b310 C_154d30 C_14b318 C_154d38 C_14b320 C_154d28 R_ctx R_thr R_dtls R_v24 F_96 F_88 R_fs R_sp W_sp H_hint H_flag W_hint W_flag W_frame W_shad. apply know_ok_app; [exact kn0v1_ok | kn_place]. Qed.

    Definition RS : list (saddr * Z) :=
      [(SA (EVar 2) (-208), 208%Z); (SA (EVar 64) 40, 8%Z); (SA (EAlu ALU_ADD (EVar 64) (EVar 72)) 0x8c00, 1%Z);
       (SA (EAlu ALU_ADD (EVar 64) (EMd M_MUL (ELit 2048) (EVar 72))) (0x509000 + 24), 8%Z);
       (SA (EAlu ALU_ADD (EVar 64) (EMd M_MUL (ELit 2048) (EVar 72))) (0x509000 + 2040), 8%Z);
       (SA (EAlu ALU_ADD (EMd M_MUL (ELit 256) (EVar 72)) (EAlu ALU_SRL (EVar 64) (ELit 3))) (SB + 0xa1200), 256%Z)].
    Lemma RS_denot : regions_denot E RS =
      [(Z_to_bv 64 (bv_unsigned sp - 208), 208%Z); (Z_to_bv 64 (fs + 8 * 5), 8%Z); (Z_to_bv 64 fa, 1%Z);
       (Z_to_bv 64 (F + 24), 8%Z); (Z_to_bv 64 (F + 2048 - 8), 8%Z); (Z_to_bv 64 (AS_SB + F / 8), 2048 / 8)%Z].
    Proof using ceil FPI regs rom sp h ctx thr t48 t56 dtls v24 mid fs Hsp R_fs R_sp.
      unfold regions_denot, RS. cbn [map fst snd]. unfold adenot. cbn [a_base a_off].
      rewrite den_flagbase, den_framebase, den_shbase. cbn [edenot]. ev_simpl E. rewrite Hsp.
      pose proof pos_range. pose proof fs8. unfold FS_SIZE in R_fs.
      assert (0 <= fs / 8)%Z by (apply Z.div_pos; lia).
      unfold v_addi. rewrite Ufs, !u_small by lia.
      subst fa F. unfold AS_SB, SB.
      replace ((fs + 5279744 + 2048 * pos) / 8)%Z with (fs / 8 + 659968 + 256 * pos)%Z.
      2:{ replace (fs + 5279744 + 2048 * pos)%Z with ((fs / 8 + 659968 + 256 * pos) * 8)%Z by lia. rewrite Z.div_mul by lia. reflexivity. }
      repeat match goal with
             | |- (_ :: _) = (_ :: _) => apply f_equal2
             | |- (_, _) = (_, _) => apply f_equal2
             | |- Z_to_bv 64 _ = Z_to_bv 64 _ => apply (f_equal (Z_to_bv 64)); lia
             | |- _ => first [reflexivity | lia]
             end.
    Qed.

    Lemma RS_flat : Forall (fun r => flat E (fst r) (snd r)) RS.
    Proof using ceil FPI regs rom sp h ctx thr t48 t56 dtls v24 mid fs Hsp R_fs R_sp.
      pose proof pos_range. pose proof fs8. pose proof (u64_range sp). unfold FS_SIZE in R_fs.
      assert (0 <= fs / 8 < 2 ^ 44)%Z by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
      unfold RS. repeat lazymatch goal with |- Forall _ (_ :: _) => constructor | |- Forall _ [] => constructor end.
      all: lazymatch goal with |- Forall _ _ => fail | _ => idtac end.
      all: cbn [fst snd]; unfold flat, estart; cbn [a_base a_off];
           rewrite ?den_flagbase, ?den_framebase, ?den_shbase; cbn [edenot]; ev_simpl E; rewrite ?Hsp, ?Ufs;
           rewrite ?u_small by lia; unfold SB; lia.
    Qed.

    Theorem malloc5_run_ok :
      exists (FPI' : FPState) regs' mem',
        msteps SEGS (mkst (FP:=FPI) regs (Z_to_bv 64 0x3ca48) mem rom) (mkst (FP:=FPI') regs' ret mem' rom)
        /\ regs_kept abi_kept regs regs' /\ fregs_kept abi_fkept (fp_regs (FPState:=FPI)) (fp_regs (FPState:=FPI'))
        /\ getr regs' 10 = Z_to_bv 64 F
        /\ frame_mod mem mem' [(Z_to_bv 64 (bv_unsigned sp - 208), 208%Z); (Z_to_bv 64 (fs + 8 * 5), 8%Z); (Z_to_bv 64 fa, 1%Z);
                               (Z_to_bv 64 (F + 24), 8%Z); (Z_to_bv 64 (F + 2048 - 8), 8%Z); (Z_to_bv 64 (AS_SB + F / 8), 2048 / 8)%Z]
        /\ rdn SEGS mem' (Z_to_bv 64 (fs + 8 * 5)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned h + 1)))
        /\ rdn SEGS mem' (Z_to_bv 64 (F + 2048 - 8)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 fa)).
    Proof using ceil FPI regs mem rom ret sp h ctx thr t48 t56 dtls v24 mid fs Hra Hret Hsp Htp C_14d8d0 C_154d20 C_14c198 C_14c1a0 C_677080 C_6770d8 C_1538a8 C_1538ac C_677030 C_678088 C_ctx152 C_thr48 C_thr56 C_14b2f8 C_1e5bf1 C_14b358 C_1e3ad8 C_14c1e8 C_6770b0 C_dtls24 C_677088 C_14b308 C_154040 C_14b310 C_154d30 C_14b318 C_154d38 C_14b320 C_154d28 R_ctx R_thr R_dtls R_v24 F_96 F_88 R_fs R_sp W_sp H_hint H_flag W_hint W_flag W_frame W_shad.
      apply runs_to_contract with
        (P := fun FPI' regs' mem' => regs_kept abi_kept regs regs' /\ fregs_kept abi_fkept (fp_regs (FPState:=FPI)) (fp_regs (FPState:=FPI'))
           /\ getr regs' 10 = Z_to_bv 64 F
           /\ frame_mod mem mem' [(Z_to_bv 64 (bv_unsigned sp - 208), 208%Z); (Z_to_bv 64 (fs + 8 * 5), 8%Z); (Z_to_bv 64 fa, 1%Z);
                                  (Z_to_bv 64 (F + 24), 8%Z); (Z_to_bv 64 (F + 2048 - 8), 8%Z); (Z_to_bv 64 (AS_SB + F / 8), 2048 / 8)%Z]
           /\ rdn SEGS mem' (Z_to_bv 64 (fs + 8 * 5)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned h + 1)))
           /\ rdn SEGS mem' (Z_to_bv 64 (F + 2048 - 8)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 fa))).
      assert (HR : regs_ok E (sr_vars 0) regs) by exact (regs_ok_vars [] regs _ (blobs_ev [])).
      assert (HF : fregs_ok E (sfr_vars 32) fp_regs) by exact (fregs_ok_vars (junk_vals regs) fp_regs _ (blobs_ev [])).
      pose proof (HR : id _) as HR0. pose proof (HF : id _) as HF0.
      pin_reg HR (4%bv:reg) (ELit TP) by (regv HR (4%bv:reg); cbn [edenot]; ev_simpl E; exact Htp).
      clear HR0. pose proof (HR : id _) as HR0.
      pose proof kn0_ok as HK.
      pose proof pos_range as Hpos. pose proof (u64_range h). pose proof (u64_range sp). unfold FS_SIZE in R_fs.
      pose proof fs8 as Hfs8e. assert (Hfs8 : (0 <= fs / 8 < 2 ^ 44)%Z) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
      run_fp 300%nat [0x3cae0%Z] noscr true.
      (* [comment removed for export] *)
      pin_reg HR (17%bv:reg) (EVar 72) by
        (regv HR (17%bv:reg); cbn [edenot]; ev_simpl E; apply bv_eq; rewrite u_and64, u_lit64, Upos; unfold two64;
         rewrite (Z.mod_small 511) by lia; change 511%Z with (Z.ones 9); rewrite Z.land_ones by lia; reflexivity).
      (* [comment removed for export] *)
      destruct (app_sh_lit _ _ (proj1 (proj1 R_fs))) as [HZ|HZ];
        [ pose proof (app_img_lit _ _ (proj1 (proj1 R_fs))) as HZI;
          eassert (HK' : know_ok SEGS E _ (KRange (EVar 64) 0x5fc000 (0x7fff7000 - 0xb09000) :: _))
            by (constructor; [apply krange_intro; cbn [edenot]; ev_simpl E; rewrite Ufs; lia | exact HK])
        | eassert (HK' : know_ok SEGS E _ (KRange (EVar 64) 0x10007fff8000 (2 ^ 47 - 0xb09000) :: _))
            by (constructor; [apply krange_intro; cbn [edenot]; ev_simpl E; rewrite Ufs; lia | exact HK]) ];
        clear HK; rename HK' into HK.
      all: run_fp 200%nat (@nil Z) noscr true.
      all: fin_ret.
      all: lazymatch goal with
      | EQM1 : ?M1 = mem_denot _ mem ?log1, HLF1 : log_flat _ ?log1', EQM2 : ?M2 = mem_denot _ ?M1' ?log2, HLF2 : log_flat _ ?log2',
        HK' : know_ok _ _ ?M2' _ |- exists _ _ _, @mkst ?FPI' ?R' _ _ _ = _ /\ _ =>
        exists FPI', R', M2; split; [| split; [| split; [| split; [| split; [|split]]]]]
      end;
      [ regv HR (1%bv:reg); rewrite Hra; reflexivity
      | unfold regs_kept; eapply (regs_same_on E _ _ regs _ abi_kept); [ exact HR0 | exact HR | vm_compute; reflexivity ]
      | unfold fregs_kept; eapply (fregs_same_on E _ _ _ _ abi_fkept); [ exact HF0 | exact HF | vm_compute; reflexivity ]
      | regv_lin HR (10%bv:reg); f_equal; rewrite Ufs, Upos; subst F; lia
      | lazymatch goal with
        | EQM1 : ?M1 = mem_denot _ mem ?log1, HLF1 : log_flat _ ?log1', EQM2 : ?M2 = mem_denot _ ?M1' ?log2, HLF2 : log_flat _ ?log2' |- _ =>
          rewrite <- RS_denot; apply (frame_mod_trans_same mem M1 M2);
          [ rewrite EQM1; apply (frame_mod_mem_denot E _ _ RS HLF1 RS_flat); vm_compute; reflexivity
          | rewrite EQM2; apply (frame_mod_mem_denot E _ _ RS HLF2 RS_flat); vm_compute; reflexivity ]
        end
      | kread_fact HK (EVar 64) 40%Z 8%nat C1; [rewrite Ufs; lia|];
        unfold v_addi in C1; rewrite Ufs in C1; replace (fs + 8 * 5)%Z with (fs + 40)%Z by lia; rewrite C1;
        repeat f_equal; try (rewrite alu_add; unfold v_add; rewrite (u_small 1) by lia; reflexivity)
      | kread_fact HK (EAlu ALU_ADD (EVar 64) (EMd M_MUL (ELit 2048) (EVar 72))) 5281784%Z 8%nat C2;
        [rewrite den_framebase', u_small; lia|];
        unfold v_addi in C2; rewrite den_framebase', u_small in C2 by lia;
        replace (F + 2048 - 8)%Z with (fs + 2048 * pos + 5281784)%Z by (subst F; lia);
        rewrite C2;
        repeat f_equal; try (rewrite !alu_add; unfold v_add; rewrite den_flagbase'; rewrite !u_small by lia; subst fa; f_equal; lia) ].
    Qed.
End Class5.
End Malloc.

(* [comment removed for export] *)
Lemma areadable8_word5 : forall segs mem a,
  areadable segs mem a 8 -> exists w : word, rdn segs mem (Z_to_bv 64 a) 8 = Some (word_to_le_bytes 8 w).
Proof.
  intros segs mem a [bs Hbs]. exists (Z_to_bv 64 (bytes_le_to_Z bs)).
  rewrite word_to_le_bytes_of_lez; [exact Hbs | exact (rdn_length _ _ _ _ _ Hbs) | lia].
Qed.

Theorem stkmalloc5_asan : forall ceil, stkmalloc5_contract SEGS as_asan ceil.
Proof.
  intros ceil fs h c FPI regs mem rom ret Hra Hret PRE.
  destruct PRE as (Htp & Henv & Hhdr & Hhint & Hflag & Whint & Wflag & Wframe & Wshad & (sp & Hsp & Hfr)).
  destruct Henv as (Hcells & Hshb & Hro & Hch).
  pose proof (asan_cells64 SEGS mem Hcells) as
    (E308 & E040 & E360 & E328 & Ed30 & Ed28 & Ec010 & E8d0 & E198 & E1a0 & E310 & Emb & E318 & E320 & Ehe & E2f8 & E358 & E1e8 &
     Etp8 & Edtv & Etsd & E048 & Ekey & Everb & Einit & Erepl & Etsdi & Eitga & R38).
  destruct Hch as (Cctx & Rctx & Cthr & Rt48 & Rt56 & C48 & C56 & Cdtls & Rdtls0 & Rdtls & Cv24 & Rv24).
  destruct Hhdr as (Ctls & Cssl & Cgc & Rfs1 & Rfs2 & Rfs3). app_facts.
  destruct Hfr as ([Hst1 Hst2] & Hsal & (_ & _ & _ & Hwr)).
  destruct Whint as (_ & _ & _ & Whint). destruct Wflag as (_ & _ & _ & Wflag).
  destruct Wframe as (_ & _ & _ & Wframe). destruct Wshad as (_ & _ & _ & Wshad).
  destruct (areadable8_word5 SEGS mem 0xa78b0 R38) as [mid Hmid].
  unfold heap_cell_ok, AS_SB, FS_SIZE, FS_SSL, FS_NEEDSGC, FS_FRAMES0, FS_FLAGS0 in *.
  cbn [aa_tp aa_tsdv al_abi as_asan asan_abi] in *.
  unfold acellw, acell in *.
  unfold sm_pos, sm_frame, sm_flag, FS_FRAMES0, FS_FLAGS0 in Hflag, Wflag, Wframe, Wshad.
  replace (fs + 4096 + 31744 + bv_unsigned h mod 512)%Z with (fs + 35840 + bv_unsigned h mod 512)%Z in Hflag by lia.
  replace (fs + 4096 + 31744 + bv_unsigned h mod 512)%Z with (fs + 35840 + bv_unsigned h mod 512)%Z in Wflag by lia.
  replace (fs + 36864 + 5 * 2 ^ 20 + 2048 * (bv_unsigned h mod 512))%Z with (fs + 5279744 + 2048 * (bv_unsigned h mod 512))%Z in Wframe by lia.
  replace (fs + 36864 + 5 * 2 ^ 20 + 2048 * (bv_unsigned h mod 512))%Z with (fs + 5279744 + 2048 * (bv_unsigned h mod 512))%Z in Wshad by lia.
  replace (Z.to_nat (2048 / 8)) with 256%nat in Wshad by reflexivity.
  change (Z.to_nat 8) with 8%nat in Whint. change (Z.to_nat 1) with 1%nat in Wflag. change (Z.to_nat 2048) with 2048%nat in Wframe.
  change (Z.to_nat 208) with 208%nat in Hwr.
  replace (fs + 8 * 5)%Z with (fs + 40)%Z in Hhint by lia. replace (fs + 8 * 5)%Z with (fs + 40)%Z in Whint by lia.
  edestruct (malloc5_run_ok ceil FPI regs mem rom ret sp h (ch_ctx c) (ch_thr c) (ch_t48 c) (ch_t56 c) (ch_dtls c) (ch_v24 c) mid fs
             Hra Hret Hsp Htp
             E8d0 Einit E198 E1a0 Etp8 Edtv Etsdi Ekey Etsd Cctx Cthr C48 C56 E2f8 Eitga E358 Everb E1e8 Cdtls Cv24 Ctls
             E308 E040 E310 Emb E318 Hmid E320 Ehe
             ltac:(plc) ltac:(plc) ltac:(plc) Rv24 Cgc Cssl ltac:(unfold FS_SIZE; plc) ltac:(plc) Hwr
             Hhint Hflag Whint Wflag Wframe Wshad)
    as (FPI' & regs' & mem' & Hms & Hk1 & Hk2 & Ha0 & Hfm & Hh1 & Hfp).
  exists FPI', regs', mem'. split; [exact Hms|]. split; [exact Hk1|]. split; [exact Hk2|].
  unfold stkmalloc_post. cbn [sm_pos sm_frame sm_flag]. unfold sm_pos, sm_frame, sm_flag, FS_FRAMES0, FS_FLAGS0, acellw, acell. rewrite Hsp.
  split; [rewrite Ha0; f_equal; lia|]. split.
  { match goal with |- frame_mod _ _ ?l => replace l with
      [(Z_to_bv 64 (bv_unsigned sp - 208), 208%Z); (Z_to_bv 64 (fs + 8 * 5), 8%Z); (Z_to_bv 64 (fs + 35840 + bv_unsigned h mod 512), 1%Z);
       (Z_to_bv 64 (fs + 5279744 + 2048 * (bv_unsigned h mod 512) + 24), 8%Z);
       (Z_to_bv 64 (fs + 5279744 + 2048 * (bv_unsigned h mod 512) + 2048 - 8), 8%Z);
       (Z_to_bv 64 (AS_SB + (fs + 5279744 + 2048 * (bv_unsigned h mod 512)) / 8), 2048 / 8)%Z] end.
    - exact Hfm.
    - repeat match goal with
             | |- (_ :: _) = (_ :: _) => apply f_equal2
             | |- (_, _) = (_, _) => apply f_equal2
             | |- Z_to_bv 64 _ = Z_to_bv 64 _ => apply (f_equal (Z_to_bv 64)); lia
             | |- _ => first [reflexivity | lia]
             end. }
  split; [exact Hh1|].
  match goal with |- rdn _ _ (Z_to_bv 64 ?a) _ = _ =>
    replace a with (fs + 5279744 + 2048 * (bv_unsigned h mod 512) + 2048 - 8)%Z by lia end.
  rewrite Hfp. apply (f_equal Some). apply (f_equal (word_to_le_bytes 8)). apply (f_equal (Z_to_bv 64)). lia.
Qed.
