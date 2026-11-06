(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

(* [comment removed for export] *)
From Stdlib Require ZArith.
From Stdlib Require NArith.
From Stdlib Require List.
From Stdlib Require Lia.
From Stdlib Require Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase.
From LinuxProcessSemantics.LinuxProcessSem Require RiscvSemantics.
From LinuxProcessSemantics.LinuxProcessSem Require MemImageType.
From LinuxProcessSemantics.LinuxProcessSem Require State.
From LinuxProcessSemantics.LinuxProcessSem Require Run.
From LinuxProcessSemantics.Riscv Require Prelude.
From LinuxProcessSemantics.Riscv Require Instr.
From LinuxProcessSemantics.Riscv Require Decode.
From LinuxProcessSemantics.Riscv Require DecodeC.
From LinuxProcessSemantics.Riscv Require Sem.
From LinuxProcessSemantics.Riscv Require Fpu.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Tac.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Bytes.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require PImg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc Require RStep.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I Require IImgP.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G Require G_strlen.
Module F_strlen.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Bytes.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.PImg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)
#[local] Existing Instance OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IImgP.P_img.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.CodeAtT _ _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.CodeAt _ _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RoB _ _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RelCode _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RelSym _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RelNear _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 2 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.ZFact _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.


Definition strlen_entry := 0x20ee4%Z.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition strlen_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (a0 : word) (str slack : list byte) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (Z.of_nat (length str))) a1 a2 a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom psegs)
    /\ munch [] m m' /\ wmono psegs m m' /\ mem_inv psegs m'
    /\ bytes_at psegs m' (bv_unsigned a0) (str ++ Z_to_bv 8 0 :: slack).

Lemma strlen_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (str slack : list byte),
  bytes_at psegs m (bv_unsigned a0) (str ++ Z_to_bv 8 0 :: slack) ->
  ~ In (Z_to_bv 8 0) str ->
  ((- (bv_unsigned a0 + Z.of_nat (length str) + 1)) mod 8 <= Z.of_nat (length slack))%Z ->
  mem_inv psegs m ->
  evt psegs (strlen_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 str slack m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x20ee4) fc None m (seg_rom psegs)).
Proof. first [ exact OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_strlen.strlen_spec | (pose proof OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_strlen.strlen_spec as T_; exact T_) | exact @OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_strlen.strlen_spec | apply OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_strlen.strlen_spec | (apply (@OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_strlen.strlen_spec OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IImgP.P_img); typeclasses eauto) ]. Qed.
#[export] Instance P_strlen_contract : OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_strlen.strlen_contract := OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_strlen.strlen_contract_ok.
End F_strlen.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require Import ShapeAlg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Tac Bytes SCPS Arr.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Import PImg CJ_iface CJ_tree.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require CJ_pstr_A.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.CJ_pstr_A.CJ_print_iface.
Import F_strlen.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Lemma some_bytes_at : forall (m : word -> option byte) A (k : nat),
  0 <= A -> A + Z.of_nat k <= 2^64 ->
  (forall i, 0 <= i < Z.of_nat k -> m (wa (A + i)) <> None) ->
  exists pad, bytes_at psegs m A pad /\ length pad = k.
Proof.
  intros m A k HA HK HS. revert A HA HK HS. induction k as [|k IH]; intros A HA HK HS.
  - exists []. split; [| reflexivity]. split; [lia|]. split; [cbn; lia|]. intros i Hi. cbn in Hi. lia.
  - destruct (m (wa A)) as [b|] eqn:EB. 2:{ exfalso. apply (HS 0 ltac:(lia)). rewrite Z.add_0_r. exact EB. }
    destruct (IH (A + 1) ltac:(lia) ltac:(lia)) as (pad & BP & LP).
    { intros i Hi. replace (A + 1 + i) with (A + (1 + i)) by lia. apply HS. lia. }
    exists (b :: pad). split; [| cbn; lia].
    apply (bytes_at_app psegs m A [b] pad). split.
    + split; [lia|]. split; [cbn; lia|]. intros i Hi. cbn in Hi. assert (i = 0)%nat by lia. subst i. cbn. unfold mrd. rewrite Z.add_0_r, EB. reflexivity.
    + cbn [length Z.of_nat Pos.of_succ_nat]. exact BP.
Qed.

(* [comment removed for export] *)
Lemma first_nul : forall (bs : list byte) (off K : Z),
  0 <= off -> 0 <= K -> nth_error bs (Z.to_nat (off + K)) = Some (wb 0) ->
  exists str0 rest, skipn (Z.to_nat off) bs = str0 ++ wb 0 :: rest /\ ~ In (wb 0) str0 /\ Z.of_nat (length str0) <= K.
Proof.
  intros bs off K Hoff HK HN.
  set (tl := skipn (Z.to_nat off) bs).
  assert (HT : nth_error tl (Z.to_nat K) = Some (wb 0)). { unfold tl. rewrite nth_error_skipn. rewrite <- HN. f_equal. lia. }
  destruct (find_byte 0 tl) as [i|] eqn:FB.
  - destruct (find_byte_Some _ _ _ FB) as (Hi & (b & Hb & Hb0) & Hmin).
    destruct (nth_error_split _ _ _ Hb) as (pre & post & E & Hlen).
    exists pre, post. assert (Eb : b = wb 0) by (apply bv_eq; rewrite Hb0; reflexivity). subst b.
    split; [exact E|]. split.
    + intros Hin. apply In_nth_error in Hin. destruct Hin as [j Hj].
      assert (Hjl : (j < length pre)%nat) by (apply (proj1 (nth_error_Some pre j)); rewrite Hj; discriminate).
      apply (Hmin j (wb 0) ltac:(lia)); [| reflexivity]. rewrite E. rewrite nth_error_app1 by exact Hjl. exact Hj.
    + destruct (Nat.le_gt_cases i (Z.to_nat K)) as [LE|GT]; [subst i; lia|]. exfalso. apply (Hmin (Z.to_nat K) (wb 0) GT HT). reflexivity.
  - exfalso. exact (find_byte_None _ _ FB _ _ HT eq_refl).
Qed.

(* [comment removed for export] *)
Lemma pad_reaches : forall X E, X <= E -> (- X) mod 8 <= (E - X) + (- E) mod 8.
Proof. intros X E H. Z.div_mod_to_equations. lia. Qed.

Section S.
  Variable HI : cj_heap_iface.

  Definition strlen_upd_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (bs : list byte) (len off : Z) (m : word -> option byte) : machine_state -> Prop :=
    fun ms' => exists (k : Z) (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : word -> option byte),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 k) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom psegs)
      /\ munch [] m m' /\ wmono psegs m m' /\ mem_inv psegs m'
      /\ 0 <= k /\ off + k < len /\ nth_error bs (Z.to_nat (off + k)) = Some (wb 0).

  Lemma strlen_upd : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (mo : Model) (SPB : Z) (LB : list cblock) (buf len off : Z) (bs : list byte),
    LHEAP HI SPB LB m mo -> In (buf, len) LB -> u8arr psegs m buf bs -> Z.of_nat (length bs) = len ->
    0 <= off -> pb_nul bs len off -> mem_inv psegs m -> a0 = Z_to_bv 64 (buf + off) ->
    evt psegs (strlen_upd_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc bs len off m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x20ee4) fc None m (seg_rom psegs)).
  Proof.
    intros until bs. intros HL HIN ARR LEN OFF (K & K0 & K1 & KN) MI A0.
    pose proof (lh_block_range HI _ _ _ _ _ _ HL HIN) as (R1 & R2 & R3 & R4 & R5). try rewrite alloc_ceiling_eq in R4.
    destruct (first_nul bs off K OFF K0 KN) as (str0 & rest & E & NONUL & LS).
    destruct ARR as [BA WR].
    (* [comment removed for export] *)
    assert (BT : bytes_at psegs m (buf + off) (str0 ++ wb 0 :: rest)).
    { rewrite <- E. rewrite <- (firstn_skipn (Z.to_nat off) bs) in BA. apply bytes_at_app in BA. destruct BA as [_ BA].
      rewrite firstn_length_le in BA by lia. rewrite Z2Nat.id in BA by lia. exact BA. }
    assert (LT : off + Z.of_nat (length str0) + 1 + Z.of_nat (length rest) = len).
    { pose proof (f_equal (@length byte) E) as LE. rewrite length_skipn, length_app in LE. cbn [length] in LE. lia. }
    (* [comment removed for export] *)
    destruct (some_bytes_at m (buf + len) (Z.to_nat ((- (buf + len)) mod 8))) as (pad & BP & LP).
    { lia. } { pose proof (Z.mod_pos_bound (- (buf + len)) 8 ltac:(lia)). unfold PIMG_LO, PIMG_HI in R5. Z.div_mod_to_equations. lia. }
    { intros i Hi. replace (buf + len + i) with (buf + len + i) by lia. eapply (lh_block_slack HI); [exact HL| exact HIN| lia|].
      pose proof (Z.mod_pos_bound (- (buf + len)) 8 ltac:(lia)). Z.div_mod_to_equations. lia. }
    assert (BT2 : bytes_at psegs m (buf + off) ((str0 ++ wb 0 :: rest) ++ pad)).
    { apply bytes_at_app. split; [exact BT|]. rewrite length_app. cbn [length]. replace (buf + off + Z.of_nat (length str0 + S (length rest))) with (buf + len) by lia. exact BP. }
    rewrite <- app_assoc in BT2. cbn [app] in BT2. change (wb 0) with (Z_to_bv 8 0) in BT2, NONUL.
    subst a0.
    eapply evt_cut.
    { eapply (strlen_spec ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (buf + off))); rewrite ?unsigned_lit by lia; [exact BT2| exact NONUL| | exact MI].
      rewrite length_app. pose proof (pad_reaches (buf + off + Z.of_nat (length str0) + 1) (buf + len) ltac:(lia)). lia. }
    cbv beta. intros ms' PO.
    destruct PO as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> & MU & WM & MI' & _).
    apply evt_done. unfold strlen_upd_post. exists (Z.of_nat (length str0)). do 15 eexists. split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [exact MI'|]. split; [lia|]. split; [lia|].
    rewrite <- (firstn_skipn (Z.to_nat off) bs), E. rewrite nth_error_app2 by (rewrite firstn_length_le; lia).
    rewrite firstn_length_le by lia. replace (Z.to_nat (off + Z.of_nat (length str0)) - Z.to_nat off)%nat with (length str0) by lia.
    rewrite nth_error_app2, Nat.sub_diag by lia. reflexivity.
  Qed.
End S.


End CeilWrap.
