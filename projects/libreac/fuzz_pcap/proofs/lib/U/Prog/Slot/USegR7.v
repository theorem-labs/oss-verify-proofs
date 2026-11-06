From OSSVerify.Proofs.libreac.fuzz_pcap.lib Require Import SymAddr.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Lib Require Import PropExec MState Mem Cells Exec Frame Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.U Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.U.Prog Require Import StdioModel.
Import ListNotations.
Open Scope Z_scope.

Ltac addr_eq_tac ::= first [ apply wa_of_var; lia
                           | symmetry; first [ apply wa_of_Z_to_bv; lia | apply wa_of_var; lia | unfold wa; f_equal; lia ] ].

(* Helpers of the segment files of the ubsan slot (USegR7.v, USegE.v). *)

(* A read-only view of known bytes, for the loads of `step`. *)
Lemma ba_ro8 : forall m a v, bytes_at rsegs m a (le8 v) -> ro_cells rsegs m a [C8 v].
Proof. intros m a v H. split; [cbn; tauto | cbn [cells_bytes cbytes]; rewrite app_nil_r; exact H]. Qed.

Lemma ba_ro4 : forall m a v, bytes_at rsegs m a (le4 v) -> ro_cells rsegs m a [C4 v].
Proof. intros m a v H. split; [cbn; tauto | cbn [cells_bytes cbytes]; rewrite app_nil_r; exact H]. Qed.

Lemma ba_ro1 : forall m a d, bytes_at rsegs m a [d] -> ro_cells rsegs m a [C1 d].
Proof. intros m a d H. split; [cbn; tauto | cbn [cells_bytes cbytes]; exact H]. Qed.

Lemma rw_bytes : forall m a cs, rw_cells rsegs m a cs -> bytes_at rsegs m a (cells_bytes cs).
Proof. intros m a cs [[_ H] _]. exact H. Qed.

Ltac get_reg k :=
  lazymatch goal with
  | |- evt _ _ (MS ?R _ _ _ _ _ _) =>
      let p := eval vm_compute in (bv_key (Z_to_bv 5 k)) in
      let v := eval cbv beta iota delta [tget] in (match tget p R with Some v => v | None => Z_to_bv 64 0 end) in v
  end.

(* Replace the value of register k by t; tac proves t = v. *)
Ltac rep_reg k t tac := let v := get_reg k in replace v with t by tac.

Ltac fix_ret :=
  try (lazymatch goal with
  | |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
      replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ])
  end).

(* A branch whose condition the premises decide; the other side is refuted. *)
Ltac bad K :=
  exfalso; rewrite ?Z.shiftr_div_pow2 in K by lia; rewrite ?unsigned_lit_wrap in K;
  Z.div_mod_to_equations; lia.

Ltac bres :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) =>
      first [ if_true | if_false
            | let K := fresh "K" in if_cases K; [ zify_cond K; bad K | clear K ]
            | let K := fresh "K" in if_cases K; [ clear K | zify_cond K; bad K ]
            | lazymatch goal with |- evt _ _ (MS _ _ (if ?c then ?t else ?e) _ _ _ _) =>
                idtac "UNRESOLVED BRANCH:" c "THEN" t "ELSE" e end; fail 1 ]
  | _ => idtac
  end.

(* The saved registers of entry_fn (0x12c4c) at S - 104 = sp_h + 72, in the order of the 13 `sd` of the
   prologue: s11 at sp_h + 72, s10, ..., s1, s0, ra at sp_h + 168. *)
Definition ubs_saved (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) : list byte :=
  le8 s11 ++ le8 s10 ++ le8 s9 ++ le8 s8 ++ le8 s7 ++ le8 s6 ++ le8 s5 ++ le8 s4 ++ le8 s3 ++ le8 s2 ++
  le8 s1 ++ le8 s0 ++ le8 ra.

Definition ubs_saved_cells (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) : list cell :=
  [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

Lemma ubs_saved_cells_bytes : forall ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11,
  cells_bytes (ubs_saved_cells ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) =
  ubs_saved ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11.
Proof. intros. cbn [cells_bytes cbytes ubs_saved_cells]. rewrite app_nil_r. reflexivity. Qed.

Lemma ubs_saved_cells_wf : forall ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11,
  cells_wf (ubs_saved_cells ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11).
Proof. intros. cbn. tauto. Qed.

Lemma ubs_saved_length : forall ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11,
  length (ubs_saved ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) = 104%nat.
Proof. intros. unfold ubs_saved. rewrite !length_app, !length_le8. reflexivity. Qed.

(* R7: 0x130d4-0x13110, the epilogue: a0 = 0, ra and s0-s11 from the saved bytes, sp = sp_h + 176, ret. *)
Lemma ubs_R7_x :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (FR : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (sp_h : Z)
         (ra' s0' s1' s2' s3' s4' s5' s6' s7' s8' s9' s10' s11' : word),
    bv_unsigned sp = sp_h ->
    bytes_at rsegs m (sp_h + 72) (ubs_saved ra' s0' s1' s2' s3' s4' s5' s6' s7' s8' s9' s10' s11') ->
    evt rsegs
      (fun ms' => ms' = MS (mkR ra' (wz (sp_h + 176)) gp tp t0 t1 t2 s0' s1' (wz 0) a1 a2 a3 a4 a5 a6 a7
                                s2' s3' s4' s5' s6' s7' s8' s9' s10' s11' t3 t4 t5 t6)
                           FR (ret_pc ra') fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          FR (Z_to_bv 64 (symaddr (Symbols.Ubsan.s_LLVMFuzzerTestOneInput + 0x488)%Z)) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    FR fc m sp_h ra' s0' s1' s2' s3' s4' s5' s6' s7' s8' s9' s10' s11' HSP HB.
  subst sp_h.
  pose proof (bytes_at_bound rsegs _ _ _ HB) as BND. rewrite ubs_saved_length in BND.
  assert (RO : ro_cells rsegs m (bv_unsigned sp + 72) (ubs_saved_cells ra' s0' s1' s2' s3' s4' s5' s6' s7' s8' s9' s10' s11')).
  { split; [apply ubs_saved_cells_wf | rewrite ubs_saved_cells_bytes; exact HB]. }
  clear HB. unfold ubs_saved_cells in RO. unfold wz.
  do 16 step.
  apply evt_done. reflexivity.
Qed.
