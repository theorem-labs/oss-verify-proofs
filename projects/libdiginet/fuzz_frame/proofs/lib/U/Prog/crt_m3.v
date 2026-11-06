(* the segment crt_m3 of check_round_trip in fuzz_frame.ubsan, 0x133c4 .. 0x134bc or the jal of malloc at 0x1344c (crt_m3_stmt of crt_defs.v). *)
(* check_round_trip in fuzz_frame.ubsan, 0x133c4 .. 0x134bc or the jal of malloc at 0x1344c:
   the test of fits && !sys (s6), spec_build_frame into want with zero_sum 1, memset of out with
   0xa5, diginet_frame_build in mode 1 and the test of its answer (abort at 0x134f8), bcmp of
   out and want and the test of its answer (abort at 0x134f8), then n_want - 1 to malloc. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Sem Fpu.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.Lib Require Import PropExec MState Mem Cells Exec Frame Step Tac
  ZBridge.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.U Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.U.Spec Require Import StrFun.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.U.Prog Require Import check_parse_fields_c memset_c bcmp_c
  diginet_frame_build_c spec_build_frame_c crt_defs crt_m3_lib.
Import ListNotations.
Open Scope Z_scope.

Ltac m3_usub := repeat match goal with |- context [bv_unsigned (Z_to_bv 64 ?z)] => rewrite (unsigned_lit z) by nia end.
Ltac m3_usub_in H :=
  repeat match type of H with context [bv_unsigned (Z_to_bv 64 ?z)] => rewrite (unsigned_lit z) in H by lia end.
Ltac m3_tonat_in H :=
  repeat match type of H with context [Z.to_nat ?z] =>
    is_Zlit z; let v := eval vm_compute in (Z.to_nat z) in change (Z.to_nat z) with v in H end.

(* A branch whose condition is closed. *)
Ltac m3_brc := lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      let v := eval vm_compute in c in replace c with v by (vm_compute; reflexivity); cbv iota
  end.

(* A branch whose condition the context decides. *)
Ltac m3_take v := lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      replace c with v; [cbv iota | symmetry; unfold_cond; m3_usub; fold_lit_ux; solve_cond_rec]
  end.

Ltac m3_cur k := lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => k mm end.

(* post_call, with the addresses and sizes of the callee's post as numbers. *)
Ltac m3_post mm :=
  let ms' := fresh "ms'" in let PO := fresh "POST" in
  intros ms' PO; destruct_exs PO;
  try unfold SBF_STACK in PO;
  m3_usub_in PO; m3_tonat_in PO;
  let E := fresh "E" in let MUc := fresh "MUc" in let WMc := fresh "WMc" in let MIc := fresh "MI" in
  destruct PO as [E [MUc [WMc PO]]];
  first [ destruct PO as [MIc PO] | rename PO into MIc ];
  subst ms';
  lazymatch type of MUc with
  | munch _ mm ?m' =>
      transport_after_call rsegs mm m' MUc WMc; clear MUc WMc;
      try match goal with H : mem_inv rsegs mm |- _ => clear H end;
      try clear mm
  end;
  try destruct_ands PO;
  try (lazymatch goal with
       | |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?k)) _ _ _ _) =>
           replace (ret_pc (Z_to_bv 64 k)) with (Z_to_bv 64 k) by (symmetry; apply ret_pc_even; [ lia | reflexivity ])
       end).

(* diginet_frame_build reads the address of h from a4 (mv a4, sp): the word sp as a number. *)
Lemma m3_a4_sp : forall (Q : machine_state -> Prop)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 pc : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
  evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 (Z_to_bv 64 (bv_unsigned sp)) a5 a6 a7
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F pc fc None m (seg_rom rsegs)) ->
  evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 sp a5 a6 a7
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F pc fc None m (seg_rom rsegs)).
Proof.
  intros Q ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 pc F fc m H.
  rewrite Z_to_bv_lit_self in H. exact H.
Qed.

Lemma crt_m3_ok : crt_m3_stmt.
Proof.
  unfold crt_m3_stmt.
  intros MEMSET BCMP FB SBF ra sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    w buf out want n b j jo jw sv HC HL HN LAY RO BB RWo RWw STs SV FR MI.
  destruct (fr_body_len_ok b HC) as (BL0 & PL0 & BLe).
  destruct (fr_code_ok b HC) as (L30 & _ & _ & _).
  assert (NB : Z.of_nat (length (fr_body b)) = fr_body_len b) by (rewrite (length_fr_body b HC); lia).
  destruct LAY as (Lb0 & Lb1 & Lo0 & Lo1 & Lw0 & Lw1 & Dow & Dob & Dwb & Lsw & Lw80 & Lsp8).
  pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
  unfold spec_cells in RO.
  destruct (crt_ok b) eqn:OK; cbv iota.
  2: {
    step. m3_brc.
    apply evt_done. unfold crt_mid_post.
    do 21 eexists. exists j, m.
    split; [reflexivity|].
    split; [left; split; [exact OK | reflexivity]|].
    split; [apply munch_refl|]. split; [apply wmono_refl|]. split; [exact MI|]. exact FR. }
  pose proof OK as OK'. unfold crt_ok in OK'.
  assert (Rsend : 0 <= fr_send b < 2^32) by apply be32_range.
  assert (Rack : 0 <= fr_ack b < 2^32) by apply be32_range.
  assert (Rretry : 0 <= fr_retry b < 2^16) by apply be16_range.
  assert (Rcmd : 0 <= fr_cmd b < 2^8) by apply at8_range.
  assert (Rnc : 0 <= fr_ncmds b < 2^8) by apply at8_range.
  assert (HN' : n = Z.max 60 (30 + fr_body_len b)) by (rewrite HN; unfold frame_len; lia).
  assert (Ljw : length jw = Z.to_nat n) by exact (m3_rw_len _ _ _ _ RWw).
  assert (LJ : Z.of_nat (length jw) = n) by lia.
  rewrite <- Ljw in RWw.
  pose proof (munch_refl [(bv_unsigned sp - 240, bv_unsigned sp + 80); (out, out + n); (want, want + n)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  (* 0x133c4: s6 is 0 *)
  step. m3_brc.
  (* 0x133c8 .. 0x133f4: the loads of w's fields, then spec_build_frame (want, ..., zero_sum 1) *)
  do 12 step.
  rewrite (m3_zxb (fr_cmd b) Rcmd), (m3_zxb (fr_ncmds b) Rnc), (m3_zx16 (fr_retry b) Rretry).
  replace (Z_to_bv 64 (fr_body_len b)) with (Z_to_bv 64 (Z.of_nat (length (fr_body b)))) by (rewrite NB; reflexivity).
  m3_cur ltac:(fun mm => eapply evt_cut;
    [ eapply SBF with (out := want) (dst := buf) (src := buf + 6) (body := buf + 30) (zs := 1)
        (lo := bv_unsigned sp - 240) (send := fr_send b) (ack := fr_ack b) (retry := fr_retry b)
        (cmd := fr_cmd b) (ncmds := fr_ncmds b) (dmac := fr_dst b) (smac := fr_src b) (bb := fr_body b) (oj := jw)
    | m3_post mm ]).
  1-5: lia.
  1: { right. reflexivity. }
  1: lia.
  1: { apply m3_len_dst. lia. }
  1: { apply m3_dst_bytes. exact BB. }
  1: { apply m3_len_src. lia. }
  1: { apply m3_src_bytes; [lia | exact BB]. }
  1: { apply m3_body_bytes; [exact HC | exact BB]. }
  1: { rewrite LJ. exact HN. }
  1: { exact RWw. }
  1-3: lia.
  1: { exact STs. }
  1-5: (unfold SBF_STACK; lia).
  1: { assumption. }
  (* 0x133f8 .. 0x13404: memset (out, 0xa5, n) *)
  do 4 step.
  m3_cur ltac:(fun mm => eapply evt_cut; [eapply MEMSET with (junk := jo) | m3_post mm]).
  1: { m3_usub. exact RWo. }
  1: { assumption. }
  (* 0x13408 .. 0x13428: diginet_frame_build (out, n, dst, src, sp, body, body_len, 1) *)
  do 9 step.
  lazymatch goal with H : rw_cells rsegs _ out [CB _ (repeat ?z _)] |- _ =>
    remember (repeat z (Z.to_nat n)) as oj eqn:Eoj end.
  assert (Loj : Z.of_nat (length oj) = n) by (subst oj; rewrite repeat_length; lia).
  replace (Z_to_bv 64 n) with (Z_to_bv 64 (Z.of_nat (length oj))) by (rewrite Loj; reflexivity).
  replace (Z_to_bv 64 (fr_body_len b)) with (Z_to_bv 64 (Z.of_nat (length (fr_body b)))) by (rewrite NB; reflexivity).
  apply m3_a4_sp.
  m3_cur ltac:(fun mm => eapply evt_cut;
    [ eapply FB with (out := out) (dst := buf) (src := buf + 6) (hp := bv_unsigned sp) (body := buf + 30)
        (mode := 1) (lo := bv_unsigned sp - 240) (send := fr_send b) (ack := fr_ack b) (retry := fr_retry b)
        (cmd := fr_cmd b) (ncmds := fr_ncmds b) (dmac := fr_dst b) (smac := fr_src b) (bb := fr_body b) (oj := oj)
    | m3_post mm ]).
  1-5: lia.
  1: { right. reflexivity. }
  1: { Z.div_mod_to_equations. lia. }
  1-6: lia.
  1: { apply m3_len_dst. lia. }
  1: { apply m3_dst_bytes. exact BB. }
  1: { apply m3_len_src. lia. }
  1: { apply m3_src_bytes; [lia | exact BB]. }
  1: { change (bv_unsigned sp + 4) with (bv_unsigned sp + Z.of_nat 4).
       exact (m3_cell_bytes _ _ _ 4 _ FR eq_refl). }
  1: { apply m3_body_bytes; [exact HC | exact BB]. }
  1: { replace (length oj) with (Z.to_nat n) by lia. assumption. }
  1-4: lia.
  1: { exact Lsp8. }
  1: { assumption. }
  1-7: lia.
  1: { assumption. }
  rewrite Loj.
  assert (BC : build_code (fr_body b) n = n) by (rewrite HN; apply m3_build_code; exact OK').
  rewrite BC.
  (* 0x1342c: the answer is n (s5), no abort *)
  step. m3_take false.
  (* 0x13430 .. 0x1343c: bcmp (out, want, n) *)
  do 4 step.
  m3_cur ltac:(fun mm => eapply evt_cut;
    [ eapply BCMP with
        (ls := build_frame (fr_dst b) (fr_src b) (fr_send b) (fr_ack b) (fr_retry b) (fr_cmd b) (fr_ncmds b)
                 (fr_body b) true)
        (rs := build_frame (fr_dst b) (fr_src b) (fr_send b) (fr_ack b) (fr_retry b) (fr_cmd b) (fr_ncmds b)
                 (fr_body b) true)
        (v := 0)
    | m3_post mm ]).
  1: { m3_usub.
       lazymatch goal with H : rw_cells rsegs _ out [CB _ (build_out _ _ _ _ _ _ _ _ _ _)] |- _ =>
         pose proof (m3_rw_bytes _ _ _ _ H) as BO end.
       rewrite Eoj, HN, (m3_build_out _ _ _ _ _ _ _ _ _ OK') in BO. exact BO. }
  1: { m3_usub.
       lazymatch goal with H : rw_cells rsegs _ want [CB _ (build_frame _ _ _ _ _ _ _ _ _)] |- _ =>
         exact (m3_rw_bytes _ _ _ _ H) end. }
  1: { m3_usub. apply m3_memcmp_self.
       pose proof (length_build_frame (fr_dst b) (fr_src b) (fr_send b) (fr_ack b) (fr_retry b) (fr_cmd b)
         (fr_ncmds b) (fr_body b) true (m3_len_dst b ltac:(lia)) (m3_len_src b ltac:(lia))) as LBF.
       lia. }
  1: { assumption. }
  (* 0x13440: bcmp answers 0, no abort *)
  step. m3_brc.
  (* 0x13444 .. 0x1344c: s3 = n - 1, a0 = s3, jal malloc *)
  do 3 step.
  apply evt_done. unfold crt_mid_post.
  do 21 eexists. exists j. eexists.
  split; [reflexivity|].
  split.
  { right. split; [exact OK|]. split; [reflexivity|]. split; [reflexivity|].
    split; f_equal; try m3_usub; lia. }
  split; [exact MU|]. split; [exact WM|]. split; [assumption|]. exact FR.
Qed.
