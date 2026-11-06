(* check_round_trip in fuzz_frame.plain, 0x13310 .. 0x134c8 or the jal of malloc at 0x13460
   (crt_m3_stmt of crt_defs.v): the test of fits && !sys, the second inlined spec_build_frame
   into want in the zero-sum mode, memset of out with 0xa5, diginet_frame_build in mode 1, the
   test of its answer, bcmp of out and want, then n_want - 1 to malloc.
   Written by Theorem Labs. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Sem Fpu.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.Lib Require Import PropExec MState Mem Cells Exec Frame Step Tac
  Bytes ZBridge.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.Spec Require Import DgnSpec DgnLib StrFun.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.Prog Require Import check_parse_fields_c memset_c memcpy_c
  bcmp_c diginet_frame_build_c crt_defs crt_m3_lem.
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

Lemma m3_le1_zxb : forall x : byte, le1 (zxb x) = [x].
Proof. intros x. exact (le1_zxb x). Qed.

(* post_call, with the addresses and sizes of the callee's post as numbers. *)
Ltac m3_post mm :=
  let ms' := fresh "ms'" in let PO := fresh "POST" in
  intros ms' PO; destruct_exs PO;
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

(** * 0x13340: a2 = max 60 (30 + body_len) *)

Lemma m3_max : forall (Q : machine_state -> Prop)
    (ra sp gp tp t0 t1 t2 s0 s1 a1 a3 a4 a5 a6 a7 s2 s3 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (L n : Z),
  0 <= L < 2^40 -> n = Z.max 60 (30 + L) ->
  evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 60) a1 (Z_to_bv 64 n) a3 a4 a5 a6 a7 s2 s3
                     (Z_to_bv 64 L) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 0x13348) fc None m (seg_rom rsegs)) ->
  evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 60) a1 (Z_to_bv 64 (L + 30)) a3 a4 a5 a6 a7 s2 s3
                     (Z_to_bv 64 L) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 0x13340) fc None m (seg_rom rsegs)).
Proof.
  intros Q ra sp gp tp t0 t1 t2 s0 s1 a1 a3 a4 a5 a6 a7 s2 s3 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m L n HL HN H.
  destruct (Z.ltb_spec 60 (L + 30)) as [C|C].
  - step. m3_take true. replace (L + 30) with n by lia. exact H.
  - step. m3_take false. step. assert (E : n = 60) by lia. rewrite E in H. exact H.
Qed.

(** * 0x13408 .. jal malloc (0x13460) *)

Lemma m3_tail : memset_contract -> bcmp_contract -> diginet_frame_build_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m0 m : word -> option byte)
         (w buf out want n : Z) (b j j2 jo : list byte) (sv : list cell),
    fr_code b = 0 -> Z.of_nat (length b) < 2 ^ 26 -> n = frame_len (length (fr_body b)) -> crt_ok b = true ->
    crt_lay (bv_unsigned sp) w buf out want n (Z.of_nat (length b)) ->
    ro_cells rsegs m w (spec_cells buf b) ->
    bytes_at rsegs m buf b ->
    rw_cells rsegs m out [CB (Z.to_nat n) jo] ->
    rw_cells rsegs m want [CB (Z.to_nat n) (m3_bf b)] ->
    stk rsegs m (bv_unsigned sp - 240) (bv_unsigned sp) ->
    cells_size sv = 104%nat ->
    rw_cells rsegs m (bv_unsigned sp) (CB 16 j :: C8 (Z_to_bv 64 out) :: CB 4 j2 :: CB 12 (crt_hb b) :: sv) ->
    mem_inv rsegs m ->
    munch [(bv_unsigned sp - 240, bv_unsigned sp + 144); (out, out + n); (want, want + n)] m0 m ->
    wmono rsegs m0 m ->
    evt rsegs (crt_mid_post sp gp tp F fc w out want n b sv m0)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 want) a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 w) (Z_to_bv 64 n)
               s4 s5 s6 s7 s8 s9 (Z_to_bv 64 n) s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x13408) fc None m (seg_rom rsegs)).
Proof.
  intros MEMSET BCMP FB ra sp gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s11 t3 t4 t5 t6 F fc m0 m
    w buf out want n b j j2 jo sv HC HL HN OK LAY RO BB RWo RWw STs SV FR MI MU WM.
  destruct (fr_body_len_ok b HC) as (BL0 & PL0 & BLe).
  destruct (fr_code_ok b HC) as (L30 & _ & _ & _).
  assert (NB : Z.of_nat (length (fr_body b)) = fr_body_len b) by (rewrite (length_fr_body b HC); lia).
  destruct LAY as (Lb0 & Lb1 & Lo0 & Lo1 & Lw0 & Lw1 & Dow & Dob & Dwb & Lsw & Lw80).
  pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
  assert (HN' : n = Z.max 60 (30 + fr_body_len b)) by (rewrite HN; unfold frame_len; lia).
  pose proof OK as OK'. unfold crt_ok in OK'.
  pose proof (m3_len_bf b ltac:(lia)) as LBF.
  unfold spec_cells in RO.
  (* memset (out, 0xa5, n) *)
  do 5 step.
  m3_cur ltac:(fun mm => eapply evt_cut; [eapply MEMSET with (junk := jo) | m3_post mm]).
  1: { m3_usub. exact RWo. }
  1: { assumption. }
  (* diginet_frame_build (out, n, dst, src, sp + 0x18, body, body_len, 1) *)
  do 9 step.
  remember (repeat (Z_to_bv 8 (165 mod 256)) (Z.to_nat n)) as oj eqn:Eoj.
  assert (Loj : Z.of_nat (length oj) = n) by (subst oj; rewrite repeat_length; lia).
  replace (Z_to_bv 64 n) with (Z_to_bv 64 (Z.of_nat (length oj))) by (rewrite Loj; reflexivity).
  replace (Z_to_bv 64 (fr_body_len b)) with (Z_to_bv 64 (Z.of_nat (length (fr_body b)))) by (rewrite NB; reflexivity).
  m3_cur ltac:(fun mm => eapply evt_cut;
    [ eapply FB with (out := out) (dst := buf) (src := buf + 6) (hp := bv_unsigned sp + 24) (body := buf + 30)
        (mode := 1) (lo := bv_unsigned sp - 240) (send := fr_send b) (ack := fr_ack b) (retry := fr_retry b)
        (cmd := fr_cmd b) (ncmds := fr_ncmds b) (dmac := fr_dst b) (smac := fr_src b) (bb := fr_body b) (oj := oj)
    | m3_post mm ]).
  1-5: lia.
  1: { right. reflexivity. }
  1-2: apply be32_range.
  1: apply be16_range.
  1-2: apply at8_range.
  1: lia.
  1: { apply m3_len_dst. lia. }
  1: { apply m3_dst_bytes. exact BB. }
  1: { apply m3_len_src. lia. }
  1: { apply m3_src_bytes; [lia | exact BB]. }
  1: { replace (bv_unsigned sp + 24 + 4) with (bv_unsigned sp + Z.of_nat 28) by lia.
       exact (m3_cell_bytes _ _ _ 28 _ FR eq_refl). }
  1: { apply m3_body_bytes; [exact HC | exact BB]. }
  1: { replace (length oj) with (Z.to_nat n) by lia. assumption. }
  1-4: lia.
  1: { exact STs. }
  1-6: lia.
  1: { assumption. }
  rewrite Loj.
  assert (BC : build_code (fr_body b) n = n) by (rewrite HN; apply m3_build_code; exact OK').
  rewrite BC.
  step. m3_take false.
  (* bcmp (out, want, n) *)
  do 4 step.
  m3_cur ltac:(fun mm => eapply evt_cut; [eapply BCMP with (ls := m3_bf b) (rs := m3_bf b) (v := 0) | m3_post mm]).
  1: { m3_usub.
       lazymatch goal with H : rw_cells rsegs _ out [CB _ (build_out _ _ _ _ _ _ _ _ _ _)] |- _ =>
         pose proof (m3_rw_bytes _ _ _ _ H) as BO end.
       rewrite Eoj, HN, (m3_build_out _ _ _ _ _ _ _ _ _ OK') in BO. exact BO. }
  1: { m3_usub. exact (m3_rw_bytes _ _ _ _ RWw). }
  1: { m3_usub. apply m3_memcmp_self. lia. }
  1: { assumption. }
  step. m3_brc.
  do 3 step.
  apply evt_done. unfold crt_mid_post.
  do 26 eexists. exists (cells_bytes [CB 16 j; C8 (Z_to_bv 64 out); CB 4 j2]). eexists.
  split; [reflexivity|].
  split.
  { right. split; [exact OK|]. split; [reflexivity|]. split; [reflexivity|].
    split; f_equal; lia. }
  split; [exact MU|]. split; [exact WM|]. split; [assumption|].
  apply m3_merge3. exact FR.
Qed.

(** * 0x13310 .. 0x134c8 or jal malloc (0x13460) *)

Lemma crt_m3_ok : crt_m3_stmt.
Proof.
  unfold crt_m3_stmt.
  intros MEMSET MEMCPY BCMP FB ra sp gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s4 s7 s8 s11 t3 t4 t5 t6 F fc m
    w buf out want n b j j2 sv HC HL HN LAY RO BB STo STw STs SV FR MI.
  pose proof LAY as LAY0.
  destruct (fr_body_len_ok b HC) as (BL0 & PL0 & BLe).
  destruct (fr_code_ok b HC) as (L30 & _ & _ & _).
  assert (NB : Z.of_nat (length (fr_body b)) = fr_body_len b) by (rewrite (length_fr_body b HC); lia).
  destruct LAY as (Lb0 & Lb1 & Lo0 & Lo1 & Lw0 & Lw1 & Dow & Dob & Dwb & Lsw & Lw80).
  pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
  assert (HN' : n = Z.max 60 (30 + fr_body_len b)) by (rewrite HN; unfold frame_len; lia).
  unfold spec_cells in RO.
  destruct (crt_ok b) eqn:OK.
  2: {
    step. m3_brc.
    apply evt_done. unfold crt_mid_post.
    do 26 eexists. exists (cells_bytes [CB 16 j; C8 (Z_to_bv 64 out); CB 4 j2]), m.
    split; [reflexivity|].
    split; [left; split; [exact OK | reflexivity]|].
    split; [apply munch_refl|]. split; [apply wmono_refl|]. split; [exact MI|].
    exact (m3_merge3 _ _ _ _ _ _ FR). }
  assert (Rsend : 0 <= fr_send b < 2^32) by apply be32_range.
  assert (Rack : 0 <= fr_ack b < 2^32) by apply be32_range.
  assert (Rretry : 0 <= fr_retry b < 2^16) by apply be16_range.
  destruct (m3_stk_rw m want n STw ltac:(lia)) as [jw RWw]. clear STw.
  destruct (m3_stk_rw m out n STo ltac:(lia)) as [jo RWo]. clear STo.
  pose proof (munch_refl [(bv_unsigned sp - 240, bv_unsigned sp + 144); (out, out + n); (want, want + n)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  (* 0x13310 .. 0x13340: the loads of the second spec_build_frame *)
  step. m3_brc.
  do 11 step.
  eapply m3_max with (L := fr_body_len b) (n := n); [lia | lia |].
  (* memset (want, 0, n); the store sd a0, 0(sp) has its address in a register, and the step
     machinery reads it as the word sp *)
  step.
  m3_cur ltac:(fun mm =>
    assert (HS : store_ok rsegs mm sp 8 = true) by
      (rewrite <- (wa_of_var sp (bv_unsigned sp + Z.of_nat 0)) by lia;
       exact (rw_cells_store_ok rsegs mm (bv_unsigned sp) _ 0 _ 8 FR eq_refl eq_refl))).
  step.
  m3_cur ltac:(fun mm => lazymatch mm with write_to_mem ?m1 sp ?bs =>
    replace (write_to_mem m1 sp bs) with (write_to_mem m1 (wa (bv_unsigned sp + Z.of_nat 0)) bs)
      by (f_equal; apply wa_of_var; lia) end).
  clear HS. mem_after_store.
  do 3 step.
  m3_cur ltac:(fun mm => eapply evt_cut; [eapply MEMSET with (junk := jw) | m3_post mm]).
  1: { m3_usub. exact RWw. }
  1: { assumption. }
  lazymatch goal with H : rw_cells rsegs _ want [CB (Z.to_nat n) (repeat ?z _)] |- _ =>
    destruct (m3_slots _ want (Z.to_nat n) (length (fr_body b)) z ltac:(lia) H) as (W1 & W2 & W3 & W4 & W5);
    clear H end.
  (* memcpy (want, dst, 6) *)
  do 4 step.
  m3_cur ltac:(fun mm => eapply evt_cut; [eapply MEMCPY with (src := fr_dst b) | m3_post mm]).
  1: { m3_usub. apply m3_dst_bytes. exact BB. }
  1: { m3_usub. apply m3_len_dst. lia. }
  1: { m3_usub. exact W1. }
  1: { m3_usub. lia. }
  1: { assumption. }
  lazymatch goal with H : bytes_at rsegs _ buf (fr_dst b) |- _ => clear H end.
  lazymatch goal with H : rw_cells rsegs _ want [CB _ (fr_dst b)] |- _ => rename H into V1 end.
  (* memcpy (want + 6, src, 6) *)
  do 4 step.
  m3_cur ltac:(fun mm => eapply evt_cut; [eapply MEMCPY with (src := fr_src b) | m3_post mm]).
  1: { m3_usub. apply m3_src_bytes; [lia | exact BB]. }
  1: { m3_usub. apply m3_len_src. lia. }
  1: { m3_usub. exact W2. }
  1: { m3_usub. lia. }
  1: { assumption. }
  lazymatch goal with H : bytes_at rsegs _ (buf + 6) (fr_src b) |- _ => clear H end.
  lazymatch goal with H : rw_cells rsegs _ (want + 6) [CB _ (fr_src b)] |- _ => rename H into V2 end.
  (* the 18 header bytes at want + 12 *)
  do 9 step.
  step. rewrite (m3_le1_lit _ (0 / 2^8)) by (vm_compute; reflexivity). mem_after_store.
  step. rewrite (m3_le1_lit _ 0) by (vm_compute; reflexivity). mem_after_store.
  step. rewrite (m3_le1_sx32 (fr_send b) 24) by lia. mem_after_store.
  step. rewrite (m3_le1_sx32 (fr_send b) 16) by lia. mem_after_store.
  step.
  step. rewrite (m3_le1_sx32 (fr_send b) 8) by lia. mem_after_store.
  step. rewrite (m3_le1_sx32_0 (fr_send b)) by lia. mem_after_store.
  step. rewrite (m3_le1_sx32 (fr_ack b) 24) by lia. mem_after_store.
  step. rewrite (m3_le1_sx32 (fr_ack b) 16) by lia. mem_after_store.
  step.
  step. rewrite (m3_le1_sx32 (fr_ack b) 8) by lia. mem_after_store.
  step. rewrite (m3_le1_sx32_0 (fr_ack b)) by lia. mem_after_store.
  step. rewrite (m3_le1_sx16 (fr_retry b) 8) by lia. mem_after_store.
  step. rewrite (m3_le1_sx16_0 (fr_retry b)) by lia. mem_after_store.
  step. rewrite (m3_le1_lit _ (0x885f / 2^8)) by (vm_compute; reflexivity). mem_after_store.
  step. rewrite (m3_le1_lit _ 0x885f) by (vm_compute; reflexivity). mem_after_store.
  step. rewrite (m3_le1_srl (fr_body_len b + 16) (16 + Z.of_nat (length (fr_body b))) 8) by lia. mem_after_store.
  step. rewrite (m3_le1_eq (fr_body_len b + 16) (16 + Z.of_nat (length (fr_body b)))) by lia. mem_after_store.
  step.
  step. rewrite m3_le1_zxb. mem_after_store.
  step. rewrite m3_le1_zxb. mem_after_store.
  lazymatch goal with H : rw_cells rsegs _ (want + 12) _ |- _ => apply m3_merge_all in H; rename H into V3 end.
  (* 0x133f4: memcpy (want + 30, body, body_len) when body_len <> 0 *)
  destruct (Z.eq_dec (fr_body_len b) 0) as [L0|L0].
  - step. m3_take true.
    assert (E0 : fr_body b = []) by (apply length_zero_iff_nil; lia).
    replace (repeat (Z_to_bv 8 (0 mod 256)) (length (fr_body b))) with (fr_body b) in W4 by (rewrite E0; reflexivity).
    pose proof (m3_want _ want b _ _ eq_refl eq_refl V1 V2 V3 W4 W5) as WW. rewrite <- HN in WW.
    apply m3_merge2 in FR.
    eapply (m3_tail MEMSET BCMP FB);
      [exact HC | exact HL | exact HN | exact OK | exact LAY0 | exact RO | exact BB | exact RWo | exact WW
      | exact STs | exact SV | exact FR | assumption | exact MU | exact WM].
  - step. m3_take false.
    do 4 step.
    m3_cur ltac:(fun mm => eapply evt_cut; [eapply MEMCPY with (src := fr_body b) | m3_post mm]).
    1: { m3_usub. apply m3_body_bytes; [exact HC | exact BB]. }
    1: { m3_usub. exact (length_fr_body b HC). }
    1: { m3_usub. rewrite <- (length_fr_body b HC). exact W4. }
    1: { m3_usub. lia. }
    1: { assumption. }
    lazymatch goal with H : bytes_at rsegs _ (buf + 30) (fr_body b) |- _ => clear H end.
    lazymatch goal with H : rw_cells rsegs _ (want + 30) [CB _ (fr_body b)] |- _ =>
      rewrite <- (length_fr_body b HC) in H; rename H into V4 end.
    pose proof (m3_want _ want b _ _ eq_refl eq_refl V1 V2 V3 V4 W5) as WW. rewrite <- HN in WW.
    apply m3_merge2 in FR.
    eapply (m3_tail MEMSET BCMP FB);
      [exact HC | exact HL | exact HN | exact OK | exact LAY0 | exact RO | exact BB | exact RWo | exact WW
      | exact STs | exact SV | exact FR | assumption | exact MU | exact WM].
Qed.
