(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)


From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QsjA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsjA. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QEpW.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QEpW. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QZDE.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZDE. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QbVh.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QbVh. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QlEo.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlEo. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QWxq.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWxq. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QXup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXup.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UEQM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UEQM.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QWxq.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWxq.Mq0.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QRjH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRjH.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QHnV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QHnV. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QCcH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCcH. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QfLs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QfLs. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q0Ek.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q0Ek. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qtgi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qtgi. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QjDH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QjDH. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QjDH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QjDH.Mq0.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UC8c.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UC8c.Mq0.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qsw7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qsw7. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QJjn.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJjn. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QkMG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QkMG.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UPZI.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UPZI.Mq0.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Lib.SepCache.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.SepCache.StrFun.
Import ListNotations.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.G Require T_pe.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Unset Keyed Unification.

Notation pe_saved := G.T_pe.pe_saved.
Notation PES := G.T_pe.PES.
Notation pe_ra := G.T_pe.pe_ra.
Notation pe_s0 := G.T_pe.pe_s0.
Notation pe_s1 := G.T_pe.pe_s1.
Notation pe_s2 := G.T_pe.pe_s2.
Notation pe_s3 := G.T_pe.pe_s3.
Notation pe_s4 := G.T_pe.pe_s4.
Notation pe_s5 := G.T_pe.pe_s5.
Notation pe_s6 := G.T_pe.pe_s6.
Notation pe_s7 := G.T_pe.pe_s7.
Notation pe_s8 := G.T_pe.pe_s8.
Notation pe_s9 := G.T_pe.pe_s9.
Notation pe_s10 := G.T_pe.pe_s10.
Notation pe_s11 := G.T_pe.pe_s11.
Notation pe_fix := G.T_pe.pe_fix.
Notation PEF := G.T_pe.PEF.
Notation pf_tk := G.T_pe.pf_tk.
Notation pf_oldl := G.T_pe.pf_oldl.
Notation pf_newl := G.T_pe.pf_newl.
Notation pf_len := G.T_pe.pf_len.
Notation pf_lenr := G.T_pe.pf_lenr.
Notation pf_sb := G.T_pe.pf_sb.
Notation pf_spf := G.T_pe.pf_spf.
Notation pf_md := G.T_pe.pf_md.
Notation pf_mxd := G.T_pe.pf_mxd.
Notation pf_fl := G.T_pe.pf_fl.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Definition PE_LOOP : Z := 0x21d84.
Definition PE_REDO : Z := 0x21e14.
Definition PE_BREAK : Z := 0x23d14.
Definition PE_BREAK2 : Z := 0x23d14.
Definition PE_OUT : Z := 0x23ea8.
Definition PE_ERR : Z := 0x23ea4.
Definition PE_JTAB : Z := 0x134c0.
Definition PE_TP : Z := 0x77c00.
Definition PE_FRAME : Z := 144.

Definition nbw (j2 : list byte) : word := Z_to_bv 64 (bytes_le_to_Z (firstn 4 j2)).
Definition pe_frame (segs : list Segment) (m : word -> option byte) (SPF : Z) (obj : Z) (c : byte)
(j1 : list byte) (j2 : list byte) (utf : list byte) (sv : pe_saved) : Prop :=
rw_cells segs m SPF
[C8 (Z_to_bv 64 obj); CB 16 j1; C4 (nbw j2); CB 3 (skipn 4 j2); C1 c; CB 8 utf;
C8 (pe_s11 sv); C8 (pe_s10 sv); C8 (pe_s9 sv); C8 (pe_s8 sv); C8 (pe_s7 sv); C8 (pe_s6 sv);
C8 (pe_s5 sv); C8 (pe_s4 sv); C8 (pe_s3 sv); C8 (pe_s2 sv); C8 (pe_s1 sv); C8 (pe_s0 sv); C8 (pe_ra sv)].

#[using="Type"] Lemma nbw_zero4 : forall jb, nbw (Z_to_le_bytes 4 0 ++ jb) = Z_to_bv 64 0.
Proof. intros jb. apply bv_eq. vm_compute. reflexivity. Qed.
#[using="Type"] Lemma skipn4_zero4 : forall jb : list byte, skipn 4 (Z_to_le_bytes 4 0 ++ jb) = jb.
Proof. intros jb. reflexivity. Qed.

#[using="Type"] Lemma nbw_le4 : forall (v : word) (jb : list byte), le4 (nbw (le4 v ++ jb)) = le4 v.
Proof.
intros v jb. unfold nbw. rewrite firstn_app, length_le4, Nat.sub_diag, firstn_O, app_nil_r, firstn_all2 by (rewrite length_le4; lia).
unfold le4 at 1. rewrite Z_to_bv_unsigned.
pose proof (Z_to_le_bytes_to_Z (le4 v)) as E. rewrite length_le4 in E.
replace (bv_wrap 64 (bytes_le_to_Z (le4 v))) with (bytes_le_to_Z (le4 v)); [exact E|].
unfold le4. rewrite bytes_le_to_Z_to_le_bytes by (pose proof (bv_unsigned_in_range 64 v); lia).
symmetry. apply bv_wrap_small. change (2 ^ (8 * Z.of_nat 4)) with (2^32). unfold bv_modulus. change (2 ^ Z.of_N 64) with (2^64).
pose proof (Z.mod_pos_bound (bv_unsigned v) (2^32) ltac:(lia)). lia.
Qed.
#[using="Type"] Lemma pe_frame_nb_set : forall segs m SPF obj c j1 (v : word) jb utf sv,
rw_cells segs m SPF
[C8 (Z_to_bv 64 obj); CB 16 j1; C4 v; CB 3 jb; C1 c; CB 8 utf;
C8 (pe_s11 sv); C8 (pe_s10 sv); C8 (pe_s9 sv); C8 (pe_s8 sv); C8 (pe_s7 sv); C8 (pe_s6 sv);
C8 (pe_s5 sv); C8 (pe_s4 sv); C8 (pe_s3 sv); C8 (pe_s2 sv); C8 (pe_s1 sv); C8 (pe_s0 sv); C8 (pe_ra sv)] ->
pe_frame segs m SPF obj c j1 (le4 v ++ jb) utf sv.
Proof.
intros segs m SPF obj c j1 v jb utf sv H. unfold pe_frame.
pose proof H as [[Hwf _] _]. cbn in Hwf. destruct Hwf as (_ & L1 & _ & L3 & _ & L8 & _).
replace (skipn 4 (le4 v ++ jb)) with jb by (rewrite skipn_app, length_le4, Nat.sub_diag, skipn_all2 by (rewrite length_le4; lia); reflexivity).
destruct H as [[Hwf HB] HW]. split; [split|].
- cbn. repeat split; assumption.
- cbn [cells_bytes cbytes app] in HB |- *. rewrite nbw_le4. exact HB.
- cbn [cells_size csize] in HW |- *. exact HW.
Qed.

Definition LENW_C : Z := 2^64 - 1.
Definition LENR_OK (pf : pe_fix) : Prop :=
pf_lenr pf = pf_len pf \/ (pf_lenr pf = LENW_C /\ 1 <= pf_len pf).

Definition CSTR_OK (pf : pe_fix) (payload : list byte) : Prop :=
pf_lenr pf = pf_len pf \/ nth_error payload (Z.to_nat (pf_len pf - 1)) = Some (Z_to_bv 8 0).

Definition payload_loc (pf : pe_fix) (LB0 : list blk) : Prop :=
pf_spf pf + PE_FRAME <= pf_sb pf
\/ (exists b, In b LB0 /\ blk_addr b <= pf_sb pf /\ pf_sb pf + pf_len pf <= blk_addr b + blk_size b).

Definition pe_ms (segs : list Segment) (pf : pe_fix) (pc : Z) (co : Z)
(x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s6 s7 s8 s9 s10 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) : machine_state :=
MS (mkR x1 (Z_to_bv 64 (pf_spf pf)) gp (Z_to_bv 64 0x77c00) t0 t1 t2
(Z_to_bv 64 (pf_tk pf)) (Z_to_bv 64 (pf_oldl pf)) a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 (pf_newl pf)) (Z_to_bv 64 (pf_lenr pf)) s4 (Z_to_bv 64 (pf_sb pf + co)) s6 s7 s8
s9 s10 (Z_to_bv 64 PE_JTAB) t3 t4 t5 t6)
F (Z_to_bv 64 pc) fc None m (seg_rom segs).

#[using="Type"] Lemma le1_sxb : forall b : byte, le1 (sxb b) = [b].
Proof.
intros b. unfold le1, sxb. cbn [Z_to_le_bytes]. f_equal. apply bv_eq.
pose proof (bv_unsigned_in_range 8 b) as R. unfold bv_modulus in R. change (2 ^ Z.of_N 8)%Z with 256%Z in R.
rewrite !Z_to_bv_unsigned. unfold bv_signed, bv_swrap, bv_wrap.
change (bv_half_modulus 8) with 128%Z. change (bv_modulus 8) with 256%Z. change (bv_modulus 64) with 18446744073709551616%Z.
Z.div_mod_to_equations. nia.
Qed.

#[using="Type"] Lemma rw_cells_bytes_at' : forall segs m a cs, rw_cells segs m a cs -> bytes_at segs m a (cells_bytes cs).
Proof. intros segs m a cs [[Hwf HB] _]. exact HB. Qed.

#[using="Type"] Lemma tok_flags_byte_g : forall mxd fl m tk pb d q x,
rw_cells rsegs m tk (tok_cells_g mxd fl pb d q x) ->
ov_read_bytes rsegs m (Z_to_bv 64 (tk + 64)) 1 = Some [Z_to_bv 8 fl].
Proof.
intros mxd fl m tk pb d q x H.
pose proof (bytes_at_read rsegs m tk _ 64 1 (rw_cells_bytes_at' _ _ _ _ H) ltac:(lia)) as R.
unfold tok_cells_g in R. cbn [cells_bytes cbytes app length le8 le4 word_to_le_bytes Z_to_le_bytes Z.to_nat Pos.to_nat Pos.iter_op Nat.add skipn firstn repeat] in R.
specialize (R ltac:(cbn; lia)). change (Z.to_nat 64) with 64%nat in R. cbn [skipn firstn] in R. etransitivity; [exact R|].
f_equal. f_equal. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. symmetry.
apply Znumtheory.Zmod_div_mod; [reflexivity | reflexivity | exists (2^56); reflexivity].
Qed.

#[using="Type"] Lemma payload_byte : forall m sb payload co c,
bytes_at rsegs m sb payload -> nth_error payload (Z.to_nat co) = Some c -> 0 <= co ->
ov_read_bytes rsegs m (Z_to_bv 64 (sb + co)) 1 = Some [c].
Proof.
intros m sb payload co c B Hn Hco.
pose proof (nth_error_Some_length Hn) as L.
pose proof (bytes_at_read rsegs m sb payload co 1 B Hco ltac:(lia)) as R.
replace (firstn 1 (skipn (Z.to_nat co) payload)) with [c] in R; [exact R|].
pose proof (@nth_error_split _ payload (Z.to_nat co) c Hn) as (l1 & l2 & E & Hl1). rewrite E at 1.
rewrite <- Hl1, skipn_app, skipn_all, Nat.sub_diag. reflexivity.
Qed.

#[using="Type"] Lemma peek_cases : forall pf payload co (c : byte),
LENR_OK pf -> CSTR_OK pf payload -> 0 <= pf_lenr pf < 2^64 -> 0 <= co < pf_len pf -> pf_len pf < 2^26 ->
nth_error payload (Z.to_nat co) = Some c -> bv_unsigned c <> 0 ->
(pf_lenr pf = pf_len pf /\ co + 1 = pf_len pf) \/ (co + 1 <> pf_lenr pf /\ co + 1 < pf_len pf).
Proof.
intros pf payload co c LR CS RR Hco L26 Hc Hnz.
destruct LR as [E | [E L1]].
- destruct (Z.eq_dec (co + 1) (pf_len pf)); [left; lia | right; lia].
- right. split; [unfold LENW_C in E; lia|].
destruct CS as [E2 | LAST]; [unfold LENW_C in E; lia|].
destruct (Z.eq_dec (co + 1) (pf_len pf)); [| lia].
exfalso. apply Hnz. replace (Z.to_nat co) with (Z.to_nat (pf_len pf - 1)) in Hc by lia.
rewrite LAST in Hc. injection Hc as <-. reflexivity.
Qed.

#[using="Type"] Lemma loop_cases : forall pf co,
LENR_OK pf -> 0 <= pf_lenr pf < 2^64 -> 0 <= co <= pf_len pf -> pf_len pf < 2^26 ->
(pf_lenr pf <> pf_len pf -> co < pf_len pf) ->
(pf_lenr pf = pf_len pf /\ co = pf_len pf) \/ (co <> pf_lenr pf /\ co < pf_len pf).
Proof.
intros pf co LR RR Hco L26 CLT.
destruct LR as [E | [E L1]].
- destruct (Z.eq_dec co (pf_len pf)); [left; lia | right; lia].
- right. assert (co < pf_len pf) by (apply CLT; unfold LENW_C in E; lia). split; [unfold LENW_C in E; lia | lia].
Qed.

Definition pe_jt (st : Z) : Z :=
match st with
| 0 => 0x22398 | 1 => 0x2247c | 2 => 0x22248 | 3 => 0x2230c | 4 => 0x2345c | 5 => 0x231f0 | 6 => 0x230f4
| 7 => 0x2335c | 8 => 0x233c0 | 9 => 0x23478 | 10 => 0x23270 | 11 => 0x22280 | 12 => 0x221bc | 13 => 0x22130
| 14 => 0x21edc | 15 => 0x21e88 | 16 => 0x220b8 | 17 => 0x23520 | 18 => 0x22f94 | 19 => 0x23160 | 20 => 0x2350c
| 21 => 0x21ec4 | 22 => 0x224d0 | 23 => 0x234f0 | 24 => 0x21e88 | 25 => 0x22f94 | 26 => 0x225a4
| _ => 0
end.

Definition pe_jtab := Eval vm_compute in match image_bytes rsegs 0x134c0 108 with Some bs => bs | None => [] end.
#[using="Type"] Lemma pe_jtab_ro : forall m, mem_inv rsegs m -> ro_cells rsegs m 0x134c0 [CB 108 pe_jtab].
Proof.
intros m MI. change 108%nat with (length pe_jtab).
apply ro_cells_image; [exact MI | vm_compute; reflexivity | lia | ].
change (Z.of_nat (length pe_jtab)) with 108%Z. lia.
Qed.

#[using="Type"] Lemma map_lupd_same : forall {A B} (f : A -> B) (l : list A) i x y,
nth_error l i = Some y -> f x = f y -> map f (lupd l i x) = map f l.
Proof.
induction l as [|h t IH]; intros [|i] x y H E; cbn in *; try discriminate.
- injection H as ->. cbn. f_equal. exact E.
- f_equal. eapply IH; eauto.
Qed.

#[using="Type"] Lemma tstack_pres_g : forall L LB SP m m' q levels {mxd : Z},
heap_pres L LB SP m m' -> In (q, 32 * mxd) LB -> length levels = Z.to_nat mxd ->
tstack (hl_segs L) m q levels -> tstack (hl_segs L) m' q levels.
Proof.
intros L LB SP m m' q levels mxd HPR Hin LEN TSK j l Hl.
pose proof (nth_error_Some_length Hl) as Hj.
eapply (heap_pres_rw_cells L); [exact HPR | exact (TSK j l Hl) |].
eapply client_range_block; [exact Hin | lia | rewrite srec_cells_size; cbn [Z.of_nat]; lia].
Qed.

#[using="Type"] Lemma tstack_presx_g : forall L X LB SP m m' q levels {mxd : Z},
heap_presx L X LB SP m m' -> In (q, 32 * mxd) LB -> length levels = Z.to_nat mxd ->
tstack (hl_segs L) m q levels -> tstack (hl_segs L) m' q levels.
Proof.
intros L X LB SP m m' q levels mxd HPR Hin LEN TSK j l Hl.
pose proof (nth_error_Some_length Hl) as Hj.
eapply (heap_presx_rw_cells L); [exact HPR | exact (TSK j l Hl) |].
eapply client_rangex_block; [exact Hin | lia | rewrite srec_cells_size; cbn [Z.of_nat]; lia].
Qed.

#[using="Type"] Lemma tstack_pres' : forall L LB SP m m' q levels,
heap_pres L LB SP m m' -> In (q, 1024) LB -> length levels = 32%nat ->
tstack (hl_segs L) m q levels -> tstack (hl_segs L) m' q levels.
Proof. intros L LB SP m m' q levels HPR Hin LEN TSK. eapply (@tstack_pres_g L LB SP m m' q levels 32); eauto. Qed.

#[using="Type"] Lemma pe_frame_cbyte : forall m SPF obj cb j1 j2 utf sv,
pe_frame rsegs m SPF obj cb j1 j2 utf sv -> bytes_at rsegs m (SPF + 31) [cb].
Proof.
intros m SPF obj cb j1 j2 utf sv H. unfold pe_frame in H.
pose proof H as [[Hwf _] _]. cbn in Hwf. destruct Hwf as (_ & L1 & _ & L2 & _).
change ([C8 (Z_to_bv 64 obj); CB 16 j1; C4 (nbw j2); CB 3 (skipn 4 j2); C1 cb; CB 8 utf;
C8 (pe_s11 sv); C8 (pe_s10 sv); C8 (pe_s9 sv); C8 (pe_s8 sv); C8 (pe_s7 sv); C8 (pe_s6 sv);
C8 (pe_s5 sv); C8 (pe_s4 sv); C8 (pe_s3 sv); C8 (pe_s2 sv); C8 (pe_s1 sv); C8 (pe_s0 sv); C8 (pe_ra sv)])
with ([C8 (Z_to_bv 64 obj); CB 16 j1; C4 (nbw j2); CB 3 (skipn 4 j2)] ++ ([C1 cb] ++ [CB 8 utf;
C8 (pe_s11 sv); C8 (pe_s10 sv); C8 (pe_s9 sv); C8 (pe_s8 sv); C8 (pe_s7 sv); C8 (pe_s6 sv);
C8 (pe_s5 sv); C8 (pe_s4 sv); C8 (pe_s3 sv); C8 (pe_s2 sv); C8 (pe_s1 sv); C8 (pe_s0 sv); C8 (pe_ra sv)])) in H.
apply (proj1 (rw_cells_app rsegs _ _ _ _)) in H as [_ H]. apply (proj1 (rw_cells_app rsegs _ _ _ _)) in H as [H _].
cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in H.
destruct H as [[_ HB] _]. exact HB.
Qed.

Section Inv.
Variable HIx : heap_iface S4L.

Definition pe_blocks (pf : pe_fix) (q : Z) (LB0 : list blk) (ts : tstate) : list blk :=
tstate_blocks ts ++ (pf_tk pf, 72) :: (q, 32 * pf_mxd pf) :: LB0.

Definition PE_CORE (pf : pe_fix) (q : Z) (m : word -> option byte) (ts : tstate)
(cb : byte) (j1 j2 utf : list byte) (sv : pe_saved) : Prop :=
length (t_levels ts) = Z.to_nat (pf_mxd pf) /\ (t_depth ts < Z.to_nat (pf_mxd pf))%nat /\
0 <= t_co ts <= pf_len pf /\ ts_choff (t_x ts) = Z_to_bv 64 (t_co ts) /\
rw_cells rsegs m (pf_tk pf) (tok_cells_g (pf_mxd pf) (pf_fl pf) (t_pb ts) (Z.of_nat (t_depth ts)) q (t_x ts)) /\
pbuf rsegs m (t_pbs ts) (t_pb ts) /\ t_pb ts <> 0 /\
tstack rsegs m q (t_levels ts) /\
pe_frame rsegs m (pf_spf pf) (t_obj ts) cb j1 j2 utf sv.

Definition PE_REST (pf : pe_fix) (q : Z) (LB0 : list blk) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : Model) (A : AS S4L HIx) (ts : tstate) (errv : word) : Prop :=
HEAP S4L HIx A (pe_blocks pf q LB0 ts) m md /\
(forall i l, nth_error (t_levels ts) i = Some l -> lvl_cur rsegs S4F m (t_depth ts) i l) /\
(if zin (cur_st ts) [ST_array_add; ST_ovadd] then jopt rsegs S4F (t_objs ts) m (t_objbs ts) (t_obj ts) else t_objbs ts = []) /\
stk rsegs m lo (pf_spf pf) /\
rw_cells rsegs m (0x77c00 - 164) [C4 errv] /\
bytes_at rsegs m (pf_sb pf) payload /\ Z.of_nat (length payload) = pf_len pf /\
(pf_len pf = 0 \/ payload_loc pf LB0) /\
heap_presx S4L s4_volatile LB0 (pf_spf pf + PE_FRAME) me m /\
model_vm_only (pf_md pf) md /\
jc_glob_P m.

Definition PE_INV (pf : pe_fix) (q : Z) (LB0 : list blk) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : Model) (A : AS S4L HIx) (ts : tstate)
(cb : byte) (j1 j2 utf : list byte) (sv : pe_saved) (errv : word) : Prop :=
PE_CORE pf q m ts cb j1 j2 utf sv /\ PE_REST pf q LB0 payload me lo m md A ts errv.

Definition PE_STATIC (pf : pe_fix) (lo : Z) : Prop :=
alloc_ceiling <= lo /\ lo <= pf_spf pf - 12288  /\
pf_spf pf mod 16 = 0 /\ pf_spf pf + PE_FRAME <= hi_top S4L HIx /\ 0 <= pf_spf pf < 2^62 /\
0 <= pf_len pf < 2^26 /\ 0 <= pf_sb pf /\ pf_sb pf + pf_len pf < 2^63

/\ (0 <= pf_lenr pf < 2^64 /\ (1 <= pf_mxd pf <= 32 /\ 0 <= pf_fl pf < 2^32) /\ True ) /\ LENR_OK pf.

#[using="Type"] Lemma PE_STATIC_mxd : forall pf lo, PE_STATIC pf lo -> 1 <= pf_mxd pf <= 32 /\ 0 <= pf_fl pf < 2^32.
Proof. intros pf lo H. exact (proj1 (proj2 (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 H))))))))))). Qed.

Definition ts_set_co (ts : tstate) (co : Z) : tstate :=
TST (t_depth ts) (t_levels ts) co (t_pb ts) (t_pbs ts)
(TS (ts_isd (t_x ts)) (ts_stpos (t_x ts)) (Z_to_bv 64 co) (ts_err (t_x ts)) (ts_ucs (t_x ts)) (ts_high (t_x ts)) (ts_quote (t_x ts)))
(t_obj ts) (t_objs ts) (t_objbs ts).

Definition pe_private (pf : pe_fix) (q : Z) (pbs : list blk) (iv : Z * Z) : Prop :=
(pf_tk pf <= fst iv /\ snd iv <= pf_tk pf + 72) \/
(q <= fst iv /\ snd iv <= q + 32 * pf_mxd pf) \/
(exists a n, In (a, n) pbs /\ a <= fst iv /\ snd iv <= a + n) \/
(pf_spf pf <= fst iv /\ snd iv <= pf_spf pf + PE_FRAME).

#[using="Type"] Lemma nodup_app_ne : forall (X Y : list blk) a n b k,
List.NoDup (map blk_addr (X ++ Y)) -> In (a, n) X -> In (b, k) Y -> a <> b.
Proof.
intros X Y a n b k ND HX HY ->. exact (nodup_prefix_suffix X Y b n k ND HX HY).
Qed.

#[using="Type"] Lemma NoDup_app_in2 : forall (l1 l2 : list Z) x, List.NoDup (l1 ++ l2) -> In x l1 -> In x l2 -> False.
Proof.
induction l1 as [|y l1 IH]; intros l2 x ND H1 H2; [destruct H1|].
cbn in ND. apply List.NoDup_cons_iff in ND as [Hni ND].
destruct H1 as [->|H1]; [apply Hni; apply in_or_app; right; exact H2 | exact (IH _ _ ND H1 H2)].
Qed.

#[using="Type"] Lemma nd_pbs_ne : forall (pbs objbs C rest : list blk) b k a n,
List.NoDup (map blk_addr ((pbs ++ objbs ++ C) ++ rest)) -> In (b, k) pbs -> In (a, n) (objbs ++ C) -> a <> b.
Proof.
intros pbs objbs C rest b k a n ND Hb Ha ->.
rewrite <- app_assoc, map_app in ND.
eapply (NoDup_app_in2 _ _ b ND).
- exact (in_map blk_addr _ _ Hb).
- rewrite map_app. apply in_or_app. left. exact (in_map blk_addr _ _ Ha).
Qed.

#[using="Type"] Lemma private_disjoint : forall pf q LB0 ts A m md lo a n W,
PE_STATIC pf lo ->
HEAP S4L HIx A (pe_blocks pf q LB0 ts) m md ->
In (a, n) (pe_blocks pf q LB0 ts) -> a <> pf_tk pf -> a <> q -> (forall b k, In (b, k) (t_pbs ts) -> a <> b) ->
Forall (pe_private pf q (t_pbs ts)) W ->
disjoint_from W a n.
Proof.
intros pf q LB0 ts A m md lo a n W STC HP Hin Htk Hq Hpb HW.
destruct STC as (LO & LOS & _).
pose proof (heap_blk S4L HIx _ _ _ _ a n HP Hin) as (Hn & _ & _ & Hhi & _). unfold alloc_ceiling, sp_window_lo, stack_max_size in Hhi, LO.
assert (INtk : In (pf_tk pf, 72) (pe_blocks pf q LB0 ts)) by (unfold pe_blocks; apply in_or_app; right; left; reflexivity).
assert (INq : In (q, 32 * pf_mxd pf) (pe_blocks pf q LB0 ts)) by (unfold pe_blocks; apply in_or_app; right; right; left; reflexivity).
induction W as [|[lo' hi'] W IH]; [exact I|]. apply Forall_cons_iff in HW as [H1 HW]. cbn [disjoint_from]. split; [| apply IH; exact HW].
unfold pe_private in H1. cbn [fst snd] in H1. destruct H1 as [H1 | [H1 | [(b & k & Hb & H1) | H1]]].
- pose proof (heap_blk_disjoint S4L HIx _ _ _ _ a n _ _ HP Hin INtk Htk). lia.
- pose proof (heap_blk_disjoint S4L HIx _ _ _ _ a n _ _ HP Hin INq Hq). lia.
- assert (INb : In (b, k) (pe_blocks pf q LB0 ts)) by (unfold pe_blocks, tstate_blocks; apply in_or_app; left; apply in_or_app; left; exact Hb).
pose proof (heap_blk_disjoint S4L HIx _ _ _ _ a n _ _ HP Hin INb (Hpb b k Hb)). lia.
- lia.
Qed.

Definition payload_safe (pf : pe_fix) (LB0 LBall : list blk) (iv : Z * Z) : Prop :=
(alloc_ceiling <= fst iv /\ snd iv <= pf_spf pf + PE_FRAME)
\/ (exists a n, In (a, n) LBall /\ (forall k, ~ In (a, k) LB0) /\ a <= fst iv /\ snd iv <= a + n)
\/ (hl_img_lo S4L <= fst iv /\ snd iv <= hl_img_hi S4L).

#[using="Type"] Lemma payload_disjoint : forall pf LB0 LBall A m md lo W,
PE_STATIC pf lo -> HEAP S4L HIx A LBall m md -> incl LB0 LBall -> payload_loc pf LB0 ->
Forall (payload_safe pf LB0 LBall) W -> disjoint_from W (pf_sb pf) (pf_len pf).
Proof.
intros pf LB0 LBall A m md lo W STC HP Hincl PL HW.
pose proof STC as (LO & LOS & SPA & HT & SP0 & LEN & SB0 & SBL). unfold alloc_ceiling, sp_window_lo, stack_max_size in LO.
unfold payload_loc in PL. unfold PE_FRAME in *.
induction W as [|[lo' hi'] W IH]; [exact I|]. apply Forall_cons_iff in HW as [H1 HW].
cbn [disjoint_from fst snd] in *. split; [| apply IH; exact HW].
unfold payload_safe in H1. cbn [fst snd hl_img_lo hl_img_hi S4L] in H1. unfold PE_FRAME, alloc_ceiling, sp_window_lo, stack_max_size in H1.
destruct PL as [STKM | (b & Hb & Hb1 & Hb2)].
- destruct H1 as [H1 | [(a & n & Ha & Hnot & H1) | H1]].
+ lia.
+ pose proof (heap_blk S4L HIx _ _ _ _ _ _ HP Ha) as (_ & _ & _ & Hhi & _). unfold alloc_ceiling, sp_window_lo, stack_max_size in Hhi. lia.
+ lia.
- destruct b as [b0 k]. cbn [blk_addr blk_size fst snd] in Hb1, Hb2. pose proof (Hincl _ Hb) as HbL.
pose proof (heap_blk S4L HIx _ _ _ _ _ _ HP HbL) as (_ & _ & _ & Hbhi & _). unfold alloc_ceiling, sp_window_lo, stack_max_size in Hbhi.
destruct H1 as [H1 | [(a & n & Ha & Hnot & H1) | H1]].
+ lia.
+ assert (Hne : a <> b0) by (intros ->; exact (Hnot k Hb)).
pose proof (heap_blk_disjoint S4L HIx _ _ _ _ _ _ _ _ HP Ha HbL Hne). lia.
+ pose proof (heap_blk_img S4L HIx _ _ _ _ _ _ HP HbL) as Hbi. cbn [hl_img_lo hl_img_hi S4L] in Hbi. lia.
Qed.

#[using="Type"] Lemma payload_transport : forall pf LB0 LBall A m m' md lo W payload,
PE_STATIC pf lo -> HEAP S4L HIx A LBall m md -> incl LB0 LBall ->
bytes_at rsegs m (pf_sb pf) payload -> Z.of_nat (length payload) = pf_len pf ->
(pf_len pf = 0 \/ payload_loc pf LB0) ->
munch W m m' -> Forall (payload_safe pf LB0 LBall) W ->
bytes_at rsegs m' (pf_sb pf) payload.
Proof.
intros pf LB0 LBall A m m' md lo W payload STC HP Hincl STR PLEN SBin MU HW.
destruct SBin as [L0 | PL].
- destruct payload; [| cbn in PLEN; lia]. destruct STR as (S1 & S2 & _). split; [exact S1|]. split; [exact S2|]. intros i Hi. cbn in Hi. lia.
- eapply bytes_at_transport; [exact STR | exact MU |]. rewrite PLEN. eapply payload_disjoint; [exact STC | exact HP | exact Hincl | exact PL | exact HW].
Qed.

#[using="Type"] Lemma payload_crange : forall pf LB0 LB SP off n,
payload_loc pf LB0 -> incl LB0 LB -> SP <= pf_spf pf + PE_FRAME ->
0 <= off -> 0 <= n -> off + n <= pf_len pf ->
client_range S4L LB SP (pf_sb pf + off) n.
Proof.
intros pf LB0 LB SP off n [STKM | (b & Hb & Hb1 & Hb2)] Hincl HSP Hoff Hn Hle; [left; lia |].
right; right. exists b. split; [exact (Hincl _ Hb) | lia].
Qed.
#[using="Type"] Lemma payload_crangex : forall X pf LB0 LB SP off n,
payload_loc pf LB0 -> incl LB0 LB -> SP <= pf_spf pf + PE_FRAME ->
0 <= off -> 0 <= n -> off + n <= pf_len pf ->
client_rangex S4L X LB SP (pf_sb pf + off) n.
Proof.
intros X pf LB0 LB SP off n [STKM | (b & Hb & Hb1 & Hb2)] Hincl HSP Hoff Hn Hle; [left; lia |].
right; right. exists b. split; [exact (Hincl _ Hb) | lia].
Qed.

#[using="Type"] Lemma payload_pres : forall pf LB0 LBc SP m m' payload,
heap_pres S4L LBc SP m m' -> incl LB0 LBc -> SP <= pf_spf pf + PE_FRAME ->
bytes_at rsegs m (pf_sb pf) payload -> Z.of_nat (length payload) = pf_len pf ->
(pf_len pf = 0 \/ payload_loc pf LB0) ->
bytes_at rsegs m' (pf_sb pf) payload.
Proof.
intros pf LB0 LBc SP m m' payload HPR Hincl HSP STR PLEN [L0 | PL].
- destruct payload; [| cbn in PLEN; lia]. destruct STR as (S1 & S2 & _). split; [exact S1|]. split; [exact S2|]. intros i Hi. cbn in Hi. lia.
- eapply (heap_pres_bytes_at S4L); [exact HPR | exact STR |]. rewrite PLEN. replace (pf_sb pf) with (pf_sb pf + 0) by lia.
eapply payload_crange; [exact PL | exact Hincl | exact HSP | lia | lia | lia].
Qed.
#[using="Type"] Lemma payload_presx : forall X pf LB0 LBc SP m m' payload,
heap_presx S4L X LBc SP m m' -> incl LB0 LBc -> SP <= pf_spf pf + PE_FRAME ->
bytes_at rsegs m (pf_sb pf) payload -> Z.of_nat (length payload) = pf_len pf ->
(pf_len pf = 0 \/ payload_loc pf LB0) ->
bytes_at rsegs m' (pf_sb pf) payload.
Proof.
intros X pf LB0 LBc SP m m' payload HPR Hincl HSP STR PLEN [L0 | PL].
- destruct payload; [| cbn in PLEN; lia]. destruct STR as (S1 & S2 & _). split; [exact S1|]. split; [exact S2|]. intros i Hi. cbn in Hi. lia.
- eapply (heap_presx_bytes_at S4L); [exact HPR | exact STR |]. rewrite PLEN. replace (pf_sb pf) with (pf_sb pf + 0) by lia.
eapply payload_crangex; [exact PL | exact Hincl | exact HSP | lia | lia | lia].
Qed.

#[using="Type"] Lemma private_in_blocks : forall pf q LB0 ts a n,
In (a, n) (tstate_blocks ts ++ [(pf_tk pf, 72); (q, 32 * pf_mxd pf)]) -> In (a, n) (pe_blocks pf q LB0 ts).
Proof.
intros pf q LB0 ts a n Hin. unfold pe_blocks. apply in_app_or in Hin.
destruct Hin as [Hin | [E | [E | []]]]; [| injection E; intros <- <- | injection E; intros <- <-]; apply in_or_app;
[left; exact Hin | right; left; reflexivity | right; right; left; reflexivity].
Qed.
#[using="Type"] Lemma private_not_LB0 : forall pf q LB0 ts A m md a n k,
HEAP S4L HIx A (pe_blocks pf q LB0 ts) m md ->
In (a, n) (tstate_blocks ts ++ [(pf_tk pf, 72); (q, 32 * pf_mxd pf)]) -> ~ In (a, k) LB0.
Proof.
intros pf q LB0 ts A m md a n k HP Hin Hk. pose proof (heap_blk_nodup S4L HIx _ _ _ _ HP) as ND.
assert (ND' : List.NoDup (map blk_addr ((tstate_blocks ts ++ [(pf_tk pf, 72); (q, 32 * pf_mxd pf)]) ++ LB0))).
{ unfold pe_blocks in ND. rewrite <- app_assoc. cbn [app] in *. exact ND. }
exact (nodup_app_ne _ _ _ _ _ _ ND' Hin Hk eq_refl).
Qed.

#[using="Type"] Lemma payload_sep : forall pf q LB0 ts A m md lo a n,
PE_STATIC pf lo -> HEAP S4L HIx A (pe_blocks pf q LB0 ts) m md -> payload_loc pf LB0 ->
In (a, n) (tstate_blocks ts ++ [(pf_tk pf, 72); (q, 32 * pf_mxd pf)]) ->
pf_sb pf + pf_len pf <= a \/ a + n <= pf_sb pf.
Proof.
intros pf q LB0 ts A m md lo a n STC HP PL Hin.
pose proof (payload_disjoint pf LB0 _ _ _ _ _ [(a, a + n)] STC HP ltac:(intros x Hx; unfold pe_blocks; apply in_or_app; right; right; right; exact Hx) PL) as D.
cbn [disjoint_from] in D.
destruct (D ltac:(constructor; [| constructor]; right; left; exists a, n; cbn [fst snd]; split;
[exact (private_in_blocks _ _ _ _ _ _ Hin) | split; [intros k; exact (private_not_LB0 _ _ _ _ _ _ _ _ _ k HP Hin) | lia]])) as [D1 _]. lia.
Qed.

#[using="Type"] Lemma payload_private : forall pf q LB0 ts A m m' md lo W payload,
PE_STATIC pf lo -> HEAP S4L HIx A (pe_blocks pf q LB0 ts) m md ->
bytes_at rsegs m (pf_sb pf) payload -> Z.of_nat (length payload) = pf_len pf ->
(pf_len pf = 0 \/ payload_loc pf LB0) ->
munch W m m' -> Forall (pe_private pf q (t_pbs ts)) W ->
bytes_at rsegs m' (pf_sb pf) payload.
Proof.
intros pf q LB0 ts A m m' md lo W payload STC HP STR PLEN SBin MU HW.
pose proof STC as (LO & LOS & _).
eapply payload_transport; [exact STC | exact HP | intros x Hx; unfold pe_blocks; apply in_or_app; right; right; right; exact Hx
| exact STR | exact PLEN | exact SBin | exact MU |].
eapply Forall_impl; [| exact HW]. intros [lo' hi'] Hiv. unfold pe_private in Hiv. unfold payload_safe. cbn [fst snd] in *.
destruct Hiv as [H1 | [H1 | [(b & k & Hb & H1) | H1]]].
- right; left. exists (pf_tk pf), 72.
assert (Hin : In (pf_tk pf, 72) (tstate_blocks ts ++ [(pf_tk pf, 72); (q, 32 * pf_mxd pf)])) by (apply in_or_app; right; left; reflexivity).
split; [exact (private_in_blocks _ _ _ _ _ _ Hin) | split; [intros kk; exact (private_not_LB0 _ _ _ _ _ _ _ _ _ kk HP Hin) | lia]].
- right; left. exists q, (32 * pf_mxd pf).
assert (Hin : In (q, 32 * pf_mxd pf) (tstate_blocks ts ++ [(pf_tk pf, 72); (q, 32 * pf_mxd pf)])) by (apply in_or_app; right; right; left; reflexivity).
split; [exact (private_in_blocks _ _ _ _ _ _ Hin) | split; [intros kk; exact (private_not_LB0 _ _ _ _ _ _ _ _ _ kk HP Hin) | lia]].
- right; left. exists b, k.
assert (Hin : In (b, k) (tstate_blocks ts ++ [(pf_tk pf, 72); (q, 32 * pf_mxd pf)])) by (apply in_or_app; left; unfold tstate_blocks; apply in_or_app; left; exact Hb).
split; [exact (private_in_blocks _ _ _ _ _ _ Hin) | split; [intros kk; exact (private_not_LB0 _ _ _ _ _ _ _ _ _ kk HP Hin) | lia]].
- left. unfold alloc_ceiling, sp_window_lo, stack_max_size in *. lia.
Qed.

#[using="Type"] Lemma PE_REST_private_write : forall pf q LB0 payload me lo m m' md A ts errv W,
PE_STATIC pf lo ->
PE_REST pf q LB0 payload me lo m md A ts errv ->
munch W m m' -> wmono rsegs m m' -> mem_inv rsegs m' ->
Forall (pe_private pf q (t_pbs ts)) W ->
PE_REST pf q LB0 payload me lo m' md A ts errv.
Proof.
intros pf q LB0 payload me lo m m' md A ts errv W STC (HP & LV & OBJ & ST & ERR & STR & PLEN & SBin & HPR & MDV & JCG) MU WM MI HW.
pose proof STC as (LO & LOS & SPA & HT & SP0 & LEN & SB0 & SBL).
pose proof (heap_blk_nodup S4L HIx _ _ _ _ HP) as ND.
assert (INtk : In (pf_tk pf, 72) (pe_blocks pf q LB0 ts)) by (unfold pe_blocks; apply in_or_app; right; left; reflexivity).
assert (INq : In (q, 32 * pf_mxd pf) (pe_blocks pf q LB0 ts)) by (unfold pe_blocks; apply in_or_app; right; right; left; reflexivity).
pose proof (heap_blk S4L HIx _ _ _ _ _ _ HP INtk) as (_ & _ & _ & Htkhi & _).
pose proof (heap_blk S4L HIx _ _ _ _ _ _ HP INq) as (_ & _ & _ & Hqhi & _).
pose proof (heap_blk_img S4L HIx _ _ _ _ _ _ HP INtk) as Himg_t. pose proof (heap_blk_img S4L HIx _ _ _ _ _ _ HP INq) as Himg_q.
cbn [hl_img_lo hl_img_hi S4L] in Himg_t, Himg_q. unfold alloc_ceiling, sp_window_lo, stack_max_size in Htkhi, Hqhi, LO.

assert (AG : agree_on rsegs (t_objbs ts ++ concat (map lvl_blocks (t_levels ts))) m m').
{ eapply agree_of_munch; [exact MU | exact WM |]. intros a n Hin.
assert (HinP : In (a, n) (tstate_blocks ts)) by (unfold tstate_blocks; apply in_or_app; right; exact Hin).
assert (HinL : In (a, n) (pe_blocks pf q LB0 ts)) by (unfold pe_blocks; apply in_or_app; left; exact HinP).
unfold pe_blocks in ND.
eapply private_disjoint; [exact STC | exact HP | exact HinL | | | | exact HW].
- eapply (nodup_app_ne _ _ _ _ _ _ ND HinP). left; reflexivity.
- eapply (nodup_app_ne _ _ _ _ _ _ ND HinP). right; left; reflexivity.
- intros b k Hb. unfold tstate_blocks in ND. exact (nd_pbs_ne _ _ _ _ _ _ _ _ ND Hb Hin). }
split; [| split; [| split; [| split; [| split; [| split; [| split; [| split; [| split; [| split; [exact MDV | eapply jc_glob_P_outside; [exact JCG | exact MU | exact WM |];
eapply Forall_impl; [| exact HW]; intros [lo' hi'] Hiv; unfold pe_private in Hiv; cbn [fst snd] in *;
destruct Hiv as [H1 | [H1 | [(b & k & Hb & H1) | H1]]];
[ lia | lia
| pose proof (heap_blk_img S4L HIx _ _ _ _ b k HP ltac:(unfold pe_blocks, tstate_blocks; apply in_or_app; left; apply in_or_app; left; exact Hb)) as Hbi;
cbn [hl_img_lo hl_img_hi S4L] in Hbi; lia
| unfold PE_FRAME in H1; lia ]]]]]]]]]]].
- eapply (heap_frame S4L HIx); [exact HP | | exact WM | exact MI].
eapply (frame_writes_ok S4L HIx _ _ _ _ _ _ HP MU).
eapply Forall_impl; [| exact HW]. intros [lo' hi'] Hiv. unfold pe_private in Hiv. cbn [fst snd] in *.
destruct Hiv as [H1 | [H1 | [(b & k & Hb & H1) | H1]]].
+ right; left. exists (pf_tk pf), 72. split; [exact INtk | lia].
+ right; left. exists q, (32 * pf_mxd pf). split; [exact INq | lia].
+ right; left. exists b, k. split; [| lia]. unfold pe_blocks, tstate_blocks. apply in_or_app; left; apply in_or_app; left; exact Hb.
+ left. unfold PE_FRAME, alloc_ceiling, sp_window_lo, stack_max_size in *. lia.
- intros i l Hl. eapply (lvl_cur_agree rsegs S4F); [exact (LV i l Hl) | exact AG |].
intros b Hb. apply in_or_app; right. apply in_concat. exists (lvl_blocks l). split; [| exact Hb]. apply in_map. eapply nth_error_In; exact Hl.
- destruct (zin (cur_st ts) [ST_array_add; ST_ovadd]); [| exact OBJ].
eapply (jopt_agree rsegs S4F); [exact OBJ | exact AG | intros b Hb; apply in_or_app; left; exact Hb].
- eapply (stk_transport_disjoint rsegs); [exact ST | exact MU | exact WM |].
destruct ST as (ST0 & ST1 & _).
clear - HW LOS LO ST0 ST1 Htkhi Hqhi HP. induction W as [|[lo' hi'] W IH]; [exact I|].
apply Forall_cons_iff in HW as [H1 HW]. unfold pe_private in H1. cbn [disjoint_from fst snd] in *. split; [| apply IH; exact HW].
destruct H1 as [H1 | [H1 | [(b & k & Hb & H1) | H1]]]; try lia.
assert (INb : In (b, k) (pe_blocks pf q LB0 ts)) by (unfold pe_blocks, tstate_blocks; apply in_or_app; left; apply in_or_app; left; exact Hb).
pose proof (heap_blk S4L HIx _ _ _ _ _ _ HP INb) as (_ & _ & _ & Hbhi & _). unfold alloc_ceiling, sp_window_lo, stack_max_size in Hbhi. lia.
- eapply rw_cells_transport; [exact ERR | exact MU | exact WM |]. cbn [cells_size csize Z.of_nat].
clear - HW LOS LO Himg_t Himg_q Htkhi Hqhi HP SP0. induction W as [|[lo' hi'] W IH]; [exact I|].
apply Forall_cons_iff in HW as [H1 HW]. unfold pe_private in H1. cbn [disjoint_from fst snd] in *. split; [| apply IH; exact HW].
destruct H1 as [H1 | [H1 | [(b & k & Hb & H1) | H1]]]; try lia.
assert (INb : In (b, k) (pe_blocks pf q LB0 ts)) by (unfold pe_blocks, tstate_blocks; apply in_or_app; left; apply in_or_app; left; exact Hb).
pose proof (heap_blk_img S4L HIx _ _ _ _ _ _ HP INb) as Hbi. cbn [hl_img_lo hl_img_hi S4L] in Hbi.
pose proof (heap_blk S4L HIx _ _ _ _ _ _ HP INb) as (Hk0 & _ & _ & _ & _). lia.
- eapply payload_private; [exact STC | exact HP | exact STR | exact PLEN | exact SBin | exact MU | exact HW].
- exact PLEN.
- exact SBin.
- eapply heap_presx_trans; [exact HPR|].
eapply (heap_presx_of_munch S4L s4_volatile LB0); [exact MU | exact WM |].
eapply (client_outside S4L HIx); [exact HP | intros bb Hbb; unfold pe_blocks; apply in_or_app; right; right; right; exact Hbb | unfold PE_FRAME; unfold alloc_ceiling, sp_window_lo, stack_max_size; lia |].
eapply Forall_impl; [| exact HW]. intros [lo' hi'] Hiv. unfold pe_private in Hiv. cbn [fst snd] in *.
unfold pe_blocks in ND.
destruct Hiv as [H1 | [H1 | [(b & k & Hb & H1) | H1]]].
+ right; left. exists (pf_tk pf), 72. split; [exact INtk|]. split; [| lia].
intros Hin0. rewrite map_app in ND. apply NoDup_app_remove_l in ND. cbn [map blk_addr fst] in ND. apply List.NoDup_cons_iff in ND as [Hni _]. apply Hni. right. exact (in_map blk_addr _ _ Hin0).
+ right; left. exists q, (32 * pf_mxd pf). split; [exact INq|]. split; [| lia].
intros Hin0. rewrite map_app in ND. apply NoDup_app_remove_l in ND. cbn [map blk_addr fst] in ND. apply List.NoDup_cons_iff in ND as [_ ND]. apply List.NoDup_cons_iff in ND as [Hni _]. apply Hni. exact (in_map blk_addr _ _ Hin0).
+ right; left. exists b, k. split; [unfold pe_blocks, tstate_blocks; apply in_or_app; left; apply in_or_app; left; exact Hb|]. split; [| lia].
intros Hin0. assert (HbP : In (b, k) (tstate_blocks ts)) by (unfold tstate_blocks; apply in_or_app; left; exact Hb).
exact (nodup_app_ne _ _ _ _ _ _ ND HbP ltac:(right; right; exact Hin0) eq_refl).
+ left. unfold PE_FRAME in *. unfold alloc_ceiling, sp_window_lo, stack_max_size. lia.
Qed.

Definition pe_wtf (pf : pe_fix) (iv : Z * Z) : Prop :=
(pf_tk pf <= fst iv /\ snd iv <= pf_tk pf + 72) \/ (pf_spf pf <= fst iv /\ snd iv <= pf_spf pf + PE_FRAME).

#[using="Type"] Lemma pe_wtf_private : forall pf q pbs W, Forall (pe_wtf pf) W -> Forall (pe_private pf q pbs) W.
Proof. intros pf q pbs W H. eapply Forall_impl; [| exact H]. intros iv [A|A]; [left; exact A | right; right; right; exact A]. Qed.

#[using="Type"] Lemma agree_wtf : forall pf q LB0 ts A m m' md lo W BS,
PE_STATIC pf lo -> HEAP S4L HIx A (pe_blocks pf q LB0 ts) m md ->
munch W m m' -> wmono rsegs m m' -> Forall (pe_wtf pf) W ->
(forall a n, In (a, n) BS -> In (a, n) (pe_blocks pf q LB0 ts) /\ a <> pf_tk pf) ->
agree_on rsegs BS m m'.
Proof.
intros pf q LB0 ts A m m' md lo W BS STC HP MU WM HW HBS.
destruct STC as (LO & LOS & _). unfold alloc_ceiling, sp_window_lo, stack_max_size in LO.
assert (INtk : In (pf_tk pf, 72) (pe_blocks pf q LB0 ts)) by (unfold pe_blocks; apply in_or_app; right; left; reflexivity).
eapply agree_of_munch; [exact MU | exact WM |]. intros a n Hin. destruct (HBS a n Hin) as [HinL Hne].
pose proof (heap_blk S4L HIx _ _ _ _ a n HP HinL) as (_ & _ & _ & Hhi & _). unfold alloc_ceiling, sp_window_lo, stack_max_size in Hhi.
pose proof (heap_blk_disjoint S4L HIx _ _ _ _ a n _ _ HP HinL INtk Hne) as Hd.
clear - HW Hd Hhi LO LOS. induction W as [|[lo' hi'] W IH]; [exact I|].
apply Forall_cons_iff in HW as [H1 HW]. unfold pe_wtf in H1. cbn [disjoint_from fst snd] in *. split; [| apply IH; exact HW].
unfold PE_FRAME in H1. lia.
Qed.

#[using="Type"] Lemma tstack_wtf : forall pf q LB0 ts A m m' md lo W,
PE_STATIC pf lo -> HEAP S4L HIx A (pe_blocks pf q LB0 ts) m md ->
tstack rsegs m q (t_levels ts) -> length (t_levels ts) = Z.to_nat (pf_mxd pf) ->
munch W m m' -> wmono rsegs m m' -> Forall (pe_wtf pf) W ->
tstack rsegs m' q (t_levels ts).
Proof.
intros pf q LB0 ts A m m' md lo W STC HP TSK LEN MU WM HW.
assert (INq : In (q, 32 * pf_mxd pf) (pe_blocks pf q LB0 ts)) by (unfold pe_blocks; apply in_or_app; right; right; left; reflexivity).
assert (Hq : q <> pf_tk pf).
{ pose proof (heap_blk_nodup S4L HIx _ _ _ _ HP) as ND. unfold pe_blocks in ND. rewrite map_app in ND. apply NoDup_app_remove_l in ND.
cbn [map blk_addr fst] in ND. apply List.NoDup_cons_iff in ND as [Hni _]. intros E. apply Hni. left. exact E. }
pose proof (agree_wtf pf q LB0 ts A m m' md lo W [(q, 32 * pf_mxd pf)] STC HP MU WM HW ltac:(intros a n [E|[]]; injection E as <- <-; split; [exact INq | exact Hq])) as AG.
intros j l Hl. pose proof (nth_error_Some_length Hl) as Hj.
eapply rw_cells_agree; [exact (TSK j l Hl) | exact AG |]. exists q, (32 * pf_mxd pf). split; [left; reflexivity|]. rewrite srec_cells_size. cbn [Z.of_nat]. lia.
Qed.

#[using="Type"] Lemma pbuf_wtf : forall pf q LB0 ts A m m' md lo W,
PE_STATIC pf lo -> HEAP S4L HIx A (pe_blocks pf q LB0 ts) m md ->
pbuf rsegs m (t_pbs ts) (t_pb ts) ->
munch W m m' -> wmono rsegs m m' -> Forall (pe_wtf pf) W ->
pbuf rsegs m' (t_pbs ts) (t_pb ts).
Proof.
intros pf q LB0 ts A m m' md lo W STC HP PB MU WM HW.
eapply pbuf_agree; [exact PB | | apply incl_refl].
eapply agree_wtf; [exact STC | exact HP | exact MU | exact WM | exact HW |].
intros a n Hin. assert (HinL : In (a, n) (pe_blocks pf q LB0 ts)) by (unfold pe_blocks, tstate_blocks; apply in_or_app; left; apply in_or_app; left; exact Hin).
split; [exact HinL|].
pose proof (heap_blk_nodup S4L HIx _ _ _ _ HP) as ND. unfold pe_blocks in ND.
intros ->. refine (nodup_app_ne _ _ _ _ _ _ ND _ _ eq_refl); [unfold tstate_blocks; apply in_or_app; left; exact Hin | left; reflexivity].
Qed.

Definition pe_wtq (pf : pe_fix) (q : Z) (iv : Z * Z) : Prop :=
pe_wtf pf iv \/ (q <= fst iv /\ snd iv <= q + 32 * pf_mxd pf).

#[using="Type"] Lemma pe_wtq_private : forall pf q pbs W, Forall (pe_wtq pf q) W -> Forall (pe_private pf q pbs) W.
Proof. intros pf q pbs W H. eapply Forall_impl; [| exact H]. intros iv [[A|A]|A]; [left; exact A | right; right; right; exact A | right; left; exact A]. Qed.

#[using="Type"] Lemma agree_wtq : forall pf q LB0 ts A m m' md lo W BS,
PE_STATIC pf lo -> HEAP S4L HIx A (pe_blocks pf q LB0 ts) m md ->
munch W m m' -> wmono rsegs m m' -> Forall (pe_wtq pf q) W ->
(forall a n, In (a, n) BS -> In (a, n) (pe_blocks pf q LB0 ts) /\ a <> pf_tk pf /\ a <> q) ->
agree_on rsegs BS m m'.
Proof.
intros pf q LB0 ts A m m' md lo W BS STC HP MU WM HW HBS.
destruct STC as (LO & LOS & _). unfold alloc_ceiling, sp_window_lo, stack_max_size in LO.
assert (INtk : In (pf_tk pf, 72) (pe_blocks pf q LB0 ts)) by (unfold pe_blocks; apply in_or_app; right; left; reflexivity).
assert (INq : In (q, 32 * pf_mxd pf) (pe_blocks pf q LB0 ts)) by (unfold pe_blocks; apply in_or_app; right; right; left; reflexivity).
eapply agree_of_munch; [exact MU | exact WM |]. intros a n Hin. destruct (HBS a n Hin) as (HinL & Hne & Hnq).
pose proof (heap_blk S4L HIx _ _ _ _ a n HP HinL) as (_ & _ & _ & Hhi & _). unfold alloc_ceiling, sp_window_lo, stack_max_size in Hhi.
pose proof (heap_blk_disjoint S4L HIx _ _ _ _ a n _ _ HP HinL INtk Hne) as Hd.
pose proof (heap_blk_disjoint S4L HIx _ _ _ _ a n _ _ HP HinL INq Hnq) as Hdq.
clear - HW Hd Hdq Hhi LO LOS. induction W as [|[lo' hi'] W IH]; [exact I|].
apply Forall_cons_iff in HW as [H1 HW]. unfold pe_wtq, pe_wtf in H1. cbn [disjoint_from fst snd] in *. split; [| apply IH; exact HW].
unfold PE_FRAME in H1. lia.
Qed.

#[using="Type"] Lemma pbuf_wtq : forall pf q LB0 ts A m m' md lo W,
PE_STATIC pf lo -> HEAP S4L HIx A (pe_blocks pf q LB0 ts) m md ->
pbuf rsegs m (t_pbs ts) (t_pb ts) ->
munch W m m' -> wmono rsegs m m' -> Forall (pe_wtq pf q) W ->
pbuf rsegs m' (t_pbs ts) (t_pb ts).
Proof.
intros pf q LB0 ts A m m' md lo W STC HP PB MU WM HW.
eapply pbuf_agree; [exact PB | | apply incl_refl].
eapply agree_wtq; [exact STC | exact HP | exact MU | exact WM | exact HW |].
intros a n Hin. assert (HinL : In (a, n) (pe_blocks pf q LB0 ts)) by (unfold pe_blocks, tstate_blocks; apply in_or_app; left; apply in_or_app; left; exact Hin).
split; [exact HinL|].
pose proof (heap_blk_nodup S4L HIx _ _ _ _ HP) as ND. unfold pe_blocks in ND. split.
- intros ->. refine (nodup_app_ne _ _ _ _ _ _ ND _ _ eq_refl); [unfold tstate_blocks; apply in_or_app; left; exact Hin | left; reflexivity].
- intros ->. refine (nodup_app_ne _ _ _ _ _ _ ND _ _ eq_refl); [unfold tstate_blocks; apply in_or_app; left; exact Hin | right; left; reflexivity].
Qed.

#[using="Type"] Lemma srec_join8 : forall m a l,
rw_cells rsegs m a (srec_cells l) ->
rw_cells rsegs m a (CB 8 (le4 (Z_to_bv 64 (tl_st l)) ++ le4 (Z_to_bv 64 (tl_ss l))) :: [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 (tl_cur l)); C8 (Z_to_bv 64 (tl_name l))]).
Proof. intros m a l H. eapply rw_cells_recast; [exact H | cbn; repeat split; reflexivity | reflexivity | reflexivity]. Qed.

#[using="Type"] Lemma lvl_cur_restate : forall m depth l st' ss' c hn c' ,
lvl_cur rsegs S4F m depth depth l ->
lvl_mode (tl_st l) (tl_ss l) = Some (c, hn) ->
lvl_mode st' ss' = Some (c', hn) -> 0 <= st' <= 26 -> 0 <= ss' <= 26 ->
(c' = c \/ c' = CAny) ->
lvl_cur rsegs S4F m depth depth (TL st' ss' (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l)).
Proof.
intros m depth l st' ss' c hn c' (R1 & R2 & J & M) Hm Hm' Hst Hss Hc.
rewrite Nat.ltb_irrefl, Nat.eqb_refl in M. destruct M as (c0 & hn0 & E0 & CLS & NM).
rewrite Hm in E0. injection E0 as <- <-.
split; [exact Hst|]. split; [exact Hss|]. split; [exact J|].
cbn [tl_st tl_ss tl_cs]. rewrite Nat.ltb_irrefl, Nat.eqb_refl.
exists c', hn. split; [exact Hm'|]. split.
- destruct Hc as [-> | ->]; [exact CLS | exact I].
- destruct hn; cbn in *; exact NM.
Qed.

#[using="Type"] Lemma PE_REST_call_pb : forall pf q LB0 payload me lo m1 m2 md md2 A A2 ts errv errv2 LBc co2 pb2 pbs2 x2,
PE_STATIC pf lo ->
PE_REST pf q LB0 payload me lo m1 md A ts errv ->
model_vm_only md md2 ->
heap_pres S4L LBc (pf_spf pf) m1 m2 ->
incl (t_objbs ts ++ concat (map lvl_blocks (t_levels ts)) ++ LB0) LBc ->
let ts2 := TST (t_depth ts) (t_levels ts) co2 pb2 pbs2 x2 (t_obj ts) (t_objs ts) (t_objbs ts) in
HEAP S4L HIx A2 (pe_blocks pf q LB0 ts2) m2 md2 ->
stk rsegs m2 lo (pf_spf pf) ->
rw_cells rsegs m2 (0x77c00 - 164) [C4 errv2] ->
PE_REST pf q LB0 payload me lo m2 md2 A2 ts2 errv2.
Proof.
intros pf q LB0 payload me lo m1 m2 md md2 A A2 ts errv errv2 LBc co2 pb2 pbs2 x2 STC (HP & LV & OBJ & ST & ERR & STR & PLEN & SBin & HPR & MDV & JCG) VM12 HPRc Hincl ts2 HP2 ST2 ERR2.
assert (AG : agree_on rsegs (t_objbs ts ++ concat (map lvl_blocks (t_levels ts)) ++ LB0) m1 m2).
{ eapply (agree_of_heap_pres rsegs S4L); [exact HPRc | reflexivity | exact Hincl]. }
split; [exact HP2|]. split; [| split; [| split; [exact ST2 | split; [exact ERR2 | split; [| split; [exact PLEN | split; [exact SBin |]]]]]]].
- intros i l Hl. cbn. eapply (lvl_cur_agree rsegs S4F); [exact (LV i l Hl) | exact AG |].
intros b Hb. apply in_or_app; right. apply in_or_app; left. apply in_concat. exists (lvl_blocks l). split; [| exact Hb]. apply in_map. eapply nth_error_In; exact Hl.
- revert OBJ. unfold cur_st. cbn [t_levels t_depth t_objs t_objbs t_obj]. destruct (zin _ _); intros OBJ; [| exact OBJ].
eapply (jopt_agree rsegs S4F); [exact OBJ | exact AG | intros b Hb; apply in_or_app; left; exact Hb].
- eapply payload_pres; [exact HPRc | intros x Hx; apply Hincl; apply in_or_app; right; apply in_or_app; right; exact Hx | unfold PE_FRAME; lia | exact STR | exact PLEN | exact SBin].
- split; [| split; [eapply model_vm_only_trans; [exact MDV | exact VM12] | eapply jc_glob_P_pres; [exact HPRc | exact JCG]]].
eapply heap_presx_trans; [exact HPR|]. eapply heap_presx_weaken; [apply heap_pres_presx; exact HPRc | unfold PE_FRAME; lia | | intros a Xa; exact Xa].
intros b Hb. apply Hincl. apply in_or_app; right; apply in_or_app; right; exact Hb.
Qed.
End Inv.
End RC__1.

Ltac pe_gen f :=
rename f into fl;
try (lazymatch goal with
| S : PE_STATIC _ _ _ |- _ => let M := fresh "MXB" in pose proof (PE_STATIC_mxd _ _ _ S) as M; cbn [pf_mxd pf_fl] in M
end).
