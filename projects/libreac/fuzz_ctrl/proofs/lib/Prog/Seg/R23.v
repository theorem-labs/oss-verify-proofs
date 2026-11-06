(* Segment R23 of fuzz_ctrl LLVMFuzzerTestOneInput (plain): [0x13524, 0x13588], K13524 -> K1358c (strcmp of
   RID_7's model name with the row's name) or K13598 (has_identity_record(m) = 0). The id checks #24-#30 pass by
   RTM (b2_rtm_fw, b2_rtm_ver, b2_rtm_hid, b2_rtm_name); the row bytes are b1_row_bytes; the row's name string is
   read from the image (r23_nm_rows). libreac v1.9.0: id sp+138 -> sp+154 (its fields 140 / 141 / 158 / 160 /
   162 / 164 / 174 -> 156 / 157 / 174 / 176 / 178 / 180 / 190, table 5a), strcmp by its contract; K13598 stays at
   0x13598 (SlotInv.v), so the exit and the walk are those of v1.8: no memset here (it is S_P01's head). *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Import Contract Img0 FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells Tac.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import SlotModel SlotInv strcmp_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require RcIdentModel RcDecl RcSynth RcEmit RcPorts.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Bytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Spec Require StrFun.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.Seg Require Import Tac_slot Tac_b3 Tac_b1 Tac_b2.
Import ListNotations.
Open Scope Z_scope.

Definition z0 : byte := Z_to_bv 8 0.

(* ---- list and byte helpers ---- *)
Lemma r23_skipn_cons : forall (l : list byte) k, (k < length l)%nat -> skipn k l = nth k l z0 :: skipn (S k) l.
Proof.
  induction l as [|x l IH]; intros k Hk; cbn in Hk; [lia|].
  destruct k as [|k]; [reflexivity|]. cbn [skipn nth]. apply IH. lia.
Qed.

Lemma r23_firstn_seq : forall (l : list byte) n k, (k + n <= length l)%nat ->
  firstn n (skipn k l) = map (fun i => nth i l z0) (seq k n).
Proof.
  intros l n. induction n as [|n IH]; intros k Hk; [reflexivity|].
  rewrite (r23_skipn_cons l k) by lia. cbn [firstn seq map]. f_equal. apply IH. lia.
Qed.

Lemma r23_rdl : forall m a bs k n, bytes_at rsegs m a bs -> (k + n <= length bs)%nat ->
  ov_read_bytes rsegs m (wa (a + Z.of_nat k)) n = Some (map (fun i => nth i bs z0) (seq k n)).
Proof.
  intros m a bs k n HB H. rewrite (bytes_at_ov_read rsegs m a bs k n HB H). f_equal. apply r23_firstn_seq. exact H.
Qed.

Lemma r23_sub : forall m a bs k n, bytes_at rsegs m a bs -> (k + n <= length bs)%nat ->
  bytes_at rsegs m (a + Z.of_nat k) (firstn n (skipn k bs)).
Proof.
  intros m a bs k n (H1 & H2 & H3) Hk. unfold bytes_at. rewrite length_firstn, length_skipn.
  split; [lia|]. split; [lia|]. intros i Hi. rewrite nth_error_firstn.
  destruct (Nat.ltb_spec i n) as [_|]; [|lia]. rewrite nth_error_skipn.
  rewrite <- (H3 (k + i)%nat) by lia. f_equal. unfold wa. f_equal. lia.
Qed.

Lemma r23_eqb_refl : forall x : word, bv_eqb x x = true.
Proof. intros x. unfold bv_eqb. apply Z.eqb_refl. Qed.

Lemma r23_zxb_nz : forall b : byte, bv_unsigned b <> 0 -> bv_eqb (zxb b) (Z_to_bv 64 0) = false.
Proof.
  intros b H. unfold bv_eqb. rewrite b3_zxb_u. rewrite MState.unsigned_lit by lia. apply Z.eqb_neq. exact H.
Qed.

Lemma r23_u16 : forall a b c d : byte, bv_unsigned a + 256 * bv_unsigned b = bv_unsigned c + 256 * bv_unsigned d ->
  a = c /\ b = d.
Proof.
  intros a b c d H.
  pose proof (bv_unsigned_in_range 8 a) as Ra. pose proof (bv_unsigned_in_range 8 b) as Rb.
  pose proof (bv_unsigned_in_range 8 c) as Rc. pose proof (bv_unsigned_in_range 8 d) as Rd.
  unfold bv_modulus in *. change (2 ^ Z.of_N 8) with 256 in *.
  split; apply bv_eq; lia.
Qed.

Lemma r23_br : forall b : byte, 0 <= bv_unsigned b < 256.
Proof.
  intros b. pose proof (bv_unsigned_in_range 8 b) as H. unfold bv_modulus in H.
  change (2 ^ Z.of_N 8) with 256 in H. exact H.
Qed.

(* The range of every byte value in the goal. *)
Ltac r23_rng := repeat match goal with
  | |- context [bv_unsigned ?b] =>
      lazymatch goal with
      | _ : 0 <= bv_unsigned b < 256 |- _ => fail
      | _ => pose proof (r23_br b)
      end
  end.

(* Multi-byte loads: the bytes as the little-endian image of one word, the form Step's load_post folds. *)
Lemma r23_l2 : forall b0 b1 : byte, [b0; b1] = le2 (Z_to_bv 64 (bv_unsigned b0 + 256 * bv_unsigned b1)).
Proof.
  intros b0 b1. pose proof (r23_br b0). pose proof (r23_br b1).
  rewrite <- le2_lit by lia.
  pose proof (StrFun.Z_to_le_bytes_to_Z [b0; b1]) as E.
  rewrite Bytes.bytes_le_to_Z_le_val in E. cbn [length map Bytes.le_val] in E.
  rewrite <- E at 1. f_equal. lia.
Qed.

Lemma r23_l4 : forall b0 b1 b2 b3 : byte, [b0; b1; b2; b3] = le4 (Z_to_bv 64
  (bv_unsigned b0 + 256 * bv_unsigned b1 + 65536 * bv_unsigned b2 + 16777216 * bv_unsigned b3)).
Proof.
  intros b0 b1 b2 b3. pose proof (r23_br b0). pose proof (r23_br b1). pose proof (r23_br b2). pose proof (r23_br b3).
  rewrite <- le4_lit by lia.
  pose proof (StrFun.Z_to_le_bytes_to_Z [b0; b1; b2; b3]) as E.
  rewrite Bytes.bytes_le_to_Z_le_val in E. cbn [length map Bytes.le_val] in E.
  rewrite <- E at 1. f_equal. lia.
Qed.

(* Field readers stated over a variable list, so that rewriting never asks the kernel to unfold a model term. *)
Lemma r23_has_fw : forall idb, RcIdentModel.has_fw idb = bv_unsigned (nth 2 idb z0).
Proof. intros idb. unfold RcIdentModel.has_fw, RcIdentModel.bz, RcIdentModel.nthb, RcIdentModel.OFF_HAS_FW. reflexivity. Qed.
Lemma r23_has_ver : forall idb, RcIdentModel.has_reac_version idb = bv_unsigned (nth 36 idb z0).
Proof. intros idb. unfold RcIdentModel.has_reac_version, RcIdentModel.bz, RcIdentModel.nthb, RcIdentModel.OFF_HAS_VER. reflexivity. Qed.
Lemma r23_has_name : forall idb, RcIdentModel.has_model_name idb = bv_unsigned (nth 20 idb z0).
Proof. intros idb. unfold RcIdentModel.has_model_name, RcIdentModel.bz, RcIdentModel.nthb, RcIdentModel.OFF_HAS_NAME. reflexivity. Qed.
Lemma r23_fw : forall idb, RcIdentModel.fw_milli idb = bv_unsigned (nth 0 idb z0) + 256 * bv_unsigned (nth 1 idb z0).
Proof. intros idb. unfold RcIdentModel.fw_milli, RcIdentModel.bz, RcIdentModel.nthb. reflexivity. Qed.
Lemma r23_major : forall idb, RcIdentModel.major idb = bv_unsigned (nth 22 idb z0) + 256 * bv_unsigned (nth 23 idb z0).
Proof. intros idb. unfold RcIdentModel.major, RcIdentModel.bz, RcIdentModel.nthb. reflexivity. Qed.
Lemma r23_minor : forall idb, RcIdentModel.minor idb = bv_unsigned (nth 24 idb z0) + 256 * bv_unsigned (nth 25 idb z0).
Proof. intros idb. unfold RcIdentModel.minor, RcIdentModel.bz, RcIdentModel.nthb. reflexivity. Qed.
Lemma r23_patch : forall idb, RcIdentModel.patch idb = bv_unsigned (nth 26 idb z0) + 256 * bv_unsigned (nth 27 idb z0).
Proof. intros idb. unfold RcIdentModel.patch, RcIdentModel.bz, RcIdentModel.nthb. reflexivity. Qed.
Lemma r23_rval : forall row k, RcDecl.rval row k = bv_unsigned (nth k row z0).
Proof. intros row k. unfold RcDecl.rval, RcDecl.rbyte. reflexivity. Qed.
Lemma r23_model_name : forall idb, RcIdentModel.model_name idb = firstn 17 (skipn 3 idb).
Proof. intros idb. unfold RcIdentModel.model_name, RcIdentModel.get, RcIdentModel.OFF_NAME, RcIdentModel.NAME_CAP. reflexivity. Qed.
Lemma r23_hid : forall row, RcEmit.em_hid row = RcPorts.rc_s32of (bv_unsigned (nth 56 row z0))
  (bv_unsigned (nth 57 row z0)) (bv_unsigned (nth 58 row z0)) (bv_unsigned (nth 59 row z0)).
Proof. intros row. unfold RcEmit.em_hid, RcPorts.rc_u8. reflexivity. Qed.

(* has_identity_record(m) = 0 is the 4 bytes at m + 56 reading 0 (the u32 the lw loads). *)
Lemma r23_hid0 : forall row : list byte, RcEmit.em_hid row = 0 ->
  bv_unsigned (nth 56 row z0) + 256 * bv_unsigned (nth 57 row z0) + 65536 * bv_unsigned (nth 58 row z0) +
  16777216 * bv_unsigned (nth 59 row z0) = 0.
Proof.
  intros row H. rewrite r23_hid in H. unfold RcPorts.rc_s32of in H. cbv zeta in H. r23_rng.
  match type of H with context [if ?c then _ else _] => destruct c eqn:Elt end;
    [apply Z.ltb_lt in Elt | apply Z.ltb_ge in Elt]; lia.
Qed.

(* The 8-byte load of the row's name pointer is rname. *)
Lemma r23_rname_rng : forall row, 0 <= RcSynth.rname row < 2 ^ 64.
Proof.
  intros row. unfold RcSynth.rname, RcSynth.rw64, RcSynth.rw32, RcSynth.rw16, RcSynth.rb. cbn [Nat.add].
  r23_rng. lia.
Qed.

Lemma r23_l8 : forall row : list byte,
  [nth 280 row z0; nth 281 row z0; nth 282 row z0; nth 283 row z0;
   nth 284 row z0; nth 285 row z0; nth 286 row z0; nth 287 row z0] = le8 (Z_to_bv 64 (RcSynth.rname row)).
Proof.
  intros row. rewrite <- le8_lit by apply r23_rname_rng.
  pose proof (StrFun.Z_to_le_bytes_to_Z [nth 280 row z0; nth 281 row z0; nth 282 row z0; nth 283 row z0;
     nth 284 row z0; nth 285 row z0; nth 286 row z0; nth 287 row z0]) as E.
  rewrite Bytes.bytes_le_to_Z_le_val in E. cbn [length map Bytes.le_val] in E.
  rewrite <- E at 1. f_equal.
  unfold RcSynth.rname, RcSynth.rw64, RcSynth.rw32, RcSynth.rw16, RcSynth.rb, RcSynth.bz. cbn [Nat.add].
  unfold z0. lia.
Qed.

(* ---- the row's name string, read from the image (computed over the 11 rows) ---- *)
Definition r23_nmok (np : Z) (nb : list byte) : bool :=
  negb (np =? 0) && (0 <=? np) && (np + Z.of_nat (length nb) <=? 2 ^ 64) &&
  forallb (fun i => ro_addr rsegs (Z_to_bv 64 (np + Z.of_nat i)) &&
                    match seg_rom rsegs (Z_to_bv 64 (np + Z.of_nat i)), nth_error nb i with
                    | Some x, Some y => bv_unsigned x =? bv_unsigned y
                    | _, _ => false
                    end) (seq 0 (length nb)).

Lemma r23_nmok_sound : forall np nb m, r23_nmok np nb = true -> MemNorm.ro_agree rsegs m ->
  np <> 0 /\ bytes_at rsegs m np nb.
Proof.
  intros np nb m H Hro. unfold r23_nmok in H.
  apply andb_prop in H as [H H4]. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
  apply negb_true_iff, Z.eqb_neq in H1. apply Z.leb_le in H2. apply Z.leb_le in H3.
  split; [exact H1|]. split; [lia|]. split; [lia|]. intros i Hi.
  rewrite forallb_forall in H4. specialize (H4 i ltac:(apply in_seq; lia)). apply andb_prop in H4 as [Hr Hs].
  unfold wa. rewrite (Hro _ Hr).
  destruct (seg_rom rsegs (Z_to_bv 64 (np + Z.of_nat i))) as [x|]; [|discriminate].
  destruct (nth_error nb i) as [y|]; [|discriminate]. apply Z.eqb_eq in Hs. f_equal. apply bv_eq. exact Hs.
Qed.

Lemma r23_nm_rows : forall inp, rt_n inp 6 <> 0 -> r23_nmok (RcSynth.rname (rt_mb inp)) (rt_nb inp) = true.
Proof. intros inp. b2_rows inp; b2_fin. Qed.

Ltac r23_brf tac :=
  match goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => replace c with false; [cbv iota | symmetry; tac] end.
Ltac r23_brt tac :=
  match goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => replace c with true; [cbv iota | symmetry; tac] end.
Ltac r23_rd HB a bs k n a' :=
  let HR := fresh "HR" in
  pose proof (r23_rdl _ a bs k n HB ltac:(lia)) as HR; cbn [seq map] in HR;
  replace (a + Z.of_nat k) with a' in HR by lia.

Lemma r23_evt : strcmp_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (spv mr : Z) (idb mb : list byte),
    sp = Z_to_bv 64 spv -> s0 = Z_to_bv 64 mr ->
    bytes_at rsegs m (spv + 154) idb -> length idb = 38%nat ->
    bytes_at rsegs m mr mb -> length mb = 296%nat ->
    bv_unsigned (nth 2 idb z0) <> 0 -> bv_unsigned (nth 36 idb z0) <> 0 ->
    nth 0 idb z0 = nth 266 mb z0 -> nth 1 idb z0 = nth 267 mb z0 ->
    nth 22 idb z0 = nth 268 mb z0 -> nth 23 idb z0 = nth 269 mb z0 ->
    nth 24 idb z0 = nth 270 mb z0 -> nth 25 idb z0 = nth 271 mb z0 ->
    nth 26 idb z0 = nth 272 mb z0 -> nth 27 idb z0 = nth 273 mb z0 ->
    (RcEmit.em_hid mb <> 0 -> bv_unsigned (nth 20 idb z0) <> 0 /\ RcSynth.rname mb <> 0 /\
       exists sy, ~ In z0 sy /\ bytes_at rsegs m (RcSynth.rname mb) (sy ++ [z0]) /\
         bytes_at rsegs m (spv + 157) (sy ++ [z0])) ->
    evt rsegs
      (fun ms' => (exists a0' a1' : word, ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' a1' a2 a3 a4 a5 a6 a7
                     s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x13598) fc None m (seg_rom rsegs)) \/
                  (exists a1' a2' a3' : word, ms' = MS (mkR (Z_to_bv 64 0x1358c) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0)
                     a1' a2' a3' a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x1358c) fc None m (seg_rom rsegs)))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x13524) fc None m (seg_rom rsegs)).
Proof.
  intros SC ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    spv mr idb mb -> -> HI LI HM LM Hfw Hver E0 E1 E22 E23 E24 E25 E26 E27 Hname.
  pose proof (bytes_at_bound rsegs _ _ _ HI) as BI. pose proof (bytes_at_bound rsegs _ _ _ HM) as BM.
  rewrite LI in BI. rewrite LM in BM.
  (* 0x13524 lbu a0,156(sp); beqz *)
  r23_rd HI (spv + 154) idb 2%nat 1%nat (spv + 156). step. clear HR.
  step. r23_brf ltac:(apply r23_zxb_nz; exact Hfw).
  (* fw: lhu, lhu, bne *)
  r23_rd HI (spv + 154) idb 0%nat 2%nat (spv + 154). rewrite E0, E1, r23_l2 in HR. step. clear HR.
  r23_rd HM mr mb 266%nat 2%nat (mr + 266). rewrite r23_l2 in HR. step. clear HR.
  step. r23_brf ltac:(rewrite r23_eqb_refl; reflexivity).
  (* has_reac_version: lbu a0,190(sp); beqz *)
  r23_rd HI (spv + 154) idb 36%nat 1%nat (spv + 190). step. clear HR.
  step. r23_brf ltac:(apply r23_zxb_nz; exact Hver).
  (* major *)
  r23_rd HI (spv + 154) idb 22%nat 2%nat (spv + 176). rewrite E22, E23, r23_l2 in HR. step. clear HR.
  r23_rd HM mr mb 268%nat 2%nat (mr + 268). rewrite r23_l2 in HR. step. clear HR.
  step. r23_brf ltac:(rewrite r23_eqb_refl; reflexivity).
  (* minor *)
  r23_rd HI (spv + 154) idb 24%nat 2%nat (spv + 178). rewrite E24, E25, r23_l2 in HR. step. clear HR.
  r23_rd HM mr mb 270%nat 2%nat (mr + 270). rewrite r23_l2 in HR. step. clear HR.
  step. r23_brf ltac:(rewrite r23_eqb_refl; reflexivity).
  (* patch *)
  r23_rd HI (spv + 154) idb 26%nat 2%nat (spv + 180). rewrite E26, E27, r23_l2 in HR. step. clear HR.
  r23_rd HM mr mb 272%nat 2%nat (mr + 272). rewrite r23_l2 in HR. step. clear HR.
  step. r23_brf ltac:(rewrite r23_eqb_refl; reflexivity).
  (* has_identity_record: lw a0,56(s0); beqz a0,13598 *)
  r23_rd HM mr mb 56%nat 4%nat (mr + 56). rewrite r23_l4 in HR. step. clear HR.
  step. if_cases Eh.
  - apply evt_done. left. do 2 eexists. reflexivity.
  - assert (Hh : RcEmit.em_hid mb <> 0).
    { intros H0. apply r23_hid0 in H0. rewrite H0 in Eh. vm_compute in Eh. discriminate Eh. }
    destruct (Hname Hh) as (Hn20 & Hnp & sy & Hsy & Hnb & Hsx).
    (* has_model_name: lbu a0,174(sp); beqz *)
    r23_rd HI (spv + 154) idb 20%nat 1%nat (spv + 174). step. clear HR.
    step. r23_brf ltac:(apply r23_zxb_nz; exact Hn20).
    (* ld a1,280(s0); addi a0,sp,157; bnez a1 *)
    r23_rd HM mr mb 280%nat 8%nat (mr + 280). rewrite r23_l8 in HR. step. clear HR.
    pose proof (r23_rname_rng mb) as Rn.
    step. step.
    r23_brt ltac:(unfold bv_eqb; rewrite !MState.unsigned_lit by lia;
                  apply negb_true_iff, Z.eqb_neq; exact Hnp).
    (* jal strcmp *)
    step.
    eapply evt_cut.
    { eapply SC with (sx := sy) (sy := sy).
      - rewrite MState.unsigned_lit by lia. exact Hsx.
      - exact Hsy.
      - rewrite MState.unsigned_lit by lia. exact Hnb.
      - exact Hsy. }
    intros ms' (r & x11 & x12 & x13 & -> & Hr).
    assert (Er : r = Z_to_bv 64 0) by (apply Hr; reflexivity). subst r.
    replace (ret_pc (Z_to_bv 64 0x1358c)) with (Z_to_bv 64 0x1358c) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
    apply evt_done. right. do 3 eexists. reflexivity.
Qed.

Section R23.
Context {fx : FPState} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.
Hypothesis SC : strcmp_contract.

Lemma seg_R23 : Hcut B APIf ra (Inv_K1358c B APIf ra empty) -> Hcut B APIf ra (Inv_K13598 B APIf ra empty) ->
  Hcut B APIf ra (Inv_K13524 B APIf ra empty).
Proof.
  intros H58c H598 g c (L & A & regs & mem & md & -> & HFR & HP & ((H7 & (Hc & H21 & H27) & HOUR) & H8 & HID)).
  destruct (sl_fr_bnd B APIf ra empty FF _ _ _ _ _ _ _ HFR) as (HSP & _ & _ & _ & HMI).
  pose proof HFR as (_ & _ & _ & _ & _ & _ & _ & HREL & _).
  (* #24-#29: RID_7's firmware and version fields are the row's (RTM). *)
  pose proof (b2_rtm_fw (g_in g)) as (Hfw1 & Hfw2).
  pose proof (b2_rtm_ver (g_in g)) as (Hv1 & Hv2 & Hv3 & Hv4).
  rewrite r23_has_fw in Hfw1. rewrite r23_has_ver in Hv1.
  rewrite r23_fw, !r23_rval in Hfw2. rewrite r23_major, !r23_rval in Hv2.
  rewrite r23_minor, !r23_rval in Hv3. rewrite r23_patch, !r23_rval in Hv4.
  apply r23_u16 in Hfw2 as (E0 & E1). apply r23_u16 in Hv2 as (E22 & E23).
  apply r23_u16 in Hv3 as (E24 & E25). apply r23_u16 in Hv4 as (E26 & E27).
  pose proof (proj1 (b1_RS_len (g_in g) 7)) as LI.
  assert (LM : length (rt_mb (g_in g)) = 296%nat) by (unfold rt_mb; apply b1_row_len).
  assert (HM : bytes_at rsegs mem (mrow (g_in g)) (rt_mb (g_in g))).
  { unfold mrow, rt_mb. apply (b1_row_bytes B APIf ra empty FF mem _ HREL).
    pose proof (b2_istar_range (g_in g)). unfold CAT_N. lia. }
  unfold IDB, spk in HID.
  pose proof (bytes_at_normalize rsegs mem _ _ HMI HID) as HIn.
  pose proof (bytes_at_normalize rsegs mem _ _ HMI HM) as HMn.
  (* #30 and the row's name (has_identity_record(m) != 0) *)
  assert (Hname : RcEmit.em_hid (rt_mb (g_in g)) <> 0 ->
    bv_unsigned (nth 20 (RID (g_in g) 7) z0) <> 0 /\ RcSynth.rname (rt_mb (g_in g)) <> 0 /\
    exists sy, ~ In z0 sy /\ bytes_at rsegs (normalize rsegs mem) (RcSynth.rname (rt_mb (g_in g))) (sy ++ [z0]) /\
      bytes_at rsegs (normalize rsegs mem) (fsp g + 157) (sy ++ [z0])).
  { intros Hh. apply (b2_rtm_hid (g_in g)) in Hh.
    destruct (b2_rtm_name (g_in g) Hh) as (Hn1 & Hn2 & Hn3 & Hn4 & Hn5).
    destruct (r23_nmok_sound _ _ mem (r23_nm_rows (g_in g) Hh) HMI) as (Hnp & Hnb).
    rewrite r23_has_name in Hn1. rewrite r23_model_name in Hn2.
    split; [lia|]. split; [exact Hnp|].
    apply andb_prop in Hn5 as (Hn5a & Hn5b). apply Nat.leb_le in Hn5a. apply Nat.leb_le in Hn5b.
    assert (Hne : rt_nb (g_in g) <> []) by (intros E; rewrite E in Hn5a; cbn in Hn5a; lia).
    assert (Enb : rt_nb (g_in g) = removelast (rt_nb (g_in g)) ++ [z0]).
    { rewrite (app_removelast_last (Z_to_bv 8 1) Hne) at 1. f_equal. f_equal. exact Hn3. }
    exists (removelast (rt_nb (g_in g))). split; [|split].
    - intros Hin. rewrite forallb_forall in Hn4. specialize (Hn4 _ Hin). vm_compute in Hn4. discriminate Hn4.
    - rewrite <- Enb. apply bytes_at_normalize; [exact HMI | exact Hnb].
    - rewrite <- Enb. apply bytes_at_normalize; [exact HMI|].
      rewrite firstn_firstn, Nat.min_l in Hn2 by lia. rewrite <- Hn2.
      replace (fsp g + 157) with (fsp g + 154 + Z.of_nat 3) by lia.
      apply r23_sub; [exact HID | lia]. }
  eapply (b3_mid B APIf ra empty FF g [] L A regs mem md _ []); [exact HFR | exact HP | | | |].
  - intros x Hx O. refine (b3_fp g _ x _ Hx O). apply Forall_nil.
  - rewrite sl_mkR_of.
    eapply r23_evt with (spv := fsp g) (mr := mrow (g_in g)) (idb := RID (g_in g) 7) (mb := rt_mb (g_in g));
      [exact SC | exact HSP | exact H8 | exact HIn | exact LI | exact HMn | exact LM | lia | lia
      | exact E0 | exact E1 | exact E22 | exact E23 | exact E24 | exact E25 | exact E26 | exact E27 | exact Hname].
  - intros ms [(? & ? & ->) | (? & ? & ? & ->)];
      (do 3 eexists; split; [reflexivity|]; split; [apply munch_refl|]; split; [apply wmono_refl|];
       split; [reflexivity|]; split; reflexivity).
  - intros R pc' m0' regs' m' HQ Hx Hrel MU' HFR'.
    destruct HQ as [(? & ? & HQ) | (? & ? & ? & HQ)]; injection HQ as E1' E2' E3'; subst R pc' m0'.
    + apply H598. exists L, A, regs', m', md.
      split; [reflexivity|]. split; [exact HFR'|]. split; [exact HP|].
      assert (E7 : c0 (g_in g) = 7) by (unfold c0; unfold g_n in H7; lia).
      unfold PB, CUR, OURb, rg in *. rewrite E7, !(sl_getr_eqv _ _ _ Hx).
      refine (conj (conj Hc (conj H21 H27)) _).
      apply (bytes_at_transport rsegs _ mem m' _ _ HOUR MU'). exact I.
    + apply H58c. exists L, A, regs', m', md.
      split; [reflexivity|]. split; [exact HFR'|]. split; [exact HP|].
      unfold RA, CUR, OURb, IDB, spk, rg in *. rewrite !(sl_getr_eqv _ _ _ Hx).
      refine (conj (conj H7 (conj (conj Hc (conj H21 H27)) _)) (conj H8 (conj _ eq_refl))).
      * apply (bytes_at_transport rsegs _ mem m' _ _ HOUR MU'). exact I.
      * apply (bytes_at_transport rsegs _ mem m' _ _ HID MU'). exact I.
Qed.

End R23.
