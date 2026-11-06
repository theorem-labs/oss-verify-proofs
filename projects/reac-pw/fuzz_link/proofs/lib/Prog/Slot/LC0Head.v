(* op_read (fuzz_link.c:677-700), plain image: segment S1, from the loop head (0x13a1c) to the call of
   text_buf (kc) at 0x13e4c.

   The segment runs, in order:
     0x13a1c-0x13a64  the dispatch: the operation byte b at the cursor, b mod 6 by `(b * 0xab) >> 10`
                      (hd_m6), the cursor cells get P+1 / N-1, the jump table at 0x106b0 takes op 0 to
                      0x13a68;
     0x13a68-0x13e18  name_of and the two `% 40` caps, inlined: the selector, kind and alias bytes while
                      the input lasts (hd_walkA, with the shared tails hd_e10 and hd_cb0; the byte
                      arithmetic is checked over all 256 values: hd_m6, hd_m6o, hd_m40);
     0x13e20-0x13e24  kernel (in), through mk_call.v's leaf_call with the Pre from LC0Kern;
     0x13e28-0x13e44  model_begin, inlined (hd_walkB; its memory part is c0_begin_mem, its byte lists
                      c0_begin_lists);
     0x13e48-0x13e4c  mv a0, s6; jal text_buf: the cut c0_cut_kc.
   c0_s1 is the segment lemma; the callee contract it uses (kernel) is its only Section hypothesis.

   Every address and offset is read from the plain image (the unstripped twin of the pin
   ebe34b259b9f; link/ct/dis/plain/LLVMFuzzerTestOneInput.s). *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib Require Import
  PropExec MState Mem Cells Exec Step Frame Tac Bytes Arr Image FP.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib Require Import Img0 MemNorm.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import link_spec link_mem mk_leaf kernel_c.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib Require Import Regs6ss RegisterBridge.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Spec Require StrFun.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog.Slot Require Import LDefs LC0Defs LC0Call LC0Lib LC0Kern.
Import ListNotations.
Local Open Scope Z_scope.

(* ==========================================================================
   1. Byte arithmetic the head computes
   ========================================================================== *)

Definition hd_chk (f : Z -> word) (g : Z -> Z) : bool :=
  forallb (fun n => bv_eqb (f (Z.of_nat n)) (Z_to_bv 64 (g (Z.of_nat n)))) (seq 0 256).

Lemma hd_chk_ok : forall f g, hd_chk f g = true -> forall z, 0 <= z < 256 -> f z = Z_to_bv 64 (g z).
Proof.
  intros f g H z Hz. unfold hd_chk in H. rewrite forallb_forall in H.
  specialize (H (Z.to_nat z) ltac:(apply in_seq; lia)). rewrite Z2Nat.id in H by lia.
  unfold bv_eqb in H. apply Z.eqb_eq in H. apply bv_eq. exact H.
Qed.

(* 0x13a2c-0x13a44: a3 = b - 6 * ((b * 0xab) >> 10), as a byte: b mod 6 *)
Definition hd_m6f (z : Z) : word :=
  Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 (z + bv_swrap 32
     (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (Z_to_bv 64 (Z.shiftr (bv_unsigned (Z_to_bv 64 (z * 171))) 10))) 1)) -
      bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (Z_to_bv 64 (Z.shiftr (bv_unsigned (Z_to_bv 64 (z * 171))) 10))) 3)))))) 255).
Lemma hd_m6f_chk : hd_chk hd_m6f (fun z => z mod 6) = true. Proof. vm_compute. reflexivity. Qed.
Lemma hd_m6 : forall z, 0 <= z < 256 ->
  Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 (z + bv_swrap 32
     (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (Z_to_bv 64 (Z.shiftr (bv_unsigned (Z_to_bv 64 (z * 171))) 10))) 1)) -
      bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (Z_to_bv 64 (Z.shiftr (bv_unsigned (Z_to_bv 64 (z * 171))) 10))) 3)))))) 255)
  = Z_to_bv 64 (z mod 6).
Proof. exact (hd_chk_ok _ _ hd_m6f_chk). Qed.

(* 0x13de0-0x13df8: s - 6 * mulhu(s, 0x2aaaaaaaaaaaaaab) = s mod 6 *)
Definition hd_m6of (z : Z) : word :=
  Z_to_bv 64 (z + (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (Z_to_bv 64 (Z.shiftr (z * 3074457345618258603) 64))) 1)) -
                   bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (Z_to_bv 64 (Z.shiftr (z * 3074457345618258603) 64))) 3)))).
Lemma hd_m6of_chk : hd_chk hd_m6of (fun z => z mod 6) = true. Proof. vm_compute. reflexivity. Qed.
Lemma hd_m6o : forall z, 0 <= z < 256 ->
  Z_to_bv 64 (z + (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (Z_to_bv 64 (Z.shiftr (z * 3074457345618258603) 64))) 1)) -
                   bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (Z_to_bv 64 (Z.shiftr (z * 3074457345618258603) 64))) 3))))
  = Z_to_bv 64 (z mod 6).
Proof. exact (hd_chk_ok _ _ hd_m6of_chk). Qed.

(* 0x13cc4-0x13cd0 (and 0x13cf0-0x13cfc): b - 40 * ((b * 0xcd) >> 13) = b mod 40 *)
Definition hd_m40f (z : Z) : word :=
  Z_to_bv 64 (z - bv_unsigned (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (Z.shiftr (bv_unsigned (Z_to_bv 64 (z * 205))) 13)) * 40))).
Lemma hd_m40f_chk : hd_chk hd_m40f (fun z => z mod 40) = true. Proof. vm_compute. reflexivity. Qed.
Lemma hd_m40 : forall z, 0 <= z < 256 ->
  Z_to_bv 64 (z - bv_unsigned (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (Z.shiftr (bv_unsigned (Z_to_bv 64 (z * 205))) 13)) * 40)))
  = Z_to_bv 64 (z mod 40).
Proof. exact (hd_chk_ok _ _ hd_m40f_chk). Qed.

Lemma hd_land255 : forall v, 0 <= v < 256 -> Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 v)) 255) = Z_to_bv 64 v.
Proof.
  intros v Hv. rewrite unsigned_lit by lia. change 255 with (Z.ones 8). rewrite Z.land_ones by lia.
  rewrite Z.mod_small by (change (2 ^ 8) with 256; lia). reflexivity.
Qed.

Lemma hd_zxb : forall b : byte, bv_unsigned (zxb b) = bv_unsigned b.
Proof.
  intros b. pose proof (bv_unsigned_in_range 8 b) as R. change (bv_modulus 8) with 256 in R.
  unfold zxb. rewrite unsigned_lit by lia. reflexivity.
Qed.

Lemma hd_land_zxb : forall b : byte, Z_to_bv 64 (Z.land (bv_unsigned (zxb b)) 255) = zxb b.
Proof.
  intros b. pose proof (bv_unsigned_in_range 8 b) as R. change (bv_modulus 8) with 256 in R.
  rewrite hd_zxb. unfold zxb. change 255 with (Z.ones 8). rewrite Z.land_ones by lia.
  rewrite Z.mod_small by (change (2 ^ 8) with 256; lia). reflexivity.
Qed.

Lemma hd_ne0 : forall z, 0 < z < 2 ^ 64 -> bv_eqb (Z_to_bv 64 z) (Z_to_bv 64 0) = false.
Proof. intros z Hz. unfold bv_eqb. rewrite !unsigned_lit by lia. apply Z.eqb_neq. lia. Qed.

Lemma hd_eqb_zxb : forall (b : byte) k, 0 <= k < 2 ^ 64 -> bv_eqb (zxb b) (Z_to_bv 64 k) = (bv_unsigned b =? k).
Proof. intros b k Hk. unfold bv_eqb. rewrite hd_zxb, unsigned_lit by lia. reflexivity. Qed.

Lemma hd_ltu_zxb : forall (b : byte) k, 0 <= k < 2 ^ 64 -> bv_ltu (Z_to_bv 64 k) (zxb b) = (k <? bv_unsigned b).
Proof. intros b k Hk. unfold bv_ltu. rewrite hd_zxb, unsigned_lit by lia. reflexivity. Qed.

Lemma hd_sl3 : forall x, 0 <= x < 2 ^ 60 -> Z_to_bv 64 (Z.shiftl (bv_unsigned (Z_to_bv 64 x)) 3) = Z_to_bv 64 (8 * x).
Proof. intros x Hx. rewrite unsigned_lit by lia. rewrite Z.shiftl_mul_pow2 by lia. f_equal. lia. Qed.

Lemma hd_rd1 : forall m a b l, bytes_at rsegs m a (b :: l) -> ov_read_bytes rsegs m (wa a) 1 = Some [b].
Proof.
  intros m a b l H. pose proof (bytes_at_read rsegs m a (b :: l) 0 1 H ltac:(lia) ltac:(cbn; lia)) as E.
  rewrite Z.add_0_r in E. exact E.
Qed.

Lemma hd_rd8 : forall m a w, bytes_at rsegs m a (le8 w) -> ov_read_bytes rsegs m (wa a) 8 = Some (le8 w).
Proof.
  intros m a w H. pose proof (bytes_at_read rsegs m a (le8 w) 0 8 H ltac:(lia) ltac:(rewrite length_le8; lia)) as E.
  rewrite Z.add_0_r in E. rewrite E. reflexivity.
Qed.

(* pose the one-byte read at a of the goal's current memory *)
Ltac hd_rd a :=
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    match goal with H : bytes_at rsegs mm a (_ :: _) |- _ => pose proof (hd_rd1 _ _ _ _ H) end end.

(* ==========================================================================
   2. The head walk, 0x13a1c - the jal kernel at 0x13e24
   ========================================================================== *)

(* the frame cells the head reads and the cursor it writes *)
Definition hd_cells (P nc : Z) (j0 : list byte) (c16 c24 c32 c56 : word) (j1 j2 : list byte) : list cell :=
  [CB 8 j0; C8 (wz A_ODD); C8 c16; C8 c24; C8 c32; C8 (wz A_G_NAMES);
   C8 (wz A_JT); C8 c56; C8 (wz P); C8 (wz nc); CB 40 j1; CB 256 j2].

(* the state at kernel's entry: ra = 0x13e28, a0 = sp + 0x40, s2 the name, s5 / s6 the two caps *)
Definition hd_atK (sp gp tp t0 t1 t2 s0 s1 s3 s4 s7 s10 s11 t3 t4 t5 t6 s2 : word) (F : bvmap 5 word)
    (fc : bv 32) (m0 : word -> option byte) (s5v s6v : Z) (cs : list cell) (ms : machine_state) : Prop :=
  exists (a1' a2' a3' a4' a5' a6' a7' : word) (m' : word -> option byte),
    ms = MS (mkR (wz 0x13e28) sp gp tp t0 t1 t2 s0 s1 (wz (bv_unsigned sp + 64)) a1' a2' a3' a4' a5' a6' a7'
                s2 s3 s4 (wz s5v) (wz s6v) s7 (wz 0xab) (wz 4) s10 s11 t3 t4 t5 t6)
           F (wz KERNEL) fc None m' (seg_rom rsegs) /\
    munch [(bv_unsigned sp + 64, bv_unsigned sp + 80)] m0 m' /\ wmono rsegs m0 m' /\ mem_inv rsegs m' /\
    rw_cells rsegs m' (bv_unsigned sp) cs.

Lemma hd_atK_eq : forall sp gp tp t0 t1 t2 s0 s1 s3 s4 s7 s10 s11 t3 t4 t5 t6 s2 s2' F fc m0 s5v s5v' s6v s6v' cs cs' ms,
  s2 = s2' -> s5v = s5v' -> s6v = s6v' -> cs = cs' ->
  hd_atK sp gp tp t0 t1 t2 s0 s1 s3 s4 s7 s10 s11 t3 t4 t5 t6 s2 F fc m0 s5v s6v cs ms ->
  hd_atK sp gp tp t0 t1 t2 s0 s1 s3 s4 s7 s10 s11 t3 t4 t5 t6 s2' F fc m0 s5v' s6v' cs' ms.
Proof. intros. subst. assumption. Qed.

(* 0x13e10: no cap byte left *)
Lemma hd_e10 : forall (ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m0 m : word -> option byte) (sp : word) (cs : list cell),
  munch [(bv_unsigned sp + 64, bv_unsigned sp + 80)] m0 m -> wmono rsegs m0 m -> mem_inv rsegs m ->
  rw_cells rsegs m (bv_unsigned sp) cs ->
  evt rsegs (hd_atK sp gp tp t0 t1 t2 s0 s1 s3 s4 s7 s10 s11 t3 t4 t5 t6 s2 F fc m0 0 0 cs)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 (wz 0xab) (wz 4) s10 s11 t3 t4 t5 t6)
        F (wz 0x13e10) fc None m (seg_rom rsegs)).
Proof.
  intros. unfold wz. do 6 step.
  apply evt_done. unfold hd_atK. do 8 eexists. split; [reflexivity|].
  split; [assumption|]. split; [assumption|]. split; assumption.
Qed.

(* the two caps over the input from the kind byte on *)
Definition hd_kc2 (l : list byte) : Z := c0_b l 0 mod 40.
Definition hd_ac2 (l : list byte) : Z := if (length l <? 2)%nat then 0 else c0_b l 1 mod 40.

Lemma hd_cells_eq : forall P P' N N' j0 c16 c24 c32 c56 j1 j2, P = P' -> N = N' ->
  hd_cells P N j0 c16 c24 c32 c56 j1 j2 = hd_cells P' N' j0 c16 c24 c32 c56 j1 j2.
Proof. intros. subst. reflexivity. Qed.

(* the cursor after the head, from a 0x13cb0 continuation *)
Ltac hd_fin_cells :=
  apply hd_cells_eq; unfold c0_used; cbn [length] in *; rewrite ?Nat2Z.inj_succ in *; lia.

(* 0x13cb0: the kind byte at Q, and the alias byte at Q + 1 if there is one *)
Lemma hd_cb0 : forall (ra gp tp t0 t1 t2 s0 s1 a2 a3 a4 a7 s2 s3 s4 s5 s6 s7 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m0 m : word -> option byte) (sp : word) (Q R : Z) (b : byte) (l : list byte)
    (Pc Nc : Z) (j0 : list byte) (c16 c24 c32 c56 : word) (j1 j2 : list byte),
  0 <= Q -> Q + R <= bv_unsigned sp -> bv_unsigned sp + 480 <= 2 ^ 64 ->
  R = 1 + Z.of_nat (length l) ->
  bytes_at rsegs m Q (b :: l) ->
  rw_cells rsegs m (bv_unsigned sp) (hd_cells Pc Nc j0 c16 c24 c32 c56 j1 j2) ->
  munch [(bv_unsigned sp + 64, bv_unsigned sp + 80)] m0 m -> wmono rsegs m0 m -> mem_inv rsegs m ->
  evt rsegs (hd_atK sp gp tp t0 t1 t2 s0 s1 s3 s4 s7 s10 s11 t3 t4 t5 t6 s2 F fc m0 (hd_ac2 (b :: l)) (hd_kc2 (b :: l))
               (hd_cells (Q + Z.min 2 R) (R - Z.min 2 R) j0 c16 c24 c32 c56 j1 j2))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz Q) (wz R) a2 a3 a4 (wz 40) (wz 205) a7 s2 s3 s4 s5 s6 s7 (wz 0xab) (wz 4)
             s10 s11 t3 t4 t5 t6) F (wz 0x13cb0) fc None m (seg_rom rsegs)).
Proof.
  intros ra gp tp t0 t1 t2 s0 s1 a2 a3 a4 a7 s2 s3 s4 s5 s6 s7 s10 s11 t3 t4 t5 t6 F fc m0 m sp Q R b l
    Pc Nc j0 c16 c24 c32 c56 j1 j2 HQ HQR Htop HR HB CW MU WM MI.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp. change (2 ^ Z.of_N 64) with (2 ^ 64) in Rsp.
  pose proof (bv_unsigned_in_range 8 b) as Rb. change (bv_modulus 8) with 256 in Rb.
  pose proof (Z.mod_pos_bound (bv_unsigned b) 40 ltac:(lia)) as Rb40.
  unfold hd_cells, wz in *.
  destruct l as [|c l].
  - cbn [length Z.of_nat] in HR. subst R.
    do 4 step. hd_rd Q. do 5 step.
    rewrite hd_zxb, hd_m40 by lia.
    step. if_true. do 5 step.
    rewrite hd_land255 by lia.
    apply evt_done. unfold hd_atK. do 8 eexists. split; [reflexivity|].
    split; [assumption|]. split; [assumption|]. split; assumption.
  - pose proof (bv_unsigned_in_range 8 c) as Rc. change (bv_modulus 8) with 256 in Rc.
    pose proof (Z.mod_pos_bound (bv_unsigned c) 40 ltac:(lia)) as Rc40.
    pose proof HB as HB1. apply (proj1 (bytes_at_app rsegs m Q [b] (c :: l))) in HB1. destruct HB1 as [_ HB1].
    change (Z.of_nat (length [b])) with 1 in HB1.
    cbn [length] in HR. rewrite Nat2Z.inj_succ in HR.
    replace (Z.min 2 R) with 2 by lia.
    do 4 step. hd_rd Q. do 5 step.
    rewrite hd_zxb, hd_m40 by lia.
    step. rewrite hd_ne0 by lia. cbv iota.
    do 4 step. hd_rd (Q + 1). do 2 step. rewrite hd_land_zxb.
    do 4 step. rewrite hd_zxb, hd_m40 by lia.
    do 5 step.
    rewrite !hd_land255 by lia.
    apply evt_done. unfold hd_atK. do 8 eexists. split; [reflexivity|].
    split; [assumption|]. split; [assumption|]. split; [assumption|].
    replace (R - 2) with (R + -2) by lia. assumption.
Qed.

(* the dispatch and the inlined name_of + the two caps: from the loop head to kernel's entry *)
Lemma hd_walkA : forall (ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s7 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (sp : word) (P : Z) (l : list byte)
    (nc : Z) (j0 : list byte) (c16 c24 c32 c56 : word) (j1 j2 : list byte),
  0 <= P -> P + Z.of_nat (length l) <= bv_unsigned sp -> bv_unsigned sp + 480 <= 2 ^ 64 ->
  A_ODD + 48 <= bv_unsigned sp ->
  (1 <= length l)%nat ->
  bytes_at rsegs m P l ->
  c0_b l 0 mod 6 = 0 ->
  rw_cells rsegs m (bv_unsigned sp) (hd_cells P nc j0 c16 c24 c32 c56 j1 j2) ->
  odd_at m ->
  mem_inv rsegs m ->
  evt rsegs (hd_atK sp gp tp t0 t1 t2 s0 s1 s3 s4 s7 s10 s11 t3 t4 t5 t6 (wz (sel_ptr (c0_sel l))) F fc m
               (c0_ac l) (c0_kc l)
               (hd_cells (P + c0_used l) (Z.of_nat (length l) - c0_used l) j0 c16 c24 c32 c56 j1 j2))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 (wz (Z.of_nat (length l))) s3 s4 (wz 46) (wz A_JT) s7
           (wz 0xab) (wz 4) s10 s11 t3 t4 t5 t6) F (wz L_LH) fc None m (seg_rom rsegs)).
Proof.
  intros ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s7 s10 s11 t3 t4 t5 t6 F fc m sp P l
    nc j0 c16 c24 c32 c56 j1 j2 HP HPl Htop Hodd Hl1 HB Hop CW HODD MI.
  pose proof (munch_refl [(bv_unsigned sp + 64, bv_unsigned sp + 80)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp. change (2 ^ Z.of_N 64) with (2 ^ 64) in Rsp.
  destruct l as [|b l]; [cbn in Hl1; lia|].
  pose proof (bv_unsigned_in_range 8 b) as Rb. change (bv_modulus 8) with 256 in Rb.
  unfold c0_b, bz in Hop. cbn [nth] in Hop.
  hd_rd P.
  destruct l as [|c l].
  - (* only the operation byte: 0x13c18, s2 = g_names + 0, both caps 0 *)
    cbn [length Z.of_nat Pos.of_succ_nat] in *.
    unfold hd_cells, L_LH, A_JT, wz in *.
    do 11 step. rewrite hd_zxb, hd_m6 by lia. rewrite Hop.
    do 3 step. if_false. do 5 step.
    step. if_true. do 4 step. do 4 step. if_true.
    eapply evt_mono; [eapply hd_e10; eassumption|].
    intros ms' HK. eapply hd_atK_eq; [| | | | exact HK]; reflexivity.
  - pose proof (bv_unsigned_in_range 8 c) as Rc. change (bv_modulus 8) with 256 in Rc.
    pose proof HB as HB1. apply (proj1 (bytes_at_app rsegs m P [b] (c :: l))) in HB1. destruct HB1 as [_ HB1].
    change (Z.of_nat (length [b])) with 1 in HB1.
    pose proof HB1 as HB2. apply (proj1 (bytes_at_app rsegs m (P + 1) [c] l)) in HB2. destruct HB2 as [_ HB2].
    change (Z.of_nat (length [c])) with 1 in HB2. replace (P + 1 + 1) with (P + 2) in HB2 by lia.
    destruct (HODD (Z.to_nat (bv_unsigned c mod 6)) ltac:(pose proof (Z.mod_pos_bound (bv_unsigned c) 6); lia))
      as [HO _].
    rewrite Z2Nat.id in HO by (pose proof (Z.mod_pos_bound (bv_unsigned c) 6); lia).
    unfold u64_at in HO.
    pose proof (Z.mod_pos_bound (bv_unsigned c) 6 ltac:(lia)) as Rc6.
    clear HODD.
    cbn [length] in HPl |- *. rewrite !Nat2Z.inj_succ in HPl |- *.
    unfold hd_cells, L_LH, A_JT, wz in CW, HO.
    lazymatch goal with |- evt ?s ?Q ?S => let S' := eval cbv [wz L_LH A_JT] in S in change (evt s Q S') end.
    do 11 step. rewrite hd_zxb, hd_m6 by lia. rewrite Hop.
    do 3 step. if_false. do 5 step.
    step. rewrite hd_ne0 by lia. cbv iota.
    hd_rd (P + 1).
    do 9 step. rewrite hd_eqb_zxb by lia.
    destruct (Z.eq_dec (bv_unsigned c) 255) as [E255|N255].
    + (* s = 255: the NULL name *)
      replace (negb (bv_unsigned c =? 255)) with false by (rewrite E255; reflexivity). cbv iota.
      do 2 step.
      destruct l as [|d l].
      * if_false. step.
        eapply evt_mono; [eapply hd_e10 with (cs := hd_cells _ _ j0 c16 c24 c32 c56 j1 j2); eassumption|].
        intros ms' HK. eapply hd_atK_eq; [| | | | exact HK]; try reflexivity.
        change (c0_sel [b; c]) with (bv_unsigned c). unfold sel_ptr. rewrite E255. reflexivity.
      * rewrite hd_ne0 by (cbn [length] in *; lia). change (negb false) with true. cbv iota.
        eapply evt_mono;
          [eapply hd_cb0 with (b := d) (l := l); try eassumption; cbn [length] in *; lia|].
        intros ms' HK. eapply hd_atK_eq; [| | | | exact HK].
        -- change (c0_sel (b :: c :: d :: l)) with (bv_unsigned c). unfold sel_ptr. rewrite E255. reflexivity.
        -- destruct l; reflexivity.
        -- reflexivity.
        -- hd_fin_cells.
    + replace (negb (bv_unsigned c =? 255)) with true by (rewrite (proj2 (Z.eqb_neq _ _) N255); reflexivity).
      cbv iota.
      do 2 step. rewrite hd_ltu_zxb by lia.
      destruct (Z_lt_le_dec 63 (bv_unsigned c)) as [G63|L63].
      * (* s >= 64: odd[s mod 6] *)
        rewrite (proj2 (Z.ltb_lt _ _) G63). cbv iota.
        do 7 step. rewrite hd_zxb, hd_m6o by lia. step. rewrite hd_sl3 by lia. do 2 step.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
          match goal with H : bytes_at rsegs mm (A_ODD + _) _ |- _ => pose proof (hd_rd8 _ _ _ H) as RO end end.
        do 2 step.
        assert (Esel : forall l', sel_ptr (c0_sel (b :: c :: l')) = nth (Z.to_nat (bv_unsigned c mod 6)) odd_ptrs 0).
        { intros l'. change (c0_sel (b :: c :: l')) with (bv_unsigned c). unfold sel_ptr.
          rewrite (proj2 (Z.eqb_neq _ _) N255), (proj2 (Z.ltb_ge (bv_unsigned c) 64) ltac:(lia)).
          reflexivity. }
        destruct l as [|d l].
        -- if_false.
           eapply evt_mono; [eapply hd_e10 with (cs := hd_cells _ _ j0 c16 c24 c32 c56 j1 j2); eassumption|].
           intros ms' HK. eapply hd_atK_eq; [| | | | exact HK]; try reflexivity.
           rewrite Esel. reflexivity.
        -- rewrite hd_ne0 by (cbn [length] in *; lia). change (negb false) with true. cbv iota.
           eapply evt_mono;
             [eapply hd_cb0 with (b := d) (l := l); try eassumption; cbn [length] in *; lia|].
           intros ms' HK. eapply hd_atK_eq; [| | | | exact HK].
           ++ rewrite Esel. reflexivity.
           ++ destruct l; reflexivity.
           ++ reflexivity.
           ++ hd_fin_cells.
      * (* s < 64: g_names + 8 s *)
        rewrite (proj2 (Z.ltb_ge _ _) L63). cbv iota.
        do 4 step.
        assert (Esel : forall l', Z_to_bv 64 (A_G_NAMES + Z.shiftl (bv_unsigned (zxb c)) 3) =
                                  wz (sel_ptr (c0_sel (b :: c :: l')))).
        { intros l'. change (c0_sel (b :: c :: l')) with (bv_unsigned c). unfold sel_ptr.
          rewrite (proj2 (Z.eqb_neq _ _) N255), (proj2 (Z.ltb_lt (bv_unsigned c) 64) ltac:(lia)).
          unfold wz. rewrite hd_zxb, Z.shiftl_mul_pow2 by lia. f_equal. lia. }
        destruct l as [|d l].
        -- if_true.
           eapply evt_mono; [eapply hd_e10 with (cs := hd_cells _ _ j0 c16 c24 c32 c56 j1 j2); eassumption|].
           intros ms' HK. eapply hd_atK_eq; [| | | | exact HK]; try reflexivity.
           apply Esel.
        -- rewrite hd_ne0 by (cbn [length] in *; lia). cbv iota.
           eapply evt_mono;
             [eapply hd_cb0 with (b := d) (l := l); try eassumption; cbn [length] in *; lia|].
           intros ms' HK. eapply hd_atK_eq; [| | | | exact HK].
           ++ apply Esel.
           ++ destruct l; reflexivity.
           ++ reflexivity.
           ++ hd_fin_cells.
Qed.

(* ==========================================================================
   model_begin (0x13e28 - 0x13e44) and the jal text_buf (0x13e48 - 0x13e4c)
   ========================================================================== *)

(* the addresses are literals so the walk tactics can tell the cells apart: 466316 = g_nl +
   NK_SOCKET_ERRNO, 474664 = g_nl + NK_N_SENT, 465792 = GNL40, 473984 = GNL42, 8336 = MD_N_REQ *)
Lemma hd_walkB : forall (ra gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (sp : word) (md : Z)
    (se sd ns x0 x1 x2 x3 : word) (Pc Nc : Z) (j0 : list byte) (c16 c24 c32 : word) (j1 j2 : list byte),
  0 <= md -> md + 8856 <= bv_unsigned sp -> 475640 <= bv_unsigned sp ->
  (475640 <= md \/ md + 8856 <= 203648) -> bv_unsigned sp + 480 <= 2 ^ 64 ->
  rw_cells rsegs m 466316 [C4 se; C4 sd] ->
  rw_cells rsegs m 474664 [C4 ns] ->
  rw_cells rsegs m md [C4 x0; C4 x1; C4 x2] ->
  rw_cells rsegs m (md + 8336) [C4 x3] ->
  rw_cells rsegs m (bv_unsigned sp) (hd_cells Pc Nc j0 c16 c24 c32 (wz 473984) j1 j2) ->
  mem_inv rsegs m ->
  evt rsegs (fun ms' => exists m',
      ms' = MS (mkR (wz 0x13e50) sp gp tp t0 t1 t2 (wz md) (wz 465792) s6 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7
                    (wz 0xab) (wz 4) (wz (md + 8336)) s11 t3 t4 t5 t6) F (wz 0x14fb0) fc None m' (seg_rom rsegs) /\
      munch [(md, md + 12); (md + 8336, md + 8340); (474664, 474668)] m m' /\ wmono rsegs m m' /\
      mem_inv rsegs m' /\
      rw_cells rsegs m' 466316 [C4 se; C4 sd] /\ rw_cells rsegs m' 474664 [C4 (wz 0)] /\
      rw_cells rsegs m' md [C4 (sx32 se); C4 (sx32 sd); C4 (wz 0)] /\ rw_cells rsegs m' (md + 8336) [C4 (wz 0)] /\
      rw_cells rsegs m' (bv_unsigned sp) (hd_cells Pc Nc j0 c16 c24 c32 (wz 473984) j1 j2))
    (MS (mkR ra sp gp tp t0 t1 t2 (wz md) (wz 465792) a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 (wz 0xab) (wz 4)
           (wz (md + 8336)) s11 t3 t4 t5 t6) F (wz 0x13e28) fc None m (seg_rom rsegs)).
Proof.
  intros ra gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s11 t3 t4 t5 t6 F fc m sp md
    se sd ns x0 x1 x2 x3 Pc Nc j0 c16 c24 c32 j1 j2 H0 H1 H2 H3 H4 CE CN CM CR CW MI.
  pose proof (munch_refl [(md, md + 12); (md + 8336, md + 8340); (474664, 474668)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp. change (2 ^ Z.of_N 64) with (2 ^ 64) in Rsp.
  unfold hd_cells, wz in *.
  do 10 step.
  apply evt_done. eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MI|].
  split; [exact CE|]. split; [exact CN|]. split; [exact CM|]. split; [exact CR|]. exact CW.
Qed.

(* ==========================================================================
   32-bit fields of a byte list, written in place
   ========================================================================== *)

Lemma hd_le4_slice : forall bs off, 0 <= off -> off + 4 <= Z.of_nat (length bs) ->
  le4 (wz (fld_u32 bs off)) = firstn 4 (skipn (Z.to_nat off) bs).
Proof.
  intros bs off H0 H4. unfold fld_u32, link_spec.rdn, slice, le4, wz.
  change (Z.to_nat 4) with 4%nat.
  assert (Hl : length (firstn 4 (skipn (Z.to_nat off) bs)) = 4%nat)
    by (rewrite length_firstn, length_skipn; lia).
  rewrite unsigned_lit_wrap.
  rewrite (Z_to_le_bytes_mod 4 _ 64) by lia.
  rewrite <- Hl at 1. apply StrFun.Z_to_le_bytes_to_Z.
Qed.

Lemma hd_slice_upd_same : forall bs k xs, (k + length xs <= length bs)%nat ->
  slice (upd_bytes bs k xs) (Z.of_nat k) (Z.of_nat (length xs)) = xs.
Proof.
  intros bs k xs H. unfold slice, upd_bytes. rewrite !Nat2Z.id.
  rewrite skipn_app, length_firstn, (Nat.min_l k (length bs)) by lia.
  rewrite skipn_all2 by (rewrite length_firstn; lia). rewrite Nat.sub_diag. cbn [app skipn].
  change (skipn 0 (xs ++ skipn (k + length xs) bs)) with (xs ++ skipn (k + length xs) bs).
  rewrite firstn_app, Nat.sub_diag, firstn_all. cbn [firstn]. apply app_nil_r.
Qed.

Lemma hd_slice_upd_other : forall bs k xs off n, (k + length xs <= length bs)%nat -> 0 <= off -> 0 <= n ->
  (off + n <= Z.of_nat k \/ Z.of_nat k + Z.of_nat (length xs) <= off) ->
  slice (upd_bytes bs k xs) off n = slice bs off n.
Proof.
  intros bs k xs off n H H0 H1 [Hb|Ha]; unfold slice, upd_bytes.
  - rewrite skipn_app, length_firstn, (Nat.min_l k (length bs)) by lia.
    rewrite firstn_app, length_skipn, length_firstn, (Nat.min_l k (length bs)) by lia.
    replace (Z.to_nat n - (k - Z.to_nat off))%nat with 0%nat by lia. cbn [firstn]. rewrite app_nil_r.
    rewrite skipn_firstn_comm, firstn_firstn. f_equal. lia.
  - rewrite skipn_app, length_firstn, (Nat.min_l k (length bs)) by lia.
    rewrite skipn_all2 by (rewrite length_firstn; lia). cbn [app].
    rewrite skipn_app. rewrite skipn_all2 by lia. cbn [app].
    rewrite skipn_skipn. f_equal. f_equal. lia.
Qed.

Lemma hd_fld_same : forall bs k v, (k + 4 <= length bs)%nat ->
  fld_u32 (upd_bytes bs k (le4 v)) (Z.of_nat k) = bv_unsigned v mod 2 ^ 32.
Proof.
  intros bs k v H. unfold fld_u32, link_spec.rdn.
  pose proof (hd_slice_upd_same bs k (le4 v) ltac:(rewrite length_le4; lia)) as HS.
  rewrite length_le4 in HS. change (Z.of_nat 4) with 4 in HS. rewrite HS.
  apply bytes_le_to_Z_le4.
Qed.

Lemma hd_rdn_other : forall bs k xs off n, (k + length xs <= length bs)%nat -> 0 <= off -> 0 <= n ->
  (off + n <= Z.of_nat k \/ Z.of_nat k + Z.of_nat (length xs) <= off) ->
  link_spec.rdn (upd_bytes bs k xs) off n = link_spec.rdn bs off n.
Proof. intros. unfold link_spec.rdn. rewrite hd_slice_upd_other by assumption. reflexivity. Qed.

(* ==========================================================================
   model_begin's memory: c0_begin_mem (the memory part, reusable at any pc that runs model_begin)
   ========================================================================== *)

(* what model_begin leaves: g_nl.n_sent = 0; md->socket_errno / send_errno from the fake kernel,
   md->next = 0, md->n_req = 0 (fuzz_link.c:668-675) *)
Definition c0_kb (kbs : list byte) : list byte := upd_bytes kbs (Z.to_nat NK_N_SENT) (le4 (wz 0)).
Definition c0_mb (kbs mbs : list byte) : list byte :=
  upd_bytes (upd_bytes (upd_bytes (upd_bytes mbs 0 (le4 (wz (nk_socket_errno kbs))))
                                  4 (le4 (wz (nk_send_errno kbs))))
                       8 (le4 (wz 0)))
            (Z.to_nat MD_N_REQ) (le4 (wz 0)).

Lemma hd_mrd_keep : forall W m m' x, munch W m m' -> 0 <= x < 2 ^ 64 -> outside W x ->
  mrd rsegs m' (wa x) = mrd rsegs m (wa x).
Proof.
  intros W m m' x MU Hx O. unfold mrd. rewrite (MU (wa x)); [reflexivity|]. rewrite wa_unsigned by lia. exact O.
Qed.

Lemma hd_bytes_pt : forall m a bs i, bytes_at rsegs m a bs -> (i < length bs)%nat ->
  mrd rsegs m (wa (a + Z.of_nat i)) = nth_error bs i.
Proof. intros m a bs i (_ & _ & H) Hi. exact (H i Hi). Qed.

Ltac hd_upd_cases :=
  repeat match goal with
  | |- context [if (?k <=? ?i)%nat && (?i <? ?j)%nat then _ else _] =>
      destruct ((k <=? i)%nat && (i <? j)%nat) eqn:?
  end.

Lemma c0_begin_mem : forall m m' md kbs mbs,
  nlk_at m kbs -> model_at m md mbs -> apart md MD_SIZE A_G_NL NK_SIZE ->
  munch [(md, md + 12); (md + MD_N_REQ, md + MD_N_REQ + 4); (A_G_NL + NK_N_SENT, A_G_NL + NK_N_SENT + 4)] m m' ->
  wmono rsegs m m' ->
  bytes_at rsegs m' md (le4 (wz (nk_socket_errno kbs))) ->
  bytes_at rsegs m' (md + 4) (le4 (wz (nk_send_errno kbs))) ->
  bytes_at rsegs m' (md + 8) (le4 (wz 0)) ->
  bytes_at rsegs m' (md + MD_N_REQ) (le4 (wz 0)) ->
  bytes_at rsegs m' (A_G_NL + NK_N_SENT) (le4 (wz 0)) ->
  nlk_at m' (c0_kb kbs) /\ model_at m' md (c0_mb kbs mbs).
Proof.
  intros m m' md kbs mbs ((NB & NW) & NL) ((MB & MW) & ML) AP MU WM B0 B4 B8 BR BS.
  pose proof (bytes_at_bound _ _ _ _ NB) as NBd. pose proof (bytes_at_bound _ _ _ _ MB) as MBd.
  unfold c0_kb, c0_mb, apart, MD_SIZE, NK_SIZE, MD_N_REQ, NK_N_SENT, A_G_NL in *.
  set (X1 := upd_bytes mbs 0 (le4 (wz (nk_socket_errno kbs)))).
  set (X2 := upd_bytes X1 4 (le4 (wz (nk_send_errno kbs)))).
  set (X3 := upd_bytes X2 8 (le4 (wz 0))).
  set (K1 := upd_bytes kbs (Z.to_nat 271016) (le4 (wz 0))).
  assert (L1 : length X1 = length mbs) by (apply upd_bytes_length; rewrite length_le4; lia).
  assert (L2 : length X2 = length mbs) by (unfold X2; rewrite upd_bytes_length; [exact L1|rewrite length_le4, L1; lia]).
  assert (L3 : length X3 = length mbs) by (unfold X3; rewrite upd_bytes_length; [exact L2|rewrite length_le4, L2; lia]).
  assert (L4 : length (upd_bytes X3 (Z.to_nat 8336) (le4 (wz 0))) = length mbs)
    by (rewrite upd_bytes_length; [exact L3|rewrite length_le4, L3; lia]).
  assert (LK : length K1 = length kbs) by (apply upd_bytes_length; rewrite length_le4; lia).
  split; split; [split| |split|]; try unfold A_G_NL, NK_SIZE, MD_SIZE.
  - split; [lia|]. split; [rewrite LK; lia|].
    intros i Hi. rewrite LK in Hi. unfold K1.
    rewrite upd_bytes_nth by (rewrite ?length_le4; lia). rewrite length_le4.
    destruct ((Z.to_nat 271016 <=? i)%nat && (i <? Z.to_nat 271016 + 4)%nat) eqn:E.
    + apply andb_prop in E as [E1 E2]. apply Nat.leb_le in E1. apply Nat.ltb_lt in E2.
      rewrite <- (hd_bytes_pt _ _ _ (i - Z.to_nat 271016)%nat BS ltac:(rewrite length_le4; lia)).
      f_equal. f_equal. lia.
    + apply andb_false_iff in E. rewrite Nat.leb_gt, Nat.ltb_ge in E.
      rewrite (hd_mrd_keep _ _ _ _ MU) by (first [lia | cbn [outside]; lia]).
      exact (hd_bytes_pt _ _ _ _ NB Hi).
  - rewrite LK. exact (wr_at_transport rsegs m m' _ _ NW WM).
  - rewrite LK. exact NL.
  - split; [lia|]. split; [rewrite L4; lia|].
    intros i Hi. rewrite L4 in Hi.
    rewrite upd_bytes_nth by (rewrite ?length_le4, ?L3; lia). rewrite length_le4.
    destruct ((Z.to_nat 8336 <=? i)%nat && (i <? Z.to_nat 8336 + 4)%nat) eqn:E4.
    { apply andb_prop in E4 as [E1 E2]. apply Nat.leb_le in E1. apply Nat.ltb_lt in E2.
      rewrite <- (hd_bytes_pt _ _ _ (i - Z.to_nat 8336)%nat BR ltac:(rewrite length_le4; lia)).
      f_equal. f_equal. lia. }
    apply andb_false_iff in E4. rewrite Nat.leb_gt, Nat.ltb_ge in E4.
    unfold X3. rewrite upd_bytes_nth by (rewrite ?length_le4, ?L2; lia). rewrite length_le4.
    destruct ((8 <=? i)%nat && (i <? 8 + 4)%nat) eqn:E3.
    { apply andb_prop in E3 as [E1 E2]. apply Nat.leb_le in E1. apply Nat.ltb_lt in E2.
      rewrite <- (hd_bytes_pt _ _ _ (i - 8)%nat B8 ltac:(rewrite length_le4; lia)).
      f_equal. f_equal. lia. }
    apply andb_false_iff in E3. rewrite Nat.leb_gt, Nat.ltb_ge in E3.
    unfold X2. rewrite upd_bytes_nth by (rewrite ?length_le4, ?L1; lia). rewrite length_le4.
    destruct ((4 <=? i)%nat && (i <? 4 + 4)%nat) eqn:E2.
    { apply andb_prop in E2 as [E1 E2']. apply Nat.leb_le in E1. apply Nat.ltb_lt in E2'.
      rewrite <- (hd_bytes_pt _ _ _ (i - 4)%nat B4 ltac:(rewrite length_le4; lia)).
      f_equal. f_equal. lia. }
    apply andb_false_iff in E2. rewrite Nat.leb_gt, Nat.ltb_ge in E2.
    unfold X1. rewrite upd_bytes_nth by (rewrite ?length_le4; lia). rewrite length_le4.
    destruct ((0 <=? i)%nat && (i <? 0 + 4)%nat) eqn:E1.
    { apply andb_prop in E1 as [E1 E1']. apply Nat.ltb_lt in E1'.
      rewrite <- (hd_bytes_pt _ _ _ (i - 0)%nat B0 ltac:(rewrite length_le4; lia)).
      f_equal. f_equal. lia. }
    apply andb_false_iff in E1. rewrite Nat.leb_gt, Nat.ltb_ge in E1.
    rewrite (hd_mrd_keep _ _ _ _ MU) by (first [lia | cbn [outside]; lia]).
    exact (hd_bytes_pt _ _ _ _ MB Hi).
  - rewrite L4. exact (wr_at_transport rsegs m m' _ _ MW WM).
  - rewrite L4. exact ML.
Qed.

Lemma hd_len4 : forall bs k v, (k + 4 <= length bs)%nat -> length (upd_bytes bs k (le4 v)) = length bs.
Proof. intros. apply upd_bytes_length. rewrite length_le4. exact H. Qed.

Ltac hd_len := repeat (rewrite hd_len4; [|hd_len]); lia.

Lemma hd_rdn4 : forall bs k v off n, (k + 4 <= length bs)%nat -> 0 <= off -> 0 <= n ->
  (off + n <= Z.of_nat k \/ Z.of_nat k + 4 <= off) ->
  link_spec.rdn (upd_bytes bs k (le4 v)) off n = link_spec.rdn bs off n.
Proof. intros. apply hd_rdn_other; rewrite ?length_le4; assumption. Qed.

Lemma hd_slice4 : forall bs k v off n, (k + 4 <= length bs)%nat -> 0 <= off -> 0 <= n ->
  (off + n <= Z.of_nat k \/ Z.of_nat k + 4 <= off) ->
  slice (upd_bytes bs k (le4 v)) off n = slice bs off n.
Proof. intros. apply hd_slice_upd_other; rewrite ?length_le4; assumption. Qed.

Lemma hd_fld_at : forall bs k v off, (k + 4 <= length bs)%nat -> off = Z.of_nat k ->
  fld_u32 (upd_bytes bs k (le4 v)) off = bv_unsigned v mod 2 ^ 32.
Proof. intros bs k v off H ->. exact (hd_fld_same bs k v H). Qed.
Lemma hd_rdn_at : forall bs k v off, (k + 4 <= length bs)%nat -> off = Z.of_nat k ->
  link_spec.rdn (upd_bytes bs k (le4 v)) off 4 = bv_unsigned v mod 2 ^ 32.
Proof. intros bs k v off H E. exact (hd_fld_at bs k v off H E). Qed.

Lemma c0_begin_lists : forall gbs kbs mbs,
  Z.of_nat (length kbs) = NK_SIZE -> Z.of_nat (length mbs) = MD_SIZE ->
  nlk_wf kbs -> model_wf mbs -> marks_are gbs mbs ->
  nk_next kbs = 0 -> nk_opened kbs = nk_closed kbs ->
  nlk_wf (c0_kb kbs) /\ model_wf (c0_mb kbs mbs) /\ marks_are gbs (c0_mb kbs mbs) /\
  c0_begun (c0_kb kbs) (c0_mb kbs mbs) /\
  nk_open (c0_kb kbs) = nk_open kbs /\ nk_opened (c0_kb kbs) = nk_opened kbs /\
  nk_closed (c0_kb kbs) = nk_closed kbs /\ nk_misuse (c0_kb kbs) = nk_misuse kbs /\
  nk_n_if (c0_kb kbs) = nk_n_if kbs /\ nk_socket_errno (c0_kb kbs) = nk_socket_errno kbs /\
  nk_send_errno (c0_kb kbs) = nk_send_errno kbs /\
  Z.of_nat (length (c0_kb kbs)) = NK_SIZE /\ Z.of_nat (length (c0_mb kbs mbs)) = MD_SIZE.
Proof.
  intros gbs kbs mbs LK LM NW MW MA NX OC.
  unfold NK_SIZE, MD_SIZE in LK, LM.
  assert (FK : forall off n, 0 <= off -> 0 <= n -> off + n <= NK_N_SENT \/ NK_N_SENT + 4 <= off ->
                 link_spec.rdn (c0_kb kbs) off n = link_spec.rdn kbs off n).
  { intros off n H0 H1 H2. unfold c0_kb, NK_N_SENT in *. apply hd_rdn4; lia. }
  assert (FM : forall off n, 0 <= off -> 0 <= n -> MD_N_REQ + 4 <= off ->
                 link_spec.rdn (c0_mb kbs mbs) off n = link_spec.rdn mbs off n).
  { intros off n H0 H1 H2. unfold c0_mb, MD_N_REQ in *.
    rewrite !hd_rdn4 by (first [hd_len | lia]). reflexivity. }
  assert (SM : forall off n, 0 <= off -> 0 <= n -> MD_N_REQ + 4 <= off ->
                 slice (c0_mb kbs mbs) off n = slice mbs off n).
  { intros off n H0 H1 H2. unfold c0_mb, MD_N_REQ in *.
    rewrite !hd_slice4 by (first [hd_len | lia]). reflexivity. }
  assert (KS : nk_n_sent (c0_kb kbs) = 0).
  { unfold nk_n_sent, c0_kb, NK_N_SENT. rewrite hd_fld_at by (first [lia | rewrite Z2Nat.id; lia]).
    reflexivity. }
  assert (Wse : 0 <= nk_socket_errno kbs < 2 ^ 31) by (unfold nlk_wf in NW; tauto).
  assert (Wsd : 0 <= nk_send_errno kbs < 2 ^ 31) by (unfold nlk_wf in NW; tauto).
  assert (MS0 : md_socket_errno (c0_mb kbs mbs) = nk_socket_errno kbs).
  { unfold md_socket_errno, c0_mb, MD_SOCKET_ERRNO, MD_N_REQ, fld_u32.
    rewrite !hd_rdn4 by (first [hd_len | lia]).
    rewrite hd_rdn_at by (first [lia | reflexivity]). unfold wz. rewrite unsigned_lit by lia.
    apply Z.mod_small. lia. }
  assert (MS4 : md_send_errno (c0_mb kbs mbs) = nk_send_errno kbs).
  { unfold md_send_errno, c0_mb, MD_SEND_ERRNO, MD_N_REQ, fld_u32.
    rewrite !hd_rdn4 by (first [hd_len | lia]).
    rewrite hd_rdn_at by (first [hd_len | reflexivity]). unfold wz. rewrite unsigned_lit by lia.
    apply Z.mod_small. lia. }
  assert (MS8 : md_next (c0_mb kbs mbs) = 0).
  { unfold md_next, c0_mb, MD_NEXT, MD_N_REQ, fld_u32.
    rewrite hd_rdn4 by (first [hd_len | lia]).
    rewrite hd_rdn_at by (first [hd_len | reflexivity]). reflexivity. }
  assert (MSR : md_n_req (c0_mb kbs mbs) = 0).
  { unfold md_n_req, c0_mb, MD_N_REQ.
    rewrite hd_fld_at by (first [hd_len | rewrite Z2Nat.id; lia]). reflexivity. }
  assert (EF : forall off, 0 <= off -> off + 4 <= NK_N_SENT \/ NK_N_SENT + 4 <= off ->
                 fld_u32 (c0_kb kbs) off = fld_u32 kbs off).
  { intros off H0 H1. unfold fld_u32. apply FK; lia. }
  assert (EF8 : forall off, 0 <= off -> off + 8 <= NK_N_SENT ->
                 fld_u64 (c0_kb kbs) off = fld_u64 kbs off).
  { intros off H0 H1. unfold fld_u64. apply FK; lia. }
  assert (Echk : nk_n_chunks (c0_kb kbs) = nk_n_chunks kbs) by (apply EF; unfold NK_N_CHUNKS, NK_N_SENT; lia).
  assert (Enxt : nk_next (c0_kb kbs) = nk_next kbs) by (apply EF; unfold NK_NEXT, NK_N_SENT; lia).
  assert (Eend : nk_end_errno (c0_kb kbs) = nk_end_errno kbs) by (apply EF; unfold NK_END_ERRNO, NK_N_SENT; lia).
  assert (Esck : nk_socket_errno (c0_kb kbs) = nk_socket_errno kbs)
    by (apply EF; unfold NK_SOCKET_ERRNO, NK_N_SENT; lia).
  assert (Esnd : nk_send_errno (c0_kb kbs) = nk_send_errno kbs)
    by (apply EF; unfold NK_SEND_ERRNO, NK_N_SENT; lia).
  assert (Eopn : nk_open (c0_kb kbs) = nk_open kbs) by (apply EF; unfold NK_OPEN, NK_N_SENT; lia).
  assert (Eopd : nk_opened (c0_kb kbs) = nk_opened kbs) by (apply EF; unfold NK_OPENED, NK_N_SENT; lia).
  assert (Ecls : nk_closed (c0_kb kbs) = nk_closed kbs) by (apply EF; unfold NK_CLOSED, NK_N_SENT; lia).
  assert (Emis : nk_misuse (c0_kb kbs) = nk_misuse kbs) by (apply EF; unfold NK_MISUSE, NK_N_SENT; lia).
  assert (Enif : nk_n_if (c0_kb kbs) = nk_n_if kbs) by (apply EF; unfold NK_N_IF, NK_N_SENT; lia).
  assert (Enmk : md_n_mark (c0_mb kbs mbs) = md_n_mark mbs)
    by (unfold md_n_mark, fld_u32; apply FM; unfold MD_N_MARK, MD_N_REQ; lia).
  assert (LKb : Z.of_nat (length (c0_kb kbs)) = 271992) by (unfold c0_kb, NK_N_SENT; hd_len).
  assert (LMb : Z.of_nat (length (c0_mb kbs mbs)) = 8856) by (unfold c0_mb, MD_N_REQ; hd_len).
  assert (A1 : nlk_wf (c0_kb kbs)).
  { destruct NW as (W1 & W2 & W3 & W4 & W5 & W6 & W7 & W8 & W9 & W10 & W11 & W12 & W13).
    unfold nlk_wf. rewrite Echk, Enxt, KS, Enif, Eopn, Eopd, Ecls, Emis, Eend, Esck, Esnd.
    split; [exact W1|]. split; [exact W2|]. split; [unfold NL_SENT_MAX; lia|].
    split; [exact W4|]. split; [exact W5|]. split; [exact W6|]. split; [exact W7|]. split; [exact W8|].
    split; [exact W9|]. split; [exact W10|]. split; [exact W11|]. split.
    - intros i Hi. rewrite EF8 by (unfold NK_CHUNK_LEN, NK_N_SENT, NL_CHUNKS in *; lia). exact (W12 i Hi).
    - intros i Hi. lia. }
  assert (A2 : model_wf (c0_mb kbs mbs)).
  { destruct MW as (V1 & V2 & V3 & V4 & V5 & (V6 & V7)).
    unfold model_wf, model_marks_wf. rewrite MSR, MS8, MS0, MS4, Enmk.
    split; [unfold NL_SENT_MAX; lia|]. split; [lia|]. split; [exact Wse|]. split; [exact Wsd|].
    split; [intros i Hi; lia|]. split; [exact V6|].
    intros i Hi. rewrite SM by (unfold MD_MARK, MARK_LEN, MD_N_REQ; lia). exact (V7 i Hi). }
  assert (A3 : marks_are gbs (c0_mb kbs mbs)).
  { destruct MA as [MA1 MA2]. split; [rewrite Enmk; exact MA1|]. rewrite MA2.
    unfold md_marks. rewrite Enmk. apply map_ext. intros j.
    rewrite SM by (unfold MD_MARK, MARK_LEN, MD_N_REQ; lia). reflexivity. }
  assert (A4 : c0_begun (c0_kb kbs) (c0_mb kbs mbs)).
  { unfold c0_begun. rewrite Enxt, KS, MS8, MSR, MS0, MS4, Esck, Esnd, Eopd, Ecls.
    split; [exact NX|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    split; [reflexivity|]. split; [reflexivity|]. exact OC. }
  unfold NK_SIZE, MD_SIZE.
  exact (conj A1 (conj A2 (conj A3 (conj A4 (conj Eopn (conj Eopd (conj Ecls (conj Emis
          (conj Enif (conj Esck (conj Esnd (conj LKb LMb)))))))))))).
Qed.

(* ==========================================================================
   Small facts the assembly uses
   ========================================================================== *)

Lemma hd_q_ext : forall Q, q_ext (eqv_cl Q).
Proof.
  intros Q c a (c0 & H0 & E0) E. exists c0. split; [exact H0|]. exact (c0_ms_eqv_trans _ _ _ E0 E).
Qed.

Lemma hd_le4_sx32 : forall v : word, le4 (sx32 v) = le4 v.
Proof.
  intros v. unfold le4, sx32. rewrite Z_to_bv_unsigned.
  rewrite <- (Z_to_le_bytes_mod 4 _ 32) by lia. rewrite <- (Z_to_le_bytes_mod 4 (bv_unsigned v) 32) by lia.
  f_equal. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  change (2 ^ Z.of_N 32) with (2 ^ 32). change (2 ^ Z.of_N 64) with (2 ^ 64).
  rewrite (Z.mod_mod_divide _ (2 ^ 64) (2 ^ 32)) by (exists (2 ^ 32); reflexivity).
  rewrite Zminus_mod_idemp_l. f_equal. lia.
Qed.

Lemma hd_u8_c4 : forall m A bs off, u8arr rsegs m A bs -> 0 <= off -> off + 4 <= Z.of_nat (length bs) ->
  rw_cells rsegs m (A + off) [C4 (wz (fld_u32 bs off))].
Proof.
  intros m A bs off (B & W) H0 H4. split; [split|].
  - cbn. tauto.
  - cbn [cells_bytes cbytes]. rewrite app_nil_r. rewrite hd_le4_slice by lia.
    pose proof (c0_bytes_skip m A bs (Z.to_nat off) B ltac:(lia)) as Bs. rewrite Z2Nat.id in Bs by lia.
    rewrite <- (firstn_skipn 4 (skipn (Z.to_nat off) bs)) in Bs. apply bytes_at_app in Bs as [Bs _]. exact Bs.
  - cbn [cells_size csize]. apply (c0_wr_sub m A _ off 4 W); lia.
Qed.

Lemma hd_cursor_adv : forall m p0 pl P N d, cursor_ok m p0 pl P N -> 0 <= d <= N ->
  cursor_ok m p0 pl (P + d) (N - d).
Proof.
  intros m p0 pl P N d (B & k & Hk & -> & ->) Hd. split; [exact B|]. exists (k + d). lia.
Qed.

Lemma hd_iftab_nif : forall m bs bs' tab, iftab_at m bs tab -> nk_n_if bs' = nk_n_if bs -> iftab_at m bs' tab.
Proof. intros m bs bs' tab (H1 & H2 & H3) E. split; [rewrite E; exact H1|]. split; assumption. Qed.

Lemma hd_outside_app : forall W1 W2 x, outside (W1 ++ W2) x <-> outside W1 x /\ outside W2 x.
Proof.
  induction W1 as [|[lo hi] W1 IH]; intros W2 x; cbn; [tauto|]. rewrite IH. tauto.
Qed.

Lemma hd_not_outside : forall W x, ~ outside W x -> exists lo hi, In (lo, hi) W /\ lo <= x < hi.
Proof.
  induction W as [|[lo hi] W IH]; cbn; intros x H.
  - exfalso. apply H. exact I.
  - destruct (Z_le_dec lo x) as [L|L]; [destruct (Z_lt_dec x hi) as [R|R]|].
    + exists lo, hi. split; [left; reflexivity | lia].
    + destruct (IH x) as (lo' & hi' & I & Hr); [intros O; apply H; split; [lia | exact O]|].
      exists lo', hi'. split; [right; exact I | exact Hr].
    + destruct (IH x) as (lo' & hi' & I & Hr); [intros O; apply H; split; [lia | exact O]|].
      exists lo', hi'. split; [right; exact I | exact Hr].
Qed.

Lemma hd_seg_fp : forall S hp m0 m' W, munch W m0 m' -> wmono rsegs m0 m' ->
  (forall lo hi x, In (lo, hi) W -> lo <= x < hi -> own_w S hp x) -> seg_fp S hp m0 m'.
Proof.
  intros S hp m0 m' W MU WM H. exists W. split; [exact MU|]. split; [exact WM|].
  intros x _ Ho. destruct (hd_not_outside W x Ho) as (lo & hi & I & Hr). exact (H lo hi x I Hr).
Qed.

Lemma hd_munch3 : forall W1 W2 W3 m0 m1 m2 m3, munch W1 m0 m1 -> munch W2 m1 m2 -> munch W3 m2 m3 ->
  munch (W1 ++ W2 ++ W3) m0 m3.
Proof.
  intros W1 W2 W3 m0 m1 m2 m3 M1 M2 M3 x Hx.
  apply hd_outside_app in Hx as [H1 Hx]. apply hd_outside_app in Hx as [H2 H3].
  rewrite (M3 x H3), (M2 x H2). exact (M1 x H1).
Qed.

(* c0_base across a write set inside the arm's own frame or stack window *)
Lemma hd_base_keep : forall E P N kbs mbs gbs m m' W lo hi, lenv_ok E ->
  c0_base E P N kbs mbs gbs m -> munch W m m' -> wmono rsegs m m' -> mem_inv rsegs m' ->
  stk rsegs m' (e_S E - SLOT_STACK_Z) (e_S E - SLOT_FRAME) ->
  c0_in W lo hi -> e_S E - SLOT_STACK_Z <= lo -> hi <= e_S E - 104 ->
  c0_base E P N kbs mbs gbs m'.
Proof.
  intros E P N kbs mbs gbs m m' W lo hi HE
    (SV & NL & NW & IT & NO & NM & GN & OD & PO & LA & TX & IP & MD & MW & MK & KW & MA & CU & ER & GU & MI & TM & ST)
    MU WM MI' ST' HW Hlo Hhi.
  destruct HE as (HS1 & HS2 & _ & (D1 & D2 & _) & (K1 & K2 & _) & _ & _ & _ & HPL & (P1 & P2 & _) & _ & _ & HSV).
  assert (Img : c0_out W 0x10000 (0x960e0 - 0x10000))
    by (apply (c0_out_in W _ _ _ _ HW); c0_unf; lia).
  assert (OF : c0_wfix W) by (split; eapply c0_out_sub; [exact Img|c0_unf; lia|c0_unf; lia|exact Img|c0_unf; lia|c0_unf; lia]).
  unfold c0_base. repeat match goal with |- _ /\ _ => split end.
  - apply (c0_bytes_keep W m m' _ _ SV MU). apply (c0_out_in W _ _ _ _ HW); rewrite ?HSV; c0_unf; lia.
  - apply (c0_nlk_keep W m m' _ NL MU WM). eapply c0_out_sub; [exact Img|c0_unf; lia|c0_unf; lia].
  - exact NW.
  - apply (c0_iftab_keep W m m' kbs IT IP MU); [eapply c0_out_sub; [exact Img|c0_unf; lia|c0_unf; lia] ..
      | exact OF].
  - exact NO.
  - exact NM.
  - apply (c0_gnames_keep W m m' GN MU). eapply c0_out_sub; [exact Img|c0_unf; lia|c0_unf; lia].
  - apply (c0_odd_keep W m m' OD MU); [eapply c0_out_sub; [exact Img|c0_unf; lia|c0_unf; lia] | exact OF].
  - apply (c0_policy_keep W m m' PO MU). exact (proj1 OF).
  - apply (c0_la_keep W m m' LA MU WM). eapply c0_out_sub; [exact Img|c0_unf; lia|c0_unf; lia].
  - apply (c0_texts_keep W m m' TX MU). eapply c0_out_sub; [exact Img|c0_unf; lia|c0_unf; lia].
  - apply (c0_ifptrs_keep W m m' IP MU). eapply c0_out_sub; [exact Img|c0_unf; lia|c0_unf; lia].
  - apply (c0_model_keep W m m' _ _ MD MU WM). apply (c0_out_in W _ _ _ _ HW); c0_unf; lia.
  - exact MW.
  - apply (c0_marks_keep W m m' _ _ MK MU WM). apply (c0_out_in W _ _ _ _ HW); c0_unf; lia.
  - exact KW.
  - exact MA.
  - apply (c0_cursor_keep W m m' _ _ _ _ CU MU). apply (c0_out_in W _ _ _ _ HW); c0_unf; lia.
  - exact (wr_at_transport rsegs m m' _ _ ER WM).
  - apply (c0_guard_keep W m m' GU MU); (eapply c0_out_sub; [exact Img|c0_unf; lia|c0_unf; lia]).
  - exact MI'.
  - apply (c0_task_mem_in W m m' _ _ TM MU HW). c0_unf; lia.
  - exact ST'.
Qed.

(* the kernel's writes: its frame, the chunk queue of g_nl, long_alias and the 16 cursor bytes *)
Definition hd_WK (E : lenv) : list ivl :=
  (e_S E - SLOT_FRAME - 4416, e_S E - SLOT_FRAME) ::
  [(A_G_NL + NK_CHUNK, A_G_NL + NK_OPEN); (A_LONG_ALIAS, A_LONG_ALIAS + LONG_ALIAS_SIZE);
   (e_S E - SLOT_FRAME + FO_P, e_S E - SLOT_FRAME + FO_P + 16)].

Ltac hd_out := apply c0_out_disj; cbn [disjoint_from]; unfold NK_CHUNK, NK_OPEN, NK_N_SENT in *; c0_unf; lia.

Lemma hd_kern_base : forall E P N P2 N2 kbs kbs' mbs gbs m m',
  lenv_ok E -> c0_base E P N kbs mbs gbs m ->
  munch (hd_WK E) m m' -> wmono rsegs m m' -> mem_inv rsegs m' ->
  stk rsegs m' (e_S E - SLOT_STACK_Z) (e_S E - SLOT_FRAME) ->
  nlk_at m' kbs' -> nlk_wf kbs' -> iftab_at m' kbs' link_tab ->
  nk_open kbs' = nk_open kbs -> nk_misuse kbs' = nk_misuse kbs ->
  (exists la, rw_cells rsegs m' A_LONG_ALIAS [CB (Z.to_nat 300) la; C1 (zb 0)]) ->
  (exists k, 0 <= k <= Z.of_nat (length (e_pl E)) /\ P2 = e_p0 E + k /\ N2 = Z.of_nat (length (e_pl E)) - k) ->
  c0_base E P2 N2 kbs' mbs gbs m'.
Proof.
  intros E P N P2 N2 kbs kbs' mbs gbs m m' HE
    (SV & NL & NW & IT & NO & NM & GN & OD & PO & LA & TX & IP & MD & MW & MK & KW & MA & CU & ER & GU & MI & TM & ST)
    MU WM MI' ST' NL' NW' IT' EO EM LA' K2.
  pose proof HE as HE'.
  destruct HE' as (HS1 & HS2 & _ & (D1 & D2 & D3) & (K1 & K2' & K3) & _ & _ & _ & HPL & (P1 & P2' & P3) & _ & _ & HSV).
  destruct (c0_img_named _ _ D3 ltac:(c0_unf; lia)) as (DG & _ & DL & _).
  destruct (c0_img_named _ _ K3 ltac:(c0_unf; lia)) as (KG & _ & KL & _).
  destruct (c0_img_named _ _ P3 ltac:(c0_unf; lia)) as (PG & _ & PL & _).
  unfold apart_gnl, apart in DG, DL, KG, KL, PG, PL. unfold hd_WK in MU.
  destruct (c0_ro_keep _ m m' GN OD PO TX IP GU MU) as (GN' & OD' & PO' & TX' & IP' & GU'); try hd_out.
  unfold c0_base. repeat match goal with |- _ /\ _ => split end.
  - apply (c0_bytes_keep _ m m' _ _ SV MU). rewrite HSV. hd_out.
  - exact NL'.
  - exact NW'.
  - exact IT'.
  - rewrite EO. exact NO.
  - rewrite EM. exact NM.
  - exact GN'.
  - exact OD'.
  - exact PO'.
  - destruct LA as (la & sl & _ & SL & L3). destruct LA' as (la' & R').
    exists la', sl. split; [exact R'|]. split; [|exact L3].
    apply (c0_bytes_keep _ m m' _ _ SL MU). rewrite L3. hd_out.
  - exact TX'.
  - exact IP'.
  - apply (c0_model_keep _ m m' _ _ MD MU WM). hd_out.
  - exact MW.
  - apply (c0_marks_keep _ m m' _ _ MK MU WM). hd_out.
  - exact KW.
  - exact MA.
  - destruct CU as (CB & _). split; [|exact K2]. apply (c0_bytes_keep _ m m' _ _ CB MU). hd_out.
  - exact (wr_at_transport rsegs m m' _ _ ER WM).
  - exact GU'.
  - exact MI'.
  - apply (c0_task_mem_in _ m m' A_G_NL (e_S E) TM MU).
    + intros x Hx Ho. cbn [outside] in Ho. unfold NK_CHUNK, NK_OPEN in *. c0_unf. lia.
    + exact HS2.
  - exact ST'.
Qed.

(* model_begin's writes: the first 12 bytes and n_req of md, n_sent of g_nl (474664) *)
Definition hd_WB (E : lenv) : list ivl :=
  [(e_md E, e_md E + 12); (e_md E + 8336, e_md E + 8340); (474664, 474668)].

Lemma hd_begin_base : forall E P N kbs mbs kbs' mbs' gbs m m',
  lenv_ok E -> c0_base E P N kbs mbs gbs m ->
  munch (hd_WB E) m m' -> wmono rsegs m m' -> mem_inv rsegs m' ->
  nlk_at m' kbs' -> nlk_wf kbs' -> model_at m' (e_md E) mbs' -> model_wf mbs' -> marks_are gbs mbs' ->
  nk_open kbs' = nk_open kbs -> nk_misuse kbs' = nk_misuse kbs -> nk_n_if kbs' = nk_n_if kbs ->
  c0_base E P N kbs' mbs' gbs m'.
Proof.
  intros E P N kbs mbs kbs' mbs' gbs m m' HE
    (SV & NL & NW & IT & NO & NM & GN & OD & PO & LA & TX & IP & MD & MW & MK & KW & MA & CU & ER & GU & MI & TM & ST)
    MU WM MI' NL' NW' MD' MW' MA' EO EM EI.
  pose proof HE as HE'.
  destruct HE' as (HS1 & HS2 & _ & (D1 & D2 & D3) & (K1 & K2' & K3) & _ & _ & DK & HPL & (P1 & P2' & P3) & DP & KP & HSV).
  destruct (c0_img_named _ _ D3 ltac:(c0_unf; lia)) as (DG & DN & DL & DT & DO & DE & DQ1 & DQ2 & DR).
  destruct (c0_img_named _ _ K3 ltac:(c0_unf; lia)) as (KG & _ & KL & _).
  destruct (c0_img_named _ _ P3 ltac:(c0_unf; lia)) as (PG & _ & PL & _).
  unfold apart_gnl, apart in DG, DN, DL, DT, DO, DE, DQ1, DQ2, DR, KG, KL, PG, PL. unfold hd_WB in MU.
  destruct (c0_ro_keep _ m m' GN OD PO TX IP GU MU) as (GN' & OD' & PO' & TX' & IP' & GU'); try hd_out.
  unfold c0_base. repeat match goal with |- _ /\ _ => split end.
  - apply (c0_bytes_keep _ m m' _ _ SV MU). rewrite HSV. hd_out.
  - exact NL'.
  - exact NW'.
  - apply (hd_iftab_nif m' kbs); [|exact EI].
    apply (c0_iftab_keep _ m m' kbs IT IP MU); try hd_out.
    split; hd_out.
  - rewrite EO. exact NO.
  - rewrite EM. exact NM.
  - exact GN'.
  - exact OD'.
  - exact PO'.
  - apply (c0_la_keep _ m m' LA MU WM). hd_out.
  - exact TX'.
  - exact IP'.
  - exact MD'.
  - exact MW'.
  - apply (c0_marks_keep _ m m' _ _ MK MU WM). hd_out.
  - exact KW.
  - exact MA'.
  - apply (c0_cursor_keep _ m m' _ _ _ _ CU MU). hd_out.
  - exact (wr_at_transport rsegs m m' _ _ ER WM).
  - exact GU'.
  - exact MI'.
  - apply (c0_task_mem_in _ m m' 0 (e_S E) TM MU).
    + intros x Hx Ho. cbn [outside] in Ho. c0_unf. lia.
    + exact HS2.
  - apply (stk_transport_disjoint rsegs _ m m' _ _ ST MU WM). cbn [disjoint_from]. c0_unf. lia.
Qed.

(* ==========================================================================
   The frame cells around the cursor, and segment S1
   ========================================================================== *)

Definition hd_c8 (j0 : list byte) (c16 c24 c32 c56 : word) : list cell :=
  [CB 8 j0; C8 (wz A_ODD); C8 c16; C8 c24; C8 c32; C8 (wz A_G_NAMES); C8 (wz A_JT); C8 c56].

Lemma hd_cells_split : forall m a P nc j0 c16 c24 c32 c56 j1 j2,
  rw_cells rsegs m a (hd_cells P nc j0 c16 c24 c32 c56 j1 j2) ->
  rw_cells rsegs m a (hd_c8 j0 c16 c24 c32 c56) /\
  rw_cells rsegs m (a + 64) [C8 (wz P); C8 (wz nc)] /\
  rw_cells rsegs m (a + 80) [CB 40 j1; CB 256 j2].
Proof.
  intros m a P nc j0 c16 c24 c32 c56 j1 j2 H.
  change (hd_cells P nc j0 c16 c24 c32 c56 j1 j2) with
    (hd_c8 j0 c16 c24 c32 c56 ++ [C8 (wz P); C8 (wz nc)] ++ [CB 40 j1; CB 256 j2]) in H.
  apply c0_rw_app in H as [H1 H2]. apply c0_rw_app in H2 as [H2 H3].
  replace (a + Z.of_nat (cells_size (hd_c8 j0 c16 c24 c32 c56))) with (a + 64) in H2, H3 by (cbn; lia).
  replace (a + 64 + Z.of_nat (cells_size [C8 (wz P); C8 (wz nc)])) with (a + 80) in H3 by (cbn; lia).
  auto.
Qed.

Lemma hd_cells_join : forall m a P nc j0 c16 c24 c32 c56 j1 j2,
  rw_cells rsegs m a (hd_c8 j0 c16 c24 c32 c56) ->
  rw_cells rsegs m (a + 64) [C8 (wz P); C8 (wz nc)] ->
  rw_cells rsegs m (a + 80) [CB 40 j1; CB 256 j2] ->
  rw_cells rsegs m a (hd_cells P nc j0 c16 c24 c32 c56 j1 j2).
Proof.
  intros m a P nc j0 c16 c24 c32 c56 j1 j2 H1 H2 H3.
  change (hd_cells P nc j0 c16 c24 c32 c56 j1 j2) with
    (hd_c8 j0 c16 c24 c32 c56 ++ [C8 (wz P); C8 (wz nc)] ++ [CB 40 j1; CB 256 j2]).
  apply c0_rw_join; [exact H1|].
  replace (a + Z.of_nat (cells_size (hd_c8 j0 c16 c24 c32 c56))) with (a + 64) by (cbn; lia).
  apply c0_rw_join; [exact H2|].
  replace (a + 64 + Z.of_nat (cells_size [C8 (wz P); C8 (wz nc)])) with (a + 80) by (cbn; lia).
  exact H3.
Qed.

Section S1.
Hypothesis KERN : kernel_contract.

Lemma c0_s1 : forall (E : lenv) (i : Z) (gp : word) (ms : machine_state),
  lenv_ok E -> lh_ms E i gp ms -> lh_op E ms 0 ->
  exists sel kc ac,
    evt rsegs (eqv_cl (fun ms' => (exists P N kbs' mbs' gbs, c0_cut_kc E i gp P N sel kc ac kbs' mbs' gbs ms') /\
                                  seg_fp (e_S E) (c0_hp2 E) (ms_mem ms) (ms_mem ms'))) ms.
Proof.
  intros E i gp ms HE HLH HOP.
  pose proof KERN as KL. rewrite c0_kernel_is in KL.
  destruct HLH as (ra & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & s3 & s4 & t3 & t4 & t5 & t6
    & F & fc & m & P & N & kbs & mbs & gbs & EQ & FC & Hi & HN & LM & MI & TM & ST).
  subst ms. cbn [ms_mem] in HOP |- *.
  destruct HOP as (P' & b & HP' & Hb & Hop).
  destruct LM as ((j0 & j1 & j2 & nc & CW) & SV & NL & NW & IT & NO & NM & OC & OI & GN & OD & PO & LA & TX & IP
    & MD & MW & MK & KW & MA & CU & ER & GU).
  pose proof HE as HE'.
  destruct HE' as (HS1 & HS2 & HS3 & (D1 & D2 & D3) & (K1 & K2 & K3) & _ & _ & DK & HPL & (Q1 & Q2 & Q3) & DP & KP & HSV).
  (* the base at the loop head *)
  assert (B0 : c0_base E P N kbs mbs gbs m)
    by exact (conj SV (conj NL (conj NW (conj IT (conj NO (conj NM (conj GN (conj OD (conj PO (conj LA
               (conj TX (conj IP (conj MD (conj MW (conj MK (conj KW (conj MA (conj CU (conj ER (conj GU
               (conj MI (conj TM ST)))))))))))))))))))))).
  (* the input suffix at the cursor *)
  pose proof CU as (PB & k & Hk & EP & EN).
  set (l := skipn (Z.to_nat k) (e_pl E)).
  assert (HBl : bytes_at rsegs m P l).
  { pose proof (c0_bytes_skip m _ _ (Z.to_nat k) PB ltac:(lia)) as H. rewrite Z2Nat.id in H by lia.
    rewrite EP. exact H. }
  assert (Ll : Z.of_nat (length l) = N) by (unfold l; rewrite length_skipn; lia).
  assert (USP : bv_unsigned (wz (e_S E - SLOT_FRAME)) = e_S E - SLOT_FRAME) by (apply c0_wz_u; c0_unf; lia).
  (* the frame as the head walk reads it *)
  assert (CWh : rw_cells rsegs m (e_S E - SLOT_FRAME)
                  (hd_cells P nc j0 (wz (e_md E + MD_MARK)) (wz A_EMPTY) (wz (e_mk E)) (wz GNL42) j1 j2))
    by exact CW.
  destruct (hd_cells_split _ _ _ _ _ _ _ _ _ _ _ CWh) as (_ & CC0 & _).
  (* the cell sp+0x40 holds P: P' = P *)
  assert (EPP : P' = P).
  { pose proof (bytes_at_bound _ _ _ _ Hb) as Rb.
    apply (c0_u64_eq m (e_S E - SLOT_FRAME + FO_P)); [exact HP' | | cbn in Rb; lia | c0_unf; lia].
    destruct CC0 as ((_ & CB0) & _). cbn [cells_bytes cbytes] in CB0.
    apply bytes_at_app in CB0 as [CB0 _]. unfold u64_at. unfold FO_P. exact CB0. }
  subst P'.
  (* the operation byte heads the suffix *)
  assert (Hb0 : c0_b l 0 = bz b).
  { unfold c0_b. pose proof (hd_bytes_pt _ _ _ 0 HBl ltac:(lia)) as E0.
    pose proof (hd_bytes_pt _ _ _ 0 Hb ltac:(cbn; lia)) as E1. cbn in E1. rewrite E1 in E0.
    destruct l as [|x l']; cbn in E0 |- *; [discriminate|]. inversion E0. reflexivity. }
  exists (c0_sel l), (c0_kc l), (c0_ac l).
  rewrite <- Ll.
  eapply evt_cut.
  { apply (hd_walkA ra gp (wz A_TP) t0 t1 t2 (wz (e_md E)) (wz GNL40) a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 (wz (e_mk E))
             (wz (e_md E + MD_N_REQ)) (wz i) t3 t4 t5 t6 F fc m (wz (e_S E - SLOT_FRAME)) P l nc j0
             (wz (e_md E + MD_MARK)) (wz A_EMPTY) (wz (e_mk E)) (wz GNL42) j1 j2);
      rewrite ?USP; try assumption.
    - lia.
    - rewrite Ll, EN, EP. c0_unf. lia.
    - c0_unf. lia.
    - c0_unf. lia.
    - lia.
    - rewrite Hb0. exact Hop. }
  intros ms1 (a1' & a2' & a3' & a4' & a5' & a6' & a7' & m1 & -> & MU1 & WM1 & MI1 & CW1).
  set (sp := wz (e_S E - SLOT_FRAME)) in *.
  set (Q0 := fun ms' => _) at 1.
  rewrite USP in MU1, CW1.
  (* the base after the head's cursor stores *)
  assert (ST1 : stk rsegs m1 (e_S E - SLOT_STACK_Z) (e_S E - SLOT_FRAME))
    by (apply (stk_transport_disjoint rsegs _ m m1 _ _ ST MU1 WM1); cbn [disjoint_from]; c0_unf; lia).
  assert (B1 : c0_base E P N kbs mbs gbs m1).
  { apply (hd_base_keep E P N kbs mbs gbs m m1 _ (e_S E - SLOT_FRAME + 64) (e_S E - SLOT_FRAME + 80) HE B0 MU1 WM1
             MI1 ST1); [apply c0_in_one | c0_unf; lia | c0_unf; lia]. }
  set (u := c0_used l) in *.
  assert (Hu : 0 <= u <= Z.of_nat (length l)) by (unfold u, c0_used; lia).
  destruct (hd_cells_split _ _ _ _ _ _ _ _ _ _ _ CW1) as (CA1 & CC1 & CZ1).
  (* kernel (in) at 0x13e24 *)
  eapply (leaf_call KERNEL 4416 c0_kernel_Pre c0_kernel_Wr c0_kernel_Post KL c0_kernel_post_ext _ (hd_q_ext _))
    with (lo := e_S E - SLOT_STACK_Z).
  { apply (c0_kernel_pre E _ m1 (P + u) (Z.of_nat (length l) - u) kbs HE).
    - rewrite mkR_sp. exact USP.
    - rewrite mkR_a0. rewrite USP. apply c0_wz_u. c0_unf. lia.
    - exact CC1.
    - destruct B1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & CU1 & _).
      rewrite Ll. apply hd_cursor_adv; [exact CU1 | lia].
    - exact (proj1 (proj2 B1)).
    - exact (proj1 (proj2 (proj2 B1))).
    - exact (proj1 (proj2 (proj2 (proj2 B1)))).
    - destruct B1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & IP1 & _). exact IP1.
    - destruct B1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & TX1 & _). exact TX1.
    - destruct B1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & LA1 & _). exact LA1.
    - exact MI1. }
  { exact MI1. }
  { rewrite USP. exact ST1. }
  { rewrite USP. c0_unf. lia. }
  { rewrite USP. c0_unf. lia. }
  intros ra2 t02 t12 t22 a02 a12 a22 a32 a42 a52 a62 a72 t32 t42 t52 t62 m2 MUk WMk MI2 ST2 POST.
  unfold c0_kernel_Post in POST. unfold c0_kernel_Wr in MUk. cbv beta in POST, MUk.
  rewrite ?mkR_a0, USP in MUk.
  assert (UA : bv_unsigned (wz (e_S E - SLOT_FRAME + 64)) = e_S E - SLOT_FRAME + 64) by (apply c0_wz_u; c0_unf; lia).
  rewrite UA in MUk.
  assert (MUK : munch (hd_WK E) m1 m2) by (unfold hd_WK, FO_P; exact MUk).
  clear MUk.
  destruct (POST kbs (proj1 (proj2 B1))) as (kbs' & NL2 & NW2 & NX2 & NCH2 & EE2 & SE2 & SD2 & EO2 & EOD2 & ECL2
    & EMI2 & ENS2 & ESN2 & ENI2 & ITf & CUR & LA2).
  clear POST.
  rewrite mkR_a0, USP, UA in CUR.
  destruct (CUR _ _ CC1) as (adv & Hadv & CC2). clear CUR.
  idtac.
  assert (UPu : bv_unsigned (wz (P + u)) = P + u) by (apply c0_wz_u; rewrite Ll in Hu; c0_unf; lia).
  assert (UNu : bv_unsigned (wz (Z.of_nat (length l) - u)) = Z.of_nat (length l) - u)
    by (apply c0_wz_u; c0_unf; lia).
  rewrite UPu, UNu in CC2. rewrite UNu in Hadv.
  set (P2 := P + u + adv) in *. set (N2 := Z.of_nat (length l) - u - adv) in *.
  (* the frame after kernel *)
  assert (CW2 : rw_cells rsegs m2 (e_S E - SLOT_FRAME)
                  (hd_cells P2 N2 j0 (wz (e_md E + MD_MARK)) (wz A_EMPTY) (wz (e_mk E)) (wz GNL42) j1 j2)).
  { apply hd_cells_join; [| exact CC2 |].
    - apply (c0_rw_keep _ m1 m2 _ _ CA1 MUK WMk).
      change (Z.of_nat (cells_size (hd_c8 j0 (wz (e_md E + MD_MARK)) (wz A_EMPTY) (wz (e_mk E)) (wz GNL42))))
        with 64. unfold hd_WK. hd_out.
    - apply (c0_rw_keep _ m1 m2 _ _ CZ1 MUK WMk).
      change (Z.of_nat (cells_size [CB 40 j1; CB 256 j2])) with 296. unfold hd_WK. hd_out. }
  assert (B2 : c0_base E P2 N2 kbs' mbs gbs m2).
  { apply (hd_kern_base E P N P2 N2 kbs kbs' mbs gbs m1 m2 HE B1 MUK WMk MI2); try assumption.
    - rewrite USP in ST2. exact ST2.
    - apply ITf. exact (proj1 (proj2 (proj2 (proj2 B1)))).
    - exists (k + u + adv). unfold P2, N2. rewrite Ll. rewrite Ll in Hu. lia. }
  replace (ret_pc (wz 81448)) with (wz 81448) by (unfold wz; symmetry; apply ret_pc_even; [lia | reflexivity]).
  (* model_begin and the jal text_buf *)
  pose proof (c0_img_named _ _ D3 ltac:(c0_unf; lia)) as (DG & _).
  unfold apart_gnl in DG.
  pose proof B2 as (SV2 & NL2' & NW2' & IT2 & NO2 & NM2 & GN2 & OD2 & PO2 & LA2' & TX2 & IP2 & MD2 & MW2 & MK2 & KW2
    & MA2 & CU2 & ER2 & GU2 & MI2' & TM2 & ST2').
  assert (Bse : rw_cells rsegs m2 466316 [C4 (wz (nk_socket_errno kbs')); C4 (wz (nk_send_errno kbs'))]).
  { destruct NL2 as (U2 & L2). unfold NK_SIZE in L2.
    change [C4 (wz (nk_socket_errno kbs')); C4 (wz (nk_send_errno kbs'))]
      with ([C4 (wz (nk_socket_errno kbs'))] ++ [C4 (wz (nk_send_errno kbs'))]).
    apply c0_rw_join.
    - change 466316 with (A_G_NL + NK_SOCKET_ERRNO). apply hd_u8_c4; [exact U2 | | ]; unfold NK_SOCKET_ERRNO; lia.
    - replace (466316 + Z.of_nat (cells_size [C4 (wz (nk_socket_errno kbs'))])) with (A_G_NL + NK_SEND_ERRNO)
        by (cbn; reflexivity).
      apply hd_u8_c4; [exact U2 | | ]; unfold NK_SEND_ERRNO; lia. }
  assert (Bns : rw_cells rsegs m2 474664 [C4 (wz (nk_n_sent kbs'))]).
  { destruct NL2 as (U2 & L2). unfold NK_SIZE in L2.
    change 474664 with (A_G_NL + NK_N_SENT). apply hd_u8_c4; [exact U2 | | ]; unfold NK_N_SENT; lia. }
  assert (Bmd : rw_cells rsegs m2 (e_md E) [C4 (wz (md_socket_errno mbs)); C4 (wz (md_send_errno mbs));
                                            C4 (wz (md_next mbs))]).
  { destruct MD2 as (U2 & L2). unfold MD_SIZE in L2.
    change [C4 (wz (md_socket_errno mbs)); C4 (wz (md_send_errno mbs)); C4 (wz (md_next mbs))]
      with ([C4 (wz (md_socket_errno mbs))] ++ [C4 (wz (md_send_errno mbs))] ++ [C4 (wz (md_next mbs))]).
    apply c0_rw_join; [|apply c0_rw_join].
    - rewrite <- (Z.add_0_r (e_md E)) at 1. apply hd_u8_c4; [exact U2 | | ]; unfold MD_SOCKET_ERRNO; lia.
    - replace (e_md E + Z.of_nat (cells_size [C4 (wz (md_socket_errno mbs))])) with (e_md E + MD_SEND_ERRNO)
        by (cbn; unfold MD_SEND_ERRNO; lia).
      apply hd_u8_c4; [exact U2 | | ]; unfold MD_SEND_ERRNO; lia.
    - replace (e_md E + Z.of_nat (cells_size [C4 (wz (md_socket_errno mbs))]) +
               Z.of_nat (cells_size [C4 (wz (md_send_errno mbs))])) with (e_md E + MD_NEXT)
        by (cbn; unfold MD_NEXT; lia).
      apply hd_u8_c4; [exact U2 | | ]; unfold MD_NEXT; lia. }
  assert (Bnr : rw_cells rsegs m2 (e_md E + 8336) [C4 (wz (md_n_req mbs))]).
  { destruct MD2 as (U2 & L2). unfold MD_SIZE in L2.
    apply hd_u8_c4; [exact U2 | | ]; unfold MD_N_REQ; lia. }
  eapply evt_cut.
  { apply (hd_walkB ra2 gp (wz A_TP) t02 t12 t22 a02 a12 a22 a32 a42 a52 a62 a72 (wz (sel_ptr (c0_sel l))) s3 s4
             (wz (c0_ac l)) (wz (c0_kc l)) (wz (e_mk E)) (wz i) t32 t42 t52 t62 F fc m2 sp (e_md E)
             (wz (nk_socket_errno kbs')) (wz (nk_send_errno kbs')) (wz (nk_n_sent kbs'))
             (wz (md_socket_errno mbs)) (wz (md_send_errno mbs)) (wz (md_next mbs)) (wz (md_n_req mbs))
             P2 N2 j0 (wz (e_md E + MD_MARK)) (wz A_EMPTY) (wz (e_mk E)) j1 j2);
      rewrite ?USP; try eassumption; c0_unf; lia. }
  intros ms3 (m3 & -> & MU3 & WM3 & MI3 & CE3 & CN3 & CM3 & CR3 & CW3).
  rewrite USP in CW3.
  (* model_begin's memory and its byte lists *)
  assert (MUB : munch [(e_md E, e_md E + 12); (e_md E + MD_N_REQ, e_md E + MD_N_REQ + 4);
                       (A_G_NL + NK_N_SENT, A_G_NL + NK_N_SENT + 4)] m2 m3).
  { eapply munch_weaken; [|exact MU3]. intros x Hx. cbn [outside] in *.
    unfold MD_N_REQ, A_G_NL, NK_N_SENT in *. lia. }
  destruct CM3 as ((_ & BM) & _). cbn [cells_bytes cbytes] in BM. rewrite app_nil_r, !hd_le4_sx32 in BM.
  apply bytes_at_app in BM as [BM0 BM]. apply bytes_at_app in BM as [BM4 BM8].
  rewrite length_le4 in BM4, BM8. rewrite length_le4 in BM8.
  replace (e_md E + Z.of_nat 4) with (e_md E + 4) in BM4, BM8 by lia.
  replace (e_md E + 4 + Z.of_nat 4) with (e_md E + 8) in BM8 by lia.
  destruct CR3 as ((_ & BMR) & _). cbn [cells_bytes cbytes] in BMR. rewrite app_nil_r in BMR.
  destruct CN3 as ((_ & BNS) & _). cbn [cells_bytes cbytes] in BNS. rewrite app_nil_r in BNS.
  change (e_md E + 8336) with (e_md E + MD_N_REQ) in BMR. change 474664 with (A_G_NL + NK_N_SENT) in BNS.
  destruct (c0_begin_mem m2 m3 (e_md E) kbs' mbs NL2' MD2 ltac:(unfold apart; lia) MUB WM3 BM0 BM4 BM8 BMR BNS)
    as (NL3 & MD3).
  assert (OC2 : nk_opened kbs' = nk_closed kbs') by (rewrite EOD2, ECL2; exact OC).
  destruct (c0_begin_lists gbs kbs' mbs (proj2 NL2') (proj2 MD2) NW2' MW2 MA2 NX2 OC2)
    as (NW3 & MW3 & MA3 & BEG & EO3 & EOD3 & ECL3 & EMI3 & ENI3 & _ & _ & _ & _).
  assert (B3 : c0_base E P2 N2 (c0_kb kbs') (c0_mb kbs' mbs) gbs m3)
    by exact (hd_begin_base E P2 N2 kbs' mbs (c0_kb kbs') (c0_mb kbs' mbs) gbs m2 m3 HE B2 MU3 WM3 MI3
                NL3 NW3 MD3 MW3 MA3 EO3 EMI3 ENI3).
  (* the frame as c0_frame states it: the 256-byte buffer as wk (40) and 216 more *)
  pose proof (rw_cells_split_CB rsegs m3 (e_S E - SLOT_FRAME)
    [CB 8 j0; C8 (wz A_ODD); C8 (wz (e_md E + MD_MARK)); C8 (wz A_EMPTY); C8 (wz (e_mk E)); C8 (wz A_G_NAMES);
     C8 (wz A_JT); C8 (wz 473984); C8 (wz P2); C8 (wz N2); CB 40 j1] 256 j2 [] [40%nat; 216%nat] CW3 eq_refl) as CW4.
  cbn [mk_CB_cells app] in CW4.
  (* the cut *)
  apply evt_done. apply c0_eqv_intro. unfold Q0. cbv beta. cbn [ms_mem]. split.
  - exists P2, N2, (c0_kb kbs'), (c0_mb kbs' mbs), gbs. unfold c0_cut_kc.
    exists t02, t12, t22, a12, a22, a32, a42, a52, a62, a72, s3, s4, t32, t42, t52, t62, F, fc, m3, j1, (firstn 40 j2).
    split; [reflexivity|].
    split; [exact FC|]. split; [exact Hi|].
    split; [unfold c0_sel; destruct (length l <? 2)%nat; [lia|];
            unfold c0_b, bz; pose proof (bv_unsigned_in_range 8 (nth 1 l (zb 0))) as R8;
            change (bv_modulus 8) with 256 in R8; lia|].
    split; [unfold c0_kc; destruct (length l <? 3)%nat; [lia|]; apply Z.mod_pos_bound; lia|].
    split; [unfold c0_ac; destruct (length l <? 4)%nat; [lia|]; apply Z.mod_pos_bound; lia|].
    split; [unfold N2; lia|].
    split; [rewrite EOD3, EOD2; exact OI|].
    split; [exists j0, (firstn 216 (skipn 40 j2)); exact CW4|].
    split; [exact B3|]. exact BEG.
  - apply (hd_seg_fp _ _ _ _ ([(e_S E - SLOT_FRAME + 64, e_S E - SLOT_FRAME + 80)] ++ hd_WK E ++ hd_WB E)).
    + apply (hd_munch3 _ _ _ m m1 m2 m3); [exact MU1 | exact MUK | exact MU3].
    + exact (wmono_trans rsegs m m1 m3 WM1 (wmono_trans rsegs m1 m2 m3 WMk WM3)).
    + intros lo hi x HI Hx. unfold hd_WK, hd_WB in HI. cbn [app In] in HI.
      unfold own_w.
      repeat destruct HI as [HI|HI]; try contradiction; injection HI as <- <-;
        first [ left; c0_unf; unfold FO_P in *; lia
              | right; left; unfold NK_CHUNK, NK_OPEN in *; c0_unf; lia
              | right; right; right; left; c0_unf; lia
              | right; right; right; right; right; exists (e_md E), MD_SIZE; split;
                [unfold c0_hp2; left; reflexivity | c0_unf; lia] ].
Qed.
End S1.
