From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.U.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.U Require Import Contract Img0.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.U Require MemNorm.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells Tac Bytes ZBridge Image.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Lib Require Regs6ss RegisterBridge FP.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.U.Spec Require Import StrFun.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.U.Prog Require Import Boxreg BoxregRd BoxregUpd BoxregStep
  range_free_c lowest_free_base_c printf_facts_c snprintf_c reac_boxreg_set_name_c reac_boxreg_declare_c
  reac_boxreg_declare_inv bcmp_c strncmp_c.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.U.Prog Require Import
  LLVMFuzzerTestOneInput_c LLVMFuzzerTestOneInput_fr LLVMFuzzerTestOneInput_inv LLVMFuzzerTestOneInput_top
  LLVMFuzzerTestOneInput_seg LLVMFuzzerTestOneInput_rn LLVMFuzzerTestOneInput_c0a.
Import ListNotations.
Open Scope Z_scope.

Lemma c0_op8 : forall op, Z.land op 8 = 0 \/ Z.land op 8 = 8.
Proof.
  intros op. destruct (Z.testbit op 3) eqn:T; [right | left]; apply Z.bits_inj'; intros i Hi;
    rewrite Z.land_spec; change 8 with (2 ^ 3); destruct (Z.eq_dec i 3) as [->|N].
  - rewrite T, Z.pow2_bits_true by lia. reflexivity.
  - rewrite !Z.pow2_bits_false by lia. apply andb_false_r.
  - rewrite T. rewrite Z.bits_0. reflexivity.
  - rewrite Z.pow2_bits_false by lia. rewrite Z.bits_0. apply andb_false_r.
Qed.

Lemma c0_given : forall op nm, 0 <= op < 256 -> 0 <= nm < 2 ^ 64 ->
  Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 (Z.shiftr (bv_unsigned (Z_to_bv 64
    (Z.land (bv_unsigned (Z_to_bv 64 op)) 8))) 3 + -1))) (bv_unsigned (Z_to_bv 64 nm))) =
  Z_to_bv 64 (if Z.land op 8 =? 0 then nm else 0).
Proof.
  intros op nm Hop Hnm. rewrite (unsigned_lit op) by lia. rewrite (unsigned_lit nm) by lia.
  destruct (c0_op8 op) as [E|E]; rewrite E.
  - change (Z.shiftr (bv_unsigned (Z_to_bv 64 0)) 3 + -1) with (-1).
    change (bv_unsigned (Z_to_bv 64 (-1))) with (Z.ones 64). rewrite Z.land_comm, Z.land_ones by lia.
    rewrite Z.mod_small by lia. reflexivity.
  - reflexivity.
Qed.

Lemma c0_rfo_ok : forall bs k b, range_free_ok bs b k (bx_fabric bs) -> range_ok bs k b.
Proof.
  intros bs k b [H1 H2]. split; [lia|]. split; [lia|]. intros (i & Hi & Hm). exact (H2 i Hi Hm).
Qed.

Lemma c0_ok_rfo : forall bs k b, range_ok bs k b -> range_free_ok bs b k (bx_fabric bs).
Proof.
  intros bs k b (H1 & H2 & H3). split; [lia|]. intros i Hi Hm. apply H3. exists i. split; [exact Hi | exact Hm].
Qed.

Definition c0_lfr (bs : list byte) (nch fabric z : Z) : Prop :=
  (z = -1 /\ forall b, 0 <= b <= fabric - nch -> ~ range_free_ok bs b nch fabric) \/
  (0 <= z <= fabric - nch /\ range_free_ok bs z nch fabric /\
   forall b, 0 <= b < z -> ~ range_free_ok bs b nch fabric).

Definition c0_want (bs : list byte) (nch base want : Z) : Prop :=
  (~ (box_width_ok nch (bx_fabric bs) /\ bx_n bs < 5) /\ want = -1) \/
  (box_width_ok nch (bx_fabric bs) /\ bx_n bs < 5 /\ 0 <= base /\
     ((range_free_ok bs base nch (bx_fabric bs) /\ want = base) \/
      (~ range_free_ok bs base nch (bx_fabric bs) /\ want = -1))) \/
  (box_width_ok nch (bx_fabric bs) /\ bx_n bs < 5 /\ base < 0 /\ c0_lfr bs nch (bx_fabric bs) want).

Lemma c0_link_refused : forall bs nch base want,
  c0_want bs nch base want -> declare_refused bs nch base -> want = -1.
Proof.
  intros bs nch base want HW HR.
  destruct HW as [(_ & E) | [(Hw & Hn & Hb & [(Hf & E) | (_ & E)]) | (Hw & Hn & Hb & Hl)]]; try exact E.
  - exfalso. destruct HR as [HR | [HR | [(_ & HR) | (HR & _)]]]; [tauto | lia | | lia].
    exact (HR (c0_rfo_ok bs nch base Hf)).
  - destruct HR as [HR | [HR | [(HR & _) | (_ & HR)]]]; [tauto | lia | lia |].
    destruct Hl as [(E & _) | (H1 & H2 & _)]; [exact E|].
    exfalso. destruct HR as [(_ & HR) | (HR & _)]; [|lia].
    destruct (c0_rfo_ok bs nch want H2) as (_ & _ & HF). apply HF. apply HR; [lia|]. destruct H2; lia.
Qed.

Lemma c0_link_placed : forall bs nch base want b p,
  c0_want bs nch base want -> declare_placed bs nch base b p -> want = b.
Proof.
  intros bs nch base want b p HW (Hw & Hn & HP).
  destruct HW as [(HN & _) | [(_ & _ & Hb & [(Hf & E) | (Hf & E)]) | (_ & _ & Hb & Hl)]].
  - exfalso. tauto.
  - destruct HP as [(_ & -> & _) | (HP & _)]; [exact E | lia].
  - exfalso. destruct HP as [(_ & -> & _ & Hr) | (HP & _)]; [| lia]. exact (Hf (c0_ok_rfo bs nch base Hr)).
  - destruct HP as [(HP & _) | (_ & _ & Hb0 & HL)]; [lia|].
    destruct HL as [(E & _) | (L1 & L2 & L3 & L4)]; [lia|].
    destruct Hl as [(E & H) | (H1 & H2 & H3)].
    + exfalso. apply (H b); [lia|]. apply c0_ok_rfo. split; [lia|]. split; [lia | exact L3].
    + destruct (Z.lt_trichotomy want b) as [Lt | [Eq | Gt]]; [| exact Eq |].
      * exfalso. destruct (c0_rfo_ok bs nch want H2) as (_ & _ & HF). apply HF. apply L4. lia.
      * exfalso. apply (H3 b); [lia|]. apply c0_ok_rfo. split; [lia|]. split; [lia | exact L3].
Qed.

Lemma c0_kept_placed : forall bs b k p s, boxreg_inv bs -> bx_n bs < 5 -> llvm_kept bs (decl_bytes bs b k p s) (-1).
Proof.
  intros bs b k p s [[HL [H1 _]] _] Hn5 j Hj. unfold boxreg_B1 in H1.
  pose proof (decl_row_length b k p s) as HR.
  replace (decl_bytes bs b k p s) with (new_row_bytes bs (decl_row b k p s)) by reflexivity.
  assert (Hn : 0 <= bx_n bs <= 4) by lia.
  unfold bx_base, bx_nch, bx_pinned, bx_mac, bx_name, rd4.
  rewrite !(new_row_old bs (decl_row b k p s) HL Hn HR j) by lia.
  replace (56 * j) with (56 * j + 0) by lia.
  rewrite !(new_row_old bs (decl_row b k p s) HL Hn HR j) by lia.
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [right; reflexivity | right; reflexivity].
Qed.

Lemma c0_zero_at : forall m, mem_inv rsegs m -> bytes_at rsegs m 0x10392 zero6.
Proof.
  intros m MI. apply ro_bytes_at; [exact MI | lia | cbn [length zero6 repeat]; lia |].
  apply ro_bytes_b_sound. vm_compute. reflexivity.
Qed.

Lemma c0_empty_at : forall m, mem_inv rsegs m -> bytes_at rsegs m 0x102cd [Z_to_bv 8 0].
Proof.
  intros m MI. apply ro_bytes_at; [exact MI | lia | cbn [length]; lia |].
  apply ro_bytes_b_sound. vm_compute. reflexivity.
Qed.

Lemma c0_lor1 : forall x : word, Z.lor 18446744073709551615 (bv_unsigned x) = 18446744073709551615.
Proof.
  intros x. pose proof (bv_unsigned_in_range 64 x) as R. unfold bv_modulus in R. change (2 ^ Z.of_N 64) with (2 ^ 64) in R.
  change 18446744073709551615 with (Z.ones 64).
  apply Z.bits_inj'. intros i Hi. rewrite Z.lor_spec.
  destruct (Z.lt_ge_cases i 64) as [L|L].
  - rewrite Z.ones_spec_low by lia. reflexivity.
  - rewrite Z.ones_spec_high by lia. rewrite <- (Z.mod_small (bv_unsigned x) (2 ^ 64)) by lia.
    rewrite Z.mod_pow2_bits_high by lia. reflexivity.
Qed.

Lemma c0_kept_refl : forall bs, llvm_kept bs bs (-1).
Proof. intros bs j Hj. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; right; reflexivity. Qed.

Lemma c0_row_bsub : forall bs b k p s o w, length bs = 288%nat -> 0 <= bx_n bs <= 4 -> 0 <= o -> 0 <= w -> o + w <= 56 ->
  bsub (decl_bytes bs b k p s) (56 * bx_n bs + o) w = bsub (decl_row b k p s) o w.
Proof.
  intros bs b k p s o w HL Hn Ho Hw Hl.
  change (decl_bytes bs b k p s) with (new_row_bytes bs (decl_row b k p s)).
  rewrite new_row_new by first [exact HL | lia | apply decl_row_length]. reflexivity.
Qed.

Lemma c0_decl_length : forall bs b k p s, length bs = 288%nat -> 0 <= bx_n bs <= 4 ->
  length (decl_bytes bs b k p s) = 288%nat.
Proof.
  intros bs b k p s HL Hn. change (decl_bytes bs b k p s) with (new_row_bytes bs (decl_row b k p s)).
  rewrite new_row_length by first [exact HL | lia | apply decl_row_length]. reflexivity.
Qed.

Lemma c0_row_rd : forall m r bs b k p s o v, bytes_at rsegs m r (decl_bytes bs b k p s) -> length bs = 288%nat ->
  0 <= bx_n bs <= 4 -> 0 <= o -> o + 4 <= 56 -> bsub (decl_row b k p s) o 4 = le4 (Z_to_bv 64 v) ->
  -2^31 <= v < 2^31 ->
  ov_read_bytes rsegs m (wa (r + (56 * bx_n bs + o))) 4 = Some (le4 (Z_to_bv 64 v)).
Proof.
  intros m r bs b k p s o v HB HL Hn Ho Hl Hr Hv.
  assert (E : bsub (decl_bytes bs b k p s) (56 * bx_n bs + o) 4 = le4 (Z_to_bv 64 v))
    by (rewrite c0_row_bsub by lia; exact Hr).
  pose proof (rd4_le4 _ _ v Hv E) as Er.
  apply bx_ov4. rewrite <- Er. apply rd4_bytes_at; [exact HB | lia |].
  rewrite c0_decl_length by assumption. lia.
Qed.

Lemma c0_decl_n : forall bs b k p s, length bs = 288%nat -> 0 <= bx_n bs <= 4 ->
  bx_n (decl_bytes bs b k p s) = bx_n bs + 1.
Proof.
  intros bs b k p s HL Hn. change (decl_bytes bs b k p s) with (new_row_bytes bs (decl_row b k p s)).
  rewrite new_row_n by first [exact HL | lia | apply decl_row_length]. reflexivity.
Qed.

Lemma c0_decl_fabric : forall bs b k p s, length bs = 288%nat -> 0 <= bx_n bs <= 4 ->
  bx_fabric (decl_bytes bs b k p s) = bx_fabric bs.
Proof.
  intros bs b k p s HL Hn. change (decl_bytes bs b k p s) with (new_row_bytes bs (decl_row b k p s)).
  rewrite new_row_fabric by first [exact HL | lia | apply decl_row_length]. reflexivity.
Qed.

Lemma c0_pin_val : forall z, -2^63 <= z < 2^63 ->
  Z_to_bv 64 (Z.lxor (bv_unsigned (v_slti (Z_to_bv 64 z) 0)) 1) = Z_to_bv 64 (if z <? 0 then 0 else 1).
Proof. intros z Hz. unfold v_slti, zsig. rewrite bx_signed by lia. destruct (z <? 0); reflexivity. Qed.

Lemma c0_lts56 : forall z, -128 <= z < 128 -> bv_lts (Z_to_bv 64 (z * 2 ^ 56)) (Z_to_bv 64 0) = (z <? 0).
Proof.
  intros z Hz.
  rewrite bx_lts by (change (2 ^ 56) with 72057594037927936; change (2 ^ 63) with 9223372036854775808; lia).
  destruct (Z.ltb_spec z 0); [apply Z.ltb_lt | apply Z.ltb_ge]; change (2 ^ 56) with 72057594037927936; lia.
Qed.

Lemma c0_swrap_small : forall z, -2^31 <= z < 2^31 -> bv_swrap 32 z = z.
Proof.
  intros z Hz. unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with 2147483648.
  change (bv_modulus 32) with 4294967296. change (2^31) with 2147483648 in Hz. Z.div_mod_to_equations. lia.
Qed.

Lemma c0_srai : forall z, 0 <= z < 2^31 ->
  Z_to_bv 64 (bv_swrap 32 (Z.shiftr (bv_swrap 32 (bv_unsigned (Z_to_bv 64 z))) 31)) = Z_to_bv 64 0.
Proof.
  intros z Hz. rewrite unsigned_lit by lia. rewrite (c0_swrap_small z) by lia.
  rewrite Z.shiftr_div_pow2 by lia. rewrite Z.div_small by lia. reflexivity.
Qed.

Lemma c0_c8cb : forall m A c0 c1 c2 w post,
  rw_cells rsegs m A (c0 :: c1 :: c2 :: C8 w :: post) ->
  rw_cells rsegs m A (c0 :: c1 :: c2 :: CB 8 (le8 w) :: post).
Proof.
  intros m A c0 c1 c2 w post H.
  pose proof (rw_cells_merge rsegs m A [c0; c1; c2] [C8 w] post H) as H'.
  cbn [app cells_size csize Nat.add cells_bytes cbytes] in H'. rewrite app_nil_r in H'. exact H'.
Qed.

Lemma c0_c8cb0 : forall m A w post,
  rw_cells rsegs m A (C8 w :: post) -> rw_cells rsegs m A (CB 8 (le8 w) :: post).
Proof.
  intros m A w post H.
  pose proof (rw_cells_merge rsegs m A [] [C8 w] post H) as H'.
  cbn [app cells_size csize Nat.add cells_bytes cbytes] in H'. rewrite app_nil_r in H'. exact H'.
Qed.

Definition c0_q2 (sp gp tp s0 s8 s9 s10 s11 : word) (lo r fab nm i q c : Z) (bs jm : list byte)
    (m0 : word -> option byte) (ms' : machine_state) : Prop :=
  exists (t0 t1 t2 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 t3 t4 t5 t6 : word) (F' : bvmap 5 word) (fc' : bv 32)
         (m' : word -> option byte) (bs' j0' j1' : list byte),
    ms' = MS (mkR (Z_to_bv 64 0x13284) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 nm) a1 a2 a3 a4 a5 a6 a7
                  s2 s3 s4 s5 s6 (Z_to_bv 64 fab) s8 s9 s10 s11 t3 t4 t5 t6)
             F' (Z_to_bv 64 0x14a48) fc' None m' (seg_rom rsegs) /\
    FP.frm0 fc' /\
    munch [(lo, bv_unsigned sp + 32); (r, r + 288)] m0 m' /\ wmono rsegs m0 m' /\
    bytes_at rsegs m' r bs' /\ wr_at rsegs m' r 288 /\
    rw_cells rsegs m' (bv_unsigned sp)
      [CB 8 j0'; C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 fab); CB 8 j1'; C8 (Z_to_bv 64 i); C8 (Z_to_bv 64 (bx_n bs));
       CB 288 bs; CB 8 jm; C8 (Z_to_bv 64 q); C8 (Z_to_bv 64 c)] /\
    boxreg_inv bs' /\ bx_fabric bs' = fab /\ llvm_kept bs bs' (-1).

Ltac c0_ifb :=
  first [ c0_if
        | (rewrite ?bx_sx32 by lia; rewrite ?c0_lor1; rewrite ?swrap_addi by lia; rewrite ?bx_off56 by lia;
           rewrite ?c0_pin_val by lia; rewrite ?c0_lts56 by lia; rewrite ?c0_srai by lia; rewrite ?Z.lor_0_l;
           rewrite ?Z_to_bv_bv_unsigned;
           repeat match goal with H : (?x <? ?y) = _ |- context [?x <? ?y] => rewrite H end;
           c0_if) ].

Ltac c0_gob stop :=
  repeat (lazymatch goal with
          | |- evt _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) =>
              tryif constr_eq pc stop then fail else first [ step | c0_rdstep ]
          end; try c0_ifb).

Lemma llvm_c0_k12fb4 :
  forall (ra sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s5 s8 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m0 m : word -> option byte)
         (lo r nch base op nm want nl i q c : Z) (j0 bs jm NB slack : list byte) (s : list Z) (canary : word),
    reac_boxreg_declare_contract -> bcmp_contract -> strncmp_contract ->
    0 <= nch < 256 -> -128 <= base < 128 -> 0 <= op < 256 ->
    boxreg_inv bs -> length bs = 288%nat -> r mod 8 = 0 -> pf_img_free r 288 -> c0_want bs nch base want ->
    bytes_at rsegs m r bs -> wr_at rsegs m r 288 ->
    rw_cells rsegs m (bv_unsigned sp)
      [CB 8 j0; C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 (bx_fabric bs)); C8 (Z_to_bv 64 want); C8 (Z_to_bv 64 i);
       C8 (Z_to_bv 64 (bx_n bs)); CB 288 bs; CB 8 jm; C8 (Z_to_bv 64 q); C8 (Z_to_bv 64 c)] ->
    stk rsegs m lo (bv_unsigned sp) -> 0x50000 <= lo -> lo + 6000 <= bv_unsigned sp -> bv_unsigned sp + 464 <= 2 ^ 47 ->
    4096 <= r -> r + 288 <= lo ->
    0 < nm -> Forall (fun c => 0 < c < 256) s -> Z.of_nat (length s) < 2 ^ 31 - 1 ->
    bytes_at rsegs m nm NB -> NB = pf_bytes (s ++ [0]) ++ slack -> Z.of_nat (length NB) = nl ->
    (- (nm + Z.of_nat (length s) + 1)) mod 8 <= Z.of_nat (length slack) ->
    nm + nl <= lo -> (nm + nl <= r \/ r + 288 <= nm) ->
    mem_inv rsegs m -> MemNorm.task_mem rsegs m0 -> FP.frm0 fc ->
    bytes_at rsegs m GOT_GUARD (le8 (Z_to_bv 64 GUARD)) -> bytes_at rsegs m GUARD (le8 canary) ->
    munch [(lo, bv_unsigned sp + 32); (r, r + 288)] m0 m -> wmono rsegs m0 m ->
    evt rsegs (c0_q2 sp gp tp (Z_to_bv 64 r) s8 (Z_to_bv 64 (-1 - r)) s10 s11 lo r (bx_fabric bs) nm i q c bs jm m0)
      (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 r) (Z_to_bv 64 op) a0 a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 nm) (Z_to_bv 64 nch) (Z_to_bv 64 base) s5 (Z_to_bv 64 (base * 2 ^ 56))
               (Z_to_bv 64 (bx_fabric bs)) s8 (Z_to_bv 64 (-1 - r)) s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x12fb4) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s5 s8 s10 s11 t3 t4 t5 t6 F fc m0 m lo r nch base op nm want nl
    i q c j0 bs jm NB slack s canary DC BC SC Hnch Hbase Hop INV HL Hr8 HIF HWANT HB HWR CW ST Hlo HLO HSP Hr4 HRL Hnm
    Hsok Hslen HNB HNBe HNBl Hmod Hnlo Hnr MI TM Hfc HG1 HG2 MU WM.
  unfold reac_boxreg_declare_contract in DC. unfold GOT_GUARD, GUARD in *.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp. change (2 ^ Z.of_N 64) with (2 ^ 64) in Rsp.
  pose proof (nm_len s slack) as HNL. rewrite <- HNBe, HNBl in HNL.
  pose proof INV as ((_ & HB1 & HB2 & _) & _). unfold boxreg_B1 in HB1. unfold boxreg_B2 in HB2.
  c0_go 0x13b6c.
  rewrite c0_given by lia.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (HNA : name_ok mm (bv_unsigned sp) lo r (if Z.land op 8 =? 0 then nm else 0)
                    (if Z.land op 8 =? 0 then s else []))
      by (destruct (Z.land op 8 =? 0);
          [ right; split; [lia|]; split; [exact Hsok|]; split; [exact Hslen|]; exists slack; rewrite <- HNBe;
            split; [assumption|]; split; [exact Hmod|]; split; lia
          | left; split; reflexivity ]);
    assert (TMm : MemNorm.task_mem rsegs mm)
      by (apply (nm_task_munch [(lo, bv_unsigned sp + 32); (r, r + 288)] m0 mm TM);
          [ assumption | intros x Hx; unfold TASK_SIZE; cbn [outside] in Hx; lia ])
  end.
  eapply evt_cut.
  { eapply DC with (r := r) (k := nch) (nm := if Z.land op 8 =? 0 then nm else 0) (b0 := base) (lo := lo) (bs := bs)
      (canary := canary) (s := if Z.land op 8 =? 0 then s else []);
      first [ reflexivity | exact HNA | exact TMm | assumption | unfold DECLARE_K; lia | unfold IMG_END; lia
            | destruct (Z.land op 8 =? 0); lia ]. }
  intros ms' (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & F' & fc' & m2
    & E & FK & Hfc' & MUc & WMc & MI2 & TM2 & ST2 & RES).
  subst ms'.
  lazymatch type of MUc with munch _ ?mm ?mm' => transport_after_call rsegs mm mm' MUc WMc end.
  clear MUc WMc.
  c1_retpc.
  destruct RES as [(HR & -> & HB2') | (b & p & HP & -> & HB2')].
  - pose proof (c0_link_refused bs nch base want HWANT HR) as ->.
    assert (R280 : ov_read_bytes rsegs m2 (wa (r + 280)) 4 = Some (le4 (Z_to_bv 64 (bx_n bs))))
      by (apply bx_ov4; exact (rd4_bytes_at m2 r bs 280 HB2' ltac:(lia) ltac:(rewrite HL; lia))).
    pose proof (rd4_range bs 280) as Rn. change (rd4 bs 280) with (bx_n bs) in Rn.
    c0_gob 0x14a48.
    apply c0_c8cb in CW.
    finish.
    all: first [exact HB2' | exact INV | exact CW | reflexivity | apply c0_kept_refl].
  - pose proof (c0_link_placed bs nch base want b p HWANT HP) as ->.
    pose proof HP as (Hwd & Hn5 & HPC).
    assert (Hn : 0 <= bx_n bs <= 4) by lia.
    assert (Hbr : 0 <= b <= 40 /\ (p = 0 \/ p = 1)).
    { destruct HPC as [(_ & -> & -> & H1 & H2 & _) | (_ & -> & H0 & [(E & _) | (H1 & H2 & _)])]; lia. }
    assert (Hp : p = if base <? 0 then 0 else 1).
    { destruct HPC as [(H0 & _ & -> & _) | (H0 & -> & _)];
        [rewrite (proj2 (Z.ltb_ge base 0) H0) | rewrite (proj2 (Z.ltb_lt base 0) H0)]; reflexivity. }
    assert (Hbb : 0 <= base -> b = base) by (destruct HPC as [(_ & E & _) | (H0 & _)]; [intros; exact E | lia]).
    set (s' := if Z.land op 8 =? 0 then s else []) in HB2', HNA.
    assert (R280 : ov_read_bytes rsegs m2 (wa (r + 280)) 4 = Some (le4 (Z_to_bv 64 (bx_n bs + 1)))).
    { apply bx_ov4. rewrite <- (c0_decl_n bs b nch p s' HL Hn).
      exact (rd4_bytes_at m2 r _ 280 HB2' ltac:(lia) ltac:(rewrite c0_decl_length by assumption; lia)). }
    pose proof (c0_row_rd m2 r bs b nch p _ 12 nch HB2' HL Hn ltac:(lia) ltac:(lia) (decl_row_nch b nch p _)
      ltac:(lia)) as R12.
    c0_gob 0x1bbcc.
    assert (HZ1 : bytes_at rsegs m2 (bv_unsigned (Z_to_bv 64 (r + 56 * bx_n bs))) zero6).
    { rewrite unsigned_lit by lia. replace (r + 56 * bx_n bs) with (r + (56 * bx_n bs + 0)) by lia.
      rewrite <- (decl_row_mac b nch p s'), <- (c0_row_bsub bs b nch p s' 0 6 HL Hn) by lia.
      apply bytes_at_bsub; [exact HB2' | lia | lia | rewrite c0_decl_length by assumption; lia]. }
    eapply evt_cut.
    { unfold bcmp_contract in BC. eapply BC with (ls := zero6) (rs := zero6) (v := 0).
      - exact HZ1.
      - rewrite unsigned_lit by lia. exact (c0_zero_at _ MI2).
      - reflexivity.
      - exact MI2. }
    post_call rsegs m2.
    rewrite (unsigned_lit op) by lia.
    subst s'. destruct (c0_op8 op) as [E8|E8]; rewrite E8 in HB2', HNA |- *; cbn [Z.eqb] in HB2', HNA |- *.
    all: destruct (Z_lt_le_dec base 0) as [Hsg|Hsg];
      [ assert (Elt : (base <? 0) = true) by (apply Z.ltb_lt; lia)
      | assert (Elt : (base <? 0) = false) by (apply Z.ltb_ge; lia); pose proof (Hbb Hsg) as Ebb; subst b ];
      rewrite Elt in Hp; subst p.
    all: lazymatch goal with
         | HB : bytes_at rsegs ?mm ?rr (decl_bytes ?b0 ?bb ?k0 ?pp ?sx) |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
             pose proof (c0_row_rd mm rr b0 bb k0 pp sx 20 pp HB HL Hn ltac:(lia) ltac:(lia) (decl_row_pin bb k0 pp sx)
               ltac:(lia)) as R20;
             pose proof (c0_row_rd mm rr b0 bb k0 pp sx 8 bb HB HL Hn ltac:(lia) ltac:(lia) (decl_row_base bb k0 pp sx)
               ltac:(lia)) as R8
         end.
    all: c0_gob 0x1c1c8.
    all: lazymatch goal with
         | HB : bytes_at rsegs ?mm ?rr (decl_bytes ?b0 ?bb ?k0 ?pp ?sx) |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
             assert (HNF : bytes_at rsegs mm (rr + (56 * bx_n b0 + 24)) (name_field sx))
               by (rewrite <- (decl_row_name bb k0 pp sx), <- (c0_row_bsub b0 bb k0 pp sx 24 32 HL Hn) by lia;
                   apply bytes_at_bsub; [exact HB | lia | lia | rewrite c0_decl_length by assumption; lia])
         end.
    all: unfold strncmp_contract in SC.
    all: lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      eapply evt_cut;
      [ eapply SC with (v := 0);
        [ match goal with |- bytes_at _ _ ?a _ =>
            replace a with (r + (56 * bx_n bs + 24)) by (rewrite unsigned_lit by lia; lia) end; exact HNF
        | match goal with |- bytes_at _ _ ?a _ =>
            first [ replace a with nm by (rewrite unsigned_lit by lia; lia); exact HNB
                  | replace a with 66253 by (rewrite unsigned_lit by lia; lia); exact (c0_empty_at _ ltac:(eassumption)) ]
          end
        | first [rewrite HNBe; exact (nm_strncmp_field s slack Hsok) | exact (nm_strncmp_field [] [] (Forall_nil _))]
        | assumption ]
      | post_call rsegs mm ] end.
    all: clear R8 R20.
    all: lazymatch goal with
         | HB : bytes_at rsegs ?mm ?rr (decl_bytes ?b0 ?bb ?k0 ?pp ?sx) |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
             pose proof (c0_row_rd mm rr b0 bb k0 pp sx 8 bb HB HL Hn ltac:(lia) ltac:(lia) (decl_row_base bb k0 pp sx)
               ltac:(lia)) as R8
         end.
    all: c0_gob 0x14a48.
    all: apply c0_c8cb in CW.
    all: finish.
    all: first [ exact HB2' | exact CW | reflexivity | apply c0_kept_placed; assumption
               | apply c0_decl_fabric; assumption
               | eapply reac_boxreg_declare_keeps_inv_holds; [exact INV | exact HP] ].
Qed.
