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
  LLVMFuzzerTestOneInput_seg LLVMFuzzerTestOneInput_rn LLVMFuzzerTestOneInput_c0a LLVMFuzzerTestOneInput_c0b.
Import ListNotations.
Open Scope Z_scope.

Lemma c0_even : forall k, k mod 2 = 0 -> Z.even k = true.
Proof. intros k H. rewrite (Z.div_mod k 2) by lia. rewrite H, Z.add_0_r, Z.even_mul. reflexivity. Qed.

Lemma c0_even_mod : forall k, Z.even k = true -> k mod 2 = 0.
Proof. intros k H. rewrite Zmod_even, H. reflexivity. Qed.

Lemma c0_wtest : forall k, 0 <= k < 256 ->
  bv_ltu (Z_to_bv 64 38) (Z_to_bv 64 (k + -2)) = negb ((2 <=? k) && (k <=? 40)).
Proof.
  intros k Hk. unfold bv_ltu. rewrite !unsigned_lit_wrap. change (2 ^ 64) with 18446744073709551616.
  destruct (Z.leb_spec 2 k), (Z.leb_spec k 40); cbn [andb negb];
    first [apply Z.ltb_ge | apply Z.ltb_lt]; Z.div_mod_to_equations; lia.
Qed.

Lemma c0_rf_one : forall z : Z,
  Z_to_bv 64 (Z.lor (bv_unsigned (Z_to_bv 64 (bv_swrap 32 (bv_unsigned (v_sltu (Z_to_bv 64 0) (Z_to_bv 64 1)) + -1))))
    (bv_unsigned (Z_to_bv 64 z))) = Z_to_bv 64 z.
Proof.
  intros z.
  replace (bv_unsigned (Z_to_bv 64 (bv_swrap 32 (bv_unsigned (v_sltu (Z_to_bv 64 0) (Z_to_bv 64 1)) + -1)))) with 0
    by (vm_compute; reflexivity).
  rewrite Z.lor_0_l. apply Z_to_bv_bv_unsigned.
Qed.

Lemma c0_rf_zero : forall z : Z,
  Z_to_bv 64 (Z.lor (bv_unsigned (Z_to_bv 64 (bv_swrap 32 (bv_unsigned (v_sltu (Z_to_bv 64 0) (Z_to_bv 64 0)) + -1))))
    (bv_unsigned (Z_to_bv 64 z))) = Z_to_bv 64 (-1).
Proof.
  intros z.
  replace (bv_unsigned (Z_to_bv 64 (bv_swrap 32 (bv_unsigned (v_sltu (Z_to_bv 64 0) (Z_to_bv 64 0)) + -1))))
    with 18446744073709551615 by (vm_compute; reflexivity).
  rewrite c0_lor1. apply Z_to_bv_eqm. reflexivity.
Qed.

Lemma c0_cnt : forall f n, 0 <= n <= f -> f <= 40 ->
  Z_to_bv 64 (bv_swrap 32 (bv_unsigned (Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 (0 - bv_unsigned (v_slt (Z_to_bv 64 0)
    (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 f) - bv_unsigned (Z_to_bv 64 n))))))) (bv_unsigned (Z_to_bv 64
    (bv_unsigned (Z_to_bv 64 f) - bv_unsigned (Z_to_bv 64 n)))))) + 1)) = Z_to_bv 64 (f - n + 1).
Proof.
  intros f n H1 H2. rewrite (unsigned_lit f), (unsigned_lit n) by lia.
  unfold v_slt, c_lts. rewrite bx_lts by lia.
  destruct (Z.ltb_spec 0 (f - n)) as [Hd|Hd].
  - change (bv_unsigned (Z_to_bv 64 1)) with 1. change (0 - 1) with (-1).
    change (bv_unsigned (Z_to_bv 64 (-1))) with (Z.ones 64).
    rewrite (unsigned_lit (f - n)) by lia. rewrite Z.land_comm, Z.land_ones by lia. rewrite Z.mod_small by lia.
    rewrite (unsigned_lit (f - n)) by lia. rewrite c0_swrap_small by lia. reflexivity.
  - replace (f - n) with 0 by lia. replace (0 + 1) with 1 by lia. vm_compute. reflexivity.
Qed.

Lemma llvm_c0_loop :
  forall (k : nat) (ra sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s8 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m0 m : word -> option byte)
         (lo r nch base op nm b nl i q c : Z) (bs jm NB slack : list byte) (s : list Z) (canary : word),
    range_free_contract -> reac_boxreg_declare_contract -> bcmp_contract -> strncmp_contract ->
    Z.of_nat k = bx_fabric bs - nch - b -> 0 <= b ->
    (forall b', 0 <= b' < b -> ~ range_free_ok bs b' nch (bx_fabric bs)) ->
    box_width_ok nch (bx_fabric bs) -> bx_n bs < 5 -> base < 0 ->
    0 <= nch < 256 -> -128 <= base < 128 -> 0 <= op < 256 ->
    boxreg_inv bs -> length bs = 288%nat -> r mod 8 = 0 -> pf_img_free r 288 ->
    bytes_at rsegs m r bs -> wr_at rsegs m r 288 ->
    rw_cells rsegs m (bv_unsigned sp)
      [C8 (Z_to_bv 64 (base * 2 ^ 56)); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 (bx_fabric bs)); C8 (Z_to_bv 64 (-1));
       C8 (Z_to_bv 64 i); C8 (Z_to_bv 64 (bx_n bs)); CB 288 bs; CB 8 jm; C8 (Z_to_bv 64 q); C8 (Z_to_bv 64 c)] ->
    bytes_at rsegs m (bv_unsigned sp + 48) bs -> bv_unsigned sp mod 16 = 0 ->
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
               (Z_to_bv 64 nm) (Z_to_bv 64 nch) (Z_to_bv 64 base) (Z_to_bv 64 b)
               (Z_to_bv 64 (bx_fabric bs - nch + 1)) (Z_to_bv 64 (bx_fabric bs)) s8 (Z_to_bv 64 (-1 - r)) s10 s11
               t3 t4 t5 t6)
          F (Z_to_bv 64 0x132b8) fc None m (seg_rom rsegs)).
Proof.
  induction k as [|k IH];
    intros ra sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s8 s10 s11 t3 t4 t5 t6 F fc m0 m lo r nch base op nm b nl i q c
      bs jm NB slack s canary RF DC BC SC Hk Hb0 Hlow Hw Hn5 Hneg Hnch Hbase Hop INV HL Hr8 HIF HB HWR CW HP Hsp16 ST
      Hlo HLO HSP Hr4 HRL Hnm Hsok Hslen HNB HNBe HNBl Hmod Hnlo Hnr MI TM Hfc HG1 HG2 MU WM.
  all: unfold GOT_GUARD, GUARD in *.
  all: pose proof INV as ((_ & HB1 & HB2 & HB3 & _) & _).
  all: assert (Hn : 0 <= bx_n bs <= 5) by exact HB1.
  all: assert (Hfb : 1 <= bx_fabric bs <= 40) by exact HB2.
  all: pose proof Hw as (_ & Hw2 & Hw3).
  all: pose proof (bv_unsigned_in_range 64 sp) as Rsp; unfold bv_modulus in Rsp; change (2 ^ Z.of_N 64) with (2 ^ 64) in Rsp.
  all: c0_gob 0x13858.
  all: eapply evt_cut;
    [ unfold range_free_contract in RF;
      eapply RF with (t := bv_unsigned sp + 48) (base := b) (nch := nch) (fabric := bx_fabric bs) (bs := bs);
      first [ reflexivity | assumption | lia | (clear - Hsp16; Z.div_mod_to_equations; lia) ] | ].
  all: intros ms' (t0' & t1' & t2' & rr & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & E & HRF).
  all: subst ms'.
  all: c1_retpc.
  all: destruct HRF as [(-> & Hok) | (-> & Hnok)].
  - c0_gob 0x12fb4. apply c0_c8cb0 in CW.
    eapply llvm_c0_k12fb4 with (want := b); try eassumption; try lia.
    right. right. split; [exact Hw|]. split; [lia|]. split; [lia|]. right. split; [lia|]. split; [exact Hok | exact Hlow].
  - c0_gob 0x12fb4. apply c0_c8cb0 in CW.
    eapply llvm_c0_k12fb4 with (want := -1); try eassumption; try lia.
    right. right. split; [exact Hw|]. split; [lia|]. split; [lia|]. left. split; [reflexivity|].
    intros b' Hb'. destruct (Z.eq_dec b' b) as [->|Hne]; [exact Hnok | apply Hlow; lia].
  - c0_gob 0x12fb4. apply c0_c8cb0 in CW.
    eapply llvm_c0_k12fb4 with (want := b); try eassumption; try lia.
    right. right. split; [exact Hw|]. split; [lia|]. split; [lia|]. right. split; [lia|]. split; [exact Hok | exact Hlow].
  - c0_gob 0x132b8. rewrite ?swrap_addi by lia.
    eapply IH with (b := b + 1); try eassumption; try lia.
    intros b' Hb'. destruct (Z.eq_dec b' b) as [->|Hne]; [exact Hnok | apply Hlow; lia].
Qed.

Ltac c0_br := first [ c0_if | idtac ].

Ltac c0_fin w := eapply llvm_c0_k12fb4 with (want := w); try eassumption; try lia.

Lemma llvm_c0_k12f5c :
  forall (ra sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2 s5 s8 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m0 m : word -> option byte)
         (lo r nch base op nm nl i q c : Z) (j0 j1 bs jm NB slack : list byte) (s : list Z) (canary : word),
    range_free_contract -> reac_boxreg_declare_contract -> bcmp_contract -> strncmp_contract ->
    0 <= nch < 256 -> -128 <= base < 128 -> 0 <= op < 256 ->
    boxreg_inv bs -> length bs = 288%nat -> r mod 8 = 0 -> pf_img_free r 288 ->
    bytes_at rsegs m r bs -> wr_at rsegs m r 288 ->
    rw_cells rsegs m (bv_unsigned sp)
      [CB 8 j0; C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 (bx_fabric bs)); CB 8 j1;
       C8 (Z_to_bv 64 i); C8 (Z_to_bv 64 (bx_n bs)); CB 288 bs; CB 8 jm; C8 (Z_to_bv 64 q); C8 (Z_to_bv 64 c)] ->
    bytes_at rsegs m (bv_unsigned sp + 48) bs -> bv_unsigned sp mod 16 = 0 ->
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
      (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 r) (Z_to_bv 64 op) (Z_to_bv 64 nm) a1 a2 a3 a4 a5 a6 a7
               s2 (Z_to_bv 64 nch) (Z_to_bv 64 base) s5 (Z_to_bv 64 (base * 2 ^ 56))
               (Z_to_bv 64 (bx_fabric bs)) s8 (Z_to_bv 64 (-1 - r)) s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x12f5c) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2 s5 s8 s10 s11 t3 t4 t5 t6 F fc m0 m lo r nch base op nm nl i q c
    j0 j1 bs jm NB slack s canary RF DC BC SC Hnch Hbase Hop INV HL Hr8 HIF HB HWR CW HP Hsp16 ST Hlo HLO HSP Hr4 HRL
    Hnm Hsok Hslen HNB HNBe HNBl Hmod Hnlo Hnr MI TM Hfc HG1 HG2 MU WM.
  unfold GOT_GUARD, GUARD in *.
  pose proof INV as ((_ & HB1 & HB2 & HB3 & _) & _).
  assert (Hn : 0 <= bx_n bs <= 5) by exact HB1.
  assert (Hfb : 1 <= bx_fabric bs <= 40) by exact HB2.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp. change (2 ^ Z.of_N 64) with (2 ^ 64) in Rsp.
  step. step. rewrite bx_lts by lia.
  destruct (Z_lt_le_dec (bx_fabric bs) nch) as [T1|T1]; c0_br.
  { c0_gob 0x12fb4. c0_fin (-1). left. split; [intros ((_ & _ & Hle) & _); lia | reflexivity]. }
  step. step. step. rewrite c0_wtest by lia.
  destruct (Z.leb_spec 2 nch) as [W1|W1]; destruct (Z.leb_spec nch 40) as [W2|W2]; cbn [andb negb]; c0_br;
    try solve [c0_gob 0x12fb4; c0_fin (-1); left; split; [intros ((_ & Hr & _) & _); lia | reflexivity]].
  2,3: c0_gob 0x12fb4; c0_fin (-1); try (left; split; [intros ((_ & Hr & _) & _); lia | reflexivity]).
  step. rewrite bx_land1 by lia.
  step. rewrite bx_eqb by (pose proof (Z.mod_pos_bound nch 2); lia).
  destruct (Z.eqb_spec (nch mod 2) 0) as [E2|E2]; cbn [negb]; c0_br;
    [| c0_gob 0x12fb4; c0_fin (-1); try (left; split; [intros ((He & _) & _); apply c0_even_mod in He; lia | reflexivity])].
  assert (Hw : box_width_ok nch (bx_fabric bs)) by (split; [apply c0_even; exact E2 | lia]).
  step. step. step. rewrite bx_lts by lia.
  destruct (Z.ltb_spec 4 (bx_n bs)) as [N4|N4]; c0_br.
  { c0_gob 0x12fb4; c0_fin (-1); try (left; split; [intros (_ & Hn5); lia | reflexivity]). }
  step. rewrite c0_lts56 by lia.
  destruct (Z.ltb_spec base 0) as [Hneg|Hpos]; c0_br.
  - assert (HS : store_ok rsegs m sp 8 = true).
    { eapply rw_cells_store_ok_at with (k := 0%nat); [exact CW | reflexivity | reflexivity |].
      symmetry. apply wa_of_var. lia. }
    step.
    replace (write_to_mem m sp) with (write_to_mem m (wa (bv_unsigned sp + Z.of_nat 0)))
      by (f_equal; apply wa_of_var; lia).
    mem_after_store.
    c0_gob 0x132b8. rewrite c0_cnt by lia.
    eapply llvm_c0_loop with (k := Z.to_nat (bx_fabric bs - nch)) (b := 0); try eassumption; try lia.
    all: try (intros b' Hb'; lia).
  - c0_gob 0x13858.
    eapply evt_cut;
      [ unfold range_free_contract in RF;
        eapply RF with (t := bv_unsigned sp + 48) (base := base) (nch := nch) (fabric := bx_fabric bs) (bs := bs);
        first [ reflexivity | assumption | lia | (clear - Hsp16; Z.div_mod_to_equations; lia) ] | ].
    intros ms' (t0' & t1' & t2' & rr & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & E & HRF).
    subst ms'.
    c1_retpc.
    destruct HRF as [(-> & Hok) | (-> & Hnok)].
    + c0_gob 0x12fb4. rewrite ?c0_rf_one in CW |- *.
      c0_fin base.
      right. left. split; [exact Hw|]. split; [lia|]. split; [lia|]. left. split; [exact Hok | reflexivity].
    + c0_gob 0x12fb4. rewrite ?c0_rf_zero in CW |- *.
      c0_fin (-1).
      right. left. split; [exact Hw|]. split; [lia|]. split; [lia|]. right. split; [exact Hnok | reflexivity].
Qed.
